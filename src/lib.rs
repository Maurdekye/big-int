#![allow(incomplete_features)]
#![feature(min_specialization)]
#![feature(generic_const_exprs)]
//! ## `big_int` - Arbitrary precision, arbitrary base integer arithmetic library.
//!
//! ```
//! use big_int::*;
//!
//! let mut a: BigInt<10> = "9000000000000000000000000000000000000000".parse().unwrap();
//!
//! a /= 13.into();
//! assert_eq!(a, "692307692307692307692307692307692307692".parse().unwrap());
//!
//! let mut b: BigInt<16> = a.convert();
//! assert_eq!(b, "208D59C8D8669EDC306F76344EC4EC4EC".parse().unwrap());
//!
//! b >>= 16.into();
//! let c: BigInt<2> = b.convert();
//! assert_eq!(c, "100000100011010101100111001000110110000110011010011110110111000011".parse().unwrap());
//! ```

use std::{
    cmp::Ordering,
    fmt::Display,
    ops::{
        Add, AddAssign, Deref, DerefMut, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr,
        ShrAssign, Sub, SubAssign,
    },
    str::FromStr,
};

use error::{BigIntError, ParseError};
use get_back::GetBack;

pub mod base64;
pub mod error;
mod get_back;
pub mod loose;
pub mod tight;

pub const STANDARD_ALPHABET: &str =
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/";

pub type Digit = u64;
pub type DoubleDigit = u128;

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Sign {
    Positive,
    Negative,
}

impl Neg for Sign {
    type Output = Sign;

    fn neg(self) -> Self::Output {
        match self {
            Self::Positive => Self::Negative,
            Self::Negative => Self::Positive,
        }
    }
}

impl Mul for Sign {
    type Output = Sign;

    fn mul(self, rhs: Self) -> Self::Output {
        if self == rhs {
            Self::Negative
        } else {
            Self::Positive
        }
    }
}

pub trait BigIntBuilder<const BASE: usize> {
    fn new() -> Self;
    fn push_front(&mut self, digit: Digit);
    fn push_back(&mut self, digit: Digit);
    fn is_empty(&self) -> bool;
    fn with_sign(self, sign: Sign) -> Self;
}

impl<const BASE: usize, BB, B> From<BB> for BigInt<BASE, B>
where
    BB: BigIntBuilder<{ BASE }>,
    B: BigIntImplementation<{ BASE }> + From<BB>,
{
    fn from(value: BB) -> Self {
        Self(value.into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigInt<const BASE: usize, B: BigIntImplementation<{ BASE }>>(pub B);

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> BigInt<BASE, B> {
    pub fn zero() -> Self {
        Self(B::zero())
    }

    pub fn with_sign(self, sign: Sign) -> Self {
        Self(self.0.with_sign(sign))
    }

    pub fn shl(self, amount: usize) -> Self {
        Self(self.0.shl(amount))
    }

    pub fn shl_assign(&mut self, amount: usize) {
        self.0.shl_assign(amount)
    }

    pub fn shr(self, amount: usize) -> Self {
        Self(self.0.shr(amount))
    }

    pub fn shr_assign(&mut self, amount: usize) {
        self.0.shr_assign(amount)
    }

    pub fn normalized(self) -> Self {
        Self(self.0.normalized())
    }

    pub fn parse(value: &str, alphabet: &str) -> Result<Self, ParseError> {
        B::parse(value, alphabet).map(Self)
    }

    /// Divide one int by another, returning the quotient & remainder as a pair,
    /// or an error if dividing by zero. This algorithm has a different time complexity
    /// than `BigInt::div_rem_lowmem` which makes it faster for most use cases, but also uses more memory.
    ///
    /// `b` - base\
    /// `d` - number of digits in quotient\
    /// Time complexity: `O(d * log(b))`\
    /// Memory complexity: `O(d * log(b))`\
    ///
    /// ```
    /// use big_int::loose::*;
    ///
    /// let a: BigInt<10> = 999_999_999.into();
    /// let b = 56_789.into();
    /// assert_eq!(a.div_rem(b), Ok((17_609.into(), 2_498.into())));
    /// ```
    pub fn div_rem(mut self, mut other: Self) -> Result<(Self, Self), BigIntError> {
        if other.clone().normalized() == Self::zero() {
            return Err(BigIntError::DivisionByZero);
        }
        if other.len() > self.len() {
            return Ok((Self::zero(), self));
        }
        let sign = self.sign() * other.sign();
        self.set_sign(Sign::Positive);
        other.set_sign(Sign::Positive);
        let quot_digits = self.len() - other.len() + 1;
        let mut quot = B::Builder::new();
        let mut prod = Self::zero();
        let mut addend = other.clone().shl(quot_digits);
        let mut addends = Vec::new();
        let mut power = 1;
        while power < BASE {
            addends.push(addend.clone());
            addend += addend.clone();
            power <<= 1;
        }

        for _ in 0..quot_digits {
            let mut digit_value = 0;
            for power in (0..addends.len()).rev() {
                let new_prod = prod.clone() + addends[power].clone();
                if new_prod <= self {
                    digit_value += 1 << power;
                    prod = new_prod;
                }
                addends[power].shr_assign(1);
            }
            quot.push_front(digit_value);
        }

        let mut rem = self - prod;
        if rem != Self::zero() {
            rem.set_sign(sign);
        }

        Ok((quot.with_sign(sign).into(), rem))
    }

    /// Convert an int from its own base to another target base.
    ///
    /// ```
    /// use big_int::loose::*;
    ///
    /// assert_eq!(
    ///     BigInt::<10>::from(99825).convert(),
    ///     BigInt::<16>::from(99825)
    /// );
    /// ```
    pub fn convert<const TO: usize, T: BigIntImplementation<{ TO }>>(mut self) -> BigInt<TO, T> {
        if BASE == TO {
            let mut result = T::Builder::new();
            for digit in self.iter() {
                result.push_back(digit);
            }
            BigInt(result.with_sign(self.sign()).into())
        } else {
            let sign = self.sign();
            let mut result = T::Builder::new();
            self.set_sign(Sign::Positive);
            let to_base = Self::from(TO);
            while self >= to_base {
                let (quot, rem) = self.div_rem(to_base.clone()).unwrap();
                self = quot;
                result.push_front(Digit::from(rem));
            }
            result.push_front(Digit::from(self));
            BigInt(result.with_sign(sign).into())
        }
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Deref for BigInt<BASE, B> {
    type Target = B;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> DerefMut for BigInt<BASE, B> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> GetBack for BigInt<BASE, B> {
    type Item = Digit;

    fn get_back(&self, index: usize) -> Option<Self::Item> {
        self.len()
            .checked_sub(index)
            .and_then(|index| self.get_digit(index))
    }
}

pub trait BigIntImplementation<const BASE: usize>
where
    Self: From<Self::Builder> + Clone + PartialEq + Eq,
{
    type Builder: BigIntBuilder<{ BASE }>;
    type DigitIterator<'a>: DoubleEndedIterator<Item = Digit> where Self: 'a;

    /// The length of the big int.
    fn len(&self) -> usize;

    /// Get the digit of the big int at position `digit`,
    /// or None if the number does not have that many digits / the digit is negative.
    fn get_digit(&self, digit: usize) -> Option<Digit>;

    /// Set the digit of the big int to `value` at position `digit`.
    /// Return `Some(Digit)` of the digit's existing value, or None if no digit was
    /// set.
    fn set_digit(&mut self, digit: usize, value: Digit) -> Option<Digit>;

    /// The constant zero represented as a big int.
    fn zero() -> Self;

    /// The sign of the big int.
    fn sign(&self) -> Sign;

    /// The big int with the desired parity of `sign`.
    fn with_sign(self, sign: Sign) -> Self;

    /// Set the sign of the big int to `sign`.
    fn set_sign(&mut self, sign: Sign);

    fn push_back(&mut self, digit: Digit);
    fn push_front(&mut self, digit: Digit);

    fn shr(self, amount: usize) -> Self;
    fn shr_assign(&mut self, amount: usize);

    fn shl(self, amount: usize) -> Self;
    fn shl_assign(&mut self, amount: usize);

    fn iter<'a>(&'a self) -> Self::DigitIterator<'a>;

    /// Return a normalized version of the int. Remove trailing zeros, and disable the parity flag
    /// if the resulting number is zero.
    ///
    /// ```
    /// use big_int::loose::*;
    ///
    /// let n = unsafe { BigInt::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
    /// assert_eq!(n.normalized(), 83.into());
    /// ```
    fn normalized(self) -> Self;

    /// Normalize a `Loose` big int in place. Remove trailing zeros, and disable the parity flag
    /// if the resulting number is zero.
    ///
    /// ```
    /// use big_int::loose::*;
    ///
    /// let mut n = unsafe { BigInt::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
    /// n.normalize();
    /// assert_eq!(n, 83.into());
    /// ```
    fn normalize(&mut self) {
        *self = self.clone().normalized();
    }

    /// Convert a big int to a printable string using the provided alphabet `alphabet`.
    /// `Display` uses this method with the default alphabet `STANDARD_ALPHABET`.
    ///
    /// ```
    /// use big_int::loose::*;
    ///
    /// assert_eq!(
    ///     BigInt::<10>::from(6012).display(STANDARD_ALPHABET).unwrap(),
    ///     "6012".to_string()
    /// );
    /// ```
    fn display(&self, alphabet: &str) -> Result<String, BigIntError> {
        let digits = self
            .iter()
            .map(|digit| {
                alphabet
                    .chars()
                    .nth(digit as usize)
                    .ok_or(BigIntError::BaseTooHigh(BASE, alphabet.len()))
            })
            .collect::<Result<String, _>>()?;
        if self.sign() == Sign::Negative {
            Ok(format!("-{digits}"))
        } else {
            Ok(digits)
        }
    }

    /// Parse a `Loose` big int from a `value: &str`, referencing the provided `alphabet`
    /// to determine what characters represent which digits. `FromStr` uses this method
    /// with the default alphabet `STANDARD_ALPHABET`.
    ///
    /// ```
    /// use big_int::loose::*;
    ///
    /// assert_eq!(BigInt::parse("125", STANDARD_ALPHABET), Ok(BigInt::<10>::from(125)));
    /// ```
    fn parse(value: &str, alphabet: &str) -> Result<Self, ParseError> {
        let mut builder = Self::Builder::new();
        let (sign, chars) = match value.chars().next() {
            Some('-') => (Sign::Negative, value.chars().skip(1)),
            Some(_) => (Sign::Positive, value.chars().skip(0)),
            None => return Err(ParseError::NotEnoughCharacters),
        };
        for char in chars {
            match alphabet.chars().position(|c| c == char) {
                Some(pos) => {
                    if pos >= BASE {
                        return Err(ParseError::DigitTooLarge(char, pos, BASE));
                    } else {
                        builder.push_back(pos as Digit);
                    }
                }
                None => return Err(ParseError::UnrecognizedCharacter(char)),
            }
        }
        if builder.is_empty() {
            Err(ParseError::NotEnoughCharacters)
        } else {
            Ok(builder.with_sign(sign).into())
        }
    }
}

// default impl<const BASE: usize, F, T> From<BigInt<BASE, F>> for BigInt<BASE, T>
// where
//     F: BigIntImplementation<{ BASE }>,
//     T: BigIntImplementation<{ BASE }>,
// {
//     fn from(value: BigInt<BASE, F>) -> Self {
//         let mut result = T::Builder::new();
//         for digit in value.iter() {
//             result.push_back(digit);
//         }
//         result.sign(value).into()
//     }
// }

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Default for BigInt<BASE, B> {
    fn default() -> Self {
        Self::zero()
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> FromStr for BigInt<BASE, B> {
    type Err = BigIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        B::parse(s, STANDARD_ALPHABET)
            .map_err(BigIntError::ParseFailed)
            .map(BigInt)
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<u128> for BigInt<BASE, B> {
    fn from(mut value: u128) -> Self {
        let base = BASE as u128;
        let mut result = B::Builder::new();
        while value >= base {
            let (new_value, rem) = (value / base, value % base);
            value = new_value;
            result.push_front(rem as Digit);
        }
        result.push_front(value as Digit);
        BigInt(result.into())
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<i128> for BigInt<BASE, B> {
    fn from(value: i128) -> Self {
        if value < 0 {
            Self::from((-value) as u128).with_sign(Sign::Negative)
        } else {
            Self::from(value as u128)
        }
    }
}

macro_rules! bigint_from_int {
    ($b:ident; $($i:ident),*) => {
        $(
            impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<$i> for BigInt<BASE, B> {
                fn from(value: $i) -> Self {
                    (value as $b).into()
                }
            }
        )*
    };
}

bigint_from_int!(i128; i8, i16, i32, i64, isize);
bigint_from_int!(u128; u8, u16, u32, u64, usize);

macro_rules! int_from_bigint {
    ($(($i:ident, $u:ident)),*) => {
        $(
            impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<BigInt<BASE, B>> for $i {
                fn from(value: BigInt<BASE, B>) -> Self {
                    let mut total: $i = 0;
                    let mut place: $i = 0;
                    for digit in value.iter().rev() {
                        place = if place == 0 { 1 } else { place * BASE as $i };
                        total += (digit as $i) * place;
                    }
                    if value.sign() == Sign::Negative {
                        total = -total;
                    }
                    total
                }
            }

            impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<BigInt<BASE, B>> for $u {
                fn from(value: BigInt<BASE, B>) -> Self {
                    $i::from(value) as $u
                }
            }
        )*
    };
}

int_from_bigint!(
    (i128, u128),
    (i64, u64),
    (i32, u32),
    (i16, u16),
    (i8, u8),
    (isize, usize)
);

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Display for BigInt<BASE, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.display(STANDARD_ALPHABET)
                .map_err(|_| std::fmt::Error)?
        )
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Neg for BigInt<BASE, B> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let sign = -self.sign();
        self.with_sign(-sign)
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Add for BigInt<BASE, B> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.0 != rhs.0 {
            self - (-rhs)
        } else {
            let mut carry = 0;
            let mut result = B::Builder::new();
            for i in 1.. {
                match (self.get_back(i), rhs.get_back(i), carry) {
                    (None, None, 0) => break,
                    (left_digit, right_digit, carry_in) => {
                        let left_digit = left_digit.unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.unwrap_or_default() as DoubleDigit;
                        let mut sum = left_digit + right_digit + carry_in;
                        if sum >= BASE as DoubleDigit {
                            sum -= BASE as DoubleDigit;
                            carry = 1;
                        } else {
                            carry = 0;
                        }
                        result.push_front(sum as Digit);
                    }
                }
            }
            result.with_sign(self.sign()).into()
        }
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> AddAssign for BigInt<BASE, B> {
    fn add_assign(&mut self, rhs: Self) {
        if self.0 != rhs.0 {
            *self -= -rhs;
        } else {
            let self_len = self.len();
            let mut carry = 0;
            for i in 1.. {
                match (self.get_back(i), rhs.get_back(i), carry) {
                    (None, None, 0) => break,
                    (left_digit, right_digit, carry_in) => {
                        let left_digit = left_digit.unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.unwrap_or_default() as DoubleDigit;
                        let mut sum = left_digit + right_digit + carry_in;
                        if sum >= BASE as DoubleDigit {
                            sum -= BASE as DoubleDigit;
                            carry = 1;
                        } else {
                            carry = 0;
                        }
                        if i <= self_len {
                            self.set_digit(self_len - i, sum as Digit);
                        } else {
                            self.push_front(sum as Digit);
                        }
                    }
                }
            }
        }
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Sub for BigInt<BASE, B> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        if self.0 != rhs.0 {
            self + (-rhs)
        } else if rhs > self {
            -(rhs - self)
        } else {
            let mut result = B::Builder::new();
            for i in 1.. {
                match (self.get_back(i), rhs.get_back(i)) {
                    (None, None) => break,
                    (left_digit, right_digit) => {
                        let mut left_digit = left_digit.unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.unwrap_or_default() as DoubleDigit;
                        if left_digit < right_digit {
                            for j in i + 1.. {
                                match self.get_back(j) {
                                    None => unreachable!("big int subtraction with overflow"),
                                    Some(0) => {
                                        self.set_digit(j, (BASE - 1) as Digit);
                                    }
                                    Some(digit) => {
                                        self.set_digit(j, digit - 1);
                                        break;
                                    }
                                }
                            }
                            left_digit += BASE as DoubleDigit;
                        }
                        result.push_front((left_digit - right_digit) as Digit);
                    }
                }
            }
            result.with_sign(self.sign()).into()
        }
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> SubAssign for BigInt<BASE, B> {
    fn sub_assign(&mut self, mut rhs: Self) {
        if self.0 != rhs.0 {
            *self += -rhs;
        } else if rhs > *self {
            rhs -= self.clone();
            *self = -rhs;
        } else {
            let self_len = self.len();
            for i in 1.. {
                match (self.get_back(i), rhs.get_back(i)) {
                    (None, None) => break,
                    (left_digit, right_digit) => {
                        let mut left_digit = left_digit.unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.unwrap_or_default() as DoubleDigit;
                        if left_digit < right_digit {
                            for j in i + 1.. {
                                match self.get_back(j) {
                                    None => unreachable!("big int subtraction with overflow"),
                                    Some(0) => {
                                        self.set_digit(j, (BASE - 1) as Digit);
                                    }
                                    Some(digit) => {
                                        self.set_digit(j, digit - 1);
                                        break;
                                    }
                                }
                            }
                            left_digit += BASE as DoubleDigit;
                        }
                        let difference = (left_digit - right_digit) as Digit;
                        if i <= self_len {
                            self.set_digit(self_len - i, difference);
                        } else {
                            self.push_front(difference);
                        }
                    }
                }
            }
        }
        self.normalize();
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Mul for BigInt<BASE, B> {
    type Output = Self;

    fn mul(mut self, mut rhs: Self) -> Self::Output {
        let sign = self.sign() * rhs.sign();
        self.set_sign(Sign::Positive);
        rhs.set_sign(Sign::Positive);
        let mut result = Self::zero();
        for i in 1.. {
            if let Some(digit) = self.get_back(i) {
                for _ in 0..digit {
                    result += rhs.clone();
                }
                rhs.shl_assign(1);
            } else {
                break;
            }
        }
        result.normalized().with_sign(sign)
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> MulAssign for BigInt<BASE, B> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Div for BigInt<BASE, B> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).unwrap().0
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> DivAssign for BigInt<BASE, B> {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Shl for BigInt<BASE, B> {
    type Output = Self;

    /// Shifts a `Loose` big int left by multiples of its `BASE` (not by 2).
    fn shl(self, rhs: Self) -> Self::Output {
        self.shl(rhs.into())
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> ShlAssign for BigInt<BASE, B> {
    /// Shifts a big int left by multiples of its `BASE` (not by 2).
    fn shl_assign(&mut self, rhs: Self) {
        self.shl_assign(rhs.into());
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Shr for BigInt<BASE, B> {
    type Output = Self;

    /// Shifts a big int right by multiples of its `BASE` (not by 2).
    fn shr(self, rhs: Self) -> Self::Output {
        self.shr(rhs.into())
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> ShrAssign for BigInt<BASE, B> {
    /// Shifts a big int right by multiples of its `BASE` (not by 2).
    fn shr_assign(&mut self, rhs: Self) {
        self.shr_assign(rhs.into())
    }
}

impl<const BASE: usize, B> Ord for BigInt<BASE, B>
where
    B: BigIntImplementation<{ BASE }>,
{
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.sign(), other.sign()) {
            (Sign::Positive, Sign::Negative) => Ordering::Greater,
            (Sign::Negative, Sign::Positive) => Ordering::Less,
            (Sign::Positive, Sign::Positive) => cmp(&self, &other),
            (Sign::Negative, Sign::Negative) => cmp(&other, &self),
        }
    }
}

/// Helper function used for comparing two big ints.
fn cmp<const BASE: usize, B>(a: &BigInt<BASE, B>, b: &BigInt<BASE, B>) -> Ordering
where
    B: BigIntImplementation<{ BASE }>,
{
    match a.len().cmp(&b.len()) {
        Ordering::Equal => {
            for (a_digit, b_digit) in a.iter().zip(b.iter()) {
                match a_digit.cmp(&b_digit) {
                    Ordering::Equal => {}
                    ordering => return ordering,
                }
            }
            Ordering::Equal
        }
        order => order,
    }
}

impl<const BASE: usize, B> PartialOrd for BigInt<BASE, B>
where
    B: BigIntImplementation<{ BASE }>,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
