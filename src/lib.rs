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
    collections::VecDeque,
    fmt::Display,
    ops::{
        Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};
use thiserror::Error;

pub const STANDARD_ALPHABET: &str =
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/";
pub const BASE64_ALPHABET: &str =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

#[derive(Error, Debug, PartialEq, Eq)]
pub enum BigIntError {
    #[error("base too large: number has {0} digits, alphabet can only represent {1} digits")]
    BaseTooHigh(usize, usize),
    #[error("parsing failed: {0}")]
    ParseFailed(ParseError),
    #[error("division by zero")]
    DivisionByZero,
}

#[derive(Error, Debug, PartialEq, Eq)]
pub enum ParseError {
    #[error("unrecognized character: {0:?}")]
    UnrecognizedCharacter(char),
    #[error("not enough characters")]
    NotEnoughCharacters,
    #[error("char {0:?} is {1}; too large to be represented in base {2}")]
    DigitTooLarge(char, usize, usize),
}

/// Safely retrieve items from a collection with negative indexing.
pub trait GetBack {
    type Item;

    /// Safely retrieve items from a collection with negative indexing.
    /// Returns `None` if the index is larger than the length of the collection.
    fn get_back(&self, index: usize) -> Option<&Self::Item>;
}

impl<T> GetBack for Vec<T> {
    type Item = T;
    fn get_back(&self, index: usize) -> Option<&Self::Item> {
        self.len()
            .checked_sub(index)
            .and_then(|index| self.get(index))
    }
}

/// Safely retrieve a mutable reference from a collection with negative indexing.
pub trait GetBackMut {
    type Item;

    /// Safely retrieve a mutable reference from a collection with negative indexing.
    /// Returns `None` if the index is larger than the length of the collection.
    fn get_back_mut(&mut self, index: usize) -> Option<&mut Self::Item>;
}

impl<T> GetBackMut for Vec<T> {
    type Item = T;
    fn get_back_mut(&mut self, index: usize) -> Option<&mut Self::Item> {
        self.len()
            .checked_sub(index)
            .and_then(|index| self.get_mut(index))
    }
}

/// change these if you want to represent bases larger than 256
pub type Digit = u8;
/// this must be twice the size of Digit (for overflow prevention)
pub type DoubleDigit = u16;

/// `BigInt`: represents an arbitrary-size integer in base `BASE`.
///
/// `BASE` may be anywhere from 2-256.
/// If you would like to be able to represent a larger base than 256, then increase `Digit`
/// and `DoubleDigit` as needed, as high as `u64` + `u128`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigInt<const BASE: usize>(bool, Vec<Digit>);

impl<const BASE: usize> BigInt<BASE> {
    /// Create a new `BigInt` directly from a `Vec` of individual digits.
    ///
    /// Ensure the resulting int is properly normalized, and that no digits are greater than or
    /// equal to the base, to preserve soundness.
    ///
    /// To construct a negative `BigInt` from raw parts, simply apply the negation
    /// operator (`-`) afterwards.
    ///
    /// ```
    /// use big_int::*;
    ///
    /// assert_eq!(
    ///     unsafe { -BigInt::<10>::from_raw_parts(vec![1, 5]) },
    ///     (-15).into()
    /// );
    /// ```
    pub unsafe fn from_raw_parts(digits: Vec<Digit>) -> Self {
        BigInt(false, digits)
    }

    /// The constant zero represented as a `BigInt`.
    pub fn zero() -> Self {
        BigInt(false, vec![0])
    }

    /// Convert a `BigInt` to a printable string using the provided alphabet `alphabet`.
    /// `Display` uses this method with the default alphabet `STANDARD_ALPHABET`.
    ///
    /// ```
    /// use big_int::*;
    ///
    /// assert_eq!(
    ///     BigInt::<10>::from(6012).display(STANDARD_ALPHABET).unwrap(),
    ///     "6012".to_string()
    /// );
    /// ```
    pub fn display(&self, alphabet: &str) -> Result<String, BigIntError> {
        let digits = self
            .1
            .iter()
            .map(|digit| {
                alphabet
                    .chars()
                    .nth(*digit as usize)
                    .ok_or(BigIntError::BaseTooHigh(BASE, alphabet.len()))
            })
            .collect::<Result<String, _>>()?;
        if self.0 {
            Ok(format!("-{digits}"))
        } else {
            Ok(digits)
        }
    }

    /// Return a normalized version of the `BigInt`. Remove trailing zeros, and disable the parity flag
    /// if the resulting number is zero.
    ///
    /// ```
    /// use big_int::*;
    ///
    /// let n = unsafe { BigInt::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
    /// assert_eq!(n.normalized(), 83.into());
    /// ```
    pub fn normalized(self) -> Self {
        match self.1.iter().position(|digit| *digit != 0) {
            None => BigInt::zero(),
            Some(pos @ 1..) => BigInt(self.0, self.1[pos..].to_vec()),
            _ => self,
        }
    }

    /// Normalize a `BigInt` in place. Remove trailing zeros, and disable the parity flag
    /// if the resulting number is zero.
    ///
    /// ```
    /// use big_int::*;
    ///
    /// let mut n = unsafe { BigInt::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
    /// n.normalize();
    /// assert_eq!(n, 83.into());
    /// ```
    pub fn normalize(&mut self) {
        match self.1.iter().position(|digit| *digit != 0) {
            None => *self = BigInt(false, vec![0]),
            Some(pos @ 1..) => self.1 = self.1[pos..].to_vec(),
            _ => {}
        }
    }

    /// Parse a `BigInt` from a `value: &str`, referencing the provided `alphabet`
    /// to determine what characters represent which digits. `FromStr` uses this method
    /// with the default alphabet `STANDARD_ALPHABET`.
    ///
    /// ```
    /// use big_int::*;
    ///
    /// assert_eq!(BigInt::parse("125", STANDARD_ALPHABET), Ok(BigInt::<10>::from(125)));
    /// ```
    pub fn parse(value: &str, alphabet: &str) -> Result<Self, ParseError> {
        let mut digits = VecDeque::new();
        let (sign, chars) = match value.chars().next() {
            Some('-') => (true, value.chars().skip(1)),
            Some(_) => (false, value.chars().skip(0)),
            None => return Err(ParseError::NotEnoughCharacters),
        };
        for char in chars {
            match alphabet.chars().position(|c| c == char) {
                Some(pos) => {
                    if pos >= BASE {
                        return Err(ParseError::DigitTooLarge(char, pos, BASE));
                    } else {
                        digits.push_back(pos as Digit);
                    }
                }
                None => return Err(ParseError::UnrecognizedCharacter(char)),
            }
        }
        if digits.is_empty() {
            Err(ParseError::NotEnoughCharacters)
        } else {
            Ok(BigInt(sign, digits.into()).normalized())
        }
    }

    /// Divide one `BigInt` by another, returning the quotient & remainder as a pair,
    /// or an error if dividing by zero. This algorithm has a different time complexity
    /// than `BigInt::div_rem_lowmem` which makes it faster for most use cases, but also uses more memory.
    ///
    /// `b` - base\
    /// `d` - number of digits in quotient\
    /// Time complexity: `O(d * log(b))`\
    /// Memory complexity: `O(d * log(b))`\
    ///
    /// ```
    /// use big_int::*;
    ///
    /// let a: BigInt<10> = 999_999_999.into();
    /// let b = 56_789.into();
    /// assert_eq!(a.div_rem(b), Ok((17_609.into(), 2_498.into())));
    /// ```
    pub fn div_rem(mut self, mut other: Self) -> Result<(Self, Self), BigIntError> {
        if other.clone().normalized() == BigInt::zero() {
            return Err(BigIntError::DivisionByZero);
        }
        if other.1.len() > self.1.len() {
            return Ok((BigInt(false, vec![0]), self));
        }
        let sign = self.0 != other.0;
        self.0 = false;
        other.0 = false;
        let quot_digits = self.1.len() - other.1.len() + 1;
        let mut quot = BigInt(false, vec![0; quot_digits]);
        let mut prod = BigInt::zero();
        let mut addend = BigInt(false, [other.1, vec![0; quot_digits - 1]].concat());
        let mut addends = Vec::new();
        let mut power = 1;
        while power < BASE {
            addends.push(addend.clone());
            addend += addend.clone();
            power <<= 1;
        }

        for digit in 0..quot.1.len() {
            let mut digit_value = 0;
            for power in (0..addends.len()).rev() {
                let new_prod = prod.clone() + addends[power].clone();
                if new_prod <= self {
                    digit_value += 1 << power;
                    prod = new_prod;
                }
                addends[power].1.pop();
            }
            quot.1[digit] = digit_value;
        }

        quot.0 = sign;
        let mut rem = self - prod;
        if rem != BigInt::zero() {
            rem.0 = sign;
        }

        Ok((quot.normalized(), rem))
    }

    /// Divide one `BigInt` by another, returning the quotient & remainder as a pair,
    /// or an error if dividing by zero.
    ///
    /// `b` - base\
    /// `d` - number of digits in quotient\
    /// Time complexity: `O(d * b)`\
    /// Memory complexity: `O(d)`\
    ///
    /// ```
    /// use big_int::*;
    ///
    /// let a: BigInt<10> = 999_999_999.into();
    /// let b = 56_789.into();
    /// assert_eq!(a.div_rem_lowmem(b), Ok((17_609.into(), 2_498.into())));
    /// ```
    pub fn div_rem_lowmem(mut self, mut other: Self) -> Result<(Self, Self), BigIntError> {
        if other.clone().normalized() == BigInt::zero() {
            return Err(BigIntError::DivisionByZero);
        }
        if other.1.len() > self.1.len() {
            return Ok((BigInt(false, vec![0]), self));
        }
        let sign = self.0 != other.0;
        self.0 = false;
        other.0 = false;
        let quot_digits = self.1.len() - other.1.len() + 1;
        let mut quot = BigInt(false, vec![0; quot_digits]);
        let mut addend = BigInt(false, [other.1, vec![0; quot_digits - 1]].concat());
        let mut prod = BigInt::zero();

        for digit in 0..quot.1.len() {
            for digit_value in 0..BASE {
                let new_prod = prod.clone() + addend.clone();
                if new_prod > self {
                    quot.1[digit] = digit_value as Digit;
                    break;
                } else {
                    prod = new_prod;
                }
            }
            addend.1.pop();
        }

        quot.0 = sign;
        let mut rem = self - prod;
        if rem != BigInt::zero() {
            rem.0 = sign;
        }

        Ok((quot.normalized(), rem))
    }

    /// Convert a `BigInt` from its own base to another target base using the provided division function.
    /// You should prefer to use one of either `BigInt::convert` or `BigInt::convert_lowmem` instead of this.
    fn convert_with<const TO: usize>(
        mut self,
        div_fn: impl Fn(BigInt<BASE>, BigInt<BASE>) -> Result<(BigInt<BASE>, BigInt<BASE>), BigIntError>,
    ) -> BigInt<TO> {
        let sign = self.0;
        self.0 = false;
        let mut digits = VecDeque::new();
        let to_base = BigInt::<BASE>::from(TO);
        while self >= to_base {
            let (quot, rem) = div_fn(self, to_base.clone()).unwrap();
            self = quot;
            digits.push_front(Digit::from(rem));
        }
        digits.push_front(Digit::from(self));
        BigInt::<TO>(sign, digits.into()).normalized()
    }

    /// Convert a `BigInt` from its own base to another target base.
    ///
    /// ```
    /// use big_int::*;
    ///
    /// assert_eq!(
    ///     BigInt::<10>::from(99825).convert(),
    ///     BigInt::<16>::from(99825)
    /// );
    /// ```
    pub fn convert<const TO: usize>(self) -> BigInt<TO> {
        self.convert_with(BigInt::div_rem)
    }

    /// Convert a `BigInt` from its own base to another target base using `BigInt::div_rem_lowmem`.
    /// Has lower memory usage, but greater time complexity.
    ///
    /// ```
    /// use big_int::*;
    ///
    /// assert_eq!(
    ///     BigInt::<10>::from(99825).convert_lowmem(),
    ///     BigInt::<16>::from(99825)
    /// );
    /// ```
    pub fn convert_lowmem<const TO: usize>(self) -> BigInt<TO> {
        self.convert_with(BigInt::div_rem_lowmem)
    }
}

impl<const BASE: usize> Default for BigInt<BASE> {
    fn default() -> Self {
        BigInt::zero()
    }
}

impl<const BASE: usize> FromStr for BigInt<BASE> {
    type Err = BigIntError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s, STANDARD_ALPHABET).map_err(BigIntError::ParseFailed)
    }
}

impl<const BASE: usize> From<u128> for BigInt<BASE> {
    fn from(mut value: u128) -> Self {
        let base = BASE as u128;
        let mut result = VecDeque::new();
        while value >= base {
            let (new_value, rem) = (value / base, value % base);
            value = new_value;
            result.push_front(rem as Digit);
        }
        result.push_front(value as Digit);
        BigInt(false, result.into()).normalized()
    }
}

impl<const BASE: usize> From<i128> for BigInt<BASE> {
    fn from(value: i128) -> Self {
        if value < 0 {
            let mut bigint = BigInt::<BASE>::from((-value) as u128);
            bigint.0 = true;
            bigint
        } else {
            BigInt::<BASE>::from(value as u128)
        }
    }
}

macro_rules! bigint_from_int {
    ($b:ident; $($i:ident),*) => {
        $(
            impl<const BASE: usize> From<$i> for BigInt<BASE> {
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
            impl<const BASE: usize> From<BigInt<BASE>> for $i {
                fn from(value: BigInt<BASE>) -> Self {
                    let mut digits = value.1;
                    let mut total: $i = 0;
                    let mut place: $i = 1;
                    while let Some(digit) = digits.pop() {
                        total += (digit as $i) * place;
                        place *= BASE as $i;
                    }
                    if value.0 {
                        total = -total;
                    }
                    total
                }
            }

            impl<const BASE: usize> From<BigInt<BASE>> for $u {
                fn from(value: BigInt<BASE>) -> Self {
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

impl<const BASE: usize> Display for BigInt<BASE> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.display(STANDARD_ALPHABET)
                .map_err(|_| std::fmt::Error)?
        )
    }
}

impl<const BASE: usize> Neg for BigInt<BASE> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        BigInt(!self.0, self.1)
    }
}

impl<const BASE: usize> Add for BigInt<BASE> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.0 != rhs.0 {
            self - (-rhs)
        } else {
            let mut carry = 0;
            let mut result = VecDeque::with_capacity(self.1.len().max(rhs.1.len()) + 1);
            for i in 1.. {
                match (self.1.get_back(i), rhs.1.get_back(i), carry) {
                    (None, None, 0) => break,
                    (left_digit, right_digit, carry_in) => {
                        let left_digit = left_digit.copied().unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.copied().unwrap_or_default() as DoubleDigit;
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
            BigInt(self.0, result.into()).normalized()
        }
    }
}

impl<const BASE: usize> AddAssign for BigInt<BASE> {
    fn add_assign(&mut self, rhs: Self) {
        if self.0 != rhs.0 {
            *self -= -rhs;
        } else {
            let self_len = self.1.len();
            let mut carry = 0;
            for i in 1.. {
                match (self.1.get_back(i), rhs.1.get_back(i), carry) {
                    (None, None, 0) => break,
                    (left_digit, right_digit, carry_in) => {
                        let left_digit = left_digit.copied().unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.copied().unwrap_or_default() as DoubleDigit;
                        let mut sum = left_digit + right_digit + carry_in;
                        if sum >= BASE as DoubleDigit {
                            sum -= BASE as DoubleDigit;
                            carry = 1;
                        } else {
                            carry = 0;
                        }
                        if i <= self_len {
                            self.1[self_len - i] = sum as Digit;
                        } else {
                            self.1.insert(0, sum as Digit);
                        }
                    }
                }
            }
        }
    }
}

impl<const BASE: usize> Sub for BigInt<BASE> {
    type Output = Self;

    fn sub(mut self, rhs: Self) -> Self::Output {
        if self.0 != rhs.0 {
            self + (-rhs)
        } else if rhs > self {
            -(rhs - self)
        } else {
            let self_len = self.1.len();
            let mut result = VecDeque::with_capacity(self_len.max(rhs.1.len()) + 1);
            for i in 1.. {
                match (self.1.get_back(i), rhs.1.get_back(i)) {
                    (None, None) => break,
                    (left_digit, right_digit) => {
                        let mut left_digit = left_digit.copied().unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.copied().unwrap_or_default() as DoubleDigit;
                        if left_digit < right_digit {
                            for j in i + 1.. {
                                match self.1.get_back_mut(j) {
                                    None => unreachable!("`BigInt` subtraction with overflow"),
                                    Some(digit @ 0) => *digit = (BASE - 1) as Digit,
                                    Some(digit) => {
                                        *digit -= 1;
                                        break;
                                    }
                                }
                            }
                            left_digit += BASE as DoubleDigit;
                        }
                        let difference = left_digit - right_digit;
                        result.push_front(difference as Digit);
                    }
                }
            }
            BigInt(self.0, result.into()).normalized()
        }
    }
}

impl<const BASE: usize> SubAssign for BigInt<BASE> {
    fn sub_assign(&mut self, mut rhs: Self) {
        if self.0 != rhs.0 {
            *self += -rhs;
        } else if rhs > *self {
            rhs -= self.clone();
            *self = -rhs;
        } else {
            let self_len = self.1.len();
            for i in 1.. {
                match (self.1.get_back(i), rhs.1.get_back(i)) {
                    (None, None) => break,
                    (left_digit, right_digit) => {
                        let mut left_digit = left_digit.copied().unwrap_or_default() as DoubleDigit;
                        let right_digit = right_digit.copied().unwrap_or_default() as DoubleDigit;
                        if left_digit < right_digit {
                            for j in i + 1.. {
                                match self.1.get_back_mut(j) {
                                    None => unreachable!("subtraction with overflow"),
                                    Some(digit @ 0) => *digit = (BASE - 1) as Digit,
                                    Some(digit) => {
                                        *digit -= 1;
                                        break;
                                    }
                                }
                            }
                            left_digit += BASE as DoubleDigit;
                        }
                        self.1[self_len - i] = (left_digit - right_digit) as Digit;
                    }
                }
            }
        }
        self.normalize();
    }
}

impl<const BASE: usize> Mul for BigInt<BASE> {
    type Output = Self;

    fn mul(mut self, mut rhs: Self) -> Self::Output {
        let sign = self.0 != rhs.0;
        self.0 = false;
        rhs.0 = false;
        let mut result = BigInt::from(0);
        for i in 1.. {
            if let Some(&digit) = self.1.get_back(i) {
                for _ in 0..digit {
                    result += rhs.clone();
                }
                rhs.1.push(0);
            } else {
                break;
            }
        }
        result.0 = sign;
        result.normalized()
    }
}

impl<const BASE: usize> MulAssign for BigInt<BASE> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<const BASE: usize> Div for BigInt<BASE> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).unwrap().0
    }
}

impl<const BASE: usize> DivAssign for BigInt<BASE> {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }
}

impl<const BASE: usize> Shl for BigInt<BASE> {
    type Output = Self;

    /// Shifts a `BigInt` left by multiples of its `BASE` (not by 2).
    fn shl(self, rhs: Self) -> Self::Output {
        BigInt(self.0, [self.1, vec![0; rhs.into()]].concat())
    }
}

impl<const BASE: usize> ShlAssign for BigInt<BASE> {
    /// Shifts a `BigInt` left by multiples of its `BASE` (not by 2).
    fn shl_assign(&mut self, rhs: Self) {
        *self = self.clone() << rhs;
    }
}

impl<const BASE: usize> Shr for BigInt<BASE> {
    type Output = Self;

    /// Shifts a `BigInt` right by multiples of its `BASE` (not by 2).
    fn shr(self, rhs: Self) -> Self::Output {
        BigInt(self.0, self.1[..self.1.len() - usize::from(rhs)].to_vec()).normalized()
    }
}

impl<const BASE: usize> ShrAssign for BigInt<BASE> {
    /// Shifts a `BigInt` right by multiples of its `BASE` (not by 2).
    fn shr_assign(&mut self, rhs: Self) {
        *self = self.clone() >> rhs;
        self.normalize()
    }
}

impl<const BASE: usize> Ord for BigInt<BASE> {
    fn cmp(&self, other: &Self) -> Ordering {
        match (self.0, other.0) {
            (false, true) => Ordering::Greater,
            (true, false) => Ordering::Less,
            _ => cmp(&self.1, &other.1),
        }
    }
}

impl<const BASE: usize> PartialOrd for BigInt<BASE> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Helper function called recursively when comparing two `BigInt`s.
fn cmp(a: &[Digit], b: &[Digit]) -> Ordering {
    if a.len() > b.len() {
        Ordering::Greater
    } else if a.len() < b.len() {
        Ordering::Less
    } else {
        match (a.split_first(), b.split_first()) {
            (None, None) => Ordering::Equal,
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (Some((a_digit, rest_a)), Some((b_digit, rest_b))) => match a_digit.cmp(b_digit) {
                Ordering::Equal => cmp(rest_a, rest_b),
                ordering => ordering,
            },
        }
    }
}

/// Encode an array of bytes into base64 data.
///
/// Note: probably slower than using a standalone
/// library to perform this conversion. However, it's very neat :3
///
/// Note: may fail if the data begins with zeros.
///
/// ```
/// use big_int::*;
/// assert_eq!(base64_encode(b"Hello world!"), "SGVsbG8gd29ybGQh");
/// ```
pub fn base64_encode(bytes: &[u8]) -> String {
    let mut digits = bytes
        .into_iter()
        .copied()
        .map(Digit::from)
        .collect::<Vec<_>>();
    let padding = 3 - ((digits.len() - 1) % 3) - 1;
    digits.extend(vec![0; padding]);
    let data_as_int: BigInt<256> = BigInt(false, digits);
    let base64_data: BigInt<64> = data_as_int.convert();
    let base64_string = base64_data.display(BASE64_ALPHABET).unwrap();
    base64_string[..base64_string.len() - padding].to_string()
}

/// Decode a base64 string into an array of bytes.
///
/// Note: probably slower than using a standalone
/// library to perform this conversion. However, again, it's very neat c:
///
/// Note: may fail if the data begins with zeros.
///
/// ```
/// use big_int::*;
/// assert_eq!(base64_decode("SGVsbG8gd29ybGQh").unwrap(), b"Hello world!");
/// ```
pub fn base64_decode(b64_string: impl Into<String>) -> Result<Vec<u8>, BigIntError> {
    let mut b64_string = b64_string.into();
    let padding = 4 - ((b64_string.len() - 1) % 4) - 1;
    b64_string.extend(vec!['A'; padding]);
    let string_as_int: BigInt<64> =
        BigInt::parse(&b64_string, BASE64_ALPHABET).map_err(BigIntError::ParseFailed)?;
    let bytes_int: BigInt<256> = string_as_int.convert();
    let bytes = bytes_int
        .1
        .into_iter()
        .map(u8::try_from)
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let bytes = bytes[..bytes.len() - padding].to_vec();
    Ok(bytes)
}
