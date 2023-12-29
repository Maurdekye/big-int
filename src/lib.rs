#![feature(min_specialization)]
//! `big_int` - Arbitrary precision, arbitrary base integer arithmetic library.
//!
//! ```
//! use big_int::prelude::*;
//!
//! let mut a: LooseInt<10> = "9000000000000000000000000000000000000000".parse().unwrap();
//! a /= 13.into();
//! assert_eq!(a, "692307692307692307692307692307692307692".parse().unwrap());
//!
//! let mut b: LooseInt<16> = a.convert();
//! assert_eq!(b, "208D59C8D8669EDC306F76344EC4EC4EC".parse().unwrap());
//! b >>= 16.into();
//!
//! let c: LooseInt<2> = b.convert();
//! assert_eq!(c, "100000100011010101100111001000110110000110011010011110110111000011".parse().unwrap());
//!
//! let mut d: TightInt<256> = c.convert();
//! d += vec![15, 90, 0].into();
//! assert_eq!(d, vec![2, 8, 213, 156, 141, 134, 121, 71, 195].into());
//!
//! let e: TightInt<10> = d.convert();
//! assert_eq!(format!("{e}"), "37530075201422313411".to_string());
//! ```
//!
//! This crate contains two primary big int implementations:
//! * `LooseInt<BASE>` - A collection of loosely packed ints representing each digit.
//!     Very memory inefficient, but with minimal performance overhead.
//! * `TightInt<BASE>` - A collection of tightly packed bits representing each digit.
//!     Maximally memory efficient; however, the additional indirection adds some performance overhead.
//!
//! Ints support most basic arithmetic operations, including addition, subtraction, multiplication,
//! division, and left/right shifting. Notably, shifting acts on the `BASE` of the associated number, increasing
//! or decreasing the magnitude by powers of `BASE` as opposed to powers of 2.

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

use self::Sign::*;

pub mod prelude {
    //! Default exports: includes `LooseInt`, `TightInt`, & `Sign`
    pub use crate::loose::*;
    pub use crate::tight::*;
    pub use crate::Sign::*;
    pub use crate::*;
}

mod get_back;

pub(crate) mod test_utils;

pub mod base64;
pub mod error;
pub mod loose;
pub mod tight;

/// Standard alphabet used when translating between text and big ints.
pub const STANDARD_ALPHABET: &str =
    "0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz+/";

/// Size of an individual big int digit.
pub type Digit = u64;
pub(crate) type DoubleDigit = u128;

/// Safely create a bitmask of `n` bits in size shifted 
/// to the right side of the number without overflowing.
#[macro_export(local_inner_macros)]
macro_rules! mask {
    ($n:expr) => {
        (((1 << (($n) - 1)) - 1) << 1) + 1
    };
}

/// A big int implementation.
/// 
/// Encapsulates all the underlying mechanics necessary to store and retrieve the individual
/// digits of a big int.
/// 
/// Arithmetic cannot be performed directly on a big int implementation; it must be wrapped in
/// a `BigInt` first.
/// 
/// ```
/// use big_int::prelude::*;
/// 
/// let mut a = TightBuilder::<10>::new();
/// a.push_back(1);
/// a.push_back(0);
/// a.push_back(4);
/// let a: Tight<10> = a.build();
/// assert_eq!(BigInt::from(a), 104.into());
/// ```
pub trait BigIntImplementation<const BASE: usize>
where
    Self: Clone + PartialEq + Eq + std::fmt::Debug,
{
    type Builder: BigIntBuilder<{ BASE }> + Build<Self>;
    type DigitIterator<'a>: DoubleEndedIterator<Item = Digit>
    where
        Self: 'a;

    /// The length of the big int in digits.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 211864.into();
    /// assert_eq!(a.len(), 6);
    /// ```
    fn len(&self) -> usize;

    /// Get the digit of the big int at position `digit`,
    /// or None if the number does not have that many digits.
    /// 
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 12345.into();
    /// assert_eq!(a.get_digit(2), Some(3));
    /// assert_eq!(a.get_digit(6), None);
    /// ```
    fn get_digit(&self, digit: usize) -> Option<Digit>;

    /// Set the digit of the big int to `value` at position `digit`.
    /// 
    /// If the set digit causes the leftmost digit of the number to be zero,
    /// the number will become denormal, and should be normalized before being used.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: TightInt<10> = 10000.into();
    /// a.set_digit(1, 7);
    /// a.set_digit(4, 9);
    /// assert_eq!(a, 17009.into());
    /// ```
    fn set_digit(&mut self, digit: usize, value: Digit);

    /// The value zero represented as a big int.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: TightInt<10> = 13.into();
    /// let b = 13.into();
    /// assert_eq!(a - b, BigInt::zero());
    /// ```
    fn zero() -> Self;

    /// The sign of the big int.
    /// 
    /// The value zero represented as a big int.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: TightInt<10> = 5.into();
    /// assert_eq!(a.sign(), Positive);
    /// a -= 14.into();
    /// assert_eq!(a.sign(), Negative);
    /// ```
    fn sign(&self) -> Sign;

    /// The big in with the given sign.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: TightInt<10> = 95.into();
    /// assert_eq!(a.with_sign(Negative), (-95).into());
    /// ```
    fn with_sign(self, sign: Sign) -> Self;

    /// Set the sign of the big int to `sign`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: TightInt<10> = (-109).into();
    /// a.set_sign(Positive);
    /// assert_eq!(a, 109.into());
    /// ```
    fn set_sign(&mut self, sign: Sign);

    /// Append a digit to the right side of the int. Equivalent to `(int << 1) + digit`
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: TightInt<10> = 6.into();
    /// a.push_back(1);
    /// assert_eq!(a, 61.into());
    /// ```
    fn push_back(&mut self, digit: Digit);

    /// Append a digit to the left side of the int. May cause the resulting
    /// int to be denormalized; make sure to call .normalize() afterwards 
    /// to prevent undefined functionality.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: TightInt<10> = 6.into();
    /// a.push_front(1);
    /// assert_eq!(a.normalized(), 16.into());
    /// ```
    fn push_front(&mut self, digit: Digit);

    /// Divide the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shr_assign`; at least one of `shr` or `shr_assign` must be defined.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 600.into();
    /// assert_eq!(a.shr(2), 6.into());
    /// ```
    fn shr(mut self, amount: usize) -> Self {
        self.shr_assign(amount);
        self
    }

    /// Divide the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shr`; at least one of `shr` or `shr_assign` must be defined.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: TightInt<10> = 600.into();
    /// a.shr_assign(2);
    /// assert_eq!(a, 6.into());
    /// ```
    fn shr_assign(&mut self, amount: usize) {
        *self = self.clone().shr(amount);
    }

    /// Multiply the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shl_assign`; at least one of `shl` or `shl_assign` must be defined.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 3.into();
    /// assert_eq!(a.shl(2), 300.into());
    /// ```
    fn shl(mut self, amount: usize) -> Self {
        self.shl_assign(amount);
        self
    }

    /// Multiply the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shl`; at least one of `shl` or `shl_assign` must be defined.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: TightInt<10> = 3.into();
    /// a.shl_assign(2);
    /// assert_eq!(a, 300.into());
    /// ```
    fn shl_assign(&mut self, amount: usize) {
        *self = self.clone().shl(amount);
    }

    /// Iterate over the digits of the int.
    /// 
    /// `impl`s `DoubleEndedIterator`, so digits can be iterated over forward or in reverse.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 12345.into();
    /// assert_eq!(a.iter().collect::<Vec<_>>(), vec![1, 2, 3, 4, 5]);
    /// assert_eq!(a.iter().rev().collect::<Vec<_>>(), vec![5, 4, 3, 2, 1]);
    /// ```
    fn iter<'a>(&'a self) -> Self::DigitIterator<'a>;

    /// Return a normalized version of the int. A normalized int:
    /// * has no trailing zeros
    /// * has at least one digit
    /// * is not negative zero
    /// Additionally, `TightInt`s will be aligned to the beginning of their data segment
    /// when normalized.
    /// 
    /// Defined in terms of `normalize`; at least one of `normalize` or `normalized`
    /// must be defined.
    /// 
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let n = BigInt::from(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) });
    /// assert_eq!(n.normalized(), 83.into());
    /// ```
    fn normalized(mut self) -> Self {
        self.normalize();
        self
    }

    /// Normalize a big int in place. 
    /// * has no trailing zeros
    /// * has at least one digit
    /// * is not negative zero
    /// Additionally, `TightInt`s will be aligned to the beginning of their data segment
    /// when normalized.
    /// 
    /// Defined in terms of `normalized`; at least one of `normalize` or `normalized`
    /// must be defined.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut n = BigInt::from(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) });
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
    /// use big_int::prelude::*;
    ///
    /// assert_eq!(
    ///     LooseInt::<10>::from(6012).display(STANDARD_ALPHABET).unwrap(),
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
        if self.sign() == Negative {
            Ok(format!("-{digits}"))
        } else {
            Ok(digits)
        }
    }

    /// Parse a big int from a `value: &str`, referencing the provided `alphabet`
    /// to determine what characters represent which digits. `FromStr` uses this method
    /// with the default alphabet `STANDARD_ALPHABET`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// assert_eq!(LooseInt::parse("125", STANDARD_ALPHABET), Ok(LooseInt::<10>::from(125)));
    /// ```
    fn parse(value: &str, alphabet: &str) -> Result<Self, ParseError> {
        let mut builder = Self::Builder::new();
        let (sign, chars) = match value.chars().next() {
            Some('-') => (Negative, value.chars().skip(1)),
            Some(_) => (Positive, value.chars().skip(0)),
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
            Ok(builder.with_sign(sign).build())
        }
    }
}

/// A builder for a big int. Use this to construct a big int one digit at a time,
/// then call .build() to finalize the builder.
/// 
/// You're most likely better off using one of the `From` implementations
/// as opposed to directly building your int via a builder.
/// 
/// ```
/// use big_int::prelude::*;
/// 
/// let mut a = TightBuilder::<10>::new();
/// a.push_back(5);
/// a.push_back(3);
/// a.push_back(0);
/// a.push_back(4);
/// let a: Tight<10> = a.build();
/// let a: TightInt<10> = BigInt::from(a);
/// assert_eq!(a, 5304.into());
/// ```
pub trait BigIntBuilder<const BASE: usize>
where
    Self: std::fmt::Debug,
{
    /// Create a new builder.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a = TightBuilder::<10>::new();
    /// a.push_back(5);
    /// assert_eq!(BigInt::from(a.build()), 5.into());
    /// ```
    fn new() -> Self;

    /// Push a new digit to the end of the int.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a = TightBuilder::<10>::new();
    /// a.push_back(5);
    /// a.push_back(6);
    /// assert_eq!(BigInt::from(a.build()), 56.into());
    /// ```
    fn push_front(&mut self, digit: Digit);

    /// Push a new digit to the beginning of the int.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a = TightBuilder::<10>::new();
    /// a.push_front(5);
    /// a.push_front(6);
    /// assert_eq!(BigInt::from(a.build()), 65.into());
    /// ```
    fn push_back(&mut self, digit: Digit);

    /// Check if the builder is empty.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a = TightBuilder::<10>::new();
    /// assert!(a.is_empty());
    /// a.push_front(5);
    /// assert!(!a.is_empty());
    /// ```
    fn is_empty(&self) -> bool;

    /// The builder with the given sign.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a = TightBuilder::<10>::new();
    /// a.push_back(9);
    /// assert_eq!(BigInt::from(a.with_sign(Negative).build()), (-9).into());
    /// ```
    fn with_sign(self, sign: Sign) -> Self;
}

/// Trait that represents the final build step of a BigIntBuilder.
/// 
/// ```
/// use big_int::prelude::*;
/// 
/// let mut a = TightBuilder::<10>::new();
/// a.push_back(5);
/// a.push_back(3);
/// a.push_back(0);
/// a.push_back(4);
/// let a: Tight<10> = a.build();
/// assert_eq!(BigInt::from(a), 5304.into());
/// ```
pub trait Build<B> {

    /// Build the value and return the finalized result.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a = TightBuilder::<10>::new();
    /// a.push_back(5);
    /// a.push_back(3);
    /// a.push_back(0);
    /// a.push_back(4);
    /// let a: Tight<10> = a.build();
    /// assert_eq!(BigInt::from(a), 5304.into());
    /// ```
    fn build(self) -> B;
}

/// Represents the sign of a big int; either Positive or Negative.
/// 
/// ```
/// use big_int::prelude::*;
/// 
/// let mut a: TightInt<10> = 18.into();
/// let s = a.sign();
/// assert_eq!(s, Positive);
/// a *= (-1).into();
/// let s = a.sign();
/// assert_eq!(s, Negative);
/// ```
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Sign {
    Positive,
    Negative,
}

impl Neg for Sign {
    type Output = Sign;

    fn neg(self) -> Self::Output {
        match self {
            Positive => Negative,
            Negative => Positive,
        }
    }
}

impl Mul for Sign {
    type Output = Sign;

    fn mul(self, rhs: Self) -> Self::Output {
        if self == rhs {
            Positive
        } else {
            Negative
        }
    }
}

/// A big int.
///
/// Must be constructed from a specific implementation.
///
/// You should prefer to use the type aliases `LooseInt` / `TightInt` instead of
/// using this type directly.
///
/// ```
/// use big_int::prelude::*;
///
/// let a = BigInt::<10, Loose<10>>::from(unsafe { Loose::<10>::from_raw_parts(vec![9, 0, 1]) });
/// assert_eq!(a, LooseInt::<10>::from(901));
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigInt<const BASE: usize, B: BigIntImplementation<{ BASE }>>(B);

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> BigInt<BASE, B> {
    /// The value zero represented as a big int.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: TightInt<10> = 13.into();
    /// let b = 13.into();
    /// assert_eq!(a - b, BigInt::zero());
    /// ```
    pub fn zero() -> Self {
        Self(B::zero())
    }

    /// The big in with the given sign.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: TightInt<10> = 95.into();
    /// assert_eq!(a.with_sign(Negative), (-95).into());
    /// ```
    pub fn with_sign(self, sign: Sign) -> Self {
        Self(self.0.with_sign(sign))
    }

    /// Multiply the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: TightInt<10> = 45.into();
    /// assert_eq!(a.shl(1), 450.into());
    /// ```
    pub fn shl(self, amount: usize) -> Self {
        Self(self.0.shl(amount))
    }

    /// Multiply the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: TightInt<10> = 45.into();
    /// assert_eq!(a.shl(1), 450.into());
    /// ```
    pub fn shl_assign(&mut self, amount: usize) {
        self.0.shl_assign(amount)
    }

    /// Divide the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 600.into();
    /// assert_eq!(a.shr(2), 6.into());
    /// ```
    pub fn shr(self, amount: usize) -> Self {
        Self(self.0.shr(amount))
    }

    /// Divide the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 600.into();
    /// assert_eq!(a.shr(2), 6.into());
    /// ```
    pub fn shr_assign(&mut self, amount: usize) {
        self.0.shr_assign(amount)
    }

    /// Return a normalized version of the int. A normalized int:
    /// * has no trailing zeros
    /// * has at least one digit
    /// * is not negative zero
    /// Additionally, `TightInt`s will be aligned to the beginning of their data segment
    /// when normalized.
    /// 
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let n = BigInt::from(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) });
    /// assert_eq!(n.normalized(), 83.into());
    /// ```
    pub fn normalized(self) -> Self {
        Self(self.0.normalized())
    }

    /// Parse a big int from a `value: &str`, referencing the provided `alphabet`
    /// to determine what characters represent which digits. `FromStr` uses this method
    /// with the default alphabet `STANDARD_ALPHABET`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// assert_eq!(LooseInt::parse("125", STANDARD_ALPHABET), Ok(LooseInt::<10>::from(125)));
    /// ```
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
    /// use big_int::prelude::*;
    ///
    /// let a: LooseInt<10> = 999_999_999.into();
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
        self.set_sign(Positive);
        other.set_sign(Positive);
        let quot_digits = self.len() - other.len() + 1;
        let mut quot = B::Builder::new();
        let mut prod = Self::zero();
        let mut addend = other.clone().shl(quot_digits - 1);
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
            quot.push_back(digit_value);
        }

        let mut rem = self - prod;
        if rem != Self::zero() {
            rem.set_sign(sign);
        }

        Ok((quot.with_sign(sign).build().into(), rem))
    }

    /// Convert an int from its own base to another target base.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// assert_eq!(
    ///     LooseInt::<10>::from(99825).convert(),
    ///     LooseInt::<16>::from(99825)
    /// );
    /// ```
    pub fn convert<const TO: usize, T: BigIntImplementation<{ TO }>>(mut self) -> BigInt<TO, T> {
        let sign = self.sign();
        let mut result = T::Builder::new();
        if BASE == TO {
            for digit in self.iter() {
                result.push_back(digit);
            }
        } else {
            self.set_sign(Positive);
            let to_base = Self::from(TO);
            while self >= to_base {
                let (quot, rem) = self.div_rem(to_base.clone()).unwrap();
                self = quot;
                result.push_front(Digit::from(rem));
            }
            result.push_front(Digit::from(self));
        }
        result.with_sign(sign).build().into()
    }

    /// Compare the absolute magnitude of two big ints, ignoring their sign.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: TightInt<10> = (-105).into();
    /// let b = 15.into();
    /// assert!(a.cmp_magnitude(&b).is_gt());
    /// ```
    pub fn cmp_magnitude(&self, rhs: &Self) -> Ordering {
        match self.len().cmp(&rhs.len()) {
            Ordering::Equal => {
                for (self_digit, rhs_digit) in self.iter().zip(rhs.iter()) {
                    match self_digit.cmp(&rhs_digit) {
                        Ordering::Equal => {}
                        ordering => return ordering,
                    }
                }
                Ordering::Equal
            }
            order => order,
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

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<B> for BigInt<BASE, B> {
    fn from(value: B) -> Self {
        BigInt(value)
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

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> FromIterator<Digit> for BigInt<BASE, B> {
    fn from_iter<T: IntoIterator<Item = Digit>>(iter: T) -> Self {
        let mut builder = B::Builder::new();
        for digit in iter {
            builder.push_back(digit);
        }
        builder.build().into()
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<Vec<Digit>> for BigInt<BASE, B> {
    fn from(value: Vec<Digit>) -> Self {
        value.into_iter().collect()
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<&[Digit]> for BigInt<BASE, B> {
    fn from(value: &[Digit]) -> Self {
        value.into_iter().copied().collect()
    }
}

impl<const BASE: usize, const N: usize, B: BigIntImplementation<{ BASE }>> From<[Digit; N]>
    for BigInt<BASE, B>
{
    fn from(value: [Digit; N]) -> Self {
        value.into_iter().collect()
    }
}

impl<const N: usize, B: BigIntImplementation<256>> From<&[u8; N]> for BigInt<256, B> {
    fn from(value: &[u8; N]) -> Self {
        value.into_iter().map(|d| *d as Digit).collect()
    }
}

impl<B: BigIntImplementation<256>> From<&[u8]> for BigInt<256, B> {
    fn from(value: &[u8]) -> Self {
        value.into_iter().map(|d| *d as Digit).collect()
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
        BigInt(result.build().into())
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> From<i128> for BigInt<BASE, B> {
    fn from(value: i128) -> Self {
        if value < 0 {
            Self::from((-value) as u128).with_sign(Negative)
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
                    if value.sign() == Negative {
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
        self.with_sign(sign)
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Add for BigInt<BASE, B> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        if self.sign() != rhs.sign() {
            self - (-rhs)
        } else {
            let sign = self.sign();
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
            result.with_sign(sign).build().into()
        }
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> AddAssign for BigInt<BASE, B> {
    fn add_assign(&mut self, rhs: Self) {
        if self.sign() != rhs.sign() {
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
        if self.sign() != rhs.sign() {
            self + (-rhs)
        } else if rhs.cmp_magnitude(&self).is_gt() {
            -(rhs - self)
        } else {
            let sign = self.sign();
            let mut result = B::Builder::new();
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
                                        self.set_digit(self_len - j, (BASE - 1) as Digit);
                                    }
                                    Some(digit) => {
                                        self.set_digit(self_len - j, digit - 1);
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
            result.with_sign(sign).build().into()
        }
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> SubAssign for BigInt<BASE, B> {
    fn sub_assign(&mut self, mut rhs: Self) {
        if self.sign() != rhs.sign() {
            *self += -rhs;
        } else if rhs.cmp_magnitude(self).is_gt() {
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
                                        self.set_digit(self_len - j, (BASE - 1) as Digit);
                                    }
                                    Some(digit) => {
                                        self.set_digit(self_len - j, digit - 1);
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
        self.set_sign(Positive);
        rhs.set_sign(Positive);
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
        result.with_sign(sign).normalized()
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

    /// Multiply the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Note: using the shift operator is generally not encouraged, as it's
    /// less efficient than using `BigInt::shl` directly.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 3.into();
    /// assert_eq!(a << 2.into(), 300.into());
    /// ```
    fn shl(self, rhs: Self) -> Self::Output {
        self.shl(rhs.into())
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> ShlAssign for BigInt<BASE, B> {

    /// Multiply the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Note: using the shift operator is generally not encouraged, as it's
    /// less efficient than using `BigInt::shl_assign` directly.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: TightInt<10> = 3.into();
    /// a <<= 2.into();
    /// assert_eq!(a, 300.into());
    /// ```
    fn shl_assign(&mut self, rhs: Self) {
        self.shl_assign(rhs.into());
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> Shr for BigInt<BASE, B> {
    type Output = Self;

    /// Divide the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Note: using the shift operator is generally not encouraged, as it's
    /// less efficient than using `BigInt::shr` directly.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: TightInt<10> = 600.into();
    /// assert_eq!(a >> 2.into(), 6.into());
    /// ```
    fn shr(self, rhs: Self) -> Self::Output {
        self.shr(rhs.into())
    }
}

impl<const BASE: usize, B: BigIntImplementation<{ BASE }>> ShrAssign for BigInt<BASE, B> {
    
    /// Divide the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Note: using the shift operator is generally not encouraged, as it's
    /// less efficient than using `BigInt::shr_assign` directly.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: TightInt<10> = 600.into();
    /// a >>= 2.into();
    /// assert_eq!(a, 6.into());
    /// ```
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
            (Positive, Negative) => Ordering::Greater,
            (Negative, Positive) => Ordering::Less,
            (Positive, Positive) => self.cmp_magnitude(other),
            (Negative, Negative) => other.cmp_magnitude(self),
        }
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
