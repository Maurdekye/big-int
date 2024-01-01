//! `big_int` - Arbitrary precision, arbitrary base integer arithmetic library.
//!
//! ```
//! use big_int::prelude::*;
//!
//! let mut a: Loose<10> = "9000000000000000000000000000000000000000".parse().unwrap();
//! a /= 13.into();
//! assert_eq!(a, "692307692307692307692307692307692307692".parse().unwrap());
//!
//! let mut b: Loose<16> = a.convert();
//! assert_eq!(b, "208D59C8D8669EDC306F76344EC4EC4EC".parse().unwrap());
//! b >>= 16.into();
//!
//! let c: Loose<2> = b.convert();
//! assert_eq!(c, "100000100011010101100111001000110110000110011010011110110111000011".parse().unwrap());
//!
//! let mut d: Tight<256> = c.convert();
//! d += vec![15, 90, 0].into();
//! assert_eq!(d, vec![2, 8, 213, 156, 141, 134, 121, 71, 195].into());
//!
//! let e: Tight<10> = d.convert();
//! assert_eq!(format!("{e}"), "37530075201422313411".to_string());
//! ```
//!
//! This crate contains two primary big int implementations:
//! * `Loose<BASE>` - A collection of loosely packed ints representing each digit.
//!     Very memory inefficient, but with minimal performance overhead.
//! * `Tight<BASE>` - A collection of tightly packed bits representing each digit.
//!     Maximally memory efficient; however, the additional indirection adds some performance overhead.
//!
//! Ints support most basic arithmetic operations, including addition, subtraction, multiplication,
//! division, and left/right shifting. Notably, shifting acts on the `BASE` of the associated number, increasing
//! or decreasing the magnitude by powers of `BASE` as opposed to powers of 2.

extern crate self as big_int;

use std::{
    cmp::Ordering,
    fmt::Display,
    ops::{
        Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Shl, ShlAssign, Shr, ShrAssign, Sub,
        SubAssign,
    },
    str::FromStr,
};

use error::{BigIntError, ParseError};
use get_back::GetBack;

use self::Sign::*;

pub use big_int_proc::*;

pub mod prelude {
    //! Default exports: includes `Loose`, `Tight`, & `Sign`
    pub use crate::loose::*;
    pub use crate::tight::*;
    pub use crate::Sign::*;
    pub use crate::*;
}

pub(crate) mod test_utils;

pub mod base64;
pub mod error;
pub mod get_back;
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

/// A big int.
///
/// Represents an arbitrary precision, arbitrary base natural number.
///
/// Supports basic arithmetic operations, as well as all utilities necessary for
/// coercing to and from various builtin types, such as primitive int types, `Vec`s, and `String`s.
///
/// ### For implementors:
/// If implementing this trait for your own type, don't be alarmed by the massive list of `Self`
/// constraints. Use the included derive macro `big_int::BigIntTraits` to automatically derive
/// all traits using default `*_inner` implementations pre-provided by `BigInt`.
///
/// At least one of `normalize` or `normalized` must be defined to prevent recursion.\
/// At least one of `shl_inner` or `shl_assign_inner` must be defined to prevent recursion.\
/// At least one of `shr_inner` or `shr_assign_inner` must be defined to prevent recursion.\
///
/// ```
/// use big_int::prelude::*;
///
/// let mut a = TightBuilder::<10>::new();
/// a.push_back(1);
/// a.push_back(0);
/// a.push_back(4);
/// let a: Tight<10> = a.build();
/// assert_eq!(a, 104.into());
/// ```
pub trait BigInt<const BASE: usize>
where
    Self: GetBack<Item = Digit>
        + Clone
        + Default
        + std::fmt::Debug
        + Display
        + PartialEq
        + Eq
        + PartialOrd
        + Ord
        + Neg<Output = Self>
        + Add<Output = Self>
        + AddAssign
        + Sub<Output = Self>
        + SubAssign
        + Div<Output = Self>
        + DivAssign
        + Mul<Output = Self>
        + MulAssign
        + Shl<Output = Self>
        + ShlAssign
        + Shr<Output = Self>
        + ShrAssign
        + FromStr<Err = BigIntError>
        + FromIterator<Digit>
        + From<Vec<Digit>>
        + From<u8>
        + From<u16>
        + From<u32>
        + From<u64>
        + From<u128>
        + From<usize>
        + From<i8>
        + From<i16>
        + From<i32>
        + From<i64>
        + From<i128>
        + From<isize>
        + Into<u8>
        + Into<u16>
        + Into<u32>
        + Into<u64>
        + Into<u128>
        + Into<usize>
        + Into<i8>
        + Into<i16>
        + Into<i32>
        + Into<i64>
        + Into<i128>
        + Into<isize>,
{
    type Builder: BigIntBuilder<{ BASE }> + Build<Self>;
    type DigitIterator<'a>: DoubleEndedIterator<Item = Digit>
    where
        Self: 'a;

    /// Default implementation of `big_int::GetBack`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn get_back_inner(&self, index: usize) -> Option<Digit> {
        self.len()
            .checked_sub(index)
            .and_then(|index| self.get_digit(index))
    }

    /// Default implementation of `Default`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn default_inner() -> Self {
        Self::zero()
    }

    /// Default implementation of `Display`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn fmt_inner(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.display(STANDARD_ALPHABET)
                .map_err(|_| std::fmt::Error)?
        )
    }

    /// Default implementation of `PartialOrd`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn partial_cmp_inner(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }

    /// Default implementation of `Ord`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn cmp_inner(&self, other: &Self) -> Ordering {
        if self.is_zero() && other.is_zero() {
            Ordering::Equal
        } else {
            match (self.sign(), other.sign()) {
                (Positive, Negative) => Ordering::Greater,
                (Negative, Positive) => Ordering::Less,
                (Positive, Positive) => self.cmp_magnitude(other),
                (Negative, Negative) => other.cmp_magnitude(self),
            }
        }
    }

    /// Default implementation of `PartialEq`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn eq_inner(&self, other: &Self) -> bool {
        matches!(self.cmp_inner(other), Ordering::Equal)
    }

    /// Default implementation of `Neg`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn neg_inner(self) -> Self {
        let sign = self.sign();
        self.with_sign(-sign)
    }

    /// Default implementation of `Add`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn add_inner(self, rhs: Self) -> Self {
        if self.sign() != rhs.sign() {
            self - (-rhs)
        } else {
            let sign = self.sign();
            let mut carry = 0;
            let mut result = Self::Builder::new();
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
            result.with_sign(sign).build()
        }
    }

    /// Default implementation of `AddAssign`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn add_assign_inner(&mut self, rhs: Self) {
        if self.sign() != rhs.sign() {
            self.sub_assign_inner(rhs.neg_inner());
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
            self.normalize();
        }
    }

    /// Default implementation of `Sub`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn sub_inner(mut self, rhs: Self) -> Self {
        if self.sign() != rhs.sign() {
            self.add_inner(rhs.neg_inner())
        } else if rhs.cmp_magnitude(&self).is_gt() {
            rhs.sub_inner(self).neg_inner()
        } else {
            let sign = self.sign();
            let mut result = Self::Builder::new();
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
            result.with_sign(sign).build()
        }
    }

    /// Default implementation of `SubAssign`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn sub_assign_inner(&mut self, mut rhs: Self) {
        if self.sign() != rhs.sign() {
            self.add_assign_inner(rhs.neg_inner());
        } else if rhs.cmp_magnitude(self).is_gt() {
            rhs.sub_assign_inner(self.clone());
            *self = rhs.neg_inner();
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
            self.normalize();
        }
        self.normalize();
    }

    /// Default implementation of `Mul`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn mul_inner(mut self, mut rhs: Self) -> Self {
        let sign = self.sign() * rhs.sign();
        self.set_sign(Positive);
        rhs.set_sign(Positive);
        let mut result = Self::zero();
        let mut addend = rhs.clone();
        let mut addends = Vec::new();
        let mut power = 1;
        while power < BASE {
            addends.push(addend.clone());
            addend += addend.clone();
            power <<= 1;
        }
        for digit in self.iter().rev() {
            for i in 0..addends.len() {
                if digit & (1 << i) != 0 {
                    result += addends[i].clone();
                }
                addends[i].shl_assign_inner(1);
            }
        }
        result.with_sign(sign).normalized()
    }

    /// Default implementation of `MulAssign`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn mul_assign_inner(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }

    /// Default implementation of `Div`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn div_inner(self, rhs: Self) -> Self {
        self.div_rem(rhs).unwrap().0
    }

    /// Default implementation of `DivAssign`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn div_assign_inner(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }

    /// Default implementation of `FromStr`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn from_str_inner(s: &str) -> Result<Self, BigIntError> {
        Self::parse(s, STANDARD_ALPHABET).map_err(BigIntError::ParseFailed)
    }

    /// Default implementation of `FromIterator`.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn from_iter_inner<T: IntoIterator<Item = Digit>>(iter: T) -> Self {
        let mut builder = Self::Builder::new();
        for digit in iter {
            builder.push_back(digit);
        }
        builder.build()
    }

    /// Default implementation of `From<_>` for all unsigned primitive int types.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn from_u128_inner(mut value: u128) -> Self {
        let base = BASE as u128;
        let mut result = Self::Builder::new();
        while value >= base {
            let (new_value, rem) = (value / base, value % base);
            value = new_value;
            result.push_front(rem as Digit);
        }
        result.push_front(value as Digit);
        result.build()
    }

    /// Default implementation of `From<_>` for all signed primitive int types.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn from_i128_inner(value: i128) -> Self {
        if value < 0 {
            Self::from_u128_inner((-value) as u128).with_sign(Negative)
        } else {
            Self::from_u128_inner(value as u128)
        }
    }

    /// Default implementation of `Into<_>` for all unsigned primitive int types.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn into_u128_inner(self) -> u128 {
        if self.sign() == Negative {
            panic!("uint conversion with underflow");
        }
        let mut total: u128 = 0;
        let mut place: u128 = 0;
        for digit in self.iter().rev() {
            place = if place == 0 { 1 } else { place * BASE as u128 };
            total += (digit as u128) * place;
        }
        total
    }

    /// Default implementation of `Into<_>` for all signed primitive int types.
    ///
    /// Trait implementation may be provided automatically by `big_int_proc::BigIntTraits`.
    fn into_i128_inner(self) -> i128 {
        let mut total: i128 = 0;
        let mut place: i128 = 0;
        for digit in self.iter().rev() {
            place = if place == 0 { 1 } else { place * BASE as i128 };
            total += (digit as i128) * place;
        }
        if self.sign() == Negative {
            total = -total;
        }
        total
    }

    /// The length of the big int in digits.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<10> = 211864.into();
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
    /// let a: Tight<10> = 12345.into();
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
    /// let mut a: Tight<10> = 10000.into();
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
    /// let a: Tight<10> = 13.into();
    /// let b = 13.into();
    /// assert_eq!(a - b, BigInt::zero());
    /// ```
    fn zero() -> Self;

    /// Check if the big int is zero.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<10> = 13.into();
    /// let b = 13.into();
    /// assert!((a - b).is_zero());
    /// ```
    fn is_zero(&self) -> bool {
        self.iter().all(|digit| digit == 0)
    }

    /// The sign of the big int.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: Tight<10> = 5.into();
    /// assert_eq!(a.sign(), Positive);
    /// a -= 14.into();
    /// assert_eq!(a.sign(), Negative);
    /// ```
    fn sign(&self) -> Sign;

    /// The big int with the given sign.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<10> = 95.into();
    /// assert_eq!(a.with_sign(Negative), (-95).into());
    /// ```
    fn with_sign(self, sign: Sign) -> Self;

    /// Set the sign of the big int to `sign`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: Tight<10> = (-109).into();
    /// a.set_sign(Positive);
    /// assert_eq!(a, 109.into());
    /// ```
    fn set_sign(&mut self, sign: Sign);

    /// Append a digit to the right side of the int. Equivalent to `(int << 1) + digit`
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: Tight<10> = 6.into();
    /// a.push_back(1);
    /// assert_eq!(a, 61.into());
    /// ```
    fn push_back(&mut self, digit: Digit);

    /// Append a digit to the left side of the int. If a zero is pushed onto the end
    /// of the int, it will become denormalized; make sure to call `.normalize()` before performing
    /// additional operations to prevent undefined functionality.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: Tight<10> = 6.into();
    /// a.push_front(1);
    /// assert_eq!(a.normalized(), 16.into());
    /// ```
    fn push_front(&mut self, digit: Digit);

    /// Divide the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shr_assign`; at least one of `shr`
    /// or `shr_assign` must be defined by implementers.
    ///
    /// Also acts as the default implementation of the `Shr` trait,
    /// as provided automatically by `big_int_proc::BigIntTraits`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<10> = 600.into();
    /// assert_eq!(a.shr_inner(2), 6.into());
    /// ```
    fn shr_inner(mut self, amount: usize) -> Self {
        self.shr_assign_inner(amount);
        self
    }

    /// Divide the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shr`; at least one of `shr`
    /// or `shr_assign` must be defined by implementers.
    ///
    /// Also acts as the default implementation of the `ShrAssign` trait,
    /// as provided automatically by `big_int_proc::BigIntTraits`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: Tight<10> = 600.into();
    /// a.shr_assign_inner(2);
    /// assert_eq!(a, 6.into());
    /// ```
    fn shr_assign_inner(&mut self, amount: usize) {
        *self = self.clone().shr_inner(amount);
    }

    /// Multiply the int by BASE^amount.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shl_assign`; at least one of `shl`
    ///  or `shl_assign` must be defined by implementers.
    ///
    /// Also acts as the default implementation of the `Shl` trait,
    /// as provided automatically by `big_int_proc::BigIntTraits`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<10> = 3.into();
    /// assert_eq!(a.shl_inner(2), 300.into());
    /// ```
    fn shl_inner(mut self, amount: usize) -> Self {
        self.shl_assign_inner(amount);
        self
    }

    /// Multiply the int by BASE^amount in place.
    ///
    /// Note: works in powers of BASE, not in powers of 2.
    ///
    /// Defined in terms of `shl`; at least one of `shl`
    ///  or `shl_assign` must be defined by implementers.
    ///
    /// Also acts as the default implementation of the `ShlAssign` trait,
    /// as provided automatically by `big_int_proc::BigIntTraits`.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut a: Tight<10> = 3.into();
    /// a.shl_assign_inner(2);
    /// assert_eq!(a, 300.into());
    /// ```
    fn shl_assign_inner(&mut self, amount: usize) {
        *self = self.clone().shl_inner(amount);
    }

    /// Iterate over the digits of the int.
    ///
    /// implements `DoubleEndedIterator`, so digits can be iterated over forward or in reverse.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<10> = 12345.into();
    /// assert_eq!(a.iter().collect::<Vec<_>>(), vec![1, 2, 3, 4, 5]);
    /// assert_eq!(a.iter().rev().collect::<Vec<_>>(), vec![5, 4, 3, 2, 1]);
    /// ```
    fn iter<'a>(&'a self) -> Self::DigitIterator<'a>;

    /// Return a normalized version of the int. A normalized int:
    /// * has no trailing zeros
    /// * has at least one digit
    /// * is not negative zero
    ///
    /// Additionally, `Tight` ints will be aligned to the beginning of their data segment
    /// when normalized.
    ///
    /// Defined in terms of `normalize`; at least one of `normalize` or `normalized`
    /// must be defined by the implementer.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let n = unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
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
    ///
    /// Additionally, `Tight` ints will be aligned to the beginning of their data segment
    /// when normalized.
    ///
    /// Defined in terms of `normalized`; at least one of `normalize` or `normalized`
    /// must be defined by the implementer.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let mut n = unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
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
    ///     Loose::<10>::from(6012).display(STANDARD_ALPHABET).unwrap(),
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
    /// assert_eq!(Loose::parse("125", STANDARD_ALPHABET), Ok(Loose::<10>::from(125)));
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

    /// Divide one int by another, returning the quotient & remainder as a pair,
    /// or an error if dividing by zero.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Loose<10> = 999_999_999.into();
    /// let b = 56_789.into();
    /// assert_eq!(a.div_rem(b), Ok((17_609.into(), 2_498.into())));
    /// ```
    fn div_rem(mut self, mut rhs: Self) -> Result<(Self, Self), BigIntError> {
        if rhs.clone().normalized() == Self::zero() {
            return Err(BigIntError::DivisionByZero);
        }
        if rhs.len() > self.len() {
            return Ok((Self::zero(), self));
        }
        let sign = self.sign() * rhs.sign();
        self.set_sign(Positive);
        rhs.set_sign(Positive);
        let quot_digits = self.len() - rhs.len() + 1;
        let mut quot = Self::Builder::new();
        let mut prod = Self::zero();
        let mut addend = rhs.clone().shl_inner(quot_digits - 1);
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
                addends[power].shr_assign_inner(1);
            }
            quot.push_back(digit_value);
        }

        let mut rem = self - prod;
        if rem != Self::zero() {
            rem.set_sign(sign);
        }

        Ok((quot.with_sign(sign).build(), rem))
    }

    /// Convert an int from its own base to another target base,
    /// to another `BigInt` type, or both at once.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<16> = Loose::<10>::from(99825).convert();
    /// assert_eq!(a, Tight::<16>::from(99825));
    /// ```
    fn convert<const TO: usize, T: BigInt<{ TO }>>(mut self) -> T {
        let to = TO as Digit;
        let sign = self.sign();
        let mut result = T::Builder::new();

        // bases are the same; just move the digits from one representation
        // into the other
        if BASE == TO {
            for digit in self.iter() {
                result.push_back(digit);
            }

        // current base is a power of the target base; perform a fast conversion
        // by converting each individual digit from the current number into
        // several contiguous digits of the target number
        } else if let Some(power) = is_power(BASE, TO) {
            for mut from_digit in self.iter().rev() {
                for _ in 0..power {
                    result.push_front(from_digit % to);
                    if from_digit >= to {
                        from_digit /= to;
                    } else {
                        from_digit = 0;
                    }
                }
            }

        // target base is a power of the current base; perform a fast conversion
        // by creating a single digit of the target number from several contiguous digits
        // of the current number
        } else if let Some(power) = is_power(TO, BASE) {
            println!("Self = {self:?}");
            let mut iter = self.iter().rev();
            loop {
                let mut to_digit = 0;
                let mut done = false;
                let mut place = 1;
                for _ in 0..power {
                    if let Some(from_digit) = iter.next() {
                        dbg!(from_digit);
                        to_digit *= from_digit * place;
                        dbg!(to_digit);
                        place *= to;
                    } else {
                        done = true;
                        break;
                    }
                }
                result.push_front(to_digit);
                println!("result = {result:?}");
                if done {
                    break;
                }
            }

        // no special conditions apply; just perform the conversion normally via
        // repeated divisons
        } else {
            self.set_sign(Positive);
            let to_base: Self = to.into();
            while self >= to_base {
                let (quot, rem) = self.div_rem(to_base.clone()).unwrap();
                self = quot;
                result.push_front(Into::<Digit>::into(rem));
            }
            result.push_front(Into::<Digit>::into(self));
        }
        result.with_sign(sign).build()
    }

    /// Compare the absolute magnitude of two big ints, ignoring their sign.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let a: Tight<10> = (-105).into();
    /// let b = 15.into();
    /// assert!(a.cmp_magnitude(&b).is_gt());
    /// ```
    fn cmp_magnitude(&self, rhs: &Self) -> Ordering {
        for i in (1..=self.len().max(rhs.len())).rev() {
            match (self.get_back(i), rhs.get_back(i)) {
                (Some(1..), None) => return Ordering::Greater,
                (None, Some(1..)) => return Ordering::Less,
                (self_digit, rhs_digit) => match self_digit
                    .unwrap_or_default()
                    .cmp(&rhs_digit.unwrap_or_default())
                {
                    Ordering::Equal => {}
                    ordering => return ordering,
                },
            }
        }
        Ordering::Equal
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
    /// assert_eq!(a.build(), 5.into());
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
    /// assert_eq!(a.build(), 56.into());
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
    /// assert_eq!(a.build(), 65.into());
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
    /// assert_eq!(a.with_sign(Negative).build(), (-9).into());
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
/// assert_eq!(a, 5304.into());
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
    /// assert_eq!(a, 5304.into());
    /// ```
    fn build(self) -> B;
}

/// Represents the sign of a big int; either Positive or Negative.
///
/// ```
/// use big_int::prelude::*;
///
/// let mut a: Tight<10> = 18.into();
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

/// Check if a number is a power of another number.
/// 
/// If `x` is a power of `y`, return `Some(n)` such that
/// `x == y^n`. If not, return `None`.
/// 
/// ```
/// use big_int::prelude::*;
/// 
/// assert_eq!(is_power(2, 3), None);
/// assert_eq!(is_power(16, 4), Some(2));
/// assert_eq!(is_power(27, 3), Some(3));
/// assert_eq!(is_power(256, 2), Some(8));
/// ```
pub fn is_power(mut x: usize, y: usize) -> Option<usize> {
    let mut power = 1;
    loop {
        match x.cmp(&y) {
            Ordering::Equal => return Some(power),
            Ordering::Less => return None,
            Ordering::Greater => {
                power += 1;
                x /= y;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use big_int::prelude::*;

    #[test]
    fn eq() {
        let a = Box::new(unsafe { Tight::<10>::from_raw_parts(vec![0b0110_0101].into(), 0, 8) });
        let b = Box::new(unsafe { Tight::<10>::from_raw_parts(vec![0b0000_0000, 0b0011001, 0b01000000].into(), 10, 18) });
        assert!(a.eq_inner(&b));
    }

    #[test]
    fn convert() {
        let n_4: Loose<4> = 78.into();
        let n_16: Loose<16> = 78.into();
        assert_eq!(n_4, n_16.convert());
    }

    #[test]
    fn convert_2() {
        let n_4: Loose<4> = 136.into();
        let n_64: Loose<64> = 136.into();
        assert_eq!(n_4, n_64.convert());
    }

    #[test]
    fn convert_3() {
        let n_4: Loose<4> = 29.into();
        let n_256: Loose<256> = 29.into();
        assert_eq!(n_256, n_4.convert());
    }

    #[test]
    fn downconvert_special_cases() {
        for n in test_values!([u8; 1000], [u16; 2000], [u32; 4000], [u64; 8000]) {
            let n_4: Tight<4> = n.into();
            let n_16: Tight<16> = n.into();
            let n_64: Tight<64> = n.into();
            let n_256: Tight<256> = n.into();
            assert_eq!(n_4, n_16.clone().convert(), "{n} 16 > 4");
            assert_eq!(n_4, n_64.clone().convert(), "{n} 64 > 4");
            assert_eq!(n_4, n_256.clone().convert(), "{n} 256 > 4");
            assert_eq!(n_16, n_64.clone().convert(), "{n} 64 > 16");
            assert_eq!(n_16, n_256.clone().convert(), "{n} 256 > 16");
            assert_eq!(n_64, n_256.convert(), "{n} 256 > 64");
        }
    }

    #[test]
    fn upconvert_special_cases() {
        for n in test_values!([u8; 1000], [u16; 2000], [u32; 4000], [u64; 8000]) {
            let n_4: Tight<4> = n.into();
            let n_16: Tight<16> = n.into();
            let n_64: Tight<64> = n.into();
            let n_256: Tight<256> = n.into();
            assert_eq!(n_256, n_4.clone().convert(), "{n} 4 > 256");
            assert_eq!(n_256, n_16.clone().convert(), "{n} 16 > 256");
            assert_eq!(n_256, n_64.clone().convert(), "{n} 64 > 256");
            assert_eq!(n_64, n_4.clone().convert(), "{n} 4 > 64");
            assert_eq!(n_64, n_16.clone().convert(), "{n} 16 > 64");
            assert_eq!(n_16, n_4.convert(), "{n} 4 > 16");
        }
    }
}
