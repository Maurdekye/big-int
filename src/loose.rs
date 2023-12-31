//! loosely packed big int implementation.
//! 
//! ```
//! use big_int::prelude::*;
//! 
//! let mut a: Loose<10> = 13.into();
//! a *= 500.into();
//! assert_eq!(a, 6500.into());
//! 
//! a.shr_assign_inner(2);
//! a += 17.into();
//! assert_eq!(a, 82.into());
//! ```


use big_int_proc::BigIntTraits;

use crate::prelude::*;
use std::{collections::VecDeque, vec};

/// A loosely-packed arbitrary base big int implementation. 
/// Supports any base from 2-u64::MAX. 
/// 
/// Each digit requires 8 bytes of storage, making this a somewhat space-inefficient 
/// implementation. however, the lack of additional complexity improves runtime efficiency over the
/// tightly-packed implementation.
/// 
/// ```
/// use big_int::prelude::*;
/// 
/// let a: Loose<10> = 593.into();
/// let b = a * 96.into();
/// assert_eq!(b, 56928.into());
/// ```
#[derive(Clone, Debug, BigIntTraits)]
pub struct Loose<const BASE: usize> {
    sign: Sign,
    digits: Vec<Digit>,
}

impl<const BASE: usize> Loose<BASE> {
    /// Create a new `Loose` int directly from a `Vec` of individual digits.
    ///
    /// Ensure the resulting int is properly normalized, and that no digits are greater than or
    /// equal to the base, to preserve soundness.
    ///
    /// To construct a negative int from raw parts, simply apply the negation
    /// operator (`-`) afterwards.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// assert_eq!(
    ///     -unsafe { Loose::<10>::from_raw_parts(vec![1, 5]) },
    ///     (-15).into()
    /// );
    /// ```
    pub unsafe fn from_raw_parts(digits: Vec<Digit>) -> Self {
        let sign = Positive;
        Loose { sign, digits }
    }
}

impl<const BASE: usize> BigInt<BASE> for Loose<BASE> {
    type Builder = LooseBuilder<{ BASE }>;
    type DigitIterator<'a> = LooseIter<'a, BASE>;

    fn len(&self) -> usize {
        self.digits.len()
    }

    fn get_digit(&self, digit: usize) -> Option<Digit> {
        self.digits.get(digit).copied()
    }

    fn set_digit(&mut self, digit: usize, value: Digit) {
        if let Some(digit) = self.digits.get_mut(digit) {
            *digit = value;
        }
    }

    fn zero() -> Self {
        let sign = Positive;
        let digits = vec![0];
        Loose { sign, digits }
    }

    fn with_sign(self, sign: Sign) -> Self {
        Loose { sign, ..self }
    }

    /// Return a normalized version of the int. Remove trailing zeros, and disable the parity flag
    /// if the resulting number is zero.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// let n = unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) };
    /// assert_eq!(n.normalized(), 83.into());
    /// ```
    fn normalized(self) -> Self {
        match self.digits.iter().position(|digit| *digit != 0) {
            None => Self::zero(),
            Some(pos @ 1..) => Loose {
                digits: self.digits[pos..].to_vec(),
                ..self
            },
            _ => self,
        }
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn set_sign(&mut self, sign: Sign) {
        self.sign = sign;
    }

    fn push_back(&mut self, digit: crate::Digit) {
        self.digits.push(digit);
    }

    fn push_front(&mut self, digit: crate::Digit) {
        self.digits.insert(0, digit);
    }

    fn shr_assign_inner(&mut self, amount: usize) {
        self.digits =
            self.digits[..self.digits.len().checked_sub(amount).unwrap_or_default()].to_vec();
    }

    fn shl_assign_inner(&mut self, amount: usize) {
        self.digits.extend(vec![0; amount]);
    }

    fn iter<'a>(&'a self) -> Self::DigitIterator<'a> {
        LooseIter {
            index: 0,
            back_index: self.len(),
            int: self,
        }
    }
}

/// An iterator over the digits of a `Loose` int.
/// 
/// ```
/// use big_int::prelude::*;
/// use std::iter::Rev;
/// 
/// let a: Loose<10> = 12345.into();
/// let it: LooseIter<10> = a.iter();
/// let rev_it: Rev<LooseIter<10>> = a.iter().rev();
/// assert_eq!(it.collect::<Vec<_>>(), vec![1, 2, 3, 4, 5]);
/// assert_eq!(rev_it.collect::<Vec<_>>(), vec![5, 4, 3, 2, 1]);
/// ```
pub struct LooseIter<'a, const BASE: usize> {
    index: usize,
    back_index: usize,
    int: &'a Loose<BASE>,
}

impl<const BASE: usize> Iterator for LooseIter<'_, BASE> {
    type Item = Digit;

    fn next(&mut self) -> Option<Self::Item> {
        (self.index < self.back_index)
            .then_some(&mut self.index)
            .and_then(|index| {
                *index += 1;
                self.int.digits.get(*index - 1)
            })
            .copied()
    }
}

impl<const BASE: usize> DoubleEndedIterator for LooseIter<'_, BASE> {
    fn next_back(&mut self) -> Option<Self::Item> {
        (self.back_index > self.index)
            .then_some(&mut self.back_index)
            .and_then(|index| {
                *index -= 1;
                self.int.digits.get(*index)
            })
            .copied()
    }
}

/// A builder for a `Loose` int.
/// 
/// You're most likely better off using one of the `From` implementations
/// as opposed to directly building your int via a builder.
/// 
/// ```
/// use big_int::prelude::*;
/// 
/// let mut a = LooseBuilder::<10>::new();
/// a.push_back(5);
/// a.push_back(3);
/// a.push_back(0);
/// a.push_back(4);
/// let a: Loose<10> = a.build();
/// assert_eq!(a, 5304.into());
/// ```
#[derive(Debug)]
pub struct LooseBuilder<const BASE: usize> {
    sign: Sign,
    digits: VecDeque<Digit>,
}

impl<const BASE: usize> BigIntBuilder<BASE> for LooseBuilder<BASE> {
    fn new() -> Self {
        LooseBuilder {
            sign: Positive,
            digits: VecDeque::new(),
        }
    }

    fn push_front(&mut self, digit: Digit) {
        self.digits.push_front(digit);
    }

    fn push_back(&mut self, digit: Digit) {
        self.digits.push_back(digit);
    }

    fn with_sign(self, sign: Sign) -> Self {
        LooseBuilder { sign, ..self }
    }

    fn is_empty(&self) -> bool {
        self.digits.is_empty()
    }
}

impl<const BASE: usize> Build<Loose<BASE>> for LooseBuilder<BASE> {
    fn build(self) -> Loose<BASE> {
        Loose::<BASE>::from(self).normalized()
    }
}

impl<const BASE: usize> From<LooseBuilder<BASE>> for Loose<BASE> {
    fn from(value: LooseBuilder<BASE>) -> Self {
        let sign = value.sign;
        let digits = value.digits.into();
        Loose { sign, digits }
    }
}
