use std::{collections::VecDeque, mem, vec};
use crate::prelude::*;

pub type LooseInt<const BASE: usize> = BigInt<BASE, Loose<BASE>>;

/// `Loose`: represents an arbitrary-size integer in base `BASE`.
///
/// `BASE` may be anywhere from 2-u64::MAX.
#[derive(Clone, Debug, PartialEq, Eq)]
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
    ///     -BigInt(unsafe { Loose::<10>::from_raw_parts(vec![1, 5]) }),
    ///     (-15).into()
    /// );
    /// ```
    pub unsafe fn from_raw_parts(digits: Vec<Digit>) -> Self {
        let sign = Positive;
        Loose { sign, digits }
    }

    /// Extract the underlying digit Vec from the int.
    ///
    /// Can only be used to recreate the original int with the unsafe `from_raw_parts` fn.
    ///
    /// ```
    /// use big_int::prelude::*;
    ///
    /// assert_eq!(
    ///     LooseInt::<10>::from(539).0.digits(),
    ///     vec![5, 3, 9]
    /// );
    /// ```
    pub fn digits(self) -> Vec<Digit> {
        self.digits
    }
}

impl<const BASE: usize> BigIntImplementation<BASE> for Loose<BASE> {
    type Builder = LooseBuilder<{ BASE }>;

    fn len(&self) -> usize {
        self.digits.len()
    }

    fn get_digit(&self, digit: usize) -> Option<Digit> {
        self.digits.get(digit).copied()
    }

    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: Loose<10> = unsafe { Loose::from_raw_parts(vec![1, 2]) };
    /// a.set_digit(1, 0);
    /// assert_eq!(a, unsafe { Loose::from_raw_parts(vec![1, 0]) });
    /// ```
    fn set_digit(&mut self, digit: usize, value: Digit) -> Option<Digit> {
        self.digits
            .get_mut(digit)
            .map(|digit| mem::replace(digit, value))
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
    /// let n = BigInt(unsafe { Loose::<10>::from_raw_parts(vec![0, 0, 8, 3]) });
    /// assert_eq!(n.normalized(), 83.into());
    /// ```
    fn normalized(self) -> Self {
        match self.digits.iter().position(|digit| *digit != 0) {
            None => Self::zero(),
            Some(pos @ 1..) => Loose {
                sign: self.sign,
                digits: self.digits[pos..].to_vec(),
            },
            _ => self,
        }
    }

    type DigitIterator<'a> = LooseIter<'a, BASE>;

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

    fn shr(mut self, amount: usize) -> Self {
        self.shr_assign(amount);
        self
    }

    fn shr_assign(&mut self, amount: usize) {
        self.digits =
            self.digits[..self.digits.len().checked_sub(amount).unwrap_or_default()].to_vec();
    }

    fn shl(mut self, amount: usize) -> Self {
        self.shl_assign(amount);
        self
    }

    fn shl_assign(&mut self, amount: usize) {
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

impl<const BASE: usize> From<LooseBuilder<BASE>> for Loose<BASE> {
    fn from(value: LooseBuilder<BASE>) -> Self {
        let sign = value.sign;
        let digits = value.digits.into();
        Loose { sign, digits }.normalized()
    }
}
