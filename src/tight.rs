//! ## `tight` - More compact BigInt, for better memory efficiency

use std::collections::VecDeque;

use crate::{BigIntBuilder, BigIntImplementation, Digit, Sign};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tight<const BASE: usize> {
    sign: bool,
    data: Vec<u8>,
    digits: usize,
}

impl<const BASE: usize> BigIntImplementation<{ BASE }> for Tight<BASE> {
    type Builder = TightBuilder<{ BASE }>;
    type DigitIterator<'a> = TightIter<'a, BASE>;

    fn len(&self) -> usize {
        todo!()
    }

    fn get_digit(&self, digit: usize) -> Option<Digit> {
        todo!()
    }

    fn set_digit(&mut self, digit: usize, value: Digit) -> Option<Digit> {
        todo!()
    }

    fn zero() -> Self {
        todo!()
    }

    fn sign(&self) -> Sign {
        todo!()
    }

    fn with_sign(self, sign: Sign) -> Self {
        todo!()
    }

    fn set_sign(&mut self, sign: Sign) {
        todo!()
    }

    fn push_back(&mut self, digit: Digit) {
        todo!()
    }
    fn push_front(&mut self, digit: Digit) {
        todo!()
    }

    fn shr(self, amount: usize) -> Self {
        todo!()
    }
    fn shr_assign(&mut self, amount: usize) {
        todo!()
    }

    fn shl(self, amount: usize) -> Self {
        todo!()
    }
    fn shl_assign(&mut self, amount: usize) {
        todo!()
    }

    fn iter<'a>(&'a self) -> Self::DigitIterator<'a> {
        todo!()
    }

    fn normalized(self) -> Self {
        todo!()
    }
}

pub struct TightIter<'a, const BASE: usize> {
    index: usize,
    back_index: usize,
    int: &'a Tight<BASE>,
}

impl<const BASE: usize> Iterator for TightIter<'_, BASE> {
    type Item = Digit;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

impl<const BASE: usize> DoubleEndedIterator for TightIter<'_, BASE> {
    fn next_back(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

#[derive(Debug)]
pub struct TightBuilder<const BASE: usize> {
    sign: bool,
    data: VecDeque<u8>,
    start_offset: usize,
    digits: usize,
}

impl<const BASE: usize> BigIntBuilder<{ BASE }> for TightBuilder<BASE> {
    fn new() -> Self {
        todo!()
    }

    fn push_front(&mut self, digit: crate::Digit) {
        todo!()
    }

    fn push_back(&mut self, digit: crate::Digit) {
        todo!()
    }

    fn is_empty(&self) -> bool {
        todo!()
    }

    fn with_sign(self, sign: crate::Sign) -> Self {
        todo!()
    }
}

impl<const BASE: usize> From<TightBuilder<{ BASE }>> for Tight<BASE> {
    fn from(value: TightBuilder<{ BASE }>) -> Self {
        todo!()
    }
}