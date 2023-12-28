//! ## `tight` - More compact BigInt, for better memory efficiency

use std::{collections::VecDeque, io::empty};

use crate::prelude::*;

type Datum = u8;

const DATUM_SIZE: usize = std::mem::size_of::<Datum>() * 8;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tight<const BASE: usize> {
    sign: Sign,
    data: VecDeque<Datum>,
    start_offset: usize,
    end_offset: usize,
}

impl<const BASE: usize> Tight<BASE> {
    const BITS_PER_DIGIT: usize = bits_per_digit(BASE);
}

impl<const BASE: usize> BigIntImplementation<{ BASE }> for Tight<BASE> {
    type Builder = TightBuilder<{ BASE }>;
    type DigitIterator<'a> = TightIter<'a, BASE>;

    fn len(&self) -> usize {
        (self.end_offset - self.start_offset) / Self::BITS_PER_DIGIT
    }

    fn get_digit(&self, digit: usize) -> Option<Digit> {
        todo!()
    }

    fn set_digit(&mut self, digit: usize, value: Digit) -> Option<Digit> {
        todo!()
    }

    fn zero() -> Self {
        Self {
            sign: Positive,
            data: VecDeque::from(vec![0; Self::BITS_PER_DIGIT.div_ceil(DATUM_SIZE)]),
            start_offset: 0,
            end_offset: Self::BITS_PER_DIGIT,
        }
    }

    fn sign(&self) -> Sign {
        self.sign
    }

    fn with_sign(self, sign: Sign) -> Self {
        Self { sign, ..self }
    }

    fn set_sign(&mut self, sign: Sign) {
        self.sign = sign;
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
        TightIter {
            index: 0,
            back_index: todo!(),
            int: self,
        }
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
    sign: Sign,
    data: VecDeque<Datum>,
    start_offset: usize,
    end_offset: usize,
}

impl<const BASE: usize> TightBuilder<BASE> {
    const BITS_PER_DIGIT: usize = bits_per_digit(BASE);

    fn aligned(mut self) -> Self {
        let empty_cells = self.start_offset / DATUM_SIZE;
        self.start_offset -= empty_cells * DATUM_SIZE;
        self.end_offset -= empty_cells * DATUM_SIZE;
        let data_cells = self.data.into_iter().skip(empty_cells);
        self.data = if self.start_offset == 0 {
            data_cells.collect()
        } else {
            let data_length = (self.end_offset - self.start_offset).div_ceil(DATUM_SIZE);
            let mut data = VecDeque::new();
            let left_half_offset = DATUM_SIZE - self.start_offset;
            let left_half_mask = ((1 << self.start_offset) - 1) << left_half_offset;
            let right_half_mask = (1 << (DATUM_SIZE - self.start_offset)) - 1;
            let mut right_half = None;
            for datum in data_cells {
                if let Some(right_half) = right_half {
                    let left_half = (datum & left_half_mask) >> left_half_offset;
                    let aligned_datum = left_half | right_half;
                    data.push_back(aligned_datum);
                    if data.len() >= data_length {
                        break;
                    }
                }
                right_half = Some((datum & right_half_mask) << self.start_offset);
            }
            if let Some(right_half) = right_half {
                if data.len() < data_length {
                    data.push_back(right_half);
                }
            }
            self.end_offset -= self.start_offset;
            data
        };
        self
    }
}

impl<const BASE: usize> BigIntBuilder<{ BASE }> for TightBuilder<BASE> {
    fn new() -> Self {
        TightBuilder {
            sign: Positive,
            data: VecDeque::new(),
            start_offset: 0,
            end_offset: 0,
        }
    }

    fn push_front(&mut self, digit: Digit) {
        let mut bits_left_to_set = Self::BITS_PER_DIGIT;
        while bits_left_to_set > 0 {
            if self.start_offset == 0 {
                self.data.push_front(0);
                self.start_offset += DATUM_SIZE;
                self.end_offset += DATUM_SIZE;
            }
            let datum_index = (self.start_offset - 1) / DATUM_SIZE;
            let space_left_in_datum = (self.start_offset - 1) % DATUM_SIZE + 1;
            let bits_to_take = space_left_in_datum.min(bits_left_to_set);
            self.start_offset -= bits_to_take;
            let mask_offset = Self::BITS_PER_DIGIT - bits_left_to_set;
            let digit_mask = ((1 << bits_to_take) - 1) << mask_offset;
            bits_left_to_set = bits_left_to_set
                .checked_sub(space_left_in_datum)
                .unwrap_or_default();
            let piece_of_digit =
                ((digit_mask & digit) >> mask_offset) << (DATUM_SIZE - space_left_in_datum);
            self.data[datum_index] |= piece_of_digit as Datum;
        }
    }

    fn push_back(&mut self, digit: Digit) {
        let mut bits_left_to_set = Self::BITS_PER_DIGIT;
        while bits_left_to_set > 0 {
            let datum_index = self.end_offset / DATUM_SIZE;
            if datum_index >= self.data.len() {
                self.data.push_back(0);
            }
            let bit_in_datum = self.end_offset % DATUM_SIZE;
            let space_left_in_datum = DATUM_SIZE - bit_in_datum;
            let bits_to_take = space_left_in_datum.min(bits_left_to_set);
            self.end_offset += bits_to_take;
            bits_left_to_set = bits_left_to_set
                .checked_sub(space_left_in_datum)
                .unwrap_or_default();
            let digit_mask = ((1 << bits_to_take) - 1) << bits_left_to_set;
            let piece_of_digit = (((digit_mask & digit) >> bits_left_to_set)
                << (DATUM_SIZE - bits_to_take))
                >> bit_in_datum;
            self.data[datum_index] |= piece_of_digit as Datum;
        }
    }

    fn is_empty(&self) -> bool {
        self.start_offset == self.end_offset
    }

    fn with_sign(self, sign: Sign) -> Self {
        Self { sign, ..self }
    }
}

impl<const BASE: usize> From<TightBuilder<{ BASE }>> for Tight<BASE> {
    fn from(value: TightBuilder<{ BASE }>) -> Self {
        if value.is_empty() {
            Self::zero()
        } else {
            let aligned = value.aligned();
            Self {
                sign: aligned.sign,
                data: aligned.data,
                start_offset: aligned.start_offset,
                end_offset: aligned.end_offset,
            }
        }
    }
}

const fn bits_per_digit(base: usize) -> usize {
    let mut bits = 1;
    let mut max_base_of_bits = 2;
    while max_base_of_bits < base {
        bits += 1;
        max_base_of_bits <<= 1;
    }
    bits
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_binary_digits() {
        let mut builder = TightBuilder::<2>::new();
        builder.push_back(1);
        builder.push_back(1);
        builder.push_back(0);
        builder.push_back(1);
        builder.push_back(0);
        builder.push_back(0);
        builder.push_back(1);
        assert_eq!(builder.data, VecDeque::from([0b11010010]));
    }

    #[test]
    fn push_small_digits() {
        let mut builder = TightBuilder::<4>::new();
        builder.push_back(0b11);
        builder.push_back(0b00);
        builder.push_back(0b11);
        builder.push_back(0b00);
        assert_eq!(builder.data, VecDeque::from([0b11001100]));
    }

    #[test]
    fn push_medium_digits() {
        let mut builder = TightBuilder::<8192>::new();
        builder.push_back(0b1010101010101);
        builder.push_back(0b1111111111111);
        assert_eq!(
            builder.data,
            VecDeque::from([0b10101010, 0b10101111, 0b11111111, 0b11000000])
        );
    }

    #[test]
    fn push_large_digits() {
        let mut builder = TightBuilder::<1048576>::new();
        builder.push_back(0b11111111111111111111);
        builder.push_back(0b10010010010010010010);
        builder.push_back(0b01101101101101101101);
        assert_eq!(
            builder.data,
            VecDeque::from([
                0b11111111, 0b11111111, 0b11111001, 0b00100100, 0b10010010, 0b01101101, 0b10110110,
                0b11010000
            ])
        );
    }

    #[test]
    fn push_front_binary_digits() {
        let mut builder = TightBuilder::<2>::new();
        builder.push_front(1);
        builder.push_front(1);
        builder.push_front(0);
        builder.push_front(1);
        builder.push_front(0);
        builder.push_front(0);
        builder.push_front(1);
        assert_eq!(builder.data, VecDeque::from([0b01001011]));
    }

    #[test]
    fn push_front_small_digits() {
        let mut builder = TightBuilder::<4>::new();
        builder.push_front(0b11);
        builder.push_front(0b00);
        builder.push_front(0b11);
        builder.push_front(0b00);
        assert_eq!(builder.data, VecDeque::from([0b00110011]));
    }

    #[test]
    fn push_front_medium_digits() {
        let mut builder = TightBuilder::<8192>::new();
        builder.push_front(0b1111111111111);
        builder.push_front(0b1010101010101);
        assert_eq!(
            builder.data,
            VecDeque::from([0b00000010, 0b10101010, 0b10111111, 0b11111111])
        );
    }

    #[test]
    fn push_front_large_digits() {
        let mut builder = TightBuilder::<1048576>::new();
        builder.push_front(0b11111111111111111111);
        builder.push_front(0b10010010010010010010);
        builder.push_front(0b01101101101101101101);
        assert_eq!(
            builder.data,
            VecDeque::from([
                0b00000110, 0b11011011, 0b01101101, 0b10010010, 0b01001001, 0b00101111, 0b11111111,
                0b11111111
            ])
        );
    }

    #[test]
    fn build() {
        let mut builder = TightBuilder::<8192>::new();
        builder.push_front(0b1111111111111);
        builder.push_front(0b1010101010101);
        let number: Tight<8192> = builder.into();
        assert_eq!(number.data, vec![0b10101010, 0b10101111, 0b11111111, 0b11000000]);
    }

    #[test]
    fn build_2() {
        let builder = TightBuilder::<10>::new();
        let number: Tight<10> = builder.into();
        assert_eq!(number.data, vec![0]);
    }
}
