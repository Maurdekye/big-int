//! tightly packed big int implementation, for better memory efficiency.
//!
//! ```
//! use big_int::prelude::*;
//!
//! let mut a: Tight<10> = 13.into();
//! a *= 500.into();
//! assert_eq!(a, 6500.into());
//!
//! a.shr_assign_inner(2);
//! a += 17.into();
//! assert_eq!(a, 82.into());
//! ```

use big_int_proc::BigIntTraits;
use std::collections::VecDeque;

use crate::prelude::*;

/// Represents a single datum of information within a `Tight` int.
/// The size of this value has no impact on the size of individual
/// digits that the number can represent; it only impacts memory and
/// runtime performance. Could be any unsigned type from u8-u128.
pub type Datum = u8;

/// Size of the chosen datum unit, in bits.
pub const DATUM_SIZE: usize = std::mem::size_of::<Datum>() * 8;

/// A tightly-packed arbitrary base big int implementation.
/// Supports any base from 2-u64::MAX.
///
/// In this implementation, bits are tightly packed against one another,
/// requiring only `ceil(log_2(BASE))` bits per digit. Signficiantly more space-efficient for
/// smaller bases compared to the loose implementation. However, the extra indirection contributes
/// to some added overhead.
///
/// ```
/// use big_int::prelude::*;
///
/// let a: Tight<10> = 593.into();
/// let b = a * 96.into();
/// assert_eq!(b, 56928.into());
/// ```
#[derive(Debug, Clone, BigIntTraits)]
pub struct Tight<const BASE: usize> {
    sign: Sign,
    data: VecDeque<Datum>,
    start_offset: usize,
    end_offset: usize,
}

impl<const BASE: usize> Tight<BASE> {
    /// Number of bits required to store a single digit in the chosen `BASE`.
    const BITS_PER_DIGIT: usize = bits_per_digit(BASE);

    /// Construct a `Tight` int directly from raw parts.
    ///
    /// Ensure the following invariants hold true to maintain soundness:
    /// * `start_offset <= end_offset`
    /// * `end_offset <= data.len() * big_int::tight::DATUM_SIZE`
    /// * `(end_offset - start_offset) % Tight::<BASE>::BITS_PER_DIGIT == 0`
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let a: Tight<10> = unsafe { Tight::from_raw_parts(
    ///     vec![0b0001_1001, 0b0101_0000].into(),
    ///     0, 16
    /// ) };
    /// 
    /// assert_eq!(a, 1950.into());
    /// ```
    pub unsafe fn from_raw_parts(
        data: VecDeque<Datum>,
        start_offset: usize,
        end_offset: usize,
    ) -> Self {
        Self {
            sign: Positive,
            data,
            start_offset,
            end_offset,
        }
    }

    /// Return the int with the bits within aligned to the beginning of the data segment
    /// and unnecessary extra data truncated.
    /// 
    /// It's likely unnecessary to invoke this directly unless using `Tight::from_raw_parts`.
    /// 
    /// ```
    /// use big_int::prelude::*;
    /// 
    /// let mut a: Tight<10> = unsafe { Tight::from_raw_parts(
    ///     vec![0b0000_0000, 0b0000_1001, 0b0101_0000, 0b0000_0000].into(),
    ///     12, 20
    /// ) };
    /// assert_eq!(a.aligned(), unsafe { Tight::from_raw_parts(
    ///     vec![0b1001_0101].into(),
    ///     0, 8
    /// ) });
    /// ```
    pub fn aligned(mut self) -> Self {
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
            let left_half_mask = mask!(self.start_offset) << left_half_offset;
            let right_half_mask = mask!(DATUM_SIZE - self.start_offset);
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
            self.start_offset = 0;
            data
        };
        self
    }
}

impl<const BASE: usize> BigInt<{ BASE }> for Tight<BASE> {
    type Builder = TightBuilder<{ BASE }>;
    type DigitIterator<'a> = TightIter<'a, BASE>;

    fn len(&self) -> usize {
        (self.end_offset - self.start_offset) / Self::BITS_PER_DIGIT
    }

    fn get_digit(&self, digit: usize) -> Option<Digit> {
        let mut digit_offset = self.start_offset + digit * Self::BITS_PER_DIGIT;
        if digit_offset >= self.end_offset {
            None
        } else {
            let mut digit_value = 0;
            let mut bits_left_to_pull = Self::BITS_PER_DIGIT;
            while bits_left_to_pull > 0 {
                let datum_index = digit_offset / DATUM_SIZE;
                let bit_in_datum = digit_offset % DATUM_SIZE;
                let bits_available_in_datum = DATUM_SIZE - bit_in_datum;
                let bits_to_take = bits_available_in_datum.min(bits_left_to_pull);
                digit_offset += bits_to_take;
                bits_left_to_pull -= bits_to_take;
                let datum_offset = bits_available_in_datum - bits_to_take;
                let datum_mask: Datum = mask!(bits_to_take) << datum_offset;
                let piece_of_digit = ((self.data[datum_index] & datum_mask) as Digit
                    >> datum_offset)
                    << bits_left_to_pull;
                digit_value |= piece_of_digit;
            }
            Some(digit_value)
        }
    }

    fn set_digit(&mut self, digit: usize, value: Digit) {
        let mut digit_offset = self.start_offset + digit * Self::BITS_PER_DIGIT;
        if digit_offset < self.end_offset {
            let mut bits_left_to_set = Self::BITS_PER_DIGIT;
            while bits_left_to_set > 0 {
                let datum_index = digit_offset / DATUM_SIZE;
                let bit_in_datum = digit_offset % DATUM_SIZE;
                let bits_left_in_datum = DATUM_SIZE - bit_in_datum;
                let bits_to_set = bits_left_in_datum.min(bits_left_to_set);
                digit_offset += bits_to_set;
                bits_left_to_set -= bits_to_set;
                let datum_offset = bits_left_in_datum - bits_to_set;
                let piece_mask = mask!(bits_to_set) << bits_left_to_set;
                let piece_of_digit = ((value & piece_mask) >> bits_left_to_set) << datum_offset;
                let datum_mask = mask!(bits_to_set) << datum_offset;
                self.data[datum_index] &= !datum_mask;
                self.data[datum_index] |= piece_of_digit as Datum;
            }
        }
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
            bits_left_to_set -= bits_to_take;
            let digit_mask = mask!(bits_to_take) << bits_left_to_set;
            let piece_of_digit = (((digit_mask & digit) >> bits_left_to_set)
                << (DATUM_SIZE - bits_to_take))
                >> bit_in_datum;
            self.data[datum_index] |= piece_of_digit as Datum;
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
            let digit_mask = mask!(bits_to_take) << mask_offset;
            bits_left_to_set -= bits_to_take;
            let piece_of_digit =
                ((digit_mask & digit) >> mask_offset) << (DATUM_SIZE - space_left_in_datum);
            self.data[datum_index] |= piece_of_digit as Datum;
        }
    }

    fn shr_assign_inner(&mut self, amount: usize) {
        self.end_offset = self
            .end_offset
            .checked_sub(amount * Self::BITS_PER_DIGIT)
            .unwrap_or_default()
            .max(self.start_offset);
        self.normalize();
    }

    fn shl_assign_inner(&mut self, amount: usize) {
        self.end_offset += Self::BITS_PER_DIGIT * amount;
        let new_len = self.end_offset.div_ceil(DATUM_SIZE);
        let cur_len = self.data.len();
        self.data.extend(vec![0; new_len - cur_len]);
    }

    fn iter<'a>(&'a self) -> Self::DigitIterator<'a> {
        TightIter {
            index: 0,
            back_index: self.len(),
            int: self,
        }
    }

    /// Return a normalized version of the int. Remove trailing zeros, disable the parity flag
    /// if the resulting number is zero, and align the internal bits to the beginning of the
    /// data array.
    fn normalized(mut self) -> Self {
        while self.start_offset < self.end_offset && self.get_digit(0) == Some(0) {
            self.start_offset += Self::BITS_PER_DIGIT;
        }
        if self.start_offset >= self.end_offset {
            Self::zero()
        } else if self.start_offset > 0 {
            self.aligned()
        } else {
            if self.data.len() * DATUM_SIZE >= self.end_offset + DATUM_SIZE {
                self.data = self
                    .data
                    .into_iter()
                    .take(self.end_offset.div_ceil(DATUM_SIZE))
                    .collect();
            }
            self
        }
    }
}

/// An iterator over the digits of a `Tight` int.
///
/// ```
/// use big_int::prelude::*;
/// use std::iter::Rev;
///
/// let a: Tight<10> = 12345.into();
/// let it: TightIter<10> = a.iter();
/// let rev_it: Rev<TightIter<10>> = a.iter().rev();
/// assert_eq!(it.collect::<Vec<_>>(), vec![1, 2, 3, 4, 5]);
/// assert_eq!(rev_it.collect::<Vec<_>>(), vec![5, 4, 3, 2, 1]);
/// ```
pub struct TightIter<'a, const BASE: usize> {
    index: usize,
    back_index: usize,
    int: &'a Tight<BASE>,
}

impl<const BASE: usize> Iterator for TightIter<'_, BASE> {
    type Item = Digit;

    fn next(&mut self) -> Option<Self::Item> {
        (self.index < self.back_index)
            .then_some(&mut self.index)
            .and_then(|index| {
                *index += 1;
                self.int.get_digit(*index - 1)
            })
    }
}

impl<const BASE: usize> DoubleEndedIterator for TightIter<'_, BASE> {
    fn next_back(&mut self) -> Option<Self::Item> {
        (self.back_index > self.index)
            .then_some(&mut self.back_index)
            .and_then(|index| {
                *index -= 1;
                self.int.get_digit(*index)
            })
    }
}

/// A builder for a `Tight` int.
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
#[derive(Debug)]
pub struct TightBuilder<const BASE: usize>(Tight<BASE>);

impl<const BASE: usize> BigIntBuilder<BASE> for TightBuilder<BASE> {
    fn new() -> Self {
        Self(Tight {
            sign: Positive,
            data: VecDeque::new(),
            start_offset: 0,
            end_offset: 0,
        })
    }

    fn push_front(&mut self, digit: Digit) {
        self.0.push_front(digit);
    }

    fn push_back(&mut self, digit: Digit) {
        self.0.push_back(digit);
    }

    fn is_empty(&self) -> bool {
        self.0.start_offset >= self.0.end_offset
    }

    fn with_sign(self, sign: Sign) -> Self {
        Self(self.0.with_sign(sign))
    }
}

impl<const BASE: usize> Build<Tight<BASE>> for TightBuilder<BASE> {
    fn build(self) -> Tight<BASE> {
        self.0.normalized()
    }
}

impl<const BASE: usize> From<TightBuilder<BASE>> for Tight<BASE> {
    fn from(value: TightBuilder<BASE>) -> Self {
        value.0
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
        assert_eq!(builder.0.data, VecDeque::from([0b11010010]));
    }

    #[test]
    fn push_small_digits() {
        let mut builder = TightBuilder::<4>::new();
        builder.push_back(0b11);
        builder.push_back(0b00);
        builder.push_back(0b11);
        builder.push_back(0b00);
        assert_eq!(builder.0.data, VecDeque::from([0b11001100]));
    }

    #[test]
    fn push_medium_digits() {
        let mut builder = TightBuilder::<8192>::new();
        builder.push_back(0b1010101010101);
        builder.push_back(0b1111111111111);
        assert_eq!(
            builder.0.data,
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
            builder.0.data,
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
        assert_eq!(builder.0.data, VecDeque::from([0b01001011]));
    }

    #[test]
    fn push_front_small_digits() {
        let mut builder = TightBuilder::<4>::new();
        builder.push_front(0b11);
        builder.push_front(0b00);
        builder.push_front(0b11);
        builder.push_front(0b00);
        assert_eq!(builder.0.data, VecDeque::from([0b00110011]));
    }

    #[test]
    fn push_front_medium_digits() {
        let mut builder = TightBuilder::<8192>::new();
        builder.push_front(0b1111111111111);
        builder.push_front(0b1010101010101);
        assert_eq!(
            builder.0.data,
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
            builder.0.data,
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
        let number: Tight<8192> = builder.build().into();
        assert_eq!(
            number.data,
            vec![0b10101010, 0b10101111, 0b11111111, 0b11000000]
        );
    }

    #[test]
    fn build_2() {
        let builder = TightBuilder::<10>::new();
        let number: Tight<10> = builder.build().into();
        assert_eq!(number.data, vec![0]);
    }

    #[test]
    fn build_3() {
        let mut builder = TightBuilder::<10>::new();
        builder.push_back(1);
        builder.push_back(2);
        builder.push_back(5);
        assert_eq!(
            Tight::<10>::from(builder),
            Tight::<10> {
                sign: Positive,
                data: VecDeque::from(vec![18, 80]),
                start_offset: 0,
                end_offset: 12,
            }
        );
    }

    #[test]
    fn get_digit() {
        let mut builder = TightBuilder::<10>::new();
        builder.push_front(4);
        builder.push_front(3);
        builder.push_front(2);
        builder.push_front(1);
        let int: Tight<10> = builder.into();
        assert_eq!(int.get_digit(0), Some(1));
        assert_eq!(int.get_digit(1), Some(2));
        assert_eq!(int.get_digit(2), Some(3));
        assert_eq!(int.get_digit(3), Some(4));
        assert_eq!(int.get_digit(4), None);
    }

    #[test]
    fn set_digit() {
        let mut builder = TightBuilder::<10>::new();
        builder.push_back(1);
        builder.push_back(2);
        builder.push_back(3);
        builder.push_back(4);
        let mut int: Tight<10> = builder.into();
        int.set_digit(1, 8);
        int.set_digit(2, 0);
        assert_eq!(int.get_digit(0), Some(1));
        assert_eq!(int.get_digit(1), Some(8));
        assert_eq!(int.get_digit(2), Some(0));
        assert_eq!(int.get_digit(3), Some(4));
        assert_eq!(int.get_digit(4), None);
    }

    // macro_rules! base_conv_print {
    //     ($d:expr; $($b:literal),*) => {
    //         let a: Tight<256> = $d.into();
    //         printbytes!(a.data);
    //         $(
    //             let a: Tight<$b> = a.convert();
    //             println!("{}: ", $b);
    //             printbytes!(a.data);
    //         )*
    //     };
    // }

    // #[test]
    // fn conversion_3() {
    //     base_conv_print!([255, 0, 0, 0]; 128, 64, 32, 16, 8, 4, 2);
    // }
}
