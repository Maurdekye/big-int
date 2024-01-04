//! tightly packed big int implementation, for better memory efficiency.
//!
//! ```
//! use big_int::prelude::*;
//!
//! let mut a: Tight<10> = 13.into();
//! a *= 500.into();
//! assert_eq!(a, 6500.into());
//! 
//! unsafe {
//!     a.shr_assign_inner(2);
//! }
//! a += 17.into();
//! assert_eq!(a, 82.into());
//! ```

use big_int_proc::BigIntTraits;
use std::collections::VecDeque;

use crate::prelude::*;

mod tests;

/// Represents a single datum of information within a `Tight` int.
/// The size of this value has no impact on the size of individual
/// digits that the number can represent; it only impacts memory and
/// runtime performance. Could be any unsigned type from u8-u128.
pub type Datum = u8;

/// Size of the chosen datum unit, in bits.
pub const DATUM_SIZE: usize = std::mem::size_of::<Datum>() * 8;

/// Shorthand for a denormalized loose int.
pub type DenormalTight<const BASE: usize> = Denormal<BASE, Tight<BASE>>;

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
    type Denormal = Denormal<BASE, Self>;

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

    unsafe fn push_front(&mut self, digit: Digit) {
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

    unsafe fn shr_assign_inner(&mut self, amount: usize) {
        self.end_offset = self
            .end_offset
            .checked_sub(amount * Self::BITS_PER_DIGIT)
            .unwrap_or_default()
            .max(self.start_offset);
        self.normalize();
    }

    unsafe fn shl_assign_inner(&mut self, amount: usize) {
        self.end_offset += Self::BITS_PER_DIGIT * amount;
        let new_len = self.end_offset.div_ceil(DATUM_SIZE);
        let cur_len = self.data.len();
        self.data.extend(vec![0; new_len - cur_len]);
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

    unsafe fn pop_front(&mut self) -> Option<Digit> {
        let digit = self.get_digit(0);
        if digit.is_some() {
            self.start_offset += Self::BITS_PER_DIGIT;
            if self.start_offset >= DATUM_SIZE {
                let new_start_offset = self.start_offset % DATUM_SIZE;
                let offset_shift = self.start_offset - new_start_offset;
                for _ in 0..self.start_offset / DATUM_SIZE {
                    self.data.pop_front();
                }
                self.start_offset = new_start_offset;
                self.end_offset -= offset_shift;
            }
        }
        digit
    }

    unsafe fn pop_back(&mut self) -> Option<Digit> {
        let digit = self.get_back(1);
        if digit.is_some() {
            self.end_offset = self
                .end_offset
                .checked_sub(Self::BITS_PER_DIGIT)
                .unwrap_or_default()
                .max(self.start_offset);
            for _ in 0..self.data.len() - self.end_offset.div_ceil(DATUM_SIZE) {
                self.data.pop_back();
            }
        }
        digit
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
/// let a: Tight<10> = a.into();
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
        unsafe { self.0.push_front(digit) };
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

impl<const BASE: usize> From<TightBuilder<BASE>> for Denormal<BASE, Tight<BASE>> {
    fn from(value: TightBuilder<BASE>) -> Self {
        Denormal(value.0)
    }
}

impl<const BASE: usize> From<TightBuilder<BASE>> for Tight<BASE> {
    fn from(value: TightBuilder<BASE>) -> Self {
        let denormal: <Self as BigInt<BASE>>::Denormal = value.into();
        denormal.unwrap()
    }
}