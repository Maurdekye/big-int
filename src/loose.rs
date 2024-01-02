//! loosely packed big int implementation.
//!
//! ```
//! use big_int::prelude::*;
//!
//! let mut a: Loose<10> = 13.into();
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

use crate::prelude::*;
use std::{collections::VecDeque, vec};

macro_rules! loose_definition {
    ($name:ident, $denormal_name:ident, $builder_name:ident, $data_type:ty) => {

        /// Shorthand for a denormalized loose int.
        pub type $denormal_name<const BASE: usize> = Denormal<BASE, $name<BASE>>;

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
        pub struct $name<const BASE: usize> {
            sign: Sign,
            digits: Vec<$data_type>,
        }

        impl<const BASE: usize> $name<BASE> {
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
                let digits = digits.into_iter().map(|digit| digit as $data_type).collect();
                $name { sign, digits }
            }
        }

        impl<const BASE: usize> BigInt<BASE> for $name<BASE> {
            type Builder = $builder_name<{ BASE }>;
            type Denormal = Denormal<BASE, Self>;

            fn len(&self) -> usize {
                self.digits.len()
            }

            fn get_digit(&self, digit: usize) -> Option<Digit> {
                self.digits.get(digit).map(|digit| *digit as Digit)
            }

            fn set_digit(&mut self, digit: usize, value: Digit) {
                if let Some(digit) = self.digits.get_mut(digit) {
                    *digit = value as $data_type;
                }
            }

            fn zero() -> Self {
                let sign = Positive;
                let digits = vec![0];
                $name { sign, digits }
            }

            fn with_sign(self, sign: Sign) -> Self {
                $name { sign, ..self }
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
                    Some(pos @ 1..) => $name {
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
                self.digits.push(digit as $data_type);
            }

            unsafe fn push_front(&mut self, digit: crate::Digit) {
                self.digits.insert(0, digit as $data_type);
            }

            unsafe fn shr_assign_inner(&mut self, amount: usize) {
                self.digits =
                    self.digits[..self.digits.len().checked_sub(amount).unwrap_or_default()].to_vec();
            }

            fn shl_assign_inner(&mut self, amount: usize) {
                self.digits.extend(vec![0; amount]);
            }

            unsafe fn pop_back(&mut self) -> Option<Digit> {
                self.digits.pop().map(|digit| digit as Digit)
            }

            unsafe fn pop_front(&mut self) -> Option<Digit> {
                (!self.digits.is_empty()).then(|| self.digits.remove(0) as Digit)
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
        /// let a: Loose<10> = a.into();
        /// assert_eq!(a, 5304.into());
        /// ```
        #[derive(Debug)]
        pub struct $builder_name<const BASE: usize> {
            sign: Sign,
            digits: VecDeque<$data_type>,
        }

        impl<const BASE: usize> BigIntBuilder<BASE> for $builder_name<BASE> {
            fn new() -> Self {
                $builder_name {
                    sign: Positive,
                    digits: VecDeque::new(),
                }
            }

            fn push_front(&mut self, digit: Digit) {
                self.digits.push_front(digit as $data_type);
            }

            fn push_back(&mut self, digit: Digit) {
                self.digits.push_back(digit as $data_type);
            }

            fn with_sign(self, sign: Sign) -> Self {
                $builder_name { sign, ..self }
            }

            fn is_empty(&self) -> bool {
                self.digits.is_empty()
            }
        }

        impl<const BASE: usize> From<$builder_name<BASE>> for Denormal<BASE, $name<BASE>> {
            fn from(value: $builder_name<BASE>) -> Self {
                let sign = value.sign;
                let digits = value.digits.into();
                Denormal($name { sign, digits })
            }
        }

        impl<const BASE: usize> From<$builder_name<BASE>> for $name<BASE> {
            fn from(value: $builder_name<BASE>) -> Self {
                let denormal: <Self as BigInt<BASE>>::Denormal = value.into();
                denormal.unwrap()
            }
        }
    };
}

loose_definition!(LooseBytes, DenormalLooseBytes, LooseBytesBuilder, u8);
loose_definition!(LooseShorts, DenormalLooseShorts, LooseShortsBuilder, u16);
loose_definition!(LooseWords, DenormalLooseWords, LooseWordsBuilder, u32);
loose_definition!(Loose, DenormalLoose, LooseBuilder, u64);