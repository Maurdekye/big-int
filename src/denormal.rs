//! Denormalized numbers.
//!
//! A denormalized number may not be in a consistent form, and may behave in
//! unexpected ways while performing mathematical operations. It is typically best
//! practice to normalize a denormalized number before using it in other contexts.
//!
//! Sometimes, however, maintaining a number in a denormalized state is desirable for
//! one reason or another; for example, performing normalization is a nonzero performance
//! cost; you may save some computation by performing several consecutive operations in a row
//! on a denormalized number before finally normalizing it at the end. Additionally, trailing
//! zeros may be desirable to maintain, for data manipulation purposes.
//!
//! ```
//! use big_int::prelude::*;
//!
//! let a: Tight<10> = 194.into();
//! let a: DenormalTight<10> = a.sub_inner::<Tight<10>, Tight<10>>(100.into());
//! assert_eq!(format!("{a}"), "094".to_string());
//! let a: Tight<10> = a.unwrap();
//! assert_eq!(format!("{a}"), "94".to_string());
//! ```
use crate::*;

/// Represents a denormalized number.
///
/// A denormalized number may not be in a consistent form, and may behave in
/// unexpected ways while performing mathematical operations. It is typically best
/// practice to normalize a denormalized number before using it in other contexts.
///
/// Sometimes, however, maintaining a number in a denormalized state is desirable for
/// one reason or another; for example, performing normalization is a nonzero performance
/// cost; you may save some computation by performing several consecutive operations in a row
/// on a denormalized number before finally normalizing it at the end. Additionally, trailing
/// zeros may be desirable to maintain, for data manipulation purposes.
///
/// ```
/// use big_int::prelude::*;
///
/// let a: Tight<10> = 194.into();
/// let a: DenormalTight<10> = a.sub_inner::<Tight<10>, Tight<10>>(100.into());
/// assert_eq!(format!("{a}"), "094".to_string());
/// let a: Tight<10> = a.unwrap();
/// assert_eq!(format!("{a}"), "94".to_string());
/// ```
#[derive(Debug, Clone)]
pub struct Denormal<const BASE: usize, B: BigInt<{ BASE }>>(pub(crate) B);

impl<const BASE: usize, B: BigInt<{ BASE }>> BigInt<BASE> for Denormal<BASE, B> {
    type Builder = DenormalBuilder<BASE, B::Builder>;
    type Denormal = Self;

    // required methods

    fn len(&self) -> usize {
        self.0.len()
    }

    fn get_digit(&self, digit: usize) -> Option<Digit> {
        self.0.get_digit(digit)
    }

    fn set_digit(&mut self, digit: usize, value: Digit) {
        self.0.set_digit(digit, value)
    }

    fn zero() -> Self {
        B::zero().into()
    }

    fn sign(&self) -> Sign {
        self.0.sign()
    }

    fn with_sign(self, sign: Sign) -> Self {
        self.0.with_sign(sign).into()
    }

    fn set_sign(&mut self, sign: Sign) {
        self.0.set_sign(sign)
    }

    fn push_back(&mut self, digit: Digit) {
        self.0.push_back(digit)
    }

    unsafe fn push_front(&mut self, digit: Digit) {
        self.0.push_front(digit)
    }

    unsafe fn pop_back(&mut self) -> Option<Digit> {
        self.0.pop_back()
    }

    unsafe fn pop_front(&mut self) -> Option<Digit> {
        self.0.pop_front()
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    fn normalized(self) -> Self {
        self.0.normalized().into()
    }

    fn normalize(&mut self) {
        self.0.normalize();
    }

    unsafe fn shl_assign_inner(&mut self, amount: usize) {
        self.0.shl_assign_inner(amount);
    }

    fn shl_inner(self, amount: usize) -> Self::Denormal {
        unsafe { self.0.shl_inner(amount).unsafe_into() }.into()
    }

    unsafe fn shr_assign_inner(&mut self, amount: usize) {
        self.0.shr_assign_inner(amount)
    }

    fn shr_inner(self, amount: usize) -> Self::Denormal {
        unsafe { self.0.shr_inner(amount).unsafe_into() }.into()
    }

    fn div_rem<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<(OUT, OUT), BigIntError> {
        self.div_rem_inner::<RHS, OUT>(rhs)
            .map(|(q, r)| unsafe { (q.unsafe_into(), r.unsafe_into()) })
    }

    fn exp<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<OUT, BigIntError> {
        self.exp_inner::<RHS, OUT>(rhs)
            .map(|x| unsafe { x.unsafe_into() })
    }

    fn log<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<OUT, BigIntError> {
        self.log_inner::<RHS, OUT>(rhs)
            .map(|x| unsafe { x.unsafe_into() })
    }

    fn root<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<OUT, BigIntError> {
        self.root_inner::<RHS, OUT>(rhs)
            .map(|x| unsafe { x.unsafe_into() })
    }

    fn sqrt<OUT: BigInt<{ BASE }>>(self) -> Result<OUT, BigIntError> {
        self.sqrt_inner::<OUT>().map(|x| unsafe { x.unsafe_into() })
    }

    fn convert<const TO: usize, OUT: BigInt<{ TO }>>(self) -> OUT {
        unsafe { self.convert_inner::<TO, OUT>().unsafe_into() }
    }

    fn get_back_inner(&self, index: usize) -> Option<Digit> {
        self.0.get_back_inner(index)
    }

    fn default_inner() -> Self {
        Self(B::default_inner())
    }

    fn fmt_inner(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_inner(f)
    }

    fn partial_cmp_inner<RHS: BigInt<{ BASE }>>(&self, other: &RHS) -> Option<Ordering> {
        self.0.partial_cmp_inner(other)
    }

    fn cmp_inner<RHS: BigInt<{ BASE }>>(&self, other: &RHS) -> Ordering {
        self.0.cmp_inner(other)
    }

    fn eq_inner<RHS: BigInt<{ BASE }>>(&self, other: &RHS) -> bool {
        self.0.eq_inner(other)
    }

    fn neg_inner(self) -> Self::Denormal {
        unsafe { self.0.neg_inner().unsafe_into() }.into()
    }

    fn add_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(self, rhs: RHS) -> OUT::Denormal {
        unsafe { self.0.add_inner::<RHS, OUT>(rhs).unsafe_into() }.into()
    }

    unsafe fn add_assign_inner<RHS: BigInt<{ BASE }>>(&mut self, rhs: RHS) {
        self.0.add_assign_inner(rhs)
    }

    fn sub_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> OUT::Denormal {
        unsafe { self.0.sub_inner::<RHS, OUT>(rhs).unsafe_into() }.into()
    }

    unsafe fn sub_assign_inner<RHS: BigInt<{ BASE }>>(&mut self, rhs: RHS) {
        self.0.sub_assign_inner(rhs)
    }

    fn mul_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> OUT::Denormal {
        unsafe { self.0.mul_inner::<RHS, OUT>(rhs).unsafe_into() }.into()
    }

    unsafe fn mul_assign_inner<RHS: BigInt<{ BASE }>>(&mut self, rhs: RHS) {
        self.0.mul_assign_inner(rhs)
    }

    fn div_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(self, rhs: RHS) -> OUT::Denormal {
        unsafe { self.0.div_inner::<RHS, OUT>(rhs).unsafe_into() }.into()
    }

    unsafe fn div_assign_inner<RHS: BigInt<{ BASE }>>(&mut self, rhs: RHS) {
        self.0.div_assign_inner(rhs)
    }

    fn from_str_inner(s: &str) -> Result<Self::Denormal, BigIntError> {
        B::from_str_inner(s).map(|x| unsafe { x.unsafe_into() }.into())
    }

    fn from_iter_inner<T: IntoIterator<Item = Digit>>(iter: T) -> Self::Denormal {
        unsafe { B::from_iter_inner(iter).unsafe_into() }.into()
    }

    unsafe fn next_inner(&mut self) -> Option<Digit> {
        self.0.next_inner()
    }

    unsafe fn next_back_inner(&mut self) -> Option<Digit> {
        self.0.next_back_inner()
    }

    fn from_u128_inner(value: u128) -> Self::Denormal {
        unsafe { B::from_u128_inner(value).unsafe_into() }.into()
    }

    fn from_i128_inner(value: i128) -> Self::Denormal {
        unsafe { B::from_i128_inner(value).unsafe_into() }.into()
    }

    fn into_u128_inner(self) -> u128 {
        self.0.into_u128_inner()
    }

    fn into_i128_inner(self) -> i128 {
        self.0.into_i128_inner()
    }

    fn div_rem_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<(OUT::Denormal, OUT::Denormal), BigIntError> {
        self.0.div_rem_inner::<RHS, OUT>(rhs).map(|(q, r)| {
            (
                unsafe { q.unsafe_into() }.into(),
                unsafe { r.unsafe_into() }.into(),
            )
        })
    }

    fn exp_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<OUT::Denormal, BigIntError> {
        self.0
            .exp_inner::<RHS, OUT>(rhs)
            .map(|x| unsafe { x.unsafe_into() }.into())
    }

    fn log_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<OUT::Denormal, BigIntError> {
        self.0
            .log_inner::<RHS, OUT>(rhs)
            .map(|x| unsafe { x.unsafe_into() }.into())
    }

    fn sqrt_inner<OUT: BigInt<{ BASE }>>(self) -> Result<OUT::Denormal, BigIntError> {
        self.0
            .sqrt_inner::<OUT>()
            .map(|x| unsafe { x.unsafe_into() }.into())
    }

    fn root_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<OUT::Denormal, BigIntError> {
        self.0
            .root_inner::<RHS, OUT>(rhs)
            .map(|x| unsafe { x.unsafe_into() }.into())
    }

    fn is_even(&self) -> bool {
        self.0.is_even()
    }

    fn iter<'a>(&'a self) -> BigIntIter<'a, BASE, Self> {
        BigIntIter {
            index: 0,
            back_index: self.len(),
            int: self,
        }
    }

    fn display(&self, alphabet: &str) -> Result<String, BigIntError> {
        self.0.display(alphabet)
    }

    fn parse(value: &str, alphabet: &str) -> Result<Self::Denormal, ParseError> {
        B::parse(value, alphabet).map(|x| unsafe { x.unsafe_into() }.into())
    }

    fn convert_inner<const TO: usize, OUT: BigInt<{ TO }>>(self) -> OUT::Denormal {
        unsafe { self.0.convert_inner::<TO, OUT>().unsafe_into() }.into()
    }

    fn cmp_magnitude<RHS: BigInt<{ BASE }>>(&self, rhs: &RHS) -> Ordering {
        self.0.cmp_magnitude(rhs)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::big_int::get_back::GetBack for Denormal<BASE, B> {
    type Item = ::big_int::Digit;

    fn get_back(&self, index: usize) -> Option<::big_int::Digit> {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::get_back_inner(self, index)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::default::Default for Denormal<BASE, B> {
    fn default() -> Self {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::default_inner()
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::fmt::Display for Denormal<BASE, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::fmt_inner(self, f)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::cmp::PartialOrd for Denormal<BASE, B> {
    fn partial_cmp(&self, other: &Self) -> ::std::option::Option<::std::cmp::Ordering> {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::partial_cmp_inner(self, other)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::cmp::Ord for Denormal<BASE, B> {
    fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::cmp_inner(self, other)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::cmp::PartialEq for Denormal<BASE, B> {
    fn eq(&self, other: &Self) -> bool {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::eq_inner(self, other)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::cmp::Eq for Denormal<BASE, B> {}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::Neg for Denormal<BASE, B> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::neg_inner(self)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::Add for Denormal<BASE, B> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        unsafe {
            <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::add_inner::<_, B>(self, rhs)
                .unsafe_into()
        }
        .into()
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::AddAssign for Denormal<BASE, B> {
    fn add_assign(&mut self, rhs: Self) {
        unsafe {
            <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::add_assign_inner(self, rhs);
        }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::Sub for Denormal<BASE, B> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        unsafe {
            <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::sub_inner::<_, B>(self, rhs)
                .unsafe_into()
        }
        .into()
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::SubAssign for Denormal<BASE, B> {
    fn sub_assign(&mut self, rhs: Self) {
        unsafe { <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::sub_assign_inner(self, rhs) }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::Mul for Denormal<BASE, B> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        unsafe {
            <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::mul_inner::<_, B>(self, rhs)
                .unsafe_into()
        }
        .into()
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::MulAssign for Denormal<BASE, B> {
    fn mul_assign(&mut self, rhs: Self) {
        unsafe { <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::mul_assign_inner(self, rhs) }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::Div for Denormal<BASE, B> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        unsafe {
            <Denormal<BASE, B> as UnsafeInto<B>>::unsafe_into(
                <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::div_inner::<_, Self>(self, rhs),
            )
        }
        .into()
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::DivAssign for Denormal<BASE, B> {
    fn div_assign(&mut self, rhs: Self) {
        unsafe { <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::div_assign_inner(self, rhs) }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::Shl for Denormal<BASE, B> {
    type Output = Self;

    fn shl(self, rhs: Self) -> Self::Output {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::shl_inner(self, rhs.into())
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::ShlAssign for Denormal<BASE, B> {
    fn shl_assign(&mut self, rhs: Self) {
        unsafe {
            <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::shl_assign_inner(self, rhs.into())
        }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::Shr for Denormal<BASE, B> {
    type Output = Self;

    fn shr(self, rhs: Self) -> Self::Output {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::shr_inner(self, rhs.into())
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::ops::ShrAssign for Denormal<BASE, B> {
    fn shr_assign(&mut self, rhs: Self) {
        unsafe {
            <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::shr_assign_inner(self, rhs.into())
        }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::str::FromStr for Denormal<BASE, B> {
    type Err = ::big_int::error::BigIntError;

    fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err> {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::from_str_inner(s)
            .map(|i| unsafe { <Denormal<BASE, B> as UnsafeInto<B>>::unsafe_into(i) }.into())
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::iter::FromIterator<::big_int::Digit>
    for Denormal<BASE, B>
{
    fn from_iter<T: IntoIterator<Item = ::big_int::Digit>>(iter: T) -> Self {
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::from_iter_inner(iter)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::iter::Iterator for Denormal<BASE, B> {
    type Item = ::big_int::Digit;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe { <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::next_inner(self) }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::iter::DoubleEndedIterator
    for Denormal<BASE, B>
{
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe { <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::next_back_inner(self) }
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> ::std::convert::From<::std::vec::Vec<::big_int::Digit>>
    for Denormal<BASE, B>
{
    fn from(value: ::std::vec::Vec<::big_int::Digit>) -> Self {
        value.into_iter().collect()
    }
}

macro_rules! int_conversions {
    ($(($from:ident, $into:ident, $from_target_type:ident, [$($int:ident),*])),*) => {
        $(
            $(
                impl<const BASE: usize, B: BigInt<{BASE}>> ::std::convert::From<$int> for Denormal<BASE, B> {
                    fn from(value: $int) -> Self {
                        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::$from(value as $from_target_type)
                    }
                }

                impl<const BASE: usize, B: BigInt<{BASE}>> ::std::convert::From<Denormal<BASE, B>> for $int {
                    fn from(value: Denormal<BASE, B>) -> Self {
                        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::$into(value) as $int
                    }
                }
            )*
        )*
    };
}

int_conversions!(
    (
        from_i128_inner,
        into_i128_inner,
        i128,
        [i128, i64, i32, i16, i8, isize]
    ),
    (
        from_u128_inner,
        into_u128_inner,
        u128,
        [u128, u64, u32, u16, u8, usize]
    )
);

/// A builder for a denormal int.
///
/// Exists purely clerically as a consequence of the abstractions present. Unlikely
/// to be used directly.
#[derive(Debug, Clone)]
pub struct DenormalBuilder<const BASE: usize, B: BigIntBuilder<{ BASE }>>(B);

impl<const BASE: usize, B: BigIntBuilder<{ BASE }>> BigIntBuilder<BASE>
    for DenormalBuilder<BASE, B>
{
    fn new() -> Self {
        Self(B::new())
    }

    fn push_front(&mut self, digit: Digit) {
        self.0.push_front(digit);
    }

    fn push_back(&mut self, digit: Digit) {
        self.0.push_back(digit);
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn with_sign(self, sign: Sign) -> Self {
        Self(self.0.with_sign(sign))
    }
}

impl<const BASE: usize, B: BigIntBuilder<{ BASE }> + Into<BB::Denormal>, BB: BigInt<{ BASE }>>
    From<DenormalBuilder<BASE, B>> for Denormal<BASE, BB>
{
    fn from(value: DenormalBuilder<BASE, B>) -> Self {
        unsafe { value.unsafe_into() }.into()
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> From<B> for Denormal<BASE, B> {
    fn from(value: B) -> Self {
        Denormal(value)
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> UnsafeInto<B> for Denormal<BASE, B> {
    unsafe fn unsafe_into(self) -> B {
        self.0
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> Unwrap<B> for Denormal<BASE, B> {
    fn unwrap(self) -> B {
        self.0.normalized()
    }
}

impl<const BASE: usize, B: BigInt<{ BASE }>> Unwrap<Self> for Denormal<BASE, B> {
    fn unwrap(self) -> Self {
        self
    }
}
