use crate::*;

#[derive(Debug, Clone)]
pub struct Denormal<const BASE: usize, B: BigInt<{ BASE }>>(pub(crate) B);

impl<const BASE: usize, B: BigInt<{ BASE }>> BigInt<BASE> for Denormal<BASE, B> {
    type Builder = DenormalBuilder<BASE, B::Builder>;
    type Denormal = Self;

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

    fn neg_inner(self) -> Self::Denormal {
        unsafe { self.0.neg_inner().unsafe_into() }.into()
    }

    fn add_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(self, rhs: RHS) -> OUT::Denormal {
        unsafe { self.0.add_inner::<_, OUT>(rhs).unsafe_into() }.into()
    }

    unsafe fn add_assign_inner<RHS: BigInt<{ BASE }>>(&mut self, rhs: RHS) {
        self.0.add_assign_inner(rhs)
    }

    fn sub_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> OUT::Denormal {
        unsafe { self.0.sub_inner::<_, OUT>(rhs).unsafe_into() }.into()
    }

    unsafe fn sub_assign_inner<RHS: BigInt<{ BASE }>>(&mut self, rhs: RHS) {
        self.0.sub_assign_inner(rhs)
    }

    fn mul_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> OUT::Denormal {
        unsafe { self.0.mul_inner::<_, OUT>(rhs).unsafe_into() }.into()
    }

    unsafe fn mul_assign_inner<RHS: BigInt<{ BASE }>>(&mut self, rhs: RHS) {
        self.0.mul_assign_inner(rhs)
    }

    fn div_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(self, rhs: RHS) -> OUT::Denormal {
        unsafe { self.0.div_inner::<_, OUT>(rhs).unsafe_into() }.into()
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
        self.0.pop_back()
    }

    fn from_u128_inner(value: u128) -> Self {
        unsafe { B::from_u128_inner(value).unsafe_into() }.into()
    }

    fn from_i128_inner(value: i128) -> Self {
        unsafe { B::from_i128_inner(value).unsafe_into() }.into()
    }

    fn into_u128_inner(self) -> u128 {
        self.0.into_u128_inner()
    }

    fn into_i128_inner(self) -> i128 {
        self.0.into_i128_inner()
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }

    fn shr_inner(self, amount: usize) -> Self::Denormal {
        unsafe { self.0.shr_inner(amount).unsafe_into() }.into()
    }

    unsafe fn shr_assign_inner(&mut self, amount: usize) {
        self.0.shr_assign_inner(amount);
    }

    fn shl_inner(self, amount: usize) -> Self {
        self.0.shl_inner(amount).into()
    }

    fn shl_assign_inner(&mut self, amount: usize) {
        self.0.shl_assign_inner(amount);
    }

    fn normalized(self) -> Self {
        self.0.normalized().into()
    }

    fn normalize(&mut self) {
        self.0.normalize();
    }

    fn display(&self, alphabet: &str) -> Result<String, BigIntError> {
        self.0.display(alphabet)
    }

    fn parse(value: &str, alphabet: &str) -> Result<Self::Denormal, ParseError> {
        B::parse(value, alphabet).map(|x| unsafe { x.unsafe_into() }.into())
    }

    fn div_rem_inner<RHS: BigInt<{ BASE }>, OUT: BigInt<{ BASE }>>(
        self,
        rhs: RHS,
    ) -> Result<(OUT::Denormal, OUT::Denormal), BigIntError> {
        self.0
            .div_rem_inner::<_, OUT>(rhs)
            .map(|(q, r): (OUT::Denormal, OUT::Denormal)| unsafe {
                (q.unsafe_into().into(), r.unsafe_into().into())
            })
    }

    fn convert_inner<const TO: usize, OUT: BigInt<{ TO }>>(self) -> OUT::Denormal {
        unsafe { self.0.convert::<TO, OUT>().unsafe_into() }.into()
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
        <Denormal<BASE, B> as ::big_int::BigInt<BASE>>::shl_assign_inner(self, rhs.into())
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