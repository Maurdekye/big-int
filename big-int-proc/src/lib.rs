use proc_macro::TokenStream;
use quote::quote;
use syn::*;

#[proc_macro_derive(BigInt)]
pub fn auto_big_int_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let name = &ast.ident;
    let gen = quote! {
        impl<const BASE: usize> crate::get_back::GetBack for #name<BASE> {
            type Item = crate::Digit;

            fn get_back(&self, index: usize) -> Option<crate::Digit> {
                <#name<BASE> as BigInt<BASE>>::get_back_inner(self, index)
            }
        }

        impl<const BASE: usize> Default for #name<BASE> {
            fn default() -> Self {
                <#name<BASE> as BigInt<BASE>>::default_inner()
            }
        }

        impl<const BASE: usize> std::fmt::Display for #name<BASE> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                <#name<BASE> as BigInt<BASE>>::fmt_inner(self, f)
            }
        }

        impl<const BASE: usize> PartialOrd for #name<BASE> {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                <#name<BASE> as BigInt<BASE>>::partial_cmp_inner(self, other)
            }
        }

        impl<const BASE: usize> Ord for #name<BASE> {
            fn cmp(&self, other: &Self) -> Ordering {
                <#name<BASE> as BigInt<BASE>>::cmp_inner(self, other)
            }
        }

        impl<const BASE: usize> Neg for #name<BASE> {
            type Output = Self;

            fn neg(self) -> Self::Output {
                <#name<BASE> as BigInt<BASE>>::neg_inner(self)
            }
        }

        impl<const BASE: usize> Add for #name<BASE> {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                <#name<BASE> as BigInt<BASE>>::add_inner(self, rhs)
            }
        }

        impl<const BASE: usize> AddAssign for #name<BASE> {
            fn add_assign(&mut self, rhs: Self) {
                <#name<BASE> as BigInt<BASE>>::add_assign_inner(self, rhs)
            }
        }
        
        impl<const BASE: usize> Sub for #name<BASE> {
            type Output = Self;

            fn sub(mut self, rhs: Self) -> Self::Output {
                <#name<BASE> as BigInt<BASE>>::sub_inner(self, rhs)
            }
        }

        impl<const BASE: usize> SubAssign for #name<BASE> {
            fn sub_assign(&mut self, rhs: Self) {
                <#name<BASE> as BigInt<BASE>>::sub_assign_inner(self, rhs)
            }
        }

        impl<const BASE: usize> Mul for #name<BASE> {
            type Output = Self;
        
            fn mul(mut self, rhs: Self) -> Self::Output {
                <#name<BASE> as BigInt<BASE>>::mul_inner(self, rhs)
            }
        }

        impl<const BASE: usize> MulAssign for #name<BASE> {
            fn mul_assign(&mut self, rhs: Self) {
                <#name<BASE> as BigInt<BASE>>::mul_assign_inner(self, rhs)
            }
        }

        impl<const BASE: usize> Div for #name<BASE> {
            type Output = Self;
        
            fn div(self, rhs: Self) -> Self::Output {
                <#name<BASE> as BigInt<BASE>>::div_inner(self, rhs)
            }
        }

        impl<const BASE: usize> DivAssign for #name<BASE> {
            fn div_assign(&mut self, rhs: Self) {
                <#name<BASE> as BigInt<BASE>>::div_assign_inner(self, rhs)
            }
        }

        impl<const BASE: usize> Shl for #name<BASE> {
            type Output = Self;

            fn shl(self, rhs: Self) -> Self::Output {
                <#name<BASE> as BigInt<BASE>>::shl_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> ShlAssign for #name<BASE> {
            fn shl_assign(&mut self, rhs: Self) {
                <#name<BASE> as BigInt<BASE>>::shl_assign_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> Shr for #name<BASE> {
            type Output = Self;
            
            fn shr(self, rhs: Self) -> Self::Output {
                <#name<BASE> as BigInt<BASE>>::shr_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> ShrAssign for #name<BASE> {
            fn shr_assign(&mut self, rhs: Self) {
                <#name<BASE> as BigInt<BASE>>::shr_assign_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> FromStr for #name<BASE> {
            type Err = crate::error::BigIntError;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                <#name<BASE> as BigInt<BASE>>::from_str_inner(s)
            }
        }

        impl<const BASE: usize> FromIterator<crate::Digit> for #name<BASE> {
            fn from_iter<T: IntoIterator<Item = crate::Digit>>(iter: T) -> Self {
                <#name<BASE> as BigInt<BASE>>::from_iter_inner(iter)
            }
        }

        impl<const BASE: usize> From<Vec<crate::Digit>> for #name<BASE> {
            fn from(value: Vec<crate::Digit>) -> Self {
                value.into_iter().collect()
            }
        }

        impl<const BASE: usize> From<u128> for #name<BASE> {
            fn from(value: u128) -> Self {
                <#name<BASE> as BigInt<BASE>>::from_u128_inner(value)
            }
        }

        impl<const BASE: usize> From<i128> for #name<BASE> {
            fn from(value: i128) -> Self {
                <#name<BASE> as BigInt<BASE>>::from_i128_inner(value)
            }
        }

        macro_rules! bigint_from_int {
            ($b:ident; $($i:ident),*) => {
                $(
                    impl<const BASE: usize> From<$i> for #name<BASE> {
                        fn from(value: $i) -> Self {
                            #name::<BASE>::from(value as $b)
                        }
                    }
                )*
            };
        }

        bigint_from_int!(i128; i8, i16, i32, i64, isize);
        bigint_from_int!(u128; u8, u16, u32, u64, usize);

        macro_rules! int_from_bigint {
            ($(($i:ident, $u:ident)),*) => {
                $(
                    impl<const BASE: usize> From<#name<BASE>> for $i {
                        fn from(value: #name<BASE>) -> Self {
                            let mut total: $i = 0;
                            let mut place: $i = 0;
                            for digit in value.iter().rev() {
                                place = if place == 0 { 1 } else { place * BASE as $i };
                                total += (digit as $i) * place;
                            }
                            if value.sign() == Negative {
                                total = -total;
                            }
                            total
                        }
                    }
        
                    impl<const BASE: usize> From<#name<BASE>> for $u {
                        fn from(value: #name<BASE>) -> Self {
                            Into::<$i>::into(value) as $u
                        }
                    }
                )*
            };
        }
        
        int_from_bigint!(
            (i128, u128),
            (i64, u64),
            (i32, u32),
            (i16, u16),
            (i8, u8),
            (isize, usize)
        );
    };
    gen.into()
}

