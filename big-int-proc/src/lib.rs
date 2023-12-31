use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::*;

#[proc_macro_derive(BigInt)]
pub fn auto_big_int_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let name = &ast.ident;

    let signed_int_conversions = [
        "i128", "i64", "i32", "i16", "i8", "isize"
    ].into_iter().map(|signed| {
            let signed = format_ident!("{signed}");
            quote! {
                impl<const BASE: usize> ::std::convert::From<#signed> for #name<BASE> {
                    fn from(value: #signed) -> Self {
                        <#name<BASE> as ::big_int::BigInt<BASE>>::from_i128_inner(value as i128)
                    }
                }

                impl<const BASE: usize> ::std::convert::From<#name<BASE>> for #signed {
                    fn from(value: #name<BASE>) -> Self {
                        <#name<BASE> as ::big_int::BigInt<BASE>>::into_i128_inner(value) as #signed
                    }
                }
            }
        });

    let unsigned_int_conversions = [
        "u128", "u64", "u32", "u16", "u8", "usize",
    ].into_iter().map(|unsigned| {
        let unsigned = format_ident!("{unsigned}");
        quote! {
            impl<const BASE: usize> ::std::convert::From<#unsigned> for #name<BASE> {
                fn from(value: #unsigned) -> Self {
                    <#name<BASE> as ::big_int::BigInt<BASE>>::from_u128_inner(value as u128)
                }
            }

            impl<const BASE: usize> ::std::convert::From<#name<BASE>> for #unsigned {
                fn from(value: #name<BASE>) -> Self {
                    <#name<BASE> as ::big_int::BigInt<BASE>>::into_u128_inner(value) as #unsigned
                }
            }
        }
    });

    let gen = quote! {
        impl<const BASE: usize> ::big_int::get_back::GetBack for #name<BASE> {
            type Item = ::big_int::Digit;

            fn get_back(&self, index: usize) -> Option<::big_int::Digit> {
                <#name<BASE> as ::big_int::BigInt<BASE>>::get_back_inner(self, index)
            }
        }

        impl<const BASE: usize> ::std::default::Default for #name<BASE> {
            fn default() -> Self {
                <#name<BASE> as ::big_int::BigInt<BASE>>::default_inner()
            }
        }

        impl<const BASE: usize> ::std::fmt::Display for #name<BASE> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                <#name<BASE> as ::big_int::BigInt<BASE>>::fmt_inner(self, f)
            }
        }

        impl<const BASE: usize> ::std::cmp::PartialOrd for #name<BASE> {
            fn partial_cmp(&self, other: &Self) -> ::std::option::Option<::std::cmp::Ordering> {
                <#name<BASE> as ::big_int::BigInt<BASE>>::partial_cmp_inner(self, other)
            }
        }

        impl<const BASE: usize> ::std::cmp::Ord for #name<BASE> {
            fn cmp(&self, other: &Self) ->::std::cmp::Ordering {
                <#name<BASE> as ::big_int::BigInt<BASE>>::cmp_inner(self, other)
            }
        }

        impl<const BASE: usize> ::std::ops::Neg for #name<BASE> {
            type Output = Self;

            fn neg(self) -> Self::Output {
                <#name<BASE> as ::big_int::BigInt<BASE>>::neg_inner(self)
            }
        }

        impl<const BASE: usize> ::std::ops::Add for #name<BASE> {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                <#name<BASE> as ::big_int::BigInt<BASE>>::add_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::AddAssign for #name<BASE> {
            fn add_assign(&mut self, rhs: Self) {
                <#name<BASE> as ::big_int::BigInt<BASE>>::add_assign_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::Sub for #name<BASE> {
            type Output = Self;

            fn sub(mut self, rhs: Self) -> Self::Output {
                <#name<BASE> as ::big_int::BigInt<BASE>>::sub_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::SubAssign for #name<BASE> {
            fn sub_assign(&mut self, rhs: Self) {
                <#name<BASE> as ::big_int::BigInt<BASE>>::sub_assign_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::Mul for #name<BASE> {
            type Output = Self;

            fn mul(mut self, rhs: Self) -> Self::Output {
                <#name<BASE> as ::big_int::BigInt<BASE>>::mul_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::MulAssign for #name<BASE> {
            fn mul_assign(&mut self, rhs: Self) {
                <#name<BASE> as ::big_int::BigInt<BASE>>::mul_assign_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::Div for #name<BASE> {
            type Output = Self;

            fn div(self, rhs: Self) -> Self::Output {
                <#name<BASE> as ::big_int::BigInt<BASE>>::div_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::DivAssign for #name<BASE> {
            fn div_assign(&mut self, rhs: Self) {
                <#name<BASE> as ::big_int::BigInt<BASE>>::div_assign_inner(self, rhs)
            }
        }

        impl<const BASE: usize> ::std::ops::Shl for #name<BASE> {
            type Output = Self;

            fn shl(self, rhs: Self) -> Self::Output {
                <#name<BASE> as ::big_int::BigInt<BASE>>::shl_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> ::std::ops::ShlAssign for #name<BASE> {
            fn shl_assign(&mut self, rhs: Self) {
                <#name<BASE> as ::big_int::BigInt<BASE>>::shl_assign_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> ::std::ops::Shr for #name<BASE> {
            type Output = Self;

            fn shr(self, rhs: Self) -> Self::Output {
                <#name<BASE> as ::big_int::BigInt<BASE>>::shr_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> ::std::ops::ShrAssign for #name<BASE> {
            fn shr_assign(&mut self, rhs: Self) {
                <#name<BASE> as ::big_int::BigInt<BASE>>::shr_assign_inner(self, rhs.into())
            }
        }

        impl<const BASE: usize> ::std::str::FromStr for #name<BASE> {
            type Err = ::big_int::error::BigIntError;

            fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err> {
                <#name<BASE> as ::big_int::BigInt<BASE>>::from_str_inner(s)
            }
        }

        impl<const BASE: usize> ::std::iter::FromIterator<::big_int::Digit> for #name<BASE> {
            fn from_iter<T: IntoIterator<Item = ::big_int::Digit>>(iter: T) -> Self {
                <#name<BASE> as ::big_int::BigInt<BASE>>::from_iter_inner(iter)
            }
        }

        impl<const BASE: usize> ::std::convert::From<::std::vec::Vec<::big_int::Digit>> for #name<BASE> {
            fn from(value: ::std::vec::Vec<::big_int::Digit>) -> Self {
                value.into_iter().collect()
            }
        }

        #(#signed_int_conversions)*
        #(#unsigned_int_conversions)*
    };
    gen.into()
}
