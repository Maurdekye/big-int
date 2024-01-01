use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::*;

#[proc_macro_derive(BigIntTraits)]
pub fn auto_big_int_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let name = &ast.ident;

    let int_conversions = [
        (
            "from_i128_inner",
            "into_i128_inner",
            "i128",
            ["i128", "i64", "i32", "i16", "i8", "isize"],
        ),
        (
            "from_u128_inner",
            "into_u128_inner",
            "u128",
            ["u128", "u64", "u32", "u16", "u8", "usize"],
        ),
    ]
    .into_iter()
    .map(|(from, into, from_target_type, int_types)| {
        int_types.map(|int| {
            let from = format_ident!("{from}");
            let into = format_ident!("{into}");
            let from_target_type = format_ident!("{from_target_type}");
            let int = format_ident!("{int}");
            quote! {
                impl<const BASE: usize> ::std::convert::From<#int> for #name<BASE> {
                    fn from(value: #int) -> Self {
                        <#name<BASE> as ::big_int::BigInt<BASE>>::#from(value as #from_target_type)
                    }
                }

                impl<const BASE: usize> ::std::convert::From<#name<BASE>> for #int {
                    fn from(value: #name<BASE>) -> Self {
                        <#name<BASE> as ::big_int::BigInt<BASE>>::#into(value) as #int
                    }
                }
            }
        })
    })
    .flatten();

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
            fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
                <#name<BASE> as ::big_int::BigInt<BASE>>::cmp_inner(self, other)
            }
        }

        impl<const BASE: usize> ::std::cmp::PartialEq for #name<BASE> {
            fn eq(&self, other: &Self) -> bool {
                <#name<BASE> as ::big_int::BigInt<BASE>>::eq_inner(self, other)
            }
        }

        impl<const BASE: usize> ::std::cmp::Eq for #name<BASE> {}

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

        impl<const BASE: usize> ::std::iter::Iterator for #name<BASE> {
            type Item = ::big_int::Digit;

            fn next(&mut self) -> Option<Self::Item> {
                <#name<BASE> as ::big_int::BigInt<BASE>>::next_inner(self)
            }
        }

        impl<const BASE: usize> ::std::iter::DoubleEndedIterator for #name<BASE> {
            fn next_back(&mut self) -> Option<Self::Item> {
                <#name<BASE> as ::big_int::BigInt<BASE>>::next_back_inner(self)
            }
        }

        impl<const BASE: usize> ::std::convert::From<::std::vec::Vec<::big_int::Digit>> for #name<BASE> {
            fn from(value: ::std::vec::Vec<::big_int::Digit>) -> Self {
                value.into_iter().collect()
            }
        }

        #(#int_conversions)*
    };
    gen.into()
}
