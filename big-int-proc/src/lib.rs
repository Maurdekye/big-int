use proc_macro::TokenStream;
use quote::{format_ident, quote};
use syn::*;

#[proc_macro_derive(BigIntTraits)]
pub fn auto_big_int_derive(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let name = &ast.ident;
    let (impl_generics, ty_generics, where_clause) = &ast.generics.split_for_impl();

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
        let from = format_ident!("{from}");
        let into = format_ident!("{into}");
        let from_target_type = format_ident!("{from_target_type}");
        int_types.map(|int| {
            let int = format_ident!("{int}");
            quote! {
                impl #impl_generics ::std::convert::From<#int> for #name #ty_generics #where_clause {
                    fn from(value: #int) -> Self {
                        <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                            <#name #ty_generics as ::big_int::BigInt<BASE>>::#from(value as #from_target_type)
                        )
                    }
                }

                impl #impl_generics ::std::convert::From<#name #ty_generics> for #int {
                    fn from(value: #name #ty_generics) -> Self {
                        <#name #ty_generics as ::big_int::BigInt<BASE>>::#into(value) as #int
                    }
                }
            }
        })
    })
    .flatten();

    let gen = quote! {
        impl #impl_generics ::big_int::get_back::GetBack for #name #ty_generics #where_clause {
            type Item = ::big_int::Digit;

            fn get_back(&self, index: usize) -> Option<::big_int::Digit> {
                <#name #ty_generics as ::big_int::BigInt<BASE>>::get_back_inner(self, index)
            }
        }

        impl #impl_generics ::std::default::Default for #name #ty_generics #where_clause {
            fn default() -> Self {
                <#name #ty_generics as ::big_int::BigInt<BASE>>::default_inner()
            }
        }

        impl #impl_generics ::std::fmt::Display for #name #ty_generics #where_clause {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                <#name #ty_generics as ::big_int::BigInt<BASE>>::fmt_inner(self, f)
            }
        }

        impl #impl_generics ::std::cmp::PartialOrd for #name #ty_generics #where_clause {
            fn partial_cmp(&self, other: &Self) -> ::std::option::Option<::std::cmp::Ordering> {
                <#name #ty_generics as ::big_int::BigInt<BASE>>::partial_cmp_inner(self, other)
            }
        }

        impl #impl_generics ::std::cmp::Ord for #name #ty_generics #where_clause {
            fn cmp(&self, other: &Self) -> ::std::cmp::Ordering {
                <#name #ty_generics as ::big_int::BigInt<BASE>>::cmp_inner(self, other)
            }
        }

        impl #impl_generics ::std::cmp::PartialEq for #name #ty_generics #where_clause {
            fn eq(&self, other: &Self) -> bool {
                <#name #ty_generics as ::big_int::BigInt<BASE>>::eq_inner(self, other)
            }
        }

        impl #impl_generics ::std::cmp::Eq for #name #ty_generics #where_clause {}

        impl #impl_generics ::std::ops::Neg for #name #ty_generics #where_clause {
            type Output = Self;

            fn neg(self) -> Self::Output {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::neg_inner(self)
                )
            }
        }

        impl #impl_generics ::std::ops::Add for #name #ty_generics #where_clause {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::add_inner::<Self, Self>(self, rhs)
                )
            }
        }

        impl #impl_generics ::std::ops::AddAssign for #name #ty_generics #where_clause {
            fn add_assign(&mut self, rhs: Self) {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::add_assign_inner(self, rhs);
                }
                <#name #ty_generics as ::big_int::BigInt<BASE>>::normalize(self);
            }
        }

        impl #impl_generics ::std::ops::Sub for #name #ty_generics #where_clause {
            type Output = Self;

            fn sub(mut self, rhs: Self) -> Self::Output {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::sub_inner::<Self, Self>(self, rhs)
                )
            }
        }

        impl #impl_generics ::std::ops::SubAssign for #name #ty_generics #where_clause {
            fn sub_assign(&mut self, rhs: Self) {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::sub_assign_inner(self, rhs)
                }
                <#name #ty_generics as ::big_int::BigInt<BASE>>::normalize(self);
            }
        }

        impl #impl_generics ::std::ops::Mul for #name #ty_generics #where_clause {
            type Output = Self;

            fn mul(mut self, rhs: Self) -> Self::Output {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::mul_inner::<Self, Self>(self, rhs)
                )
            }
        }

        impl #impl_generics ::std::ops::MulAssign for #name #ty_generics #where_clause {
            fn mul_assign(&mut self, rhs: Self) {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::mul_assign_inner(self, rhs)
                }
                <#name #ty_generics as ::big_int::BigInt<BASE>>::normalize(self);
            }
        }

        impl #impl_generics ::std::ops::Div for #name #ty_generics #where_clause {
            type Output = Self;

            fn div(self, rhs: Self) -> Self::Output {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::div_inner::<Self, Self>(self, rhs)
                )
            }
        }

        impl #impl_generics ::std::ops::DivAssign for #name #ty_generics #where_clause {
            fn div_assign(&mut self, rhs: Self) {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::div_assign_inner(self, rhs)
                }
                <#name #ty_generics as ::big_int::BigInt<BASE>>::normalize(self);
            }
        }

        impl #impl_generics ::std::ops::Shl for #name #ty_generics #where_clause {
            type Output = Self;

            fn shl(self, rhs: Self) -> Self::Output {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::shl_inner(self, rhs.into())
                )
            }
        }

        impl #impl_generics ::std::ops::ShlAssign for #name #ty_generics #where_clause {
            fn shl_assign(&mut self, rhs: Self) {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::shl_assign_inner(self, rhs.into())
                }
                <#name #ty_generics as ::big_int::BigInt<BASE>>::normalize(self);
            }
        }

        impl #impl_generics ::std::ops::Shr for #name #ty_generics #where_clause {
            type Output = Self;

            fn shr(self, rhs: Self) -> Self::Output {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::shr_inner(self, rhs.into())
                )
            }
        }

        impl #impl_generics ::std::ops::ShrAssign for #name #ty_generics #where_clause {
            fn shr_assign(&mut self, rhs: Self) {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::shr_assign_inner(self, rhs.into())
                }
                <#name #ty_generics as ::big_int::BigInt<BASE>>::normalize(self);
            }
        }

        impl #impl_generics ::std::str::FromStr for #name #ty_generics #where_clause {
            type Err = ::big_int::error::BigIntError;

            fn from_str(s: &str) -> ::std::result::Result<Self, Self::Err> {
                <#name #ty_generics as ::big_int::BigInt<BASE>>::from_str_inner(s).map(|i|
                    <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(i)
                )
            }
        }

        impl #impl_generics ::std::iter::FromIterator<::big_int::Digit> for #name #ty_generics #where_clause {
            fn from_iter<T: IntoIterator<Item = ::big_int::Digit>>(iter: T) -> Self {
                <<#name #ty_generics as ::big_int::BigInt<BASE>>::Denormal as ::big_int::Unwrap<#name #ty_generics>>::unwrap(
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::from_iter_inner(iter)
                )
            }
        }

        impl #impl_generics ::std::iter::Iterator for #name #ty_generics #where_clause {
            type Item = ::big_int::Digit;

            fn next(&mut self) -> Option<Self::Item> {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::next_inner(self)
                }
            }
        }

        impl #impl_generics ::std::iter::DoubleEndedIterator for #name #ty_generics #where_clause {
            fn next_back(&mut self) -> Option<Self::Item> {
                unsafe {
                    <#name #ty_generics as ::big_int::BigInt<BASE>>::next_back_inner(self)
                }
            }
        }

        impl #impl_generics ::std::convert::From<::std::vec::Vec<::big_int::Digit>> for #name #ty_generics #where_clause {
            fn from(value: ::std::vec::Vec<::big_int::Digit>) -> Self {
                value.into_iter().collect()
            }
        }

        #(#int_conversions)*
    };
    gen.into()
}
