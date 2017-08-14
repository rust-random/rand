//! Support for `#[derive(Rand)]`
//!
//! # Examples
//!
//! ```
//! extern crate rand;
//! #[macro_use]
//! extern crate rand_derive;
//!
//! #[derive(Rand, Debug)]
//! struct MyStruct {
//!     a: i32,
//!     b: u32,
//! }
//!
//! fn main() {
//!     println!("{:?}", rand::random::<MyStruct>());
//! }
//! ```

extern crate proc_macro;
#[macro_use]
extern crate quote;
extern crate syn;

use proc_macro::TokenStream;

#[proc_macro_derive(Rand)]
pub fn rand_derive(input: TokenStream) -> TokenStream {
    let s = input.to_string();
    let ast = syn::parse_derive_input(&s).unwrap();
    let gen = impl_rand_derive(&ast);
    gen.parse().unwrap()
}

fn impl_rand_derive(ast: &syn::MacroInput) -> quote::Tokens {
    let name = &ast.ident;
    let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();

    let rand = match ast.body {
        syn::Body::Struct(syn::VariantData::Struct(ref body)) => {
            let fields = body
                .iter()
                .filter_map(|field| field.ident.as_ref())
                .map(|ident| quote! { #ident: __rng.gen() })
                .collect::<Vec<_>>();

            quote! { #name { #(#fields,)* } }
        },
        syn::Body::Struct(syn::VariantData::Tuple(ref body)) => {
            let fields = (0..body.len())
                .map(|_| quote! { __rng.gen() })
                .collect::<Vec<_>>();

            quote! { #name (#(#fields),*) }
        },
        syn::Body::Struct(syn::VariantData::Unit) => {
            quote! { #name }
        },
        syn::Body::Enum(ref body) => {
            if body.is_empty() {
                panic!("`Rand` cannot be derived for enums with no variants");
            }

            let len = body.len();
            let mut arms = body
                .iter()
                .map(|variant| {
                    let ident = &variant.ident;
                    match variant.data {
                        syn::VariantData::Struct(ref body) => {
                            let fields = body
                                .iter()
                                .filter_map(|field| field.ident.as_ref())
                                .map(|ident| quote! { #ident: __rng.gen() })
                                .collect::<Vec<_>>();
                            quote! { #name::#ident { #(#fields,)* } }
                        },
                        syn::VariantData::Tuple(ref body) => {
                            let fields = (0..body.len())
                                .map(|_| quote! { __rng.gen() })
                                .collect::<Vec<_>>();

                            quote! { #name::#ident (#(#fields),*) }
                        },
                        syn::VariantData::Unit => quote! { #name::#ident }
                    }
                });

            match len {
                1 => quote! { #(#arms)* },
                2 => {
                    let (a, b) = (arms.next(), arms.next());
                    quote! { if __rng.gen() { #a } else { #b } }
                },
                _ => {
                    let mut variants = arms
                        .enumerate()
                        .map(|(index, arm)| quote! { #index => #arm })
                        .collect::<Vec<_>>();
                    variants.push(quote! { _ => unreachable!() });
                    quote! { match __rng.gen_range(0, #len) { #(#variants,)* } }
                },
            }
        }
    };

    quote! {
        impl #impl_generics ::rand::Rand for #name #ty_generics #where_clause {
            #[inline]
            fn rand<__R: ::rand::Rng>(__rng: &mut __R) -> Self {
                #rand
            }
        }
    }
}
