//! Support for `#[derive(RngCore, SeedableRng)]` on wrapper types.
//! 
//! Supports named- and tuple-structs where the first field implements the
//! deriving type.
//!
//! # Examples
//!
//! ```norun
//! extern crate rand;
//! #[macro_use]
//! extern crate rand_derive;
//! 
//! use rand::{Rng, RngCore, NewRng, IsaacRng};
//!
//! #[derive(Clone, Debug, RngCore, SeedableRng)]
//! struct MyRng(IsaacRng);
//!
//! fn main() {
//!     let mut rng = MyRng::new();
//!     println!("Random output: {:?}", rng.gen::<[u32; 4]>());
//! }
//! ```

#![recursion_limit="128"]

// Based on heapsize example:
// https://github.com/dtolnay/syn/blob/master/examples/heapsize/heapsize_derive/src/lib.rs

extern crate proc_macro;
#[macro_use]
extern crate quote;
extern crate syn;

use proc_macro::TokenStream;
use syn::{DeriveInput, Data, Fields};
use quote::Tokens;

#[proc_macro_derive(RngCore)]
pub fn derive_rng_core(input: TokenStream) -> TokenStream {
    let input: DeriveInput = syn::parse(input).unwrap();
    let name = input.ident;
    
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    
    let (inner, _) = get_inner(&input.data);
    
    let expanded = quote! {
        impl #impl_generics ::rand::RngCore for #name #ty_generics #where_clause {
            fn next_u32(&mut self) -> u32 {
                #inner.next_u32()
            }

            fn next_u64(&mut self) -> u64 {
                #inner.next_u64()
            }

            fn fill_bytes(&mut self, dest: &mut [u8]) {
                #inner.fill_bytes(dest);
            }

            fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), ::rand::Error> {
                #inner.try_fill_bytes(dest)
            }
        }
    };
    
    expanded.into()
}

#[proc_macro_derive(SeedableRng)]
pub fn derive_seedable_rng(input: TokenStream) -> TokenStream {
    let input: DeriveInput = syn::parse(input).unwrap();
    let name = input.ident;
    
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
    
    let r = quote!{ r };
    let (ty_inner, construction) = get_construction(&input.data, r.clone());
    
    let expanded = quote! {
        impl #impl_generics ::rand::SeedableRng for #name #ty_generics #where_clause {
            type Seed = <#ty_inner as ::rand::SeedableRng>::Seed;

            fn from_seed(seed: Self::Seed) -> Self {
                let #r = #ty_inner::from_seed(seed);
                #name #construction
            }

            fn from_rng<R: ::rand::RngCore>(rng: &mut R) -> Result<Self, ::rand::Error> {
                #ty_inner::from_rng(rng).map(|#r| #name #construction)
            }
        }
    };
    
    expanded.into()
}

fn get_inner(data: &Data) -> (Tokens, Tokens) {
    match *data {
        Data::Struct(ref data) => {
            match data.fields {
                Fields::Named(ref fields) => {
                    // type presumably implies there is at least one field
                    let first = fields.named.first().unwrap();
                    let name = first.value().ident.unwrap();    // named, thus should have ident
                    let ty = &first.value().ty;
                    // TODO: type constraint ty
                    (quote!{ self.#name }, quote!{ #ty })
                },
                Fields::Unnamed(ref fields) => {
                    // again, presumably we must have at least one field
                    let first = fields.unnamed.first().unwrap();
                    let ty = &first.value().ty;
                    // TODO: type constraint ty
                    (quote!{ self.0 }, quote!{ #ty })
                },
                Fields::Unit => {
                    panic!("rand-dervie cannot derive unit structs")
                },
            }
        },
        _ => {
            panic!("rand-derive only supports struct types")
        }
    }
}

fn get_construction(data: &Data, r: Tokens) -> (Tokens, Tokens) {
    match *data {
        Data::Struct(ref data) => {
            match data.fields {
                Fields::Named(ref fields) => {
                    if fields.named.len() != 1 {
                        panic!("SeedableRng only derivable for structs with a single field");
                    }
                    let first = fields.named.first().unwrap();
                    let name = first.value().ident.unwrap();    // named, thus should have ident
                    let ty = &first.value().ty;
                    // TODO: type constraint ty
                    (quote!{ #ty }, quote!{ { #name: #r } })
                },
                Fields::Unnamed(ref fields) => {
                    if fields.unnamed.len() != 1 {
                        panic!("SeedableRng only derivable for structs with a single field");
                    }
                    let first = fields.unnamed.first().unwrap();
                    let ty = &first.value().ty;
                    // TODO: type constraint ty
                    (quote!{ #ty }, quote!{ ( #r ) })
                },
                Fields::Unit => {
                    panic!("rand-dervie cannot derive unit structs")
                },
            }
        },
        _ => {
            panic!("rand-derive only supports struct types")
        }
    }
}
