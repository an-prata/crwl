// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

// NOTE: If ever the proc-macro stuff can be put in the same crate as other code
// that should be public this stuff should get moved to aprox_eq.

use proc_macro::TokenStream;
use quote::quote;
use syn::{self, punctuated::Punctuated, token::Comma, DeriveInput, Field};

#[proc_macro_derive(AproxEq)]
pub fn aprox_eq_derive(input: TokenStream) -> TokenStream {
    let ast: DeriveInput = syn::parse(input).unwrap();
    impl_aprox_eq(&ast)
}

fn impl_aprox_eq(input: &DeriveInput) -> TokenStream {
    let name = &input.ident;

    // Get the named struct fields, if what we got was not a struct panic.
    let fields: &Punctuated<Field, Comma> = match &input.data {
        syn::Data::Struct(syn::DataStruct {
            fields: syn::Fields::Named(fields),
            ..
        }) => &fields.named,

        _ => panic!("Cannot derive `AproxEq` on non-struct."),
    };

    // Get the names of all those fields.
    let field_name = fields.iter().map(|field| &field.ident);

    let gen = quote! {
        impl AproxEq for #name {
            fn aprox_eq(&self, other: &Self) -> bool {
                // Rust voodoo magic. Check the aproximate equality of all
                // fields, if one is not aproximately equal the struct isn't
                // either.
                true #(&& self.#field_name.aprox_eq(&other.#field_name))*
            }
        }
    };

    gen.into()
}
