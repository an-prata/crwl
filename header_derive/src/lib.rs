// cwrl Copyright (c) 2023 Evan Overman (https://an-prata.it).
// Licensed under the MIT License.
// See LICENSE file in repository root for complete license text.

use proc_macro::TokenStream;
use quote::quote;
use syn::{self, DeriveInput};

#[proc_macro_derive(Header)]
pub fn aprox_eq_derive(input: TokenStream) -> TokenStream {
    let ast: DeriveInput = syn::parse(input).unwrap();
    impl_aprox_eq(&ast)
}

fn impl_aprox_eq(input: &DeriveInput) -> TokenStream {
    let name = &input.ident;

    let gen = quote! {
        impl Header for #name {
            fn addr(&self) -> u8 {
                self.addr
            }

            fn cmd(&self) -> u8 {
                self.cmd
            }
        }
    };

    gen.into()
}
