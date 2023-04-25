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
            fn get(&self) -> (u8, u8) {
                (self.addr, self.cmd)
            }

            fn extract<T>(packet: &serial::Packet<(u8, u8), T>) -> Self
            where
                T: serial::Data
            {
                Self {
                    addr: packet.head.0,
                    cmd: packet.head.1,
                }
            }
        }

        impl Into<(u8, u8)> for #name {
            fn into(&self) -> (u8, u8) {
                self.get()
            }
        }

        impl From<(u8, u8)> for #name {
            fn from(tup: (u8, u8)) -> Self {
                Self {
                    addr: tup.0,
                    cmd: tup.1,
                }
            }
        }
    };

    gen.into()
}
