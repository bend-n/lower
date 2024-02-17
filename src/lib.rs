//! a lil macro crate.
//!
//! provides a handy macro for converting `a + b` to `a.add(b)` for when you cant easily overload the `Add` trait.
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, spanned::Spanned, Expr, ExprBinary, ExprUnary};

fn walk(e: Expr) -> proc_macro2::TokenStream {
    match e {
        Expr::Binary(ExprBinary {
            left, op, right, ..
        }) => {
            let left = walk(*left);
            let right = walk(*right);
            use syn::BinOp::*;
            match op {
                Add(_) => quote!((#left).add(#right)),
                Sub(_) => quote!((#left).sub(#right)),
                Mul(_) => quote!((#left).mul(#right)),
                Div(_) => quote!((#left).div(#right)),
                Rem(_) => quote!((#left).rem(#right)),
                And(_) => quote!((#left).and(#right)),
                Or(_) => quote!((#left).or(#right)),
                BitXor(_) => quote!((#left).bitxor(#right)),
                BitAnd(_) => quote!((#left).bitand(#right)),
                BitOr(_) => quote!((#left).bitor(#right)),
                Shl(_) => quote!((#left).shl(#right)),
                Shr(_) => quote!((#left).shr(#right)),
                Eq(_) => quote!((#left).eq(#right)),
                Lt(_) => quote!((#left).lt(#right)),
                Le(_) => quote!((#left).le(#right)),
                Ne(_) => quote!((#left).ne(#right)),
                Ge(_) => quote!((#left).ge(#right)),
                Gt(_) => quote!((#left).gt(#right)),
                // don't support assigning ops
                e => syn::Error::new(e.span(), format!("{}", quote!(op #e not supported)))
                    .to_compile_error(),
            }
        }
        Expr::Unary(ExprUnary { op, expr, .. }) => {
            let x = walk(*expr);
            match op {
                syn::UnOp::Deref(_) => quote!((#x).deref()),
                syn::UnOp::Not(_) => quote!((#x).not()),
                syn::UnOp::Neg(_) => quote!((#x).neg()),
                e => syn::Error::new(
                    e.span(),
                    "it would appear a new operation has been added! please tell me.",
                )
                .to_compile_error(),
            }
        }
        e => quote!(#e),
    }
}

/// Lower math to method calls.
/// ```
/// # use std::ops::*;
/// let [a, b, c] = [5i32, 6, 7];
/// assert_eq!(lower::math! { a * *&b + -c }, a * *&b + -c);
/// // expands to
/// // a.mul((&b).deref()).add(c.neg())
/// ```
#[proc_macro]
pub fn math(input: TokenStream) -> TokenStream {
    walk(parse_macro_input!(input as Expr)).into()
}
