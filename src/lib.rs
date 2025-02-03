//! a lil macro crate.
//!
//! provides a handy macro for converting `a + b` to `a.add(b)` for when you cant easily overload the `Add` trait.
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{spanned::Spanned, *};

macro_rules! quote_with {
    ($($k: ident = $v: expr);+ => $($tt:tt)+) => {{
        $(let $k = $v;)+
        quote!($($tt)+)
    }};
}
trait Sub {
    fn sub_bin(op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream;
    fn sub_unop(op: UnOp, x: TokenStream) -> TokenStream;
}

struct Basic;
impl Sub for Basic {
    fn sub_bin(op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
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
            e => {
                Error::new(e.span(), format!("{}", quote!(op #e not supported))).to_compile_error()
            }
        }
    }

    fn sub_unop(op: UnOp, x: TokenStream) -> TokenStream {
        match op {
            UnOp::Deref(_) => quote!((#x).deref()),
            UnOp::Not(_) => quote!((#x).not()),
            UnOp::Neg(_) => quote!((#x).neg()),
            e => Error::new(
                e.span(),
                "it would appear a new operation has been added! please tell me.",
            )
            .to_compile_error(),
        }
    }
}

struct Algebraic;
impl Sub for Algebraic {
    fn sub_bin(op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
        use syn::BinOp::*;
        match op {
            Add(_) => quote!(core::intrinsics::fadd_algebraic(#left, #right)),
            Sub(_) => quote!(core::intrinsics::fsub_algebraic(#left, #right)),
            Mul(_) => quote!(core::intrinsics::fmul_algebraic(#left, #right)),
            Div(_) => quote!(core::intrinsics::fdiv_algebraic(#left, #right)),
            Rem(_) => quote!(core::intrinsics::frem_algebraic(#left, #right)),
            And(_) => quote!(core::intrinsics::fand_algebraic(#left, #right)),
            _ => quote!((#left) #op (#right)),
        }
    }

    fn sub_unop(op: UnOp, x: TokenStream) -> TokenStream {
        quote!(#op #x)
    }
}

struct Fast;
impl Sub for Fast {
    fn sub_bin(op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
        use syn::BinOp::*;
        match op {
            Add(_) => quote!(core::intrinsics::fadd_fast(#left, #right)),
            Sub(_) => quote!(core::intrinsics::fsub_fast(#left, #right)),
            Mul(_) => quote!(core::intrinsics::fmul_fast(#left, #right)),
            Div(_) => quote!(core::intrinsics::fdiv_fast(#left, #right)),
            Rem(_) => quote!(core::intrinsics::frem_fast(#left, #right)),
            And(_) => quote!(core::intrinsics::fand_fast(#left, #right)),
            Eq(_) => quote!(/* eq */ ((#left) + 0.0).to_bits() == ((#right) + 0.0).to_bits()),
            _ => quote!((#left) #op (#right)),
        }
    }

    fn sub_unop(op: UnOp, x: TokenStream) -> TokenStream {
        quote!(#op #x)
    }
}

fn walk<T: Sub>(e: Expr) -> TokenStream {
    let walk = walk::<T>;
    match e {
        Expr::Binary(ExprBinary {
            left, op, right, ..
        }) => {
            let left = walk(*left);
            let right = walk(*right);
            T::sub_bin(op, left, right)
        }
        Expr::Unary(ExprUnary { op, expr, .. }) => T::sub_unop(op, walk(*expr)),
        Expr::Break(ExprBreak {
            label,
            expr: Some(expr),
            ..
        }) => {
            let expr = walk(*expr);
            quote!(#label #expr)
        }
        Expr::Call(ExprCall { func, args, .. }) => {
            let f = walk(*func);
            let args = args.into_iter().map(walk);
            quote!(#f ( #(#args),* ))
        }
        Expr::Closure(ExprClosure {
            lifetimes,
            constness,
            movability,
            asyncness,
            capture,
            inputs,
            output,
            body,
            ..
        }) => {
            let body = walk(*body);
            quote!(#lifetimes #constness #movability #asyncness #capture |#inputs| #output #body)
        }
        Expr::ForLoop(ExprForLoop {
            label,
            pat,
            expr,
            body,
            ..
        }) => {
            let (expr, body) = (walk(*expr), map_block::<T>(body));
            quote!(#label for #pat in #expr #body)
        }
        Expr::Let(ExprLet { pat, expr, .. }) => {
            quote_with!(expr = walk(*expr) => let #pat = #expr)
        }
        Expr::Const(ExprConst { block, .. }) => {
            quote_with!(block = map_block::<T>(block) => const #block)
        }
        Expr::Range(ExprRange {
            start, limits, end, ..
        }) => {
            let (start, end) = (start.map(|x| walk(*x)), end.map(|x| walk(*x)));
            quote!(#start #limits #end)
        }
        Expr::Return(ExprReturn { expr, .. }) => {
            let expr = expr.map(|x| walk(*x));
            quote!(return #expr;)
        }
        Expr::Try(ExprTry { expr, .. }) => {
            let expr = walk(*expr);
            quote!(#expr ?)
        }
        Expr::TryBlock(ExprTryBlock { block, .. }) => {
            let block = map_block::<T>(block);
            quote!(try #block)
        }
        Expr::Unsafe(ExprUnsafe { block, .. }) => {
            quote_with!(block = map_block::<T>(block) => unsafe #block)
        }
        Expr::While(ExprWhile {
            label, cond, body, ..
        }) => {
            quote_with!(cond = walk(*cond); body = map_block::<T>(body) => #label while #cond #body)
        }
        Expr::Loop(ExprLoop { label, body, .. }) => {
            quote_with!(body = map_block::<T>(body) => #label loop #body)
        }
        Expr::Reference(ExprReference {
            mutability, expr, ..
        }) => {
            let expr = walk(*expr);
            quote!(& #mutability #expr)
        }
        Expr::MethodCall(ExprMethodCall {
            receiver,
            method,
            turbofish,
            args,
            ..
        }) => {
            let receiver = walk(*receiver);
            let args = args.into_iter().map(walk);
            quote!(#receiver . #method #turbofish (#(#args,)*))
        }
        Expr::If(ExprIf {
            cond,
            then_branch,
            else_branch: Some((_, else_branch)),
            ..
        }) => {
            let (cond, then_branch, else_branch) =
                (walk(*cond), map_block::<T>(then_branch), walk(*else_branch));
            quote!(if #cond #then_branch else #else_branch)
        }
        Expr::If(ExprIf {
            cond, then_branch, ..
        }) => {
            let (cond, then_branch) = (walk(*cond), map_block::<T>(then_branch));
            quote!(if #cond #then_branch)
        }
        Expr::Async(ExprAsync {
            attrs,
            capture,
            block,
            ..
        }) => {
            let block = map_block::<T>(block);
            quote!(#(#attrs)* async #capture #block)
        }
        Expr::Await(ExprAwait { base, .. }) => {
            let base = walk(*base);
            quote!(#base.await)
        }
        Expr::Assign(ExprAssign { left, right, .. }) => {
            let (left, right) = (walk(*left), walk(*right));
            quote!(#left = #right;)
        }
        Expr::Paren(ExprParen { expr, .. }) => {
            let expr = walk(*expr);
            quote!(#expr)
        }
        Expr::Tuple(ExprTuple { elems, .. }) => {
            let ts = elems.into_iter().map(walk);
            quote!((#(#ts,)*))
        }
        Expr::Array(ExprArray { elems, .. }) => {
            let ts = elems.into_iter().map(walk);
            quote!([#(#ts,)*])
        }
        Expr::Repeat(ExprRepeat { expr, len, .. }) => {
            let x = walk(*expr);
            let len = walk(*len);
            quote!([ #x ; #len ])
        }
        Expr::Block(ExprBlock {
            block,
            label: Some(label),
            ..
        }) => {
            let b = map_block::<T>(block);
            quote! { #label: #b }
        }
        Expr::Block(ExprBlock { block, .. }) => map_block::<T>(block),
        e => quote!(#e),
    }
}

fn map_block<T: Sub>(Block { stmts, .. }: Block) -> TokenStream {
    let stmts = stmts.into_iter().map(walk_stmt::<T>);
    quote! { { #(#stmts)* } }
}

fn walk_stmt<T: Sub>(x: Stmt) -> TokenStream {
    let walk = walk::<T>;
    match x {
        Stmt::Local(Local {
            pat,
            init:
                Some(LocalInit {
                    expr,
                    diverge: Some((_, diverge)),
                    ..
                }),
            ..
        }) => {
            let expr = walk(*expr);
            let diverge = walk(*diverge);
            quote!(let #pat = #expr else { #diverge };)
        }
        Stmt::Local(Local {
            pat,
            init: Some(LocalInit { expr, .. }),
            ..
        }) => {
            let expr = walk(*expr);
            quote!(let #pat = #expr;)
        }
        Stmt::Item(x) => walk_item::<T>(x),
        Stmt::Expr(e, t) => {
            let e = walk(e);
            quote!(#e #t)
        }
        e => quote!(#e),
    }
}

fn walk_item<T: Sub>(x: Item) -> TokenStream {
    let walk = walk::<T>;
    match x {
        Item::Const(ItemConst {
            vis,
            ident,
            ty,
            expr,
            ..
        }) => {
            let expr = walk(*expr);
            quote!(#vis const #ident : #ty = #expr;)
        }
        Item::Fn(ItemFn {
            vis,
            attrs,
            sig,
            block,
        }) => {
            let block = map_block::<T>(*block);
            quote!( #(#attrs)* #vis #sig #block)
        }
        Item::Impl(ItemImpl {
            attrs,
            unsafety,
            defaultness,
            generics,
            trait_,
            self_ty,
            items,
            ..
        }) => {
            let items = items.into_iter().map(|x| match x {
                ImplItem::Const(ImplItemConst {
                    vis,
                    attrs,
                    defaultness,
                    ident,
                    ty,
                    expr,
                    ..
                }) => {
                    let expr = walk(expr);
                    quote!(#(#attrs)* #vis #defaultness const #ident: #ty = #expr;)
                }
                ImplItem::Fn(ImplItemFn {
                    attrs,
                    vis,
                    defaultness,
                    sig,
                    block,
                }) => {
                    let block = map_block::<T>(block);
                    quote!(#(#attrs)* #vis #defaultness #sig #block)
                }
                e => quote!(#e),
            });
            let trait_ = trait_.map(|(n, pat, _)| quote!(#n #pat));
            quote!(#(#attrs)* #unsafety #defaultness impl #generics #trait_ #self_ty { #(#items)* })
        }
        Item::Mod(ItemMod {
            attrs,
            vis,
            ident,
            content: Some((_, content)),
            ..
        }) => {
            let content = content.into_iter().map(walk_item::<T>);
            quote!(#(#attrs)* #vis mod #ident { #(#content)* })
        }
        Item::Static(ItemStatic {
            attrs,
            vis,
            mutability,
            ident,
            ty,
            expr,
            ..
        }) => {
            let expr = walk(*expr);
            quote!(#(#attrs)* #vis static #mutability #ident: #ty = #expr)
        }
        e => quote!(#e),
    }
}

macro_rules! walk {
    ($input:ident,$t:ty) => {
        match parse::<Expr>($input.clone())
            .map(walk::<$t>)
            .map_err(|x| x.to_compile_error().into_token_stream())
        {
            Ok(x) => x,
            Err(e) => parse::<Stmt>($input).map(walk_stmt::<$t>).unwrap_or(e),
        }
        .into()
    };
}

#[proc_macro]
pub fn math(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Basic)
}

#[proc_macro]
pub fn fast(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Fast)
}

#[proc_macro]
pub fn algebraic(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Algebraic)
}

#[proc_macro_attribute]
pub fn apply(
    args: proc_macro::TokenStream,
    input: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
    match &*args.to_string() {
        "basic" | "" => math(input),
        "fast" => fast(input),
        "algebraic" => algebraic(input),
        _ => quote! { compile_error!("type must be {fast, basic, algebraic}") }.into(),
    }
}
