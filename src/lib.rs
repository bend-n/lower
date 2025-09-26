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
    fn sub_bin(&self, op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream;
    fn sub_unop(&self, op: UnOp, x: TokenStream) -> TokenStream;
}

struct Basic;
impl Sub for Basic {
    fn sub_bin(&self, op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
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

    fn sub_unop(&self, op: UnOp, x: TokenStream) -> TokenStream {
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

struct Wrapping;
impl Sub for Wrapping {
    fn sub_bin(&self, op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
        use syn::BinOp::*;
        match op {
            Add(_) => quote!((#left).wrapping_add(#right)),
            Sub(_) => quote!((#left).wrapping_sub(#right)),
            Mul(_) => quote!((#left).wrapping_mul(#right)),
            Div(_) => quote!((#left).wrapping_div(#right)),
            Rem(_) => quote!((#left).wrapping_rem(#right)),
            Shl(_) => quote!((#left).wrapping_shl(#right)),
            Shr(_) => quote!((#left).wrapping_shr(#right)),

            SubAssign(_) => quote!(#left = #left.wrapping_sub(#right)),
            AddAssign(_) => quote!(#left = #left.wrapping_add(#right)),
            MulAssign(_) => quote!(#left = #left.wrapping_mul(#right)),
            DivAssign(_) => quote!(#left = #left.wrapping_div(#right)),
            RemAssign(_) => quote!(#left = #left.wrapping_rem(#right)),
            ShlAssign(_) => quote!(#left = #left.wrapping_shl(#right)),
            ShrAssign(_) => quote!(#left = #left.wrapping_shr(#right)),

            _ => quote!((#left) #op (#right)),
        }
    }

    fn sub_unop(&self, op: UnOp, x: TokenStream) -> TokenStream {
        match op {
            UnOp::Neg(_) => quote!((#x).wrapping_neg()),
            _ => quote!(#op #x),
        }
    }
}

struct Saturating;
impl Sub for Saturating {
    fn sub_bin(&self, op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
        use syn::BinOp::*;
        match op {
            Add(_) => quote!((#left).saturating_add(#right)),
            Sub(_) => quote!((#left).saturating_sub(#right)),
            Mul(_) => quote!((#left).saturating_mul(#right)),
            Div(_) => quote!((#left).saturating_div(#right)),
            Rem(_) => quote!((#left).saturating_rem(#right)),
            Shl(_) => quote!((#left).saturating_shl(#right)),
            Shr(_) => quote!((#left).saturating_shr(#right)),

            SubAssign(_) => quote!(#left = #left.saturating_sub(#right)),
            AddAssign(_) => quote!(#left = #left.saturating_add(#right)),
            MulAssign(_) => quote!(#left = #left.saturating_mul(#right)),
            DivAssign(_) => quote!(#left = #left.saturating_div(#right)),
            RemAssign(_) => quote!(#left = #left.saturating_rem(#right)),
            ShlAssign(_) => quote!(#left = #left.saturating_shl(#right)),
            ShrAssign(_) => quote!(#left = #left.saturating_shr(#right)),

            _ => quote!((#left) #op (#right)),
        }
    }

    fn sub_unop(&self, op: UnOp, x: TokenStream) -> TokenStream {
        match op {
            UnOp::Neg(_) => quote!((#x).saturating_neg()),
            _ => quote!(#op #x),
        }
    }
}

struct Algebraic;
impl Sub for Algebraic {
    fn sub_bin(&self, op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
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

    fn sub_unop(&self, op: UnOp, x: TokenStream) -> TokenStream {
        quote!(#op #x)
    }
}

struct Fast;
impl Sub for Fast {
    fn sub_bin(&self, op: BinOp, left: TokenStream, right: TokenStream) -> TokenStream {
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

    fn sub_unop(&self, op: UnOp, x: TokenStream) -> TokenStream {
        quote!(#op #x)
    }
}

fn walk(sub: &impl Sub, e: Expr) -> TokenStream {
    let walk = |e| walk(sub, e);
    let map_block = |b| map_block(sub, b);
    match e {
        Expr::Binary(ExprBinary {
            left, op, right, ..
        }) => {
            let left = walk(*left);
            let right = walk(*right);
            sub.sub_bin(op, left, right)
        }
        Expr::Unary(ExprUnary { op, expr, .. }) => sub.sub_unop(op, walk(*expr)),
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
            quote!(#lifetimes #constness #movability #asyncness #capture |#inputs| #output { #body })
        }
        Expr::ForLoop(ExprForLoop {
            label,
            pat,
            expr,
            body,
            ..
        }) => {
            let (expr, body) = (walk(*expr), map_block(body));
            quote!(#label for #pat in #expr #body)
        }
        Expr::Let(ExprLet { pat, expr, .. }) => {
            quote_with!(expr = walk(*expr) => let #pat = #expr)
        }
        Expr::Const(ExprConst { block, .. }) => {
            quote_with!(block =map_block(block) => const #block)
        }
        Expr::Range(ExprRange {
            start, limits, end, ..
        }) => {
            let (start, end) = (start.map(|x| walk(*x)), end.map(|x| walk(*x)));
            quote!((#start #limits #end))
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
            let block = map_block(block);
            quote!(try #block)
        }
        Expr::Unsafe(ExprUnsafe { block, .. }) => {
            quote_with!(block =map_block(block) => unsafe #block)
        }
        Expr::While(ExprWhile {
            label, cond, body, ..
        }) => {
            quote_with!(cond = walk(*cond); body =map_block(body) => #label while #cond #body)
        }
        Expr::Index(ExprIndex { expr, index, .. }) => {
            let expr = walk(*expr);
            let index = walk(*index);
            quote!(#expr [ #index ])
        }
        Expr::Loop(ExprLoop { label, body, .. }) => {
            quote_with!(body =map_block(body) => #label loop #body)
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
        Expr::Match(ExprMatch { expr, arms, .. }) => {
            let arms = arms.into_iter().map(
                |Arm {
                     pat,
                     guard,

                     body,
                     //  comma,
                     ..
                 }| {
                    let b = walk(*body);
                    let guard = match guard {
                        Some((i, x)) => {
                            let z = walk(*x);
                            quote! { #i #z }
                        }
                        None => quote! {},
                    };
                    quote! { #pat #guard => { #b } }
                },
            );
            quote!(match #expr { #(#arms)* })
        }
        Expr::If(ExprIf {
            cond,
            then_branch,
            else_branch: Some((_, else_branch)),
            ..
        }) => {
            let (cond, then_branch, else_branch) =
                (walk(*cond), map_block(then_branch), walk(*else_branch));
            quote!(if #cond #then_branch else #else_branch)
        }
        Expr::If(ExprIf {
            cond, then_branch, ..
        }) => {
            let (cond, then_branch) = (walk(*cond), map_block(then_branch));
            quote!(if #cond #then_branch)
        }
        Expr::Async(ExprAsync {
            attrs,
            capture,
            block,
            ..
        }) => {
            let block = map_block(block);
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
            let b = map_block(block);
            quote! { #label: #b }
        }
        Expr::Block(ExprBlock { block, .. }) => map_block(block),
        Expr::Cast(ExprCast {
            expr, as_token, ty, ..
        }) => {
            let e = walk(*expr);
            quote! { #e #as_token #ty }
        }
        e => quote!(#e),
    }
}

fn map_block(sub: &impl Sub, Block { stmts, .. }: Block) -> TokenStream {
    let stmts = stmts.into_iter().map(|x| walk_stmt(sub, x));
    quote! { { #(#stmts)* } }
}

fn walk_stmt(sub: &impl Sub, x: Stmt) -> TokenStream {
    let walk = |e| walk(sub, e);
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
        Stmt::Item(x) => walk_item(sub, x),
        Stmt::Expr(e, t) => {
            let e = walk(e);
            quote!(#e #t)
        }
        e => quote!(#e),
    }
}

fn walk_item(sub: &impl Sub, x: Item) -> TokenStream {
    let walk = |e| walk(sub, e);
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
            let block = map_block(sub, *block);
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
                    let block = map_block(sub, block);
                    quote!(#(#attrs)* #vis #defaultness #sig #block)
                }
                e => quote!(#e),
            });
            let trait_ = trait_.map(|(n, pat, fr)| quote!(#n #pat #fr));
            quote!(#(#attrs)* #unsafety #defaultness impl #generics #trait_ #self_ty { #(#items)* })
        }
        Item::Mod(ItemMod {
            attrs,
            vis,
            ident,
            content: Some((_, content)),
            ..
        }) => {
            let content = content.into_iter().map(|x| walk_item(sub, x));
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
    ($input:ident,$t:expr) => {
        match parse::<Expr>($input.clone())
            .map(|x| walk(&$t, x))
            .map_err(|x| x.to_compile_error().into_token_stream())
        {
            Ok(x) => x,
            Err(e) => parse::<Stmt>($input)
                .map(|x| walk_stmt(&$t, x))
                .unwrap_or(e),
        }
        .into()
    };
}

#[proc_macro]
pub fn math(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Basic {})
}

#[proc_macro]
pub fn fast(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Fast {})
}

#[proc_macro]
pub fn algebraic(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Algebraic {})
}

#[proc_macro]
pub fn wrapping(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Wrapping {})
}

#[proc_macro]
pub fn saturating(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    walk!(input, Saturating {})
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
        "wrapping" => wrapping(input),
        "saturating" => saturating(input),
        _ => {
            quote! { compile_error!("type must be {fast, basic, algebraic, wrapping, saturating}") }
                .into()
        }
    }
}
