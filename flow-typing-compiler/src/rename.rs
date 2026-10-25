//! Conversion to de Bruijn indices and other basic well-formedness checking.

use std::collections::VecDeque;

use logos::Span;

use crate::{
    error::{Diagnostic, Errors},
    parse::{self, Flow, Literal, Pattern, PrimOp, PrimTy},
};

#[derive(Debug, Clone)]

pub struct Decl<'src> {
    pub name: &'src str,
    pub span: Span,
    pub ty: Type<'src>,
}

impl<'src> Decl<'src> {
    /// Contains no duplicates.
    pub fn ty_vars(&self) -> Vec<&'src str> {
        let mut vars = self.ty.vars();
        vars.sort();
        vars.dedup();
        vars
    }
}

#[derive(Debug, Clone)]
pub struct Def<'src> {
    pub name: &'src str,
    pub span: Span,
    pub patterns: Vec<(Flow, Pattern<'src>)>,
    pub expr: Expr<'src>,
}

#[derive(Debug, Clone)]
pub enum Type<'src> {
    Var(&'src str, Span),
    Prim(PrimTy, Span),
    Arrow(Box<TType<'src>>, Box<TType<'src>>, Span),
    Tuple(Vec<Type<'src>>, Span),
    Either(Box<Type<'src>>, Box<Type<'src>>, Span),
    List(Box<Type<'src>>, Span),
    Tree(Box<Type<'src>>, Span),
}

impl<'src> Type<'src> {
    fn span(&self) -> Span {
        match self {
            Type::Var(_, span) => span.clone(),
            Type::Prim(_, span) => span.clone(),
            Type::Arrow(_, _, span) => span.clone(),
            Type::Tuple(_, span) => span.clone(),
            Type::Either(_, _, span) => span.clone(),
            Type::List(_, span) => span.clone(),
            Type::Tree(_, span) => span.clone(),
        }
    }

    /// Contains duplicates.
    pub fn vars(&self) -> Vec<&'src str> {
        match self {
            Type::Var(name, _) => vec![name],
            Type::Prim(_, _) => Vec::new(),
            Type::Arrow(l, r, _) => l.vars().into_iter().chain(r.vars()).collect(),
            Type::Tuple(tys, _) => tys.iter().flat_map(|ty| ty.vars()).collect(),
            Type::Either(l, r, _) => l.vars().into_iter().chain(r.vars()).collect(),
            Type::List(t, _) => t.vars(),
            Type::Tree(t, _) => t.vars(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum TType<'src> {
    Plain(Type<'src>),
    Flow(Type<'src>, Type<'src>),
}

impl<'src> TType<'src> {
    fn span(&self) -> Span {
        match self {
            TType::Plain(ty) => ty.span(),
            TType::Flow(l, r) => l.span().start..r.span().end,
        }
    }

    /// Contains duplicates.
    pub fn vars(&self) -> Vec<&'src str> {
        match self {
            TType::Plain(t) => t.vars(),
            TType::Flow(l, r) => l.vars().into_iter().chain(r.vars()).collect(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<'src> {
    /// De Bruijn indexed.
    Var(usize, Span),
    Inst(&'src str, Span),
    Tilde(Box<Expr<'src>>, Span),
    App(Box<Expr<'src>>, Box<Expr<'src>>, Span),
    Assign(Box<Expr<'src>>, Box<Expr<'src>>, Span),
    Literal(Literal, Span),
    PrimOp(Box<Expr<'src>>, Box<Expr<'src>>, PrimOp, Span),
    Tuple(Vec<Expr<'src>>, Span),
    EmptyList(Span),
    Cons(Box<Expr<'src>>, Box<Expr<'src>>, Span),
    Left(Box<Expr<'src>>, Span),
    Right(Box<Expr<'src>>, Span),
    Let {
        flow: Flow,
        pattern: Pattern<'src>,
        value: Box<Expr<'src>>,
        body: Box<Expr<'src>>,
        span: Span,
    },
    Case {
        flow: Flow,
        scrutinee: Box<Expr<'src>>,
        branches: Vec<(Pattern<'src>, Expr<'src>)>,
        span: Span,
    },
    Lambda {
        patterns: Vec<(Flow, Pattern<'src>)>,
        body: Box<Expr<'src>>,
        span: Span,
    },
}

impl<'src> Expr<'src> {
    pub fn span(&self) -> Span {
        match self {
            Expr::Var(_, span) => span.clone(),
            Expr::Inst(_, span) => span.clone(),
            Expr::Tilde(_, span) => span.clone(),
            Expr::App(_, _, span) => span.clone(),
            Expr::Assign(_, _, span) => span.clone(),
            Expr::Literal(_, span) => span.clone(),
            Expr::PrimOp(_, _, _, span) => span.clone(),
            Expr::Tuple(_, span) => span.clone(),
            Expr::EmptyList(span) => span.clone(),
            Expr::Cons(_, _, span) => span.clone(),
            Expr::Left(_, span) => span.clone(),
            Expr::Right(_, span) => span.clone(),
            Expr::Let { span, .. } => span.clone(),
            Expr::Case { span, .. } => span.clone(),
            Expr::Lambda { span, .. } => span.clone(),
        }
    }
}

pub fn rename<'src>(
    errors: &mut Errors,
    items: Vec<parse::Item<'src>>,
) -> (Vec<Decl<'src>>, Vec<Def<'src>>) {
    let mut decls = Vec::<Decl<'src>>::new();
    let mut todo_defs = Vec::new();
    for item in items {
        match item {
            parse::Item::Decl { name, span, ty } => {
                for decl in &decls {
                    if decl.name == name {
                        errors.push(Diagnostic::error(
                            span.clone(),
                            "duplicate definition name".to_owned(),
                        ));
                    }
                }
                decls.extend(rename_ty(errors, ty).map(|ty| Decl { name, span, ty }));
            }
            parse::Item::Def {
                name,
                span,
                patterns,
                expr,
            } => todo_defs.push((name, span, patterns, expr)),
        }
    }

    let mut defs = Vec::new();
    for (name, span, patterns, expr) in todo_defs {
        defs.extend(
            rename_expr(
                errors,
                &decls,
                &patterns
                    .iter()
                    .fold(RenameCtx::default(), |ctx, (_, pat)| ctx.extend(pat)),
                expr,
            )
            .map(|expr| Def {
                name,
                span,
                patterns,
                expr,
            }),
        )
    }

    (decls, defs)
}

fn rename_ty<'src>(errors: &mut Errors, ty: parse::PreType<'src>) -> Option<Type<'src>> {
    rename_tty(errors, ty).and_then(|ty| match ty {
        TType::Plain(ty) => Some(ty),
        TType::Flow(l, r) => {
            errors.push(Diagnostic::error(
                l.span().start..r.span().end,
                "flow type not allowed here".to_owned(),
            ));
            None
        }
    })
}

fn rename_tty<'src>(errors: &mut Errors, ty: parse::PreType<'src>) -> Option<TType<'src>> {
    match ty {
        parse::PreType::Var(var, span) => Some(TType::Plain(Type::Var(var, span))),
        parse::PreType::Prim(prim, span) => Some(TType::Plain(Type::Prim(prim, span))),
        parse::PreType::Flow(l, r, _) => {
            Some(TType::Flow(rename_ty(errors, *l)?, rename_ty(errors, *r)?))
        }
        parse::PreType::Either(span) | parse::PreType::List(span) | parse::PreType::Tree(span) => {
            errors.push(Diagnostic::error(span, "incomplete type".to_owned()));
            None
        }
        parse::PreType::App(left, right, span) => match *left {
            parse::PreType::App(lleft, lright, _) => match *lleft {
                parse::PreType::Either(_) => Some(TType::Plain(Type::Either(
                    Box::new(rename_ty(errors, *lright)?),
                    Box::new(rename_ty(errors, *right)?),
                    span,
                ))),
                _ => {
                    errors.push(Diagnostic::error(
                        span,
                        "invalid type application".to_owned(),
                    ));
                    None
                }
            },
            parse::PreType::List(_) => Some(TType::Plain(Type::List(
                Box::new(rename_ty(errors, *right)?),
                span,
            ))),
            parse::PreType::Tree(_) => Some(TType::Plain(Type::Tree(
                Box::new(rename_ty(errors, *right)?),
                span,
            ))),
            _ => {
                errors.push(Diagnostic::error(
                    span,
                    "invalid type application".to_owned(),
                ));
                None
            }
        },
        parse::PreType::Arrow(l, r, span) => Some(TType::Plain(Type::Arrow(
            Box::new(rename_tty(errors, *l)?),
            Box::new(rename_tty(errors, *r)?),
            span,
        ))),
        parse::PreType::Tuple(tys, span) => Some(TType::Plain(Type::Tuple(
            tys.into_iter()
                .filter_map(|ty| rename_ty(errors, ty))
                .collect(),
            span,
        ))),
    }
}

#[derive(Default, Clone)]
struct RenameCtx<'src> {
    vars: VecDeque<&'src str>,
}

impl<'src> RenameCtx<'src> {
    fn extend(mut self, pattern: &Pattern<'src>) -> Self {
        self.extend_mut(pattern);
        self
    }

    fn extend_mut(&mut self, pattern: &Pattern<'src>) {
        match pattern {
            Pattern::Var(name, _) => {
                self.vars.push_front(name);
            }
            Pattern::Literal(_, _) => {}
            Pattern::Tuple(patterns, _) => {
                for pat in patterns {
                    self.extend_mut(pat);
                }
            }
            Pattern::EmptyList(_) => {}
            Pattern::Cons(head, tail, _) => {
                self.extend_mut(head);
                self.extend_mut(tail);
            }
            Pattern::Left(pat, _) => self.extend_mut(pat),
            Pattern::Right(pat, _) => self.extend_mut(pat),
        }
    }
}

fn rename_expr<'src>(
    errors: &mut Errors,
    decls: &[Decl<'src>],
    ctx: &RenameCtx<'src>,
    expr: parse::Expr<'src>,
) -> Option<Expr<'src>> {
    match expr {
        parse::Expr::Var(name, span) => {
            match ctx.vars.iter().position(|var| *var == name) {
                Some(ix) => {
                    // This is the de Bruijn index for this variable.
                    Some(Expr::Var(ix, span))
                }
                None => {
                    // Silly O(n). This is not a production language!
                    if decls.iter().any(|decl| decl.name == name) {
                        Some(Expr::Inst(name, span))
                    } else {
                        errors.push(Diagnostic::error(
                            span,
                            format!("variable '{name}' not found in scope"),
                        ));
                        None
                    }
                }
            }
        }
        parse::Expr::Tilde(expr, span) => Some(Expr::Tilde(
            Box::new(rename_expr(errors, decls, ctx, *expr)?),
            span,
        )),
        parse::Expr::App(l, r, span) => Some(Expr::App(
            Box::new(rename_expr(errors, decls, ctx, *l)?),
            Box::new(rename_expr(errors, decls, ctx, *r)?),
            span,
        )),
        parse::Expr::Assign(l, r, span) => Some(Expr::Assign(
            Box::new(rename_expr(errors, decls, ctx, *l)?),
            Box::new(rename_expr(errors, decls, ctx, *r)?),
            span,
        )),
        parse::Expr::Literal(literal, span) => Some(Expr::Literal(literal, span)),
        parse::Expr::PrimOp(l, r, op, span) => Some(Expr::PrimOp(
            Box::new(rename_expr(errors, decls, ctx, *l)?),
            Box::new(rename_expr(errors, decls, ctx, *r)?),
            op,
            span,
        )),
        parse::Expr::Tuple(exprs, span) => Some(Expr::Tuple(
            exprs
                .into_iter()
                .filter_map(|e| rename_expr(errors, decls, ctx, e))
                .collect(),
            span,
        )),
        parse::Expr::EmptyList(span) => Some(Expr::EmptyList(span)),
        parse::Expr::Cons(head, tail, span) => Some(Expr::Cons(
            Box::new(rename_expr(errors, decls, ctx, *head)?),
            Box::new(rename_expr(errors, decls, ctx, *tail)?),
            span,
        )),
        parse::Expr::Let {
            flow,
            pattern,
            value,
            body,
            span,
        } => {
            let ctx2 = ctx.clone().extend(&pattern);
            Some(Expr::Let {
                flow,
                pattern,
                value: Box::new(rename_expr(errors, decls, ctx, *value)?),
                body: Box::new(rename_expr(errors, decls, &ctx2, *body)?),
                span,
            })
        }
        parse::Expr::Case {
            flow,
            scrutinee,
            branches,
            span,
        } => Some(Expr::Case {
            flow,
            scrutinee: Box::new(rename_expr(errors, decls, ctx, *scrutinee)?),
            branches: branches
                .into_iter()
                .filter_map(|(pat, body)| {
                    let ctx = ctx.clone().extend(&pat);
                    rename_expr(errors, decls, &ctx, body).map(|body| (pat, body))
                })
                .collect(),
            span,
        }),
        parse::Expr::Lambda(patterns, expr, span) => {
            let ctx2 = patterns
                .iter()
                .fold(ctx.clone(), |ctx, (_, pat)| ctx.extend(pat));
            Some(Expr::Lambda {
                patterns,
                body: Box::new(rename_expr(errors, decls, &ctx2, *expr)?),
                span,
            })
        }
        parse::Expr::Left(expr, span) => Some(Expr::Left(
            Box::new(rename_expr(errors, decls, ctx, *expr)?),
            span,
        )),
        parse::Expr::Right(expr, span) => Some(Expr::Right(
            Box::new(rename_expr(errors, decls, ctx, *expr)?),
            span,
        )),
    }
}
