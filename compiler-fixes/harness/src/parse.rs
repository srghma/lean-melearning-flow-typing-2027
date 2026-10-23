//! The data types of the compiler's `parse.rs` (lines 1-186), without the `chumsky` parser.
use std::fmt::Display;

use logos::Span;


#[derive(Debug, Clone)]
pub enum Item<'src> {
    Decl {
        name: &'src str,
        span: Span,
        ty: PreType<'src>,
    },
    Def {
        name: &'src str,
        span: Span,
        patterns: Vec<(Flow, Pattern<'src>)>,
        expr: Expr<'src>,
    },
}

/// Parse, don't validate.
/// We don't check if these are really well-formed types yet.
#[derive(Debug, Clone)]
pub enum PreType<'src> {
    Var(&'src str, Span),
    Prim(PrimTy, Span),
    Either(Span),
    List(Span),
    Tree(Span),
    App(Box<PreType<'src>>, Box<PreType<'src>>, Span),
    Flow(Box<PreType<'src>>, Box<PreType<'src>>, Span),
    Arrow(Box<PreType<'src>>, Box<PreType<'src>>, Span),
    Tuple(Vec<PreType<'src>>, Span),
}

impl<'src> PreType<'src> {
    fn span(&self) -> Span {
        match self {
            PreType::Var(_, span) => span.clone(),
            PreType::Prim(_, span) => span.clone(),
            PreType::Either(span) => span.clone(),
            PreType::List(span) => span.clone(),
            PreType::Tree(span) => span.clone(),
            PreType::App(_, _, span) => span.clone(),
            PreType::Flow(_, _, span) => span.clone(),
            PreType::Arrow(_, _, span) => span.clone(),
            PreType::Tuple(_, span) => span.clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimTy {
    Int,
    Bool,
    Char,
    Handle,
    World,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Flow {
    Plain,
    Flow,
}

#[derive(Debug, Clone)]
pub enum Pattern<'src> {
    Var(&'src str, Span),
    Literal(Literal, Span),
    Tuple(Vec<Pattern<'src>>, Span),
    EmptyList(Span),
    Cons(Box<Pattern<'src>>, Box<Pattern<'src>>, Span),
    Left(Box<Pattern<'src>>, Span),
    Right(Box<Pattern<'src>>, Span),
}

impl<'src> Pattern<'src> {
    pub fn span(&self) -> Span {
        match self {
            Pattern::Var(_, span) => span.clone(),
            Pattern::Literal(_, span) => span.clone(),
            Pattern::Tuple(_, span) => span.clone(),
            Pattern::EmptyList(span) => span.clone(),
            Pattern::Cons(_, _, span) => span.clone(),
            Pattern::Left(_, span) => span.clone(),
            Pattern::Right(_, span) => span.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Expr<'src> {
    Var(&'src str, Span),
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
    Lambda(Vec<(Flow, Pattern<'src>)>, Box<Expr<'src>>, Span),
}

#[derive(Debug, Clone)]
pub enum Literal {
    Integer(u64),
    Bool(bool),
    Char(char),
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Literal::Integer(integer) => write!(f, "{integer}"),
            Literal::Bool(false) => write!(f, "False"),
            Literal::Bool(true) => write!(f, "True"),
            Literal::Char(c) => write!(f, "{c:?}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Eq,
    Seq,
}

impl Display for PrimOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PrimOp::Add => write!(f, "+"),
            PrimOp::Sub => write!(f, "-"),
            PrimOp::Mul => write!(f, "*"),
            PrimOp::Div => write!(f, "/"),
            PrimOp::Eq => write!(f, "=="),
            PrimOp::Seq => write!(f, ";"),
        }
    }
}

impl<'src> Expr<'src> {
    fn span(&self) -> Span {
        match self {
            Expr::Var(_, span) => span.clone(),
            Expr::Tilde(_, span) => span.clone(),
            Expr::App(_, _, span) => span.clone(),
            Expr::Assign(_, _, span) => span.clone(),
            Expr::Literal(_, span) => span.clone(),
            Expr::PrimOp(_, _, _, span) => span.clone(),
            Expr::Left(_, span) => span.clone(),
            Expr::Right(_, span) => span.clone(),
            Expr::Let { span, .. } => span.clone(),
            Expr::Case { span, .. } => span.clone(),
            Expr::Tuple(_, span) => span.clone(),
            Expr::EmptyList(span) => span.clone(),
            Expr::Cons(_, _, span) => span.clone(),
            Expr::Lambda(_, _, span) => span.clone(),
        }
    }
}
