use std::fmt::Display;

use chumsky::prelude::*;
use logos::Span;

use crate::{
    error::{Diagnostic, Errors},
    layout::Token,
};

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

pub fn parse<'src>(es: &mut Errors, tokens: Vec<(Token<'src>, Span)>) -> Vec<Item<'src>> {
    let output = parser().parse(&tokens);
    // println!("{output:#?}");
    for error in output.errors() {
        es.push(Diagnostic::error(
            tokens[error.span().start.min(tokens.len() - 1)].1.start
                ..tokens[error.span().end.saturating_sub(1).min(tokens.len() - 1)]
                    .1
                    .end,
            match error.reason() {
                chumsky::error::RichReason::ExpectedFound { expected, found } => {
                    let mut expected = expected
                        .iter()
                        .filter_map(|pat| match pat {
                            chumsky::error::RichPattern::Label(cow) => Some(cow.to_string()),
                            chumsky::error::RichPattern::EndOfInput => {
                                Some("end of file".to_owned())
                            }
                            _ => None,
                        })
                        .collect::<Vec<_>>();
                    let found = if let Some(found) = found {
                        found.0.to_string()
                    } else {
                        "end of file".to_owned()
                    };
                    match expected.len() {
                        0 => format!("unexpected {found}"),
                        1 => format!("expected {}, found {}", expected.pop().unwrap(), found),
                        2 => {
                            let last = expected.pop().unwrap();
                            format!(
                                "expected {} or {last}, found {}",
                                expected.pop().unwrap(),
                                found
                            )
                        }
                        _ => {
                            let last = expected.pop().unwrap();
                            format!(
                                "expected {}, or {last}, found {}",
                                expected.join(", "),
                                found
                            )
                        }
                    }
                }
                chumsky::error::RichReason::Custom(message) => message.to_owned(),
            },
        ));
    }
    output.into_output().unwrap_or_default()
}

trait P<'a, 'src: 'a, T>:
    Parser<'a, &'a [(Token<'src>, Span)], T, chumsky::extra::Err<Rich<'a, (Token<'src>, Span)>>> + Clone
{
}

impl<'a, 'src: 'a, T, U> P<'a, 'src, T> for U where
    U: Parser<'a, &'a [(Token<'src>, Span)], T, chumsky::extra::Err<Rich<'a, (Token<'src>, Span)>>>
        + Clone
{
}

fn parser<'a, 'src: 'a>() -> impl P<'a, 'src, Vec<Item<'src>>> {
    item()
        .separated_by(semicolon())
        .allow_leading()
        .allow_trailing()
        .collect()
}

fn item<'a, 'src: 'a>() -> impl P<'a, 'src, Item<'src>> {
    choice((
        ident()
            .then_ignore(exact(Token::Type))
            .then(ty())
            // .then_ignore(exact(Token::Semicolon))
            .map(|((name, span), ty)| Item::Decl { name, span, ty }),
        ident()
            .then(fpattern().repeated().collect())
            .then_ignore(exact(Token::Define))
            .then(expr())
            // .then_ignore(exact(Token::Semicolon))
            .map(|(((name, span), patterns), expr)| Item::Def {
                name,
                span,
                patterns,
                expr,
            }),
    ))
}

fn ty<'a, 'src: 'a>() -> impl P<'a, 'src, PreType<'src>> {
    use chumsky::pratt::*;

    recursive(|ty| {
        let atom = choice((
            ident().map(|(ident, span)| PreType::Var(ident, span)),
            exact(Token::Int).map(|span| PreType::Prim(PrimTy::Int, span)),
            exact(Token::Bool).map(|span| PreType::Prim(PrimTy::Bool, span)),
            exact(Token::Char).map(|span| PreType::Prim(PrimTy::Char, span)),
            exact(Token::String).map(|span| {
                PreType::App(
                    Box::new(PreType::List(span.clone())),
                    Box::new(PreType::Prim(PrimTy::Char, span.clone())),
                    span,
                )
            }),
            exact(Token::Handle).map(|span| PreType::Prim(PrimTy::Handle, span)),
            exact(Token::World).map(|span| PreType::Prim(PrimTy::World, span)),
            exact(Token::Either).map(PreType::Either),
            exact(Token::List).map(PreType::List),
            exact(Token::Tree).map(PreType::Tree),
            exact(Token::LParen)
                .then(exact(Token::RParen))
                .map(|(l, r)| PreType::Tuple(Vec::new(), l.start..r.end)),
            exact(Token::LParen)
                .then(ty.clone())
                .then(
                    (exact(Token::Comma).ignore_then(
                        ty.clone()
                            .separated_by(exact(Token::Comma))
                            .collect::<Vec<_>>(),
                    ))
                    .or_not(),
                )
                .then(exact(Token::RParen))
                .map(|(((lparen, l), r), rparen)| match r {
                    Some(mut r) => {
                        r.insert(0, l);
                        PreType::Tuple(r, lparen.start..rparen.end)
                    }
                    None => l,
                }),
        ))
        .labelled("type");

        let app = atom.clone().foldl(atom.repeated(), |left, right| {
            let span = left.span().start..right.span().end;
            PreType::App(Box::new(left), Box::new(right), span)
        });

        app.pratt((
            prefix(5, exact(Token::Tilde), |_, t: PreType, _| {
                let span = t.span();
                PreType::Flow(Box::new(t.clone()), Box::new(t), span)
            }),
            infix(
                none(5),
                exact(Token::Slash),
                |l: PreType, _, r: PreType, _| {
                    let span = l.span().start..r.span().end;
                    PreType::Flow(Box::new(l), Box::new(r), span)
                },
            ),
            infix(
                right(1),
                exact(Token::Function),
                |l: PreType, _, r: PreType, _| {
                    let span = l.span().start..r.span().end;
                    PreType::Arrow(Box::new(l), Box::new(r), span)
                },
            ),
        ))
    })
    .labelled("type")
}

fn pattern<'a, 'src: 'a>() -> impl P<'a, 'src, Pattern<'src>> {
    recursive(|pat| {
        let atom = choice((
            ident().map(|(ident, span)| Pattern::Var(ident, span)),
            integer().map(|(integer, span)| Pattern::Literal(Literal::Integer(integer), span)),
            char_literal().map(|(c, span)| Pattern::Literal(Literal::Char(c), span)),
            string_literal().map(|(string, span)| {
                string
                    .chars()
                    .rev()
                    .fold(Pattern::EmptyList(span.clone()), |acc, c| {
                        Pattern::Cons(
                            Box::new(Pattern::Literal(Literal::Char(c), span.clone())),
                            Box::new(acc),
                            span.clone(),
                        )
                    })
            }),
            exact(Token::False).map(|span| Pattern::Literal(Literal::Bool(false), span)),
            exact(Token::True).map(|span| Pattern::Literal(Literal::Bool(true), span)),
            exact(Token::LSquare)
                .ignore_then(
                    pat.clone()
                        .separated_by(exact(Token::Comma))
                        .allow_trailing()
                        .collect::<Vec<_>>(),
                )
                .then(exact(Token::RSquare))
                .map(|(elements, close): (Vec<Pattern<'src>>, _)| {
                    elements
                        .into_iter()
                        .rev()
                        .fold(Pattern::EmptyList(close), |p, element| {
                            let span = element.span().start..p.span().end;
                            Pattern::Cons(Box::new(element), Box::new(p), span)
                        })
                }),
            exact(Token::LParen)
                .then(exact(Token::RParen))
                .map(|(l, r)| Pattern::Tuple(Vec::new(), l.start..r.end)),
            exact(Token::LParen)
                .then(pat.clone())
                .then(
                    (exact(Token::Comma).ignore_then(
                        pat.clone()
                            .separated_by(exact(Token::Comma))
                            .collect::<Vec<_>>(),
                    ))
                    .or_not(),
                )
                .then(exact(Token::RParen))
                .map(|(((lparen, l), r), rparen)| match r {
                    Some(mut r) => {
                        r.insert(0, l);
                        Pattern::Tuple(r, lparen.start..rparen.end)
                    }
                    None => l,
                }),
        ));

        use chumsky::pratt::*;

        atom.pratt((
            infix(
                left(0),
                exact(Token::Cons),
                |l: Pattern, _, r: Pattern, _| {
                    let span = l.span().start..r.span().end;
                    Pattern::Cons(Box::new(l), Box::new(r), span)
                },
            ),
            prefix(1, exact(Token::Left), |_, x: Pattern, _| {
                let span = x.span();
                Pattern::Left(Box::new(x), span)
            }),
            prefix(1, exact(Token::Right), |_, x: Pattern, _| {
                let span = x.span();
                Pattern::Right(Box::new(x), span)
            }),
        ))
    })
    .labelled("pattern")
}

fn fpattern<'a, 'src: 'a>() -> impl P<'a, 'src, (Flow, Pattern<'src>)> {
    exact(Token::Tilde)
        .or_not()
        .then(pattern())
        .map(|(flow, pat)| {
            (
                if flow.is_some() {
                    Flow::Flow
                } else {
                    Flow::Plain
                },
                pat,
            )
        })
}

fn expr<'a, 'src: 'a>() -> impl P<'a, 'src, Expr<'src>> {
    recursive(|expr| {
        let atom = choice((
            ident().map(|(ident, span)| Expr::Var(ident, span)),
            integer().map(|(integer, span)| Expr::Literal(Literal::Integer(integer), span)),
            char_literal().map(|(c, span)| Expr::Literal(Literal::Char(c), span)),
            string_literal().map(|(string, span)| {
                string
                    .chars()
                    .rev()
                    .fold(Expr::EmptyList(span.clone()), |acc, c| {
                        Expr::Cons(
                            Box::new(Expr::Literal(Literal::Char(c), span.clone())),
                            Box::new(acc),
                            span.clone(),
                        )
                    })
            }),
            exact(Token::False).map(|span| Expr::Literal(Literal::Bool(false), span)),
            exact(Token::True).map(|span| Expr::Literal(Literal::Bool(true), span)),
            exact(Token::Left).map(|span| {
                Expr::Lambda(
                    vec![(Flow::Plain, Pattern::Var("l", span.clone()))],
                    Box::new(Expr::Left(
                        Box::new(Expr::Var("l", span.clone())),
                        span.clone(),
                    )),
                    span,
                )
            }),
            exact(Token::Right).map(|span| {
                Expr::Lambda(
                    vec![(Flow::Plain, Pattern::Var("r", span.clone()))],
                    Box::new(Expr::Right(
                        Box::new(Expr::Var("r", span.clone())),
                        span.clone(),
                    )),
                    span,
                )
            }),
            exact(Token::LSquare)
                .ignore_then(
                    expr.clone()
                        .separated_by(exact(Token::Comma))
                        .allow_trailing()
                        .collect::<Vec<_>>(),
                )
                .then(exact(Token::RSquare))
                .map(|(elements, close): (Vec<Expr<'src>>, _)| {
                    elements
                        .into_iter()
                        .rev()
                        .fold(Expr::EmptyList(close), |p, element| {
                            let span = element.span().start..p.span().end;
                            Expr::Cons(Box::new(element), Box::new(p), span)
                        })
                }),
            exact(Token::LParen)
                .then(exact(Token::RParen))
                .map(|(l, r)| Expr::Tuple(Vec::new(), l.start..r.end)),
            exact(Token::LParen)
                .then(expr.clone())
                .then(
                    (exact(Token::Comma).ignore_then(
                        expr.clone()
                            .separated_by(exact(Token::Comma))
                            .collect::<Vec<_>>(),
                    ))
                    .or_not(),
                )
                .then(exact(Token::RParen))
                .map(|(((lparen, l), r), rparen)| match r {
                    Some(mut r) => {
                        r.insert(0, l);
                        Expr::Tuple(r, lparen.start..rparen.end)
                    }
                    None => l,
                }),
        ))
        .labelled("expression");

        let lens = exact(Token::Tilde)
            .repeated()
            .collect::<Vec<_>>()
            .then(atom)
            .map(|(tildes, atom)| {
                tildes.into_iter().rev().fold(atom, |atom, tilde| {
                    let span = tilde.start..atom.span().end;
                    Expr::Tilde(Box::new(atom), span)
                })
            });

        let app = lens.clone().foldl(lens.clone().repeated(), |left, right| {
            let span = left.span().start..right.span().end;
            Expr::App(Box::new(left), Box::new(right), span)
        });

        use chumsky::pratt::*;

        choice((
            app.pratt((
                infix(right(5), exact(Token::Cons), |l: Expr, _, r: Expr, _| {
                    let span = l.span().start..r.span().end;
                    Expr::Cons(Box::new(l), Box::new(r), span)
                }),
                infix(left(4), exact(Token::Mul), |l: Expr, _, r: Expr, _| {
                    let span = l.span().start..r.span().end;
                    Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Mul, span)
                }),
                infix(left(4), exact(Token::Slash), |l: Expr, _, r: Expr, _| {
                    let span = l.span().start..r.span().end;
                    Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Div, span)
                }),
                infix(left(3), exact(Token::Add), |l: Expr, _, r: Expr, _| {
                    let span = l.span().start..r.span().end;
                    Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Add, span)
                }),
                infix(left(3), exact(Token::Sub), |l: Expr, _, r: Expr, _| {
                    let span = l.span().start..r.span().end;
                    Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Sub, span)
                }),
                infix(left(2), exact(Token::Eq), |l: Expr, _, r: Expr, _| {
                    let span = l.span().start..r.span().end;
                    Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Eq, span)
                }),
                infix(right(1), exact(Token::Assign), |l: Expr, _, r: Expr, _| {
                    let span = l.span().start..r.span().end;
                    Expr::Assign(Box::new(l), Box::new(r), span)
                }),
                infix(
                    right(0),
                    exact(Token::Semicolon(false)),
                    |l: Expr, _, r: Expr, _| {
                        let span = l.span().start..r.span().end;
                        Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Seq, span)
                    },
                ),
            )),
            braced(
                expr.clone()
                    .foldl(semicolon().ignore_then(expr.clone()).repeated(), |l, r| {
                        let span = l.span().start..r.span().end;
                        Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Seq, span)
                    }),
            ),
            exact(Token::Lambda)
                .then(fpattern().repeated().at_least(1).collect())
                .then_ignore(exact(Token::Function))
                .then(expr.clone())
                .map(|((lam, pats), body)| {
                    let span = lam.start..body.span().end;
                    Expr::Lambda(pats, Box::new(body), span)
                }),
            exact(Token::Let)
                .then(pattern())
                .then_ignore(exact(Token::Define))
                .then(exact(Token::Tilde).or_not())
                .then(expr.clone())
                .then_ignore(semicolon())
                .then(expr.clone().foldl(
                    semicolon().ignore_then(expr.clone()).repeated(),
                    |l, r| {
                        let span = l.span().start..r.span().end;
                        Expr::PrimOp(Box::new(l), Box::new(r), PrimOp::Seq, span)
                    },
                ))
                .map(|((((let_span, pattern), flow), value), body)| {
                    let span = let_span.start..body.span().end;
                    Expr::Let {
                        flow: if flow.is_some() {
                            Flow::Flow
                        } else {
                            Flow::Plain
                        },
                        pattern,
                        value: Box::new(value),
                        body: Box::new(body),
                        span,
                    }
                }),
            exact(Token::Case)
                .then(exact(Token::Tilde).or_not())
                .then(expr.clone())
                .then(exact(Token::Of))
                .then(braced(
                    pattern()
                        .then_ignore(exact(Token::Function))
                        .then(expr.clone())
                        .separated_by(semicolon())
                        .allow_trailing()
                        .collect::<Vec<_>>(),
                ))
                .map(|((((case_span, flow), scrutinee), of_span), branches)| {
                    let span = case_span.start
                        ..branches
                            .last()
                            .map(|(_, last)| last.span().end)
                            .unwrap_or(of_span.end);
                    Expr::Case {
                        flow: if flow.is_some() {
                            Flow::Flow
                        } else {
                            Flow::Plain
                        },
                        span,
                        scrutinee: Box::new(scrutinee),
                        branches,
                    }
                }),
        ))
    })
    .labelled("expression")
}

fn semicolon<'a, 'src: 'a>() -> impl P<'a, 'src, Span> {
    exact(Token::Semicolon(false)).or(exact(Token::Semicolon(true)))
}

fn braced<'a, 'src: 'a, T>(p: impl P<'a, 'src, T>) -> impl P<'a, 'src, T> {
    (exact(Token::LBrace(false))
        .ignore_then(p.clone())
        .then_ignore(exact(Token::RBrace(false))))
    .or(exact(Token::LBrace(true))
        .ignore_then(p)
        .then_ignore(exact(Token::RBrace(true))))
}

fn exact<'a, 'src: 'a>(tok: Token) -> impl P<'a, 'src, Span> {
    let name = tok.to_string();
    any()
        .filter_map(
            move |(found_tok, span)| {
                if found_tok == tok { Some(span) } else { None }
            },
        )
        .labelled(name)
}

fn ident<'a, 'src: 'a>() -> impl P<'a, 'src, (&'src str, Span)> {
    any()
        .filter_map(|(found_tok, span)| {
            if let Token::Ident(ident) = found_tok {
                Some((ident, span))
            } else {
                None
            }
        })
        .labelled("identifier")
}

fn integer<'a, 'src: 'a>() -> impl P<'a, 'src, (u64, Span)> {
    any()
        .filter_map(|(found_tok, span)| {
            if let Token::Integer(integer) = found_tok {
                Some((integer, span))
            } else {
                None
            }
        })
        .labelled("integer")
}

fn char_literal<'a, 'src: 'a>() -> impl P<'a, 'src, (char, Span)> {
    any()
        .filter_map(|(found_tok, span)| {
            if let Token::CharLiteral(c) = found_tok {
                Some((c, span))
            } else {
                None
            }
        })
        .labelled("character literal")
}

fn string_literal<'a, 'src: 'a>() -> impl P<'a, 'src, (String, Span)> {
    any()
        .filter_map(|(found_tok, span)| {
            if let Token::StringLiteral(string) = found_tok {
                Some((string, span))
            } else {
                None
            }
        })
        .labelled("string literal")
}
