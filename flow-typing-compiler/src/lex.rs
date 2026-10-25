use logos::{Logos, Span};

use crate::error::{Diagnostic, EResult};

/// Tokens, including whitespace.
#[derive(Logos, Debug, PartialEq)]
#[logos(error(LexError, LexError::from_lexer))]
pub enum WToken {
    #[regex("(\r|\n|\r\n)")]
    NewLine,
    #[regex("[ \t]+")]
    Whitespace,
    #[regex("--", skip_comment)]
    LineComment,

    #[token("{")]
    LBrace,
    #[token("}")]
    RBrace,
    #[token("[")]
    LSquare,
    #[token("]")]
    RSquare,
    #[token("(")]
    LParen,
    #[token(")")]
    RParen,
    #[token("<<")]
    LAddPair,
    #[token(">>")]
    RAddPair,

    #[token(";")]
    Semicolon,
    #[token("!")]
    Bang,
    #[token("->")]
    Function,
    #[token("/")]
    Slash,
    #[token("~")]
    Tilde,
    #[token(",")]
    Comma,

    #[token("+")]
    Add,
    #[token("-")]
    Sub,
    #[token("*")]
    Mul,

    #[token("<=")]
    Le,
    #[token("<")]
    Lt,
    #[token(">=")]
    Ge,
    #[token(">")]
    Gt,
    #[token("==")]
    Eq,
    #[token("/=")]
    Ne,

    #[token("&&")]
    And,
    #[token("||")]
    Or,

    #[token(":=")]
    Assign,
    #[token("=")]
    Define,
    #[token("\\")]
    Lambda,
    #[token("::")]
    Type,
    #[token(":")]
    Cons,

    #[token("let")]
    Let,
    #[token("in")]
    In,
    #[token("case")]
    Case,
    #[token("of")]
    Of,

    #[token("Int")]
    Int,
    #[token("Bool")]
    Bool,
    #[token("Char")]
    Char,
    #[token("String")]
    String,
    #[token("Either")]
    Either,
    #[token("List")]
    List,
    #[token("Tree")]
    Tree,
    #[token("Handle")]
    Handle,
    #[token("World")]
    World,
    #[token("False")]
    False,
    #[token("True")]
    True,
    #[token("Left")]
    Left,
    #[token("Right")]
    Right,

    #[regex(r#"'([^'\\\x00-\x1F]|\\(['\\bnfrt/]|u[a-fA-F0-9]{4}))*'"#, |lex| lex.slice().to_owned())]
    CharLiteral(String),
    #[regex(r#""([^"\\\x00-\x1F]|\\(["\\bnfrt/]|u[a-fA-F0-9]{4}))*""#, |lex| lex.slice().to_owned())]
    StringLiteral(String),
    #[regex("[_a-zA-Z][_a-zA-Z0-9']*")]
    Ident,
    #[regex("[0-9]+", |lex| from_result_at(lex.span(), lex.slice().parse()))]
    Integer(u64),
}

fn skip_comment<'src>(lex: &mut logos::Lexer<'src, WToken>) {
    lex.bump(
        lex.remainder()
            .find(|c: char| ['\r', '\n'].contains(&c))
            .unwrap_or(lex.remainder().len()),
    );
}

#[derive(Default, Debug, Clone, PartialEq)]
pub struct LexError {
    span: Span,
    error: String,
}

impl LexError {
    fn from_lexer(lex: &mut logos::Lexer<'_, WToken>) -> Self {
        LexError {
            span: lex.span(),
            error: format!(
                "unexpected character {:?}",
                lex.slice().chars().next().unwrap()
            ),
        }
    }
}

fn from_result_at<T, U: std::error::Error>(
    span: Span,
    result: Result<T, U>,
) -> Result<T, LexError> {
    result.map_err(|e| LexError {
        span,
        error: e.to_string(),
    })
}

pub fn lex(input: &str) -> impl Iterator<Item = EResult<(WToken, Span)>> {
    WToken::lexer(input).spanned().map(|x| {
        x.0.map(|val| (val, x.1))
            .map_err(|err| Diagnostic::error(err.span, err.error))
            .into()
    })
}
