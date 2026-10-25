//! Implements a grammar-insensitive approximation to the Haskell layout algorithm:
//! <https://www.haskell.org/onlinereport/haskell2010/haskellch10.html#x17-17800010.3>

use std::fmt::Display;

use logos::Span;

use crate::{
    error::{Diagnostic, EResult, Errors},
    lex::WToken,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    /// The boolean parameter is true if this is a virtual brace.
    LBrace(bool),
    /// The boolean parameter is true if this is a virtual brace.
    RBrace(bool),
    LSquare,
    RSquare,
    LParen,
    RParen,
    LAddPair,
    RAddPair,

    /// The boolean parameter is true if this is a virtual semicolon.
    Semicolon(bool),
    Bang,
    Function,
    Slash,
    Tilde,
    Comma,

    Add,
    Sub,
    Mul,

    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    Ne,

    And,
    Or,

    Assign,
    Define,
    Lambda,
    Type,
    Cons,

    Let,
    In,
    Case,
    Of,

    Int,
    Bool,
    Char,
    String,
    Either,
    List,
    Tree,
    Handle,
    World,
    False,
    True,
    Left,
    Right,

    CharLiteral(char),
    StringLiteral(String),
    Ident(&'a str),
    Integer(u64),
}

impl<'a> Token<'a> {
    fn from_wtoken(tok: WToken, span: Span, file: &'a str, es: &mut Errors) -> Self {
        match tok {
            WToken::NewLine => unreachable!(),
            WToken::Whitespace => unreachable!(),
            WToken::LineComment => unreachable!(),
            WToken::LBrace => Token::LBrace(false),
            WToken::RBrace => Token::RBrace(false),
            WToken::LSquare => Token::LSquare,
            WToken::RSquare => Token::RSquare,
            WToken::LParen => Token::LParen,
            WToken::RParen => Token::RParen,
            WToken::LAddPair => Token::LAddPair,
            WToken::RAddPair => Token::RAddPair,
            WToken::Semicolon => Token::Semicolon(false),
            WToken::Bang => Token::Bang,
            WToken::Function => Token::Function,
            WToken::Slash => Token::Slash,
            WToken::Tilde => Token::Tilde,
            WToken::Comma => Token::Comma,
            WToken::Add => Token::Add,
            WToken::Sub => Token::Sub,
            WToken::Mul => Token::Mul,
            WToken::Le => Token::Le,
            WToken::Lt => Token::Lt,
            WToken::Ge => Token::Ge,
            WToken::Gt => Token::Gt,
            WToken::Eq => Token::Eq,
            WToken::Ne => Token::Ne,
            WToken::And => Token::And,
            WToken::Or => Token::Or,
            WToken::Assign => Token::Assign,
            WToken::Define => Token::Define,
            WToken::Lambda => Token::Lambda,
            WToken::Type => Token::Type,
            WToken::Cons => Token::Cons,
            WToken::Let => Token::Let,
            WToken::In => Token::In,
            WToken::Case => Token::Case,
            WToken::Of => Token::Of,
            WToken::Int => Token::Int,
            WToken::Bool => Token::Bool,
            WToken::Char => Token::Char,
            WToken::String => Token::String,
            WToken::Either => Token::Either,
            WToken::List => Token::List,
            WToken::Tree => Token::Tree,
            WToken::Handle => Token::Handle,
            WToken::World => Token::World,
            WToken::False => Token::False,
            WToken::True => Token::True,
            WToken::Left => Token::Left,
            WToken::Right => Token::Right,
            WToken::CharLiteral(n) => {
                Token::CharLiteral(match unescaper::unescape(&n[1..n.len() - 1]) {
                    Ok(s) => {
                        let mut it = s.chars();
                        match (it.next(), it.next()) {
                            (Some(c), None) => c,
                            _ => {
                                es.push(Diagnostic::error(
                                    span,
                                    format!("char literal was not exactly one character: {s:?}"),
                                ));
                                '\0'
                            }
                        }
                    }
                    Err(e) => {
                        es.push(Diagnostic::error(
                            span,
                            format!("invalid escape sequence: {e}"),
                        ));
                        '\0'
                    }
                })
            }
            WToken::StringLiteral(n) => {
                Token::StringLiteral(match unescaper::unescape(&n[1..n.len() - 1]) {
                    Ok(s) => s,
                    Err(e) => {
                        es.push(Diagnostic::error(
                            span,
                            format!("invalid escape sequence: {e}"),
                        ));
                        String::new()
                    }
                })
            }
            WToken::Ident => Token::Ident(&file[span]),
            WToken::Integer(n) => Token::Integer(n),
        }
    }
}

impl<'a> Display for Token<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::LBrace(false) => write!(f, "'{{'"),
            Token::LBrace(true) => write!(f, "start of block"),
            Token::RBrace(false) => write!(f, "'}}'"),
            Token::RBrace(true) => write!(f, "end of block"),
            Token::LSquare => write!(f, "'['"),
            Token::RSquare => write!(f, "']'"),
            Token::LParen => write!(f, "'('"),
            Token::RParen => write!(f, "')'"),
            Token::LAddPair => write!(f, "'<<'"),
            Token::RAddPair => write!(f, "'>>'"),
            Token::Semicolon(false) => write!(f, "';'"),
            Token::Semicolon(true) => write!(f, "end of line"),
            Token::Bang => write!(f, "'!'"),
            Token::Function => write!(f, "'->'"),
            Token::Slash => write!(f, "'/'"),
            Token::Tilde => write!(f, "'~'"),
            Token::Comma => write!(f, "','"),
            Token::Add => write!(f, "'+'"),
            Token::Sub => write!(f, "'-'"),
            Token::Mul => write!(f, "'*'"),
            Token::Le => write!(f, "'<='"),
            Token::Lt => write!(f, "'<'"),
            Token::Ge => write!(f, "'>='"),
            Token::Gt => write!(f, "'>'"),
            Token::Eq => write!(f, "'=='"),
            Token::Ne => write!(f, "'!='"),
            Token::And => write!(f, "&&''"),
            Token::Or => write!(f, "'||'"),
            Token::Assign => write!(f, "':='"),
            Token::Define => write!(f, "'='"),
            Token::Lambda => write!(f, "'\'"),
            Token::Type => write!(f, "'::'"),
            Token::Cons => write!(f, "':'"),
            Token::Let => write!(f, "let"),
            Token::In => write!(f, "in"),
            Token::Case => write!(f, "case"),
            Token::Of => write!(f, "of"),
            Token::Int => write!(f, "Int"),
            Token::Bool => write!(f, "Bool"),
            Token::Char => write!(f, "Char"),
            Token::String => write!(f, "String"),
            Token::Either => write!(f, "Either"),
            Token::List => write!(f, "List"),
            Token::Tree => write!(f, "Tree"),
            Token::Handle => write!(f, "Handle"),
            Token::World => write!(f, "World"),
            Token::False => write!(f, "False"),
            Token::True => write!(f, "True"),
            Token::Left => write!(f, "Left"),
            Token::Right => write!(f, "Right"),
            Token::CharLiteral(c) => write!(f, "{c:?}"),
            Token::StringLiteral(s) => write!(f, "{s:?}"),
            Token::Ident(ident) => write!(f, "'{ident}'"),
            Token::Integer(n) => write!(f, "'{n}'"),
        }
    }
}

pub fn layout<'a>(
    es: &mut Errors,
    tokens: impl Iterator<Item = EResult<(WToken, Span)>>,
    file: &'a str,
) -> Vec<(Token<'a>, Span)> {
    // A list of indentation levels that we've seen so far.
    // The first column is indentation level 1, and explicit braces are considered level 0.
    let mut stack = vec![1];

    // The output tokens with braces and semicolons.
    let mut output = Vec::new();

    let mut first_on_line = true;
    let mut column = 1;
    const TAB_STOP_SIZE: usize = 8;
    for token in tokens {
        if let Some((token, span)) = es.get(token) {
            match token {
                WToken::NewLine => {
                    column = 1;
                    first_on_line = true;
                }
                WToken::Whitespace => {
                    for c in file[span].chars() {
                        match c {
                            ' ' => {
                                column += 1;
                            }
                            '\t' => {
                                column += TAB_STOP_SIZE
                                    - ((column + (TAB_STOP_SIZE - 1)) % TAB_STOP_SIZE);
                            }
                            _ => {}
                        }
                    }
                }
                WToken::LineComment => {}
                _ => {
                    if first_on_line {
                        // We've indented to this column; compare to the stack.
                        first_on_line = false;

                        match column.cmp(stack.last().unwrap()) {
                            std::cmp::Ordering::Less => {
                                while column < *stack.last().unwrap() {
                                    output.push((Token::RBrace(true), span.start..span.start));
                                    output.push((Token::Semicolon(true), span.start..span.start));
                                    stack.pop();
                                }
                            }
                            std::cmp::Ordering::Equal => {
                                output.push((Token::Semicolon(true), span.start..span.start));
                            }
                            std::cmp::Ordering::Greater => {
                                output.push((Token::LBrace(true), span.start..span.start));
                                stack.push(column);
                            }
                        }
                    }
                    output.push((Token::from_wtoken(token, span.clone(), file, es), span))
                }
            }
        }
    }

    while 1 < *stack.last().unwrap() {
        output.push((Token::RBrace(true), file.len()..file.len()));
        output.push((Token::Semicolon(true), file.len()..file.len()));
        stack.pop();
    }

    // for (tok, span) in &output {
    //     match tok {
    //         Token::LBrace(true) => print!("{{ "),
    //         Token::RBrace(true) => print!("}} "),
    //         Token::Semicolon(true) => print!("; "),
    //         _ => {
    //             print!("{} ", &file[span.clone()])
    //         }
    //     }
    // }
    // println!();

    output
}
