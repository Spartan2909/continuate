use std::fmt;

use continuate_error::Error;
use continuate_error::SourceId;
use continuate_error::Span;

use logos::Lexer;
use logos::Logos;

fn string(lex: &Lexer<Token>) -> String {
    let slice = lex.slice();
    slice[1..slice.len() - 1].to_string()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Spacing {
    Alone,
    Joint,
}

fn spacing(lex: &Lexer<Token>) -> Spacing {
    const PUNCTUATION: [char; 7] = ['.', ',', ':', '=', '<', '>', ';'];

    if let Some(ch) = lex.remainder().chars().next() {
        if PUNCTUATION.contains(&ch) {
            Spacing::Joint
        } else {
            Spacing::Alone
        }
    } else {
        Spacing::Alone
    }
}

#[derive(Debug, Clone, PartialEq, Logos)]
#[logos(error = Error)]
#[logos(skip r"\s+")]
pub enum Token {
    #[regex(r"//[^\n]+", logos::skip)]
    Comment,

    #[token("fn")]
    Fn,
    #[token("if")]
    If,
    #[token("let")]
    Let,
    #[token("match")]
    Match,
    #[token("package")]
    Package,
    #[token("super")]
    Super,
    #[token("type")]
    Type,

    #[regex(r"[a-zA-Z_]\w*", |lex| lex.slice().to_string())]
    Ident(String),

    #[regex(r"\d+", |lex| lex.slice().parse::<i64>().unwrap())]
    Int(i64),
    #[regex(r"(\d+)?\.\d+", |lex| lex.slice().parse::<f64>().unwrap())]
    Float(f64),
    #[regex(r#""[^"]*""#, string)]
    String(String),

    #[token(".", spacing)]
    Dot(Spacing),
    #[token(",", spacing)]
    Comma(Spacing),
    #[token(":", spacing)]
    Colon(Spacing),
    #[token("=", spacing)]
    Eq(Spacing),
    #[token("<", spacing)]
    Lt(Spacing),
    #[token(">", spacing)]
    Gt(Spacing),
    #[token(";", spacing)]
    Semicolon(Spacing),

    #[token("(")]
    OpenParen,
    #[token("[")]
    OpenBracket,
    #[token("{")]
    OpenBrace,

    #[token(")")]
    CloseParen,
    #[token("]")]
    CloseBracket,
    #[token("}")]
    CloseBrace,

    Error,
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Token::Comment => f.write_str("<comment>"),

            Token::Fn => f.write_str("fn"),
            Token::If => f.write_str("if"),
            Token::Let => f.write_str("let"),
            Token::Match => f.write_str("match"),
            Token::Package => f.write_str("package"),
            Token::Super => f.write_str("super"),
            Token::Type => f.write_str("type"),

            Token::Ident(ref ident) => f.write_str(ident),

            Token::Int(int) => write!(f, "{int}"),
            Token::Float(float) => write!(f, "{float}"),
            Token::String(ref string) => write!(f, r#""{string}""#),

            Token::Dot(_) => f.write_str("."),
            Token::Comma(_) => f.write_str(","),
            Token::Colon(_) => f.write_str(":"),
            Token::Eq(_) => f.write_str("="),
            Token::Lt(_) => f.write_str("<"),
            Token::Gt(_) => f.write_str(">"),
            Token::Semicolon(_) => f.write_str(";"),

            Token::OpenParen => f.write_str("("),
            Token::OpenBracket => f.write_str("["),
            Token::OpenBrace => f.write_str("{"),
            Token::CloseParen => f.write_str(")"),
            Token::CloseBracket => f.write_str("]"),
            Token::CloseBrace => f.write_str("}"),
            Token::Error => f.write_str("<error>"),
        }
    }
}

pub fn lex(source: &str, source_id: SourceId) -> (Vec<(Token, Span)>, Vec<Error>) {
    let mut errors = Vec::new();
    let tokens = Token::lexer(source)
        .spanned()
        .map(|(token, span)| {
            let span = Span::new(span.start, span.end, source_id);
            match token {
                Ok(token) => (token, span),
                Err(err) => {
                    errors.push(err);
                    (Token::Error, span)
                }
            }
        })
        .collect();
    (tokens, errors)
}
