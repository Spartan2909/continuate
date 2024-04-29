use std::fmt;
use std::hash;
use std::result;
use std::str::Chars;

use continuate_error::Error;
use continuate_error::Result;
use continuate_error::SourceId;
use continuate_error::Span;

#[derive(Debug, Clone)]
pub struct Ident {
    pub string: String,
    pub span: Span,
}

impl Ident {
    pub const fn new(string: String) -> Ident {
        Ident {
            string,
            span: Span::dummy(),
        }
    }

    pub const fn new_spanned(string: String, span: Span) -> Ident {
        Ident { string, span }
    }
}

impl PartialEq for Ident {
    fn eq(&self, other: &Self) -> bool {
        self.string == other.string
    }
}

impl Eq for Ident {}

impl hash::Hash for Ident {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.string.hash(state);
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.string)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeywordKind {
    Fn,
    If,
    Let,
    Match,
    Package,
    Super,
    Type,
}

impl TryFrom<&str> for KeywordKind {
    type Error = ();

    fn try_from(value: &str) -> result::Result<Self, Self::Error> {
        let kind = match value {
            "fn" => KeywordKind::Fn,
            "if" => KeywordKind::If,
            "let" => KeywordKind::Let,
            "match" => KeywordKind::Match,
            "package" => KeywordKind::Super,
            "type" => KeywordKind::Type,
            _ => return Err(()),
        };
        Ok(kind)
    }
}

impl fmt::Display for KeywordKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let string = match self {
            KeywordKind::Fn => "fn",
            KeywordKind::If => "if",
            KeywordKind::Let => "let",
            KeywordKind::Match => "match",
            KeywordKind::Package => "package",
            KeywordKind::Super => "super",
            KeywordKind::Type => "type",
        };

        f.write_str(string)
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Keyword {
    pub kind: KeywordKind,
    pub span: Span,
}

impl Keyword {
    pub const fn new(kind: KeywordKind) -> Keyword {
        Keyword {
            kind,
            span: Span::dummy(),
        }
    }

    pub const fn new_spanned(kind: KeywordKind, span: Span) -> Keyword {
        Keyword { kind, span }
    }
}

impl PartialEq for Keyword {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for Keyword {}

impl fmt::Display for Keyword {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.kind, f)
    }
}

#[derive(Debug, Clone)]
pub enum Literal {
    Int(i64, Span),
    Float(f64, Span),
    String(String, Span),
}

impl PartialEq for Literal {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Literal::Int(i1, _), Literal::Int(i2, _)) => i1 == i2,
            (Literal::Float(f1, _), Literal::Float(f2, _)) => f1 == f2,
            (Literal::String(s1, _), Literal::String(s2, _)) => s1 == s2,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PunctKind {
    Dot,
    Comma,
}

impl TryFrom<char> for PunctKind {
    type Error = ();

    fn try_from(value: char) -> result::Result<Self, Self::Error> {
        let kind = match value {
            '.' => PunctKind::Dot,
            ',' => PunctKind::Comma,
            _ => return Err(()),
        };
        Ok(kind)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Spacing {
    Alone,
    Joint,
}

#[derive(Debug, Clone, Copy)]
pub struct Punct {
    pub kind: PunctKind,
    pub spacing: Spacing,
    pub span: Span,
}

impl Punct {
    pub const fn new(kind: PunctKind, spacing: Spacing) -> Punct {
        Punct {
            kind,
            spacing,
            span: Span::dummy(),
        }
    }

    pub const fn new_spanned(kind: PunctKind, spacing: Spacing, span: Span) -> Punct {
        Punct {
            kind,
            spacing,
            span,
        }
    }
}

impl PartialEq for Punct {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for Punct {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DelimiterKind {
    Paren,
    Bracket,
    Brace,
}

impl DelimiterKind {
    pub const fn start(self) -> char {
        match self {
            DelimiterKind::Paren => '(',
            DelimiterKind::Bracket => '[',
            DelimiterKind::Brace => '{',
        }
    }

    pub const fn end(self) -> char {
        match self {
            DelimiterKind::Paren => ')',
            DelimiterKind::Bracket => ']',
            DelimiterKind::Brace => '}',
        }
    }

    const fn start_from_char(ch: char) -> Option<DelimiterKind> {
        match ch {
            '(' => Some(DelimiterKind::Paren),
            '[' => Some(DelimiterKind::Bracket),
            '{' => Some(DelimiterKind::Brace),
            _ => None,
        }
    }

    const fn end_from_char(ch: char) -> Option<DelimiterKind> {
        match ch {
            ')' => Some(DelimiterKind::Paren),
            ']' => Some(DelimiterKind::Bracket),
            '}' => Some(DelimiterKind::Brace),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DelimiterSide {
    Open,
    Close,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Delimiter {
    kind: DelimiterKind,
    side: DelimiterSide,
    span: Span,
}

#[derive(Debug, Clone, PartialEq)]
struct Group {
    open_delimiter: Delimiter,
    close_delimiter: Delimiter,
    tokens: Vec<TokenTree>,
}

#[derive(Debug, Clone, PartialEq)]
enum TokenTree {
    Ident(Ident),
    Keyword(Keyword),
    Literal(Literal),
    Punct(Punct),
    Group(Group),
    Error(Span),
}

impl From<Ident> for TokenTree {
    fn from(value: Ident) -> Self {
        TokenTree::Ident(value)
    }
}

impl From<Keyword> for TokenTree {
    fn from(value: Keyword) -> Self {
        TokenTree::Keyword(value)
    }
}

impl From<Literal> for TokenTree {
    fn from(value: Literal) -> Self {
        TokenTree::Literal(value)
    }
}

impl From<Punct> for TokenTree {
    fn from(value: Punct) -> Self {
        TokenTree::Punct(value)
    }
}

impl From<Group> for TokenTree {
    fn from(value: Group) -> Self {
        TokenTree::Group(value)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Ident(Ident),
    Keyword(Keyword),
    Literal(Literal),
    Punct(Punct),
    Delimiter(Delimiter),
    Error(Span),
}

impl Token {
    fn from_trees(trees: Vec<TokenTree>, tokens: Option<Vec<Token>>) -> Vec<Token> {
        let mut tokens = tokens.unwrap_or_else(|| Vec::with_capacity(trees.len() * 10));
        for tree in trees {
            match tree {
                TokenTree::Ident(ident) => tokens.push(ident.into()),
                TokenTree::Keyword(kw) => tokens.push(kw.into()),
                TokenTree::Literal(lit) => tokens.push(lit.into()),
                TokenTree::Punct(punct) => tokens.push(punct.into()),
                TokenTree::Group(group) => {
                    tokens.push(group.open_delimiter.into());
                    tokens = Token::from_trees(group.tokens, Some(tokens));
                    tokens.push(group.close_delimiter.into());
                }
                TokenTree::Error(span) => tokens.push(Token::Error(span)),
            }
        }
        tokens
    }
}

impl From<Ident> for Token {
    fn from(value: Ident) -> Self {
        Token::Ident(value)
    }
}

impl From<Keyword> for Token {
    fn from(value: Keyword) -> Self {
        Token::Keyword(value)
    }
}

impl From<Literal> for Token {
    fn from(value: Literal) -> Self {
        Token::Literal(value)
    }
}

impl From<Punct> for Token {
    fn from(value: Punct) -> Self {
        Token::Punct(value)
    }
}

impl From<Delimiter> for Token {
    fn from(value: Delimiter) -> Self {
        Token::Delimiter(value)
    }
}

fn is_ident_start(ch: char) -> bool {
    ch.is_alphabetic() || ch == '_'
}

fn as_ident_body(ch: char) -> Option<char> {
    if ch.is_alphanumeric() || ch == '_' {
        Some(ch)
    } else {
        None
    }
}

struct Lexer<'a> {
    source: &'a str,
    chars: Chars<'a>,
    position: usize,
    source_id: SourceId,
    errors: Vec<Error>,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str, source_id: SourceId) -> Lexer<'a> {
        Lexer {
            source,
            chars: source.chars(),
            position: 0,
            source_id,
            errors: Vec::new(),
        }
    }

    fn eof(&self) -> Span {
        Span::new(self.source.len(), self.source.len(), self.source_id)
    }

    fn next_char_span(&mut self) -> Span {
        let current = self.position;
        self.position += 1;
        Span::new(current, current + 1, self.source_id)
    }

    #[allow(clippy::needless_pass_by_value)] // Makes the API nicer
    fn next<T: ToString>(&mut self, expected: T) -> Result<(char, Span)> {
        self.chars
            .next()
            .ok_or_else(|| {
                Error::unexpected_token(Some(Some(expected.to_string())), None, self.eof())
            })
            .map(|ch| (ch, self.next_char_span()))
    }

    fn peek(&self, offset: usize) -> Option<char> {
        self.source.chars().nth(self.position + offset)
    }

    fn group(&mut self, tokens: &mut Vec<TokenTree>) -> Option<Delimiter> {
        while let Ok((ch, span)) = self.next("") {
            let token = if is_ident_start(ch) {
                let mut ident = ch.to_string();
                let mut end_span = span;
                while let Some((ch, ch_span)) = self
                    .next("")
                    .ok()
                    .and_then(|(ch, span)| Some((as_ident_body(ch)?, span)))
                {
                    ident.push(ch);
                    end_span = ch_span;
                }

                let span = span.union(end_span).unwrap();

                if let Ok(kind) = KeywordKind::try_from(ident.as_str()) {
                    Keyword { kind, span }.into()
                } else {
                    Ident {
                        string: ident,
                        span,
                    }
                    .into()
                }
            } else if let Ok(kind) = PunctKind::try_from(ch) {
                let spacing = if self
                    .peek(0)
                    .is_some_and(|ch| PunctKind::try_from(ch).is_ok())
                {
                    Spacing::Joint
                } else {
                    Spacing::Alone
                };

                Punct {
                    kind,
                    spacing,
                    span,
                }
                .into()
            } else if let Some(kind) = DelimiterKind::start_from_char(ch) {
                let open_delimiter = Delimiter {
                    kind,
                    side: DelimiterSide::Open,
                    span,
                };
                let mut group_tokens = Vec::new();
                let close_delimiter = self.group(&mut group_tokens);
                if let Some(close_delimiter) = close_delimiter {
                    if close_delimiter.kind == open_delimiter.kind {
                        Group {
                            open_delimiter,
                            close_delimiter,
                            tokens: group_tokens,
                        }
                        .into()
                    } else {
                        self.errors.push(Error::unclosed_delimiter(
                            open_delimiter.kind.start().to_string(),
                            open_delimiter.span,
                            open_delimiter.kind.end().to_string(),
                            close_delimiter.span,
                        ));
                        TokenTree::Error(close_delimiter.span)
                    }
                } else {
                    self.errors.push(Error::unclosed_delimiter(
                        open_delimiter.kind.start().to_string(),
                        open_delimiter.span,
                        open_delimiter.kind.end().to_string(),
                        self.eof(),
                    ));
                    TokenTree::Error(self.eof())
                }
            } else if let Some(kind) = DelimiterKind::end_from_char(ch) {
                return Some(Delimiter {
                    kind,
                    side: DelimiterSide::Close,
                    span,
                });
            } else {
                TokenTree::Error(span)
            };

            tokens.push(token);
        }

        None
    }

    fn lex(mut self) -> (Vec<TokenTree>, Vec<Error>) {
        let mut tokens = vec![];

        while let Some(delimiter) = self.group(&mut tokens) {
            self.errors.push(Error::unopened_delimiter(
                delimiter.kind.end().to_string(),
                delimiter.span,
            ));
            tokens.push(TokenTree::Error(delimiter.span));
        }

        (tokens, self.errors)
    }
}

pub fn lex(source: &str, source_id: SourceId) -> (Vec<Token>, Vec<Error>) {
    let (trees, errors) = Lexer::new(source, source_id).lex();
    (Token::from_trees(trees, None), errors)
}
