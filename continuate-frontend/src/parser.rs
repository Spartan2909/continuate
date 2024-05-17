use crate::lexer::Spacing;
use crate::lexer::Token;
use crate::Expr;
use crate::Ident;
use crate::Literal;
use crate::Path;
use crate::PathIdentSegment;
use crate::PathSegment;

use chumsky::input::ValueInput;
use chumsky::prelude::*;

use continuate_error::Error;
use continuate_error::Span;

type ParserExtra = chumsky::extra::Full<Error, (), ()>;

macro_rules! filter_matches {
    ($pat:pat) => {
        any().filter(|token| matches!(token, $pat))
    };
}

fn ident<'tokens, 'src, I>() -> impl Parser<'tokens, I, Ident, ParserExtra> + Clone
where
    'src: 'tokens,
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    select! {
        Token::Ident(string) = e => Ident::new(string, e.span())
    }
    .labelled("identifier")
}

fn path<'tokens, 'src, I>() -> impl Parser<'tokens, I, Path, ParserExtra> + Clone
where
    'src: 'tokens,
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    let ident_segment = ident()
        .map(PathIdentSegment::Ident)
        .or(select! { Token::Super = e => PathIdentSegment::Super(e.span()) })
        .or(select! { Token::Package = e => PathIdentSegment::Package(e.span()) });

    let segment = ident_segment.map_with(|ident, e| PathSegment {
        ident,
        span: e.span(),
    });

    let separator = just(Token::Colon(Spacing::Joint)).then(filter_matches!(Token::Colon(_)));

    segment
        .separated_by(separator)
        .collect::<Vec<_>>()
        .map_with(|segments, e| Path {
            segments,
            span: e.span(),
        })
}

fn expr<'tokens, 'src, I>() -> impl Parser<'tokens, I, Expr, ParserExtra>
where
    'src: 'tokens,
    I: ValueInput<'tokens, Token = Token, Span = Span>,
{
    recursive(|expr| {
        let literal = select! {
            Token::Int(val) = e => Literal::Int(val, e.span()),
            Token::Float(val) = e => Literal::Float(val, e.span()),
            Token::String(val) = e => Literal::String(val, e.span()),
        }
        .labelled("literal");

        let items = expr
            .clone()
            .separated_by(filter_matches!(Token::Comma(_)))
            .allow_trailing()
            .collect::<Vec<_>>();

        let let_expr = just(Token::Let)
            .ignore_then(ident())
            .then_ignore(filter_matches!(Token::Colon(_)))
            .then(path())
            .then(expr)
            .then_ignore(filter_matches!(Token::Semicolon(_)))
            .map_with(|((name, ty), val), e| Expr::Declare {
                name,
                ty,
                value: Box::new(val),
                span: e.span(),
            });

        let array = items
            .clone()
            .delimited_by(just(Token::OpenBracket), just(Token::CloseBracket))
            .map_with(|exprs, e| Expr::Array {
                exprs,
                span: e.span(),
            });

        let tuple = items
            .delimited_by(just(Token::OpenParen), just(Token::CloseParen))
            .map_with(|exprs, e| Expr::Tuple {
                exprs,
                span: e.span(),
            });

        let atom = literal
            .map(Expr::Literal)
            .or(ident().map(Expr::Ident))
            .or(let_expr)
            .or(array)
            .or(tuple);

        atom
    })
}
