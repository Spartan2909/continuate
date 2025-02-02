use crate::lexer::Spacing;
use crate::lexer::Token;
use crate::BinaryOp;
use crate::Expr;
use crate::Ident;
use crate::Literal;
use crate::Path;
use crate::PathIdentSegment;
use crate::PathSegment;
use crate::Pattern;
use crate::UnaryOp;

use chumsky::prelude::*;

use continuate_error::Error;
use continuate_error::Span;

type ParserExtra = chumsky::extra::Full<Error, (), ()>;

type ParserInput<'tokens, 'src> = chumsky::input::MappedInput<
    Token<'src>,
    Span,
    &'tokens [(Token<'src>, Span)],
    for<'a> fn(&'a (Token<'src>, Span)) -> (&'a Token<'src>, &'a Span),
>;

/// Parse a token that matches the given pattern.
macro_rules! filter_matches {
    ($pat:pat) => {
        any().filter(|token| matches!(token, $pat))
    };
}

/// Parse a token that matches the given pattern, then map its span to the given function.
macro_rules! operator {
    ($token:path, $op:expr) => {
        filter_matches!($token(_)).to_span().map($op)
    };
}

macro_rules! wide_operator {
    ($first:path, $second:path, $op:expr) => {
        just($first(Spacing::Joint))
            .then(filter_matches!($second(_)))
            .to_span()
            .map($op)
    };
}

fn ident<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Ident<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    select! {
        Token::Ident(string) = e => Ident::new(string, e.span())
    }
    .labelled("identifier")
}

fn path<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Path<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
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

fn named_constructor_elements<'tokens, 'src, Elem>(
    element: impl Parser<'tokens, ParserInput<'tokens, 'src>, Elem, ParserExtra> + Clone,
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Vec<(Ident<'src>, Option<Elem>)>, ParserExtra>
       + Clone
where
    'src: 'tokens,
    Elem: 'tokens,
{
    ident()
        .then(
            filter_matches!(Token::Colon(_))
                .ignore_then(element)
                .or_not(),
        )
        .separated_by(filter_matches!(Token::Comma(_)))
        .allow_trailing()
        .collect()
}

fn pattern<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Pattern<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    recursive(|pattern| {
        let named_destructure = path()
            .then(
                named_constructor_elements(pattern.clone())
                    .delimited_by(just(Token::OpenBrace), just(Token::CloseBrace))
                    .map_with(|fields, e| (fields, e.span())),
            )
            .map(|(path, (fields, fields_span))| Pattern::NamedDestructure {
                ty: path,
                fields,
                brace_span: fields_span,
            });

        let anonymous_destructure = path()
            .or_not()
            .then(
                pattern
                    .separated_by(filter_matches!(Token::Comma(_)))
                    .allow_trailing()
                    .collect::<Vec<_>>()
                    .delimited_by(just(Token::OpenParen), just(Token::CloseParen))
                    .map_with(|fields, e| (fields, e.span())),
            )
            .map(
                |(path, (fields, fields_span))| Pattern::AnonymousDestructure {
                    ty: path,
                    fields,
                    paren_span: fields_span,
                },
            );

        operator!(Token::Underscore, Pattern::Wildcard)
            .or(ident().map(Pattern::Ident))
            .or(named_destructure)
            .or(anonymous_destructure)
    })
}

/// Comma-separated `Item`s with optional trailing comma.
fn items<'tokens, 'src, Item>(
    item: impl Parser<'tokens, ParserInput<'tokens, 'src>, Item, ParserExtra> + Clone,
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Vec<Item>, ParserExtra> + Clone
where
    'src: 'tokens,
    Item: 'tokens,
{
    item.separated_by(filter_matches!(Token::Comma(_)))
        .allow_trailing()
        .collect()
}

fn block<'tokens, 'src>() -> impl Parser<
    'tokens,
    ParserInput<'tokens, 'src>,
    (Vec<Expr<'src>>, Option<Expr<'src>>, Span),
    ParserExtra,
> + Clone
where
    'src: 'tokens,
{
    expr()
        .then_ignore(just(Token::Newline))
        .repeated()
        .collect()
        .then(expr().or_not())
        .delimited_by(just(Token::OpenBrace), just(Token::CloseBrace))
        .map_with(|(exprs, tail), e| (exprs, tail, e.span()))
}

fn atom<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Expr<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    let literal = select! {
        Token::Int(val) = e => Literal::Int(val, e.span()),
        Token::Float(val) = e => Literal::Float(val, e.span()),
        Token::String(val) = e => Literal::String(val, e.span()),
    }
    .labelled("literal");

    let let_expr = just(Token::Let)
        .ignore_then(ident())
        .then_ignore(filter_matches!(Token::Colon(_)))
        .then(path())
        .then(expr())
        .map_with(|((name, ty), val), e| Expr::Declare {
            name,
            ty,
            value: Box::new(val),
            span: e.span(),
        });

    let array = items(expr())
        .delimited_by(just(Token::OpenBracket), just(Token::CloseBracket))
        .map_with(|exprs, e| Expr::Array {
            exprs,
            span: e.span(),
        });

    let tuple = expr()
        .then_ignore(filter_matches!(Token::Comma(_)))
        .repeated()
        .collect::<Vec<_>>()
        .then(expr().or_not())
        .delimited_by(just(Token::OpenParen), just(Token::CloseParen))
        .map_with(|(mut exprs, trailing), e| {
            if let Some(trailing) = trailing {
                if exprs.is_empty() {
                    // Single item, no trailing comma, so not a tuple
                    return trailing;
                }
                exprs.push(trailing);
            }
            Expr::Tuple {
                exprs,
                span: e.span(),
            }
        });

    let constructor_or_ident = path()
        .then(
            named_constructor_elements(expr())
                .delimited_by(just(Token::OpenBrace), just(Token::CloseBrace))
                .map_with(|fields, e| (fields, e.span()))
                .or_not(),
        )
        .map(|(path, fields)| {
            if let Some((fields, span)) = fields {
                Expr::NamedConstructor {
                    path,
                    fields,
                    brace_span: span,
                }
            } else {
                Expr::Path(path)
            }
        });

    // FIXME: May fail on path expressions due to ambiguity with constructors.
    let match_expr = just(Token::Match)
        .ignore_then(expr())
        .then(
            pattern()
                .then_ignore(just(Token::Eq(Spacing::Joint)).then(filter_matches!(Token::Gt(_))))
                .then(expr())
                .separated_by(filter_matches!(Token::Comma(_)))
                .allow_trailing()
                .collect::<Vec<_>>()
                .delimited_by(just(Token::OpenBrace), just(Token::CloseBrace))
                .map_with(|arms, e| (arms, e.span())),
        )
        .map(|(scrutinee, (arms, brace_span))| Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms,
            brace_span,
        });

    let block = block().map(|(exprs, tail, span)| Expr::Block {
        exprs,
        tail: tail.map(Box::new),
        span,
    });

    choice((
        literal.map(Expr::Literal),
        let_expr,
        array,
        tuple,
        constructor_or_ident,
        match_expr,
        block,
    ))
}

enum CallRhs<'src> {
    Get {
        field: Ident<'src>,
    },
    Set {
        field: Ident<'src>,
        value: Expr<'src>,
    },

    Call {
        arguments: Vec<Expr<'src>>,
        paren_span: Span,
    },
    ContApplication {
        arguments: Vec<(Ident<'src>, Option<Expr<'src>>)>,
        bracket_span: Span,
    },
}

fn call_rhs<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, CallRhs<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    let get_or_set = filter_matches!(Token::Dot(_))
        .ignore_then(ident())
        .then(filter_matches!(Token::Eq(_)).ignore_then(expr()).or_not())
        .map(|(field, value)| {
            if let Some(value) = value {
                CallRhs::Set { field, value }
            } else {
                CallRhs::Get { field }
            }
        });

    let call = items(expr())
        .delimited_by(just(Token::OpenParen), just(Token::CloseParen))
        .map_with(|arguments, e| CallRhs::Call {
            arguments,
            paren_span: e.span(),
        });

    let cont_application =
        items(ident().then(filter_matches!(Token::Eq(_)).ignore_then(expr()).or_not()))
            .delimited_by(just(Token::OpenBracket), just(Token::CloseBracket))
            .map_with(|arguments, e| CallRhs::ContApplication {
                arguments,
                bracket_span: e.span(),
            });

    choice((get_or_set, call, cont_application))
}

fn expr<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Expr<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    recursive(|expr| {
        let call = atom().foldl(call_rhs().repeated(), |object, rhs| match rhs {
            CallRhs::Get { field } => Expr::Get {
                object: Box::new(object),
                field,
            },
            CallRhs::Set { field, value } => Expr::Set {
                object: Box::new(object),
                field,
                value: Box::new(value),
            },
            CallRhs::Call {
                arguments,
                paren_span,
            } => Expr::Call {
                callee: Box::new(object),
                arguments,
                paren_span,
            },
            CallRhs::ContApplication {
                arguments,
                bracket_span,
            } => Expr::ContApplication {
                callee: Box::new(object),
                arguments,
                bracket_span,
            },
        });

        let unary = recursive(|unary| {
            operator!(Token::Dash, UnaryOp::Neg)
                .or(operator!(Token::Bang, UnaryOp::Not))
                .then(unary)
                .map(|(operator, operand)| Expr::Unary {
                    operator,
                    operand: Box::new(operand),
                })
                .or(call)
        });

        let factor = unary.clone().foldl(
            operator!(Token::Asterisk, BinaryOp::Mul)
                .or(operator!(Token::Slash, BinaryOp::Div))
                .or(operator!(Token::Percent, BinaryOp::Rem))
                .then(unary)
                .repeated(),
            |left, (operator, right)| Expr::Binary {
                left: Box::new(left),
                operator,
                right: Box::new(right),
            },
        );

        let sum = factor.clone().foldl(
            operator!(Token::Plus, BinaryOp::Add)
                .or(operator!(Token::Dash, BinaryOp::Sub))
                .then(factor)
                .repeated(),
            |left, (operator, right)| Expr::Binary {
                left: Box::new(left),
                operator,
                right: Box::new(right),
            },
        );

        let comparison = sum
            .clone()
            .then(
                wide_operator!(Token::Eq, Token::Eq, BinaryOp::Eq)
                    .or(wide_operator!(Token::Bang, Token::Eq, BinaryOp::Ne))
                    .or(operator!(Token::Lt, BinaryOp::Lt))
                    .or(wide_operator!(Token::Lt, Token::Eq, BinaryOp::Le))
                    .or(operator!(Token::Gt, BinaryOp::Gt))
                    .or(wide_operator!(Token::Gt, Token::Eq, BinaryOp::Ge))
                    .then(sum)
                    .or_not(),
            )
            .map(|(left, right)| {
                if let Some((operator, right)) = right {
                    Expr::Binary {
                        left: Box::new(left),
                        operator,
                        right: Box::new(right),
                    }
                } else {
                    left
                }
            });

        comparison.or(ident()
            .then_ignore(filter_matches!(Token::Eq(_)))
            .then(expr)
            .map(|(name, value)| Expr::Assign {
                name,
                value: Box::new(value),
            }))
    })
    .labelled("expression")
}
