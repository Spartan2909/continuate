use crate::lexer::Spacing;
use crate::lexer::Token;
use crate::BinaryOp;
use crate::Expr;
use crate::Function;
use crate::Ident;
use crate::Item;
use crate::Literal;
use crate::Path;
use crate::PathIdentSegment;
use crate::PathSegment;
use crate::Pattern;
use crate::Program;
use crate::Type;
use crate::UnaryOp;
use crate::UserDefinedTy;
use crate::UserDefinedTyFields;

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
        .at_least(1)
        .collect::<Vec<_>>()
        .map_with(|segments, e| Path {
            segments,
            span: e.span(),
        })
}

enum TupleResult<Item> {
    Tuple { items: Vec<Item>, span: Span },
    Single(Item),
}

fn tuple<'tokens, 'src, Item>(
    item: impl Parser<'tokens, ParserInput<'tokens, 'src>, Item, ParserExtra> + Clone,
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, TupleResult<Item>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    item.clone()
        .then_ignore(filter_matches!(Token::Comma(_)))
        .repeated()
        .collect::<Vec<_>>()
        .then(item.or_not())
        .delimited_by(just(Token::OpenParen), just(Token::CloseParen))
        .map_with(|(mut items, trailing), e| {
            if let Some(trailing) = trailing {
                if items.is_empty() {
                    // Single item, no trailing comma, so not a tuple
                    return TupleResult::Single(trailing);
                }

                items.push(trailing);
            }
            TupleResult::Tuple {
                items,
                span: e.span(),
            }
        })
}

fn ty<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Type<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    recursive(|ty| {
        just(Token::KwBool)
            .map_with(|_, e| Type::Bool(e.span()))
            .or(just(Token::KwInt).map_with(|_, e| Type::Int(e.span())))
            .or(just(Token::KwFloat).map_with(|_, e| Type::Float(e.span())))
            .or(just(Token::KwString).map_with(|_, e| Type::String(e.span())))
            .or(path().map(Type::Path))
            .or(tuple(ty.clone()).map(|result| match result {
                TupleResult::Tuple { items, span } => Type::Tuple { items, span },
                TupleResult::Single(ty) => ty,
            }))
            .or(just(Token::Fn)
                .ignore_then(
                    items(ty.clone()).delimited_by(just(Token::OpenParen), just(Token::CloseParen)),
                )
                .then(
                    items(
                        ident()
                            .then_ignore(filter_matches!(Token::Colon(_)))
                            .then(ty),
                    )
                    .delimited_by(just(Token::OpenBracket), just(Token::CloseBracket))
                    .or_not(),
                )
                .map_with(|(params, continuations), e| Type::Function {
                    params,
                    continuations: continuations.unwrap_or(vec![]),
                    span: e.span(),
                })
                .labelled("signature"))
    })
    .labelled("type")
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
            .labelled("pattern")
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

fn literal<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Literal<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    select! {
        Token::Int(val) = e => Literal::Int(val, e.span()),
        Token::Float(val) = e => Literal::Float(val, e.span()),
        Token::String(val) = e => Literal::String(val, e.span()),
    }
    .labelled("literal")
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

#[allow(clippy::too_many_lines, reason = "no real alternative")]
fn expr<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Expr<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    recursive(|expr| {
        let array = items(expr.clone())
            .delimited_by(just(Token::OpenBracket), just(Token::CloseBracket))
            .map_with(|exprs, e| Expr::Array {
                exprs,
                span: e.span(),
            });

        let constructor_or_ident = path()
            .then(
                named_constructor_elements(expr.clone())
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
            .ignore_then(expr.clone())
            .then(
                pattern()
                    .then_ignore(
                        just(Token::Eq(Spacing::Joint)).then(filter_matches!(Token::Gt(_))),
                    )
                    .then(expr.clone())
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

        let block = expr
            .clone()
            .then_ignore(filter_matches!(Token::Semicolon(_)))
            .repeated()
            .collect()
            .then(expr.clone().or_not())
            .delimited_by(just(Token::OpenBrace), just(Token::CloseBrace))
            .map_with(|(exprs, tail), e| Expr::Block {
                exprs,
                tail: tail.map(Box::new),
                span: e.span(),
            });

        let atom = choice((
            literal().map(Expr::Literal),
            array,
            tuple(expr.clone()).map(|result| match result {
                TupleResult::Tuple { items, span } => Expr::Tuple { exprs: items, span },
                TupleResult::Single(expr) => expr,
            }),
            constructor_or_ident,
            match_expr,
            block,
        ));

        let call_rhs = {
            let get_or_set = filter_matches!(Token::Dot(_))
                .ignore_then(ident())
                .then(
                    filter_matches!(Token::Eq(_))
                        .ignore_then(expr.clone())
                        .or_not(),
                )
                .map(|(field, value)| {
                    if let Some(value) = value {
                        CallRhs::Set { field, value }
                    } else {
                        CallRhs::Get { field }
                    }
                });

            let call = items(expr.clone())
                .delimited_by(just(Token::OpenParen), just(Token::CloseParen))
                .map_with(|arguments, e| CallRhs::Call {
                    arguments,
                    paren_span: e.span(),
                });

            let cont_application = items(
                ident().then(
                    filter_matches!(Token::Eq(_))
                        .ignore_then(expr.clone())
                        .or_not(),
                ),
            )
            .delimited_by(just(Token::OpenBracket), just(Token::CloseBracket))
            .map_with(|arguments, e| CallRhs::ContApplication {
                arguments,
                bracket_span: e.span(),
            });

            choice((get_or_set, call, cont_application))
        };

        let call = atom.foldl(call_rhs.repeated(), |object, rhs| match rhs {
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

        let assign = comparison.or(ident()
            .then_ignore(filter_matches!(Token::Eq(_)))
            .then(expr.clone())
            .map(|(name, value)| Expr::Assign {
                name,
                value: Box::new(value),
            }));

        assign.or(just(Token::Let)
            .ignore_then(ident())
            .then(filter_matches!(Token::Colon(_)).ignore_then(ty()).or_not())
            .then_ignore(operator!(Token::Eq, BinaryOp::Eq))
            .then(expr)
            .map_with(|((name, ty), val), e| Expr::Declare {
                name,
                ty,
                value: Box::new(val),
                span: e.span(),
            }))
    })
    .labelled("expression")
}

fn function<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, Function<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    just(Token::Fn)
        .ignore_then(ident())
        .then(
            items(
                ident()
                    .then_ignore(filter_matches!(Token::Colon(_)))
                    .then(ty()),
            )
            .delimited_by(just(Token::OpenParen), just(Token::CloseParen)),
        )
        .then(
            items(
                ident()
                    .then_ignore(filter_matches!(Token::Colon(_)))
                    .then(ty()),
            )
            .delimited_by(just(Token::OpenBracket), just(Token::CloseBracket)),
        )
        .then(
            expr()
                .then_ignore(filter_matches!(Token::Semicolon(_)))
                .repeated()
                .collect()
                .then(expr().or_not())
                .delimited_by(just(Token::OpenBrace), just(Token::CloseBrace))
                .map(|(mut body, tail): (Vec<_>, _)| {
                    if let Some(tail) = tail {
                        body.push(tail);
                    }
                    body
                }),
        )
        .map_with(|(((name, params), continuations), body), e| Function {
            name,
            params,
            continuations,
            body,
            span: e.span(),
        })
}

fn product_ty<'tokens, 'src>() -> impl Parser<
    'tokens,
    ParserInput<'tokens, 'src>,
    (Ident<'src>, UserDefinedTyFields<'src>),
    ParserExtra,
> + Clone
where
    'src: 'tokens,
{
    ident()
        .then(
            items(
                ident()
                    .then_ignore(filter_matches!(Token::Colon(_)))
                    .then(ty()),
            )
            .delimited_by(just(Token::OpenBrace), just(Token::CloseBrace))
            .map(UserDefinedTyFields::Named)
            .or(items(ty())
                .delimited_by(just(Token::OpenParen), just(Token::CloseParen))
                .map(UserDefinedTyFields::Anonymous))
            .or_not(),
        )
        .map(|(name, fields)| (name, fields.unwrap_or(UserDefinedTyFields::Unit)))
}

fn sum_ty<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, UserDefinedTy<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    just(Token::Enum)
        .ignore_then(ident())
        .then(items(product_ty()).delimited_by(just(Token::OpenBrace), just(Token::CloseBrace)))
        .map_with(|(name, variants), e| UserDefinedTy::Sum {
            name,
            variants,
            span: e.span(),
        })
}

fn user_defined_ty<'tokens, 'src>(
) -> impl Parser<'tokens, ParserInput<'tokens, 'src>, UserDefinedTy<'src>, ParserExtra> + Clone
where
    'src: 'tokens,
{
    just(Token::Struct)
        .ignore_then(product_ty())
        .map_with(|(name, fields), e| UserDefinedTy::Product {
            name,
            fields,
            span: e.span(),
        })
        .or(sum_ty())
}

pub fn parse<'src>(
    input: &[(Token<'src>, Span)],
    eoi: Span,
    name: &str,
) -> ParseResult<Program<'src>, Error> {
    function()
        .map(Item::Function)
        .or(user_defined_ty().map(Item::UserDefinedTy))
        .repeated()
        .collect()
        .map(|items| Program {
            items,
            name: name.to_string(),
        })
        .parse(Input::map(input, eoi, |(token, span)| (token, span)))
}
