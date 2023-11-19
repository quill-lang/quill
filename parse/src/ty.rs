use std::fmt::Display;

use diagnostic::Dr;
use files::{Span, Spanned};
use internment::Intern;

use crate::{
    kind::PKind,
    lex::{Bracket, QualifiedName, ReservedSymbol, TokenTree},
    parser::{ParseError, Parser},
};

/// A parsed region.
#[derive(Debug, PartialEq, Eq)]
pub enum PRegion {
    /// A region variable.
    Variable { span: Span, name: Intern<String> },
    /// The static region.
    Static(Span),
    /// The meet of two regions.
    Meet {
        left: Box<PRegion>,
        right: Box<PRegion>,
    },
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FunctionKind {
    /// The function must be invoked exactly once.
    /// It may hold resources.
    Once,
    /// The function may be invoked arbitrarily many times from behind a borrow.
    /// It may only contain copyable resources.
    Many,
}

#[derive(Debug, PartialEq, Eq)]
pub struct PTypeBinder {
    pub variable: Intern<String>,
    pub variable_span: Span,
    pub variable_kind: Option<PKind>,
}

/// A parsed type.
#[derive(Debug, PartialEq, Eq)]
pub enum PType {
    /// A type variable, or possibly qualified name.
    Variable { name: QualifiedName, span: Span },
    /// The type of propositions.
    Prop(Span),
    /// The type of borrowed values.
    Borrow {
        /// The span of the `&` operator.
        borrow: Span,
        /// The region annotation, if one exists.
        region: Option<PRegion>,
        /// The type that we are borrowing.
        ty: Box<PType>,
    },
    /// The type of functions.
    Function {
        /// The way this function is handled.
        kind: FunctionKind,
        /// The argument type of the function.
        argument: Box<PType>,
        /// The region annotation, if one exists.
        region: Option<PRegion>,
        /// The token `->` or `=>`.
        arrow_token: Span,
        /// The return type of the function.
        result: Box<PType>,
    },
    /// An application of a polymorphic type.
    Apply { left: Box<PType>, right: Box<PType> },
    /// The type of values that are parametrised by type variables.
    Polymorphic {
        token: Span,
        /// The type variables.
        binders: Vec<PTypeBinder>,
        /// The type of the value, which may be polymorphic over the type variable.
        result: Box<PType>,
    },
    /// The type of values that are parametrised by a region variable.
    Polyregion {
        token: Span,
        /// The region variable.
        variable: Intern<String>,
        variable_span: Span,
        /// The type of the value, which may be polymorphic over the region variable.
        result: Box<PType>,
    },
}

impl Spanned for PRegion {
    fn span(&self) -> Span {
        match self {
            PRegion::Variable { span, .. } => *span,
            PRegion::Static(span) => *span,
            PRegion::Meet { left, right } => left.span().union(right.span()),
        }
    }
}

impl Spanned for PType {
    fn span(&self) -> Span {
        match self {
            PType::Variable { span, .. } => *span,
            PType::Prop(span) => *span,
            PType::Borrow { borrow, ty, .. } => borrow.union(ty.span()),
            PType::Function {
                argument, result, ..
            } => argument.span().union(result.span()),
            PType::Apply { left, right } => left.span().union(right.span()),
            PType::Polymorphic { token, result, .. } | PType::Polyregion { token, result, .. } => {
                token.union(result.span())
            }
        }
    }
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    pub(crate) fn parse_qualified_name(&mut self) -> Dr<(QualifiedName, Span), ParseError> {
        struct PQualifiedName {
            /// A list of name segments, their spans, and the spans of the following `::` token.
            segments: Vec<(Intern<String>, Span, Span)>,
            final_segment: Intern<String>,
            final_span: Span,
        }

        fn inner<'a, I>(this: &mut Parser<'a, I>) -> Dr<PQualifiedName, ParseError>
        where
            I: Iterator<Item = TokenTree>,
        {
            if let Some(TokenTree::Lexical { text, span }) = this.next() {
                if let Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Scope,
                    span: scope_span,
                }) = this.peek()
                {
                    let scope_span = *scope_span;
                    // Consume the `::` token.
                    this.next();
                    // Consume the tail qualified name.
                    inner(this).map(|mut tail| {
                        tail.segments.insert(0, (text.into(), span, scope_span));
                        tail
                    })
                } else {
                    // This name has only one segment.
                    Dr::new(PQualifiedName {
                        segments: Vec::new(),
                        final_segment: text.into(),
                        final_span: span,
                    })
                }
            } else {
                todo!()
            }
        }

        inner(self).map(|name: PQualifiedName| {
            (
                QualifiedName {
                    module: name
                        .segments
                        .iter()
                        .map(|(segment, _, _)| *segment)
                        .collect(),
                    name: name.final_segment,
                },
                name.segments
                    .first()
                    .map_or(name.final_span, |(_, span, _)| span.union(name.final_span)),
            )
        })
    }

    fn parse_type_application(&mut self, indent: usize) -> Dr<PType, ParseError> {
        let mut terms = Vec::new();

        loop {
            match self.peek() {
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Prop,
                    ..
                }) => {
                    let span = self.next().unwrap().span();
                    terms.push(Dr::new(PType::Prop(span)))
                }
                Some(TokenTree::Lexical { .. }) => terms.push(
                    self.parse_qualified_name()
                        .bind(|(name, span)| Dr::new(PType::Variable { name, span })),
                ),
                Some(TokenTree::Block {
                    bracket: Bracket::Paren,
                    ..
                }) => {
                    if let Some(TokenTree::Block {
                        open,
                        close,
                        contents,
                        ..
                    }) = self.next()
                    {
                        let mut inner = self.with_vec(open, close, contents);
                        terms.push(inner.parse_type(indent).bind(|term| {
                            inner
                                .assert_end("type inside bracketed block")
                                .map(|()| term)
                        }));
                    } else {
                        unreachable!()
                    }
                }
                _ => break,
            }
        }

        Dr::sequence(terms).bind(|terms| {
            match terms.into_iter().reduce(|left, right| PType::Apply {
                left: Box::new(left),
                right: Box::new(right),
            }) {
                Some(result) => Dr::new(result),
                None => todo!(),
            }
        })
    }

    /// Parses a single forall binder.
    pub(crate) fn parse_forall_binder(&mut self, indent: usize) -> Dr<PTypeBinder, ParseError> {
        match self.next() {
            // A single lexical token is interpreted as a binder with no explicit type.
            Some(TokenTree::Lexical { text, span }) => Dr::new(PTypeBinder {
                variable: text.into(),
                variable_span: span,
                variable_kind: None,
            }),
            Some(TokenTree::Block {
                bracket: Bracket::Paren,
                open,
                close,
                contents,
            }) => {
                // This is a binder which explicitly declares its type.
                // The form is `(name : type)`.
                let mut inner = self.with_vec(open, close, contents);
                let (text, span) = if let Some(TokenTree::Lexical { text, span }) = inner.next() {
                    (text, span)
                } else {
                    todo!()
                };
                inner
                    .require_reserved(ReservedSymbol::Colon)
                    .bind(|_| inner.parse_kind(indent))
                    .bind(|kind| {
                        inner.assert_end("parameter kind").map(|()| PTypeBinder {
                            variable: text.into(),
                            variable_span: span,
                            variable_kind: Some(kind),
                        })
                    })
            }
            _ => todo!(),
        }
    }

    /// Assuming that the next token is a `forall`, parse a `forall <types>, e` type.
    fn parse_forall_type(&mut self, indent: usize) -> Dr<PType, ParseError> {
        let forall_token = self.next().unwrap().span();

        // Parse one or more types.
        let mut binders = Vec::new();
        loop {
            match self.peek() {
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Comma,
                    ..
                }) => {
                    self.next();
                    break;
                }
                _ => {
                    let binder = self.parse_forall_binder(indent);
                    let errored = binder.is_err();
                    binders.push(binder);
                    if errored {
                        break;
                    }
                }
            }
        }

        Dr::sequence(binders).bind(|binders| {
            // TODO: Check that there is at least one binder?
            self.parse_type(indent).map(|value| PType::Polymorphic {
                token: forall_token,
                binders,
                result: Box::new(value),
            })
        })
    }

    pub fn parse_type(&mut self, indent: usize) -> Dr<PType, ParseError> {
        if matches!(
            self.peek(),
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Forall,
                ..
            })
        ) {
            self.parse_forall_type(indent)
        } else {
            self.parse_type_application(indent)
                .bind(|left| match self.peek() {
                    Some(TokenTree::Reserved {
                        symbol: symbol @ (ReservedSymbol::Arrow | ReservedSymbol::DoubleArrow),
                        ..
                    }) => {
                        let kind = match symbol {
                            ReservedSymbol::Arrow => FunctionKind::Once,
                            ReservedSymbol::DoubleArrow => FunctionKind::Many,
                            _ => unreachable!(),
                        };
                        let span = self.next().unwrap().span();
                        self.parse_type(indent).map(|right| PType::Function {
                            kind,
                            argument: Box::new(left),
                            region: None,
                            arrow_token: span,
                            result: Box::new(right),
                        })
                    }
                    _ => Dr::new(left),
                })
        }
    }
}

impl Display for PRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PRegion::Variable { name, .. } => write!(f, "'{name}"),
            PRegion::Static(_) => write!(f, "static"),
            PRegion::Meet { left, right } => write!(f, "{left} * {right}"),
        }
    }
}

impl Display for PType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PType::Variable { name, .. } => write!(f, "{name}"),
            PType::Prop(_) => write!(f, "Prop"),
            PType::Borrow {
                region: Some(region),
                ty,
                ..
            } => write!(f, "&{region} {ty}"),
            PType::Borrow {
                region: None, ty, ..
            } => write!(f, "&{ty}"),
            PType::Function {
                kind,
                argument,
                region,
                result,
                ..
            } => write!(
                f,
                "({argument}) {}{} ({result})",
                match kind {
                    FunctionKind::Once => "->",
                    FunctionKind::Many => "=>",
                },
                match region {
                    Some(region) => format!(" '{region}"),
                    None => String::new(),
                }
            ),
            PType::Apply { left, right } => write!(f, "({left}) ({right})"),
            PType::Polymorphic {
                binders, result, ..
            } => {
                write!(f, "forall")?;
                for binder in binders {
                    match &binder.variable_kind {
                        Some(kind) => write!(f, " ({}: {})", binder.variable, kind)?,
                        None => write!(f, " {}", binder.variable)?,
                    }
                }
                write!(f, ", {result}")
            }
            PType::Polyregion {
                token,
                variable,
                variable_span,
                result,
            } => todo!(),
        }
    }
}
