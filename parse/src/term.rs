//! We parse expressions in two stages.
//! We create an explicit recursive descent parser for expressions themselves,
//! and use a Pratt parser for the "Pratt expressions", a specific kind of sub-expression
//! that deals only with prefix, infix, and postfix operators, as well as function application.

use std::{fmt::Display, iter::Peekable};

use diagnostic::Dr;
use files::{Span, Spanned};
use internment::Intern;

use crate::{
    lex::{Bracket, OperatorInfo, QualifiedName, ReservedSymbol, TokenTree},
    parser::{ParseError, Parser},
    ty::{FunctionKind, PType, PTypeBinder},
};

#[derive(Debug, PartialEq, Eq)]
pub struct PBinder {
    /// The argument of the function.
    pub argument: Intern<String>,
    pub argument_span: Span,
    /// The argument type, if it is given explicitly.
    pub argument_ty: Option<PType>,
}

/// A parsed term.
#[derive(Debug, PartialEq, Eq)]
pub enum PTerm {
    /// A local variable or a (possibly qualified) name.
    Variable { name: QualifiedName, span: Span },
    /// The proposition that two values of the same type are equal.
    Equal { left: Box<PTerm>, right: Box<PTerm> },
    /// A borrowed value.
    Borrow {
        /// The span of the `&` operator.
        borrow: Span,
        /// The value that we are borrowing.
        value: Box<PTerm>,
    },
    /// A lambda abstraction.
    Function {
        /// The `fn` token.
        fn_token: Span,
        /// The way this function is handled.
        kind: FunctionKind,
        /// The arguments to the function.
        binders: Vec<PBinder>,
        /// The return value of the function.
        result: Box<PTerm>,
    },
    /// A function application.
    Apply { left: Box<PTerm>, right: Box<PTerm> },
    /// A value that is parametrised by type variables.
    Polymorphic {
        token: Span,
        /// The type variables.
        binders: Vec<PTypeBinder>,
        /// The value, which may be polymorphic over the type variables.
        value: Box<PTerm>,
    },
    /// An instantiation of a polymorphic term.
    InstantiatePolymorphic { left: Box<PTerm>, right: Box<PTerm> },
    /// A value that is parametrised by a region variable.
    Polyregion {
        token: Span,
        /// The region variable.
        variable: Intern<String>,
        variable_span: Span,
        /// The value, which may be polymorphic over the region variable.
        value: Box<PTerm>,
    },
    /// An instantiation of a region polymorphic term.
    InstantiatePolyregion { left: Box<PTerm>, right: Box<PTerm> },
}

impl Spanned for PTerm {
    fn span(&self) -> Span {
        match self {
            PTerm::Variable { span, .. } => *span,
            PTerm::Equal { left, right } => left.span().union(right.span()),
            PTerm::Borrow { borrow, value } => borrow.union(value.span()),
            PTerm::Function {
                fn_token, result, ..
            } => fn_token.union(result.span()),
            PTerm::Apply { left, right }
            | PTerm::InstantiatePolymorphic { left, right }
            | PTerm::InstantiatePolyregion { left, right } => left.span().union(right.span()),
            PTerm::Polymorphic { token, value, .. } | PTerm::Polyregion { token, value, .. } => {
                token.union(value.span())
            }
        }
    }
}

/// A piece of syntax in an expression constructed from (relatively) few tokens.
/// Easily parsable.
enum PrattExpression {
    QualifiedName {
        name: QualifiedName,
        span: Span,
    },
    Operator {
        text: Intern<String>,
        info: OperatorInfo,
        span: Span,
    },
    PTerm(PTerm),
}

impl Spanned for PrattExpression {
    fn span(&self) -> Span {
        match self {
            PrattExpression::QualifiedName { span, .. } => *span,
            PrattExpression::Operator { span, .. } => *span,
            PrattExpression::PTerm(term) => term.span(),
        }
    }
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    /// Parse all token trees that could be part of a Pratt expression.
    fn parse_pratt_expr_terms(
        &mut self,
        mut indent: usize,
    ) -> Dr<Vec<PrattExpression>, ParseError> {
        let original_indent = indent;
        let mut result = Vec::new();
        loop {
            match self.peek() {
                Some(TokenTree::Lexical { .. }) => result.push(
                    self.parse_qualified_name()
                        .map(|(name, span)| PrattExpression::QualifiedName { name, span }),
                ),
                Some(TokenTree::Operator { .. }) => {
                    if let Some(TokenTree::Operator { text, info, span }) = self.next() {
                        result.push(Dr::new(PrattExpression::Operator {
                            text: text.into(),
                            info,
                            span,
                        }));
                    } else {
                        unreachable!()
                    }
                }
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
                        result.push(inner.parse_term(indent, indent).bind(|term| {
                            inner
                                .assert_end("expression inside bracketed block")
                                .map(|()| PrattExpression::PTerm(term))
                        }));
                    } else {
                        unreachable!()
                    }
                }
                Some(TokenTree::Newline {
                    indent: newline_indent,
                    ..
                }) => {
                    if *newline_indent > original_indent {
                        indent = *newline_indent;
                        self.next();
                    } else {
                        return Dr::sequence(result);
                    }
                }
                _ => return Dr::sequence(result),
            }
        }
    }

    /// Uses the algorithm from <https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html>.
    fn parse_pratt_expr_binding_power(
        &self,
        terms: &mut Peekable<impl Iterator<Item = PrattExpression>>,
        min_power: i32,
        expr_span: Span,
    ) -> PTerm {
        let mut left = match terms.next() {
            Some(PrattExpression::QualifiedName { name, span }) => PTerm::Variable { name, span },
            Some(PrattExpression::Operator { text, info, span }) => {
                // We have a prefix operator.
                match info.prefix {
                    Some((prefix_power, prefix_function)) => {
                        let right =
                            self.parse_pratt_expr_binding_power(terms, prefix_power, expr_span);
                        match text.as_str() {
                            "&" => PTerm::Borrow {
                                borrow: span,
                                value: Box::new(right),
                            },
                            _ => PTerm::Apply {
                                left: Box::new(PTerm::Variable {
                                    name: prefix_function,
                                    span,
                                }),
                                right: Box::new(right),
                            },
                        }
                    }
                    None => {
                        // This wasn't a prefix operator.
                        todo!()
                    }
                }
            }
            Some(PrattExpression::PTerm(term)) => term,
            None => todo!(),
        };

        loop {
            match terms.peek() {
                Some(PrattExpression::QualifiedName { .. }) => {
                    if let Some(PrattExpression::QualifiedName { name, span }) = terms.next() {
                        left = PTerm::Apply {
                            left: Box::new(left),
                            right: Box::new(PTerm::Variable { name, span }),
                        }
                    } else {
                        unreachable!()
                    }
                }
                Some(PrattExpression::PTerm(_)) => {
                    if let Some(PrattExpression::PTerm(right)) = terms.next() {
                        left = PTerm::Apply {
                            left: Box::new(left),
                            right: Box::new(right),
                        }
                    } else {
                        unreachable!()
                    }
                }
                Some(PrattExpression::Operator { info, .. }) => {
                    if let Some((postfix_power, _)) = &info.postfix {
                        if *postfix_power < min_power {
                            break left;
                        }

                        if let Some(PrattExpression::Operator {
                            info:
                                OperatorInfo {
                                    postfix: Some((_, postfix_function)),
                                    ..
                                },
                            span,
                            ..
                        }) = terms.next()
                        {
                            left = PTerm::Apply {
                                left: Box::new(PTerm::Variable {
                                    name: postfix_function,
                                    span,
                                }),
                                right: Box::new(left),
                            };
                        } else {
                            unreachable!()
                        }
                    } else if let Some((left_power, _, _)) = &info.infix {
                        if *left_power < min_power {
                            break left;
                        }

                        if let Some(PrattExpression::Operator {
                            info:
                                OperatorInfo {
                                    infix: Some((_, right_power, infix_function)),
                                    ..
                                },
                            span,
                            ..
                        }) = terms.next()
                        {
                            left = PTerm::Apply {
                                left: Box::new(PTerm::Apply {
                                    left: Box::new(PTerm::Variable {
                                        name: infix_function,
                                        span,
                                    }),
                                    right: Box::new(left),
                                }),
                                right: Box::new(self.parse_pratt_expr_binding_power(
                                    terms,
                                    right_power,
                                    expr_span,
                                )),
                            };
                        } else {
                            unreachable!()
                        }
                    } else {
                        break left;
                    }
                }
                None => break left,
            }
        }
    }

    /// Parses a Pratt expression.
    fn parse_pratt_term(&mut self, indent: usize) -> Dr<PTerm, ParseError> {
        self.parse_pratt_expr_terms(indent).bind(|terms| {
            let expr_span = terms.iter().map(|expr| expr.span()).reduce(|l, r| Span {
                start: l.start,
                end: r.end,
            });
            match expr_span {
                Some(expr_span) => {
                    let mut iter = terms.into_iter().peekable();
                    let result =
                        self.parse_pratt_expr_binding_power(&mut iter, i32::MIN, expr_span);
                    match iter.next() {
                        Some(_) => todo!(),
                        None => Dr::new(result),
                    }
                }
                None => match self.peek() {
                    Some(_tt) => Dr::new_err(
                        todo!(),
                        // Report::new(ReportKind::Error, source, tt.span().start)
                        //     .with_message("expected an expression".into())
                        //     .with_label(
                        //         Label::new(source, tt.span(), LabelType::Error).with_message(
                        //             message!["expected an expression but found ", tt],
                        //         ),
                        //     ),
                    ),
                    None => match self.block_brackets() {
                        Some((_open, _close)) => Dr::new_err(
                            todo!(),
                            // Report::new(ReportKind::Error, source, close.start)
                            //     .with_message("expected an expression".into())
                            //     .with_label(
                            //         Label::new(source, close, LabelType::Error).with_message(
                            //             "expected an expression before the end of this block"
                            //                 .into(),
                            //         ),
                            //     )
                            //     .with_label(
                            //         Label::new(source, open, LabelType::Note)
                            //             .with_message("the block started here".into()),
                            //     ),
                        ),
                        None => todo!(),
                    },
                },
            }
        })
    }

    /// Parses a single lambda abstraction binder.
    fn parse_fn_binder(&mut self, indent: usize) -> Dr<PBinder, ParseError> {
        match self.next() {
            // A single lexical token is interpreted as a binder with no explicit type.
            Some(TokenTree::Lexical { text, span }) => Dr::new(PBinder {
                argument: text.into(),
                argument_span: span,
                argument_ty: None,
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
                    .bind(|_| inner.parse_type(indent))
                    .bind(|ty| {
                        inner.assert_end("parameter type").map(|()| PBinder {
                            argument: text.into(),
                            argument_span: span,
                            argument_ty: Some(ty),
                        })
                    })
            }
            Some(tt) => Dr::new_err(
                todo!(),
                // Report::new(ReportKind::Error, self.config().source, tt.span().start)
                //     .with_message(message!["expected a parameter name, but found ", &tt])
                //     .with_label(
                //         Label::new(self.config().source, tt.span(), LabelType::Error)
                //             .with_message("expected a parameter name".into()),
                //     )
                //     .with_label(
                //         Label::new(self.config().source, fn_token, LabelType::Note)
                //             .with_message("while parsing this function".into()),
                //     )
                //     .with_note(
                //         "use '=>' to end the sequence of parameters and begin the function body"
                //             .into(),
                //     ),
            ),
            None => todo!(),
        }
    }

    /// Assuming that the next token is a `fn`, parse a `fn <binders> -> / => e` expression.
    fn parse_fn_term(&mut self, min_indent: usize, indent: usize) -> Dr<PTerm, ParseError> {
        let fn_token = self.next().unwrap().span();

        // Parse one or more binders.
        let mut binders = Vec::new();
        let kind = loop {
            match self.peek() {
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Arrow,
                    ..
                }) => {
                    self.next();
                    break FunctionKind::Once;
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::DoubleArrow,
                    ..
                }) => {
                    self.next();
                    break FunctionKind::Many;
                }
                _ => {
                    let binder = self.parse_fn_binder(indent);
                    let errored = binder.is_err();
                    binders.push(binder);
                    if errored {
                        break FunctionKind::Once;
                    }
                }
            }
        };

        Dr::sequence(binders).bind(|binders| {
            // TODO: Check that there is at least one binder?
            self.parse_term(min_indent, indent)
                .map(|result| PTerm::Function {
                    fn_token,
                    kind,
                    binders,
                    result: Box::new(result),
                })
        })
    }

    /// Assuming that the next token is a `forall`, parse a `forall <types>, e` expression.
    fn parse_forall_term(&mut self, min_indent: usize, indent: usize) -> Dr<PTerm, ParseError> {
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
            self.parse_term(min_indent, indent)
                .map(|value| PTerm::Polymorphic {
                    token: forall_token,
                    binders,
                    value: Box::new(value),
                })
        })
    }

    /// An expression is:
    /// - a lambda, written `fn <binders> => e`; or
    /// - a Pratt expression.
    /// The indent parameter gives the indent level of the surrounding environment.
    /// New line tokens are consumed if their indent is greater than the environment's indent level.
    /// TODO: Check if any newlines are less indented than `min_indent`.
    pub fn parse_term(&mut self, min_indent: usize, indent: usize) -> Dr<PTerm, ParseError> {
        match self.peek() {
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Fn,
                ..
            }) => self.parse_fn_term(min_indent, indent),
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Forall,
                ..
            }) => self.parse_forall_term(min_indent, indent),
            Some(TokenTree::Block { .. }) => self.parse_pratt_term(indent),
            Some(TokenTree::Newline {
                indent: newline_indent,
                ..
            }) => {
                let newline_indent = *newline_indent;
                self.next();
                self.parse_term(min_indent, newline_indent)
            }
            _ => self.parse_pratt_term(indent),
        }
    }
}

impl Display for PTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PTerm::Variable { name, .. } => write!(f, "{name}"),
            PTerm::Equal { left, right } => write!(f, "{left} === {right}"),
            PTerm::Borrow { value, .. } => write!(f, "& ({value})"),
            PTerm::Function {
                kind,
                binders,
                result,
                ..
            } => {
                write!(f, "fn")?;
                for binder in binders {
                    match &binder.argument_ty {
                        Some(ty) => write!(f, " ({}: {})", binder.argument, ty)?,
                        None => write!(f, " {}", binder.argument)?,
                    }
                }
                match kind {
                    FunctionKind::Once => write!(f, " -> ")?,
                    FunctionKind::Many => write!(f, " => ")?,
                }
                write!(f, "{result}")
            }
            PTerm::Apply { left, right } => write!(f, "({left}) ({right})"),
            PTerm::Polymorphic { binders, value, .. } => {
                write!(f, "forall")?;
                for binder in binders {
                    match &binder.variable_kind {
                        Some(kind) => write!(f, " ({}: {})", binder.variable, kind)?,
                        None => write!(f, " {}", binder.variable)?,
                    }
                }
                write!(f, ", {value}")
            }
            PTerm::InstantiatePolymorphic { left, right } => todo!(),
            PTerm::Polyregion {
                token,
                variable,
                variable_span,
                value,
            } => todo!(),
            PTerm::InstantiatePolyregion { left, right } => todo!(),
        }
    }
}
