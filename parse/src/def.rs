use diagnostic::{Dr, Void};
use files::Span;

use crate::{
    expr::{PTerm, PType},
    lex::{QualifiedName, ReservedSymbol, TokenTree},
    parser::{ParseError, Parser},
};

/// A parsed lambda binder.
#[derive(Debug, PartialEq, Eq)]
pub struct PDefinition {
    /// The name given to the definition.
    pub name: QualifiedName,
    pub name_span: Span,
    /// The type, if explicitly given.
    /// If it is not given, it must be inferred by the elaborator.
    pub ty: Option<PType>,
    /// The body of the definition.
    pub body: PTerm,
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    /// Parses a definition.
    /// TODO: Check that after a definition is a newline with indent level zero, or nothing.
    pub fn parse_def(&mut self) -> Dr<PDefinition, ParseError> {
        self.parse_qualified_name().bind(|(name, name_span)| {
            // Either this name is followed by a type ascription with `:`,
            // or an assignment with `=`.
            match self.next() {
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Colon,
                    ..
                }) => {
                    // We first need to parse a type ascription.
                    self.parse_type(0).bind(|ty| {
                        self.require_reserved(ReservedSymbol::Assign).bind(|_| {
                            // Parse the body of the definition.
                            self.parse_term(0, 0).map(|body| PDefinition {
                                name,
                                name_span,
                                ty: Some(ty),
                                body,
                            })
                        })
                    })
                }
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Assign,
                    ..
                }) => {
                    // Parse the body of the definition.
                    self.parse_term(0, 0).map(|body| PDefinition {
                        name,
                        name_span,
                        ty: None,
                        body,
                    })
                }
                _ => todo!(),
            }
        })
    }

    pub fn parse_defs(&mut self) -> Dr<Vec<PDefinition>, Void, ParseError> {
        let mut result = Vec::new();
        let mut errors = Vec::new();
        while self.peek().is_some() {
            // Consume any extra new lines.
            while matches!(self.peek(), Some(TokenTree::Newline { .. })) {
                self.next();
            }

            match self.parse_def().destructure() {
                (Ok(def), _) => {
                    result.push(def);
                }
                (Err(err), _) => {
                    errors.push(err);
                }
            }
            if self.peek().is_none() {
                break;
            }

            if !errors.is_empty() {
                // If we errored, just ignore everything until the next newline.
                while !matches!(self.peek(), Some(TokenTree::Newline { .. })) {
                    self.next();
                }
            }

            let _ = self.require_newline();
        }

        if let (Err(err), _) = self.assert_end("definitions").destructure() {
            errors.push(err);
        }

        Dr::new(result)
            .with_many(errors)
    }
}
