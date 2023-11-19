use diagnostic::Dr;
use files::{Span, Spanned};

use crate::{
    lex::{Bracket, ReservedSymbol, TokenTree},
    parser::{ParseError, Parser},
};

/// A parsed kind.
#[derive(Debug, PartialEq, Eq)]
pub enum PKind {
    /// The kind of types.
    Type(Span),
    /// The kind of type constructors.
    Constructor {
        argument: Box<PKind>,
        result: Box<PKind>,
    },
}

impl Spanned for PKind {
    fn span(&self) -> Span {
        match self {
            PKind::Type(span) => *span,
            PKind::Constructor { argument, result } => argument.span().union(result.span()),
        }
    }
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    pub fn parse_kind(&mut self, indent: usize) -> Dr<PKind, ParseError> {
        let left = match self.peek() {
            Some(TokenTree::Reserved {
                symbol: ReservedSymbol::Type,
                ..
            }) => Dr::new(PKind::Type(self.next().unwrap().span())),
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
                    inner.parse_kind(indent).bind(|term| {
                        inner
                            .assert_end("kind inside bracketed block")
                            .map(|()| term)
                    })
                } else {
                    unreachable!()
                }
            }
            _ => todo!(),
        };

        left.bind(|left| {
            if matches!(
                self.peek(),
                Some(TokenTree::Reserved {
                    symbol: ReservedSymbol::Arrow,
                    ..
                })
            ) {
                self.next();
                self.parse_kind(indent).map(|right| PKind::Constructor {
                    argument: Box::new(left),
                    result: Box::new(right),
                })
            } else {
                Dr::new(left)
            }
        })
    }
}
