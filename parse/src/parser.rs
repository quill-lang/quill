use std::collections::BTreeMap;

use diagnostic::{miette, Dr};
use files::{SourceData, SourceSpan, Span, Spanned};
use thiserror::Error;

use crate::{
    lex::{OperatorInfo, QualifiedName, ReservedSymbol, TokenTree},
    provenance::Provenance,
};

pub struct ParserConfiguration<'a> {
    pub src: &'a SourceData,
    /// The map of known operators to this token iterator.
    /// The innermost map converts operators as strings into their information.
    /// The outermost map tracks the size of each operator; in particular, an operator with string
    /// `s` should be stored in `operators[s.len()][s]`. This allows us to parse longer operators
    /// first, which deals with situations like favouring `++` over `+`. The structure [`BTreeMap`]
    /// is used for determinism.
    ///
    /// This map should always have entries for `1` and `2`, although they can be empty.
    operators: BTreeMap<usize, BTreeMap<String, OperatorInfo>>,
}

impl<'a> ParserConfiguration<'a> {
    pub fn new(src: &'a SourceData) -> Self {
        let mut operators: BTreeMap<usize, BTreeMap<String, OperatorInfo>> = BTreeMap::new();
        operators.insert(1, Default::default());
        operators.insert(2, Default::default());
        // Add the prefix operator for `&`.
        operators.get_mut(&1).unwrap().insert(
            "&".to_owned(),
            OperatorInfo {
                prefix: Some((
                    0,
                    QualifiedName {
                        module: Vec::new(),
                        name: "&".to_owned().into(),
                    },
                )),
                infix: None,
                postfix: None,
            },
        );

        Self { src, operators }
    }

    /// Splits a lexical token tree into a string of real lexical tokens based on the
    /// operators registered to this parser.
    fn split_lexical_token(&self, text: &str, span: Span) -> Vec<TokenTree> {
        // Search for known operators, longest first.
        for (token_len, operators) in self.operators.iter().rev() {
            let reserved_symbols: &[ReservedSymbol] = match token_len {
                1 => &[
                    ReservedSymbol::Colon,
                    ReservedSymbol::Assign,
                    ReservedSymbol::Comma,
                    ReservedSymbol::Pipe,
                ],
                2 => &[
                    ReservedSymbol::Arrow,
                    ReservedSymbol::DoubleArrow,
                    ReservedSymbol::Scope,
                ],
                _ => &[],
            };

            // First, check the reserved symbols.
            for symbol in reserved_symbols {
                if let Some((before, after)) = text.split_once(&symbol.to_string()) {
                    // We found this symbol.
                    let before_len = before.chars().count();
                    let mut result = self.split_lexical_token(
                        before,
                        Span {
                            start: span.start,
                            end: span.start + before_len,
                        },
                    );
                    result.push(TokenTree::Reserved {
                        symbol: *symbol,
                        span: Span {
                            start: span.start + before_len,
                            end: span.start + before_len + token_len,
                        },
                    });
                    result.extend(self.split_lexical_token(
                        after,
                        Span {
                            start: span.start + before_len + token_len,
                            end: span.end,
                        },
                    ));
                    return result;
                }
            }

            // Now check the user-defined operators.
            for (operator, info) in operators {
                if let Some((before, after)) = text.split_once(operator) {
                    // We found an operator.
                    let before_len = before.chars().count();
                    let mut result = self.split_lexical_token(
                        before,
                        Span {
                            start: span.start,
                            end: span.start + before_len,
                        },
                    );
                    result.push(TokenTree::Operator {
                        text: operator.clone(),
                        info: info.clone(),
                        span: Span {
                            start: span.start + before_len,
                            end: span.start + before_len + token_len,
                        },
                    });
                    result.extend(self.split_lexical_token(
                        after,
                        Span {
                            start: span.start + before_len + token_len,
                            end: span.end,
                        },
                    ));
                    return result;
                }
            }
        }

        // We didn't find any other tokens in this text.
        if text.is_empty() {
            Vec::new()
        } else {
            // Treat the text as a single token.
            // TODO: Warn the user if this doesn't look like a single token.
            let symbol = match text {
                "def" => ReservedSymbol::Def,
                "fn" => ReservedSymbol::Fn,
                "forall" => ReservedSymbol::Forall,
                "let" => ReservedSymbol::Let,
                "Type" => ReservedSymbol::Type,
                "Prop" => ReservedSymbol::Prop,
                "Region" => ReservedSymbol::Region,
                _ => {
                    return vec![TokenTree::Lexical {
                        text: text.to_owned(),
                        span,
                    }]
                }
            };
            vec![TokenTree::Reserved { symbol, span }]
        }
    }
}

/// A parser, structured in the style of monadic parser combinators.
pub struct Parser<'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    config: &'a ParserConfiguration<'a>,
    /// If we're parsing in a block delimited by brackets, their spans are stored here.
    block_brackets: Option<(Span, Span)>,
    /// A peekable iterator of token trees.
    /// Should not be accessed directly.
    trees: I,
    /// A sequence of token trees to yield before returning from `trees`.
    pushed: Vec<TokenTree>,
}

impl<'a, I> Parser<'a, I>
where
    I: Iterator<Item = TokenTree>,
{
    pub fn new(config: &'a ParserConfiguration, trees: I) -> Self {
        Self {
            config,
            block_brackets: None,
            trees,
            pushed: Vec::new(),
        }
    }

    /// Constructs a "child" parser, initialised with the configuration of this parser.
    /// Usually, this is used with [`TokenTree::Block`] where `vec` is the `contents` field.
    pub fn with_vec(
        &self,
        open: Span,
        close: Span,
        vec: Vec<TokenTree>,
    ) -> Parser<'a, std::vec::IntoIter<crate::lex::TokenTree>> {
        Parser {
            config: self.config,
            block_brackets: Some((open, close)),
            trees: vec.into_iter(),
            pushed: Vec::new(),
        }
    }

    pub fn config(&self) -> &'a ParserConfiguration {
        self.config
    }

    pub fn provenance(&self, span: Span) -> Provenance {
        Provenance::Quill(SourceSpan {
            source: self.config().src.src().clone(),
            span,
        })
    }

    /// Parses the next token tree.
    /// Only this function, `next`, and `push` access `trees` and `pushed` directly.
    pub fn next(&mut self) -> Option<TokenTree> {
        match self.pushed.pop() {
            Some(tt) => Some(tt),
            None => match self.trees.next() {
                Some(TokenTree::Lexical { text, span }) => {
                    self.pushed = self.config.split_lexical_token(&text, span);
                    self.pushed.reverse();
                    self.pushed.pop()
                }
                tt => tt,
            },
        }
    }

    /// Peeks at the next token tree to be parsed.
    /// Only this function, `next`, and `push` access `trees` and `pushed` directly.
    pub fn peek(&mut self) -> Option<&TokenTree> {
        if self.pushed.is_empty() {
            match self.trees.next() {
                Some(TokenTree::Lexical { text, span }) => {
                    self.pushed = self.config.split_lexical_token(&text, span);
                    self.pushed.reverse();
                }
                Some(tt) => {
                    self.pushed.push(tt);
                }
                None => {}
            }
        }

        self.pushed.last()
    }

    /// Reverses a `next` operation.
    /// Only this function, `next`, and `peek` access `trees` and `pushed` directly.
    pub fn push(&mut self, tt: TokenTree) {
        self.pushed.push(tt);
    }

    /// Returns `true` if exactly one more invocation of `next` will yield a [`Some`] value.
    pub fn one_tree_left(&mut self) -> bool {
        match self.next() {
            Some(tt) => {
                let peek_is_none = self.peek().is_none();
                self.push(tt);
                peek_is_none
            }
            None => false,
        }
    }

    /// Parses the next token tree, and asserts that it is a lexical token.
    pub fn require_lexical(&mut self) -> Dr<(String, Span), ParseError> {
        match self.next() {
            Some(TokenTree::Lexical { text, span }) => Dr::new((text, span)),
            Some(tt) => Dr::new_err(
                ParseError::ExpectedName {
                    src: self.config.src.clone(),
                    found: tt.to_string(),
                    span: tt.span(),
                },
                // Report::new(ReportKind::Error, self.config().source, tt.span().start)
                //     .with_message(message!["expected a name, found ", &tt])
                //     .with_label(
                //         Label::new(self.config().source, tt.span(), LabelType::Error)
                //             .with_message(message!["unexpected ", &tt, " found here"]),
                //     ),
            ),
            None => todo!(),
        }
    }

    /// Parses the next token tree, and asserts that it is this reserved symbol.
    pub fn require_reserved(&mut self, symbol: ReservedSymbol) -> Dr<Span, ParseError> {
        match self.next() {
            Some(TokenTree::Reserved {
                symbol: found_symbol,
                span,
            }) => {
                if symbol == found_symbol {
                    Dr::new(span)
                } else {
                    Dr::new_err(ParseError::ExpectedSymbol {
                        src: self.config.src.clone(),
                        expected: symbol.to_string(),
                        found: found_symbol.to_string(),
                        span,
                    })
                }
            }
            Some(tt) => Dr::new_err(ParseError::ExpectedSymbol {
                src: self.config.src.clone(),
                expected: symbol.to_string(),
                found: tt.to_string(),
                span: tt.span(),
            }),
            None => todo!("{symbol}"),
        }
    }

    /// Parses the next token tree, and asserts that it is a newline token tree.
    pub fn require_newline(&mut self) -> Dr<(Span, usize), ParseError> {
        match self.next() {
            Some(TokenTree::Newline { span, indent }) => Dr::new((span, indent)),
            Some(tt) => Dr::new_err(ParseError::ExpectedNewline {
                src: self.config.src.clone(),
                found: tt.to_string(),
                span: tt.span(),
            }),
            None => todo!(),
        }
    }

    pub fn assert_end(&mut self, while_parsing: &str) -> Dr<(), ParseError> {
        let src = self.config().src.clone();
        let block_brackets = self.block_brackets;
        match self.peek() {
            Some(tt) => Dr::new_err(if let Some((open, close)) = block_brackets {
                ParseError::UnexpectedEof {
                    src,
                    found: tt.to_string(),
                    while_parsing: while_parsing.to_owned(),
                    span: tt.span(),
                    block_start: Some(open),
                    block_end: Some(close),
                }
            } else {
                ParseError::UnexpectedEof {
                    src,
                    found: tt.to_string(),
                    while_parsing: while_parsing.to_owned(),
                    span: tt.span(),
                    block_start: None,
                    block_end: None,
                }
            }),
            None => Dr::new(()),
        }
    }

    pub fn block_brackets(&self) -> Option<(Span, Span)> {
        self.block_brackets
    }
}

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq)]
// #[help("explicit spaces are preferred to tab characters because the parser is whitespace-sensitive, and inconsistent use of tabs and spaces can cause ambiguity")]
pub enum ParseError {
    #[error("expected a name, found {found}")]
    ExpectedName {
        #[source_code]
        src: SourceData,
        found: String,
        #[label("unexpected {found} found here")]
        span: Span,
    },
    #[error("expected {expected}, found {found}")]
    ExpectedSymbol {
        #[source_code]
        src: SourceData,
        expected: String,
        found: String,
        #[label("unexpected {found} found here")]
        span: Span,
    },
    #[error("expected new line, found {found}")]
    ExpectedNewline {
        #[source_code]
        src: SourceData,
        found: String,
        #[label("unexpected {found} found here")]
        span: Span,
    },
    #[error("unexpected extra tokens while parsing {while_parsing}")]
    UnexpectedEof {
        #[source_code]
        src: SourceData,
        found: String,
        while_parsing: String,
        #[label("did not expect {found} while parsing {while_parsing}")]
        span: Span,
        #[label("block started here")]
        block_start: Option<Span>,
        #[label("block ended here")]
        block_end: Option<Span>,
    },
}
