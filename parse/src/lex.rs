use std::{
    fmt::{Debug, Display},
    iter::Peekable,
};

use diagnostic::{miette, Dr, DynamicDiagnostic};
use files::{SourceData, Span, Spanned};
use internment::Intern;
use thiserror::Error;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Bracket {
    /// `(` and `)`.
    Paren,
    /// `[` and `]`.
    Square,
    /// `{` and `}`.
    Brace,
}

impl Display for Bracket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Bracket::Paren => write!(f, "parenthesis"),
            Bracket::Square => write!(f, "square bracket"),
            Bracket::Brace => write!(f, "brace bracket"),
        }
    }
}

/// A qualified name.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct QualifiedName {
    pub module: Vec<Intern<String>>,
    pub name: Intern<String>,
}

impl Display for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}::{}",
            self.module
                .iter()
                .map(|x| x.as_str())
                .collect::<Vec<_>>()
                .join("::"),
            self.name,
        )
    }
}

impl Debug for QualifiedName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct OperatorInfo {
    /// The binding power for this operator used as a prefix operator,
    /// and the function represented by this prefix operator.
    pub prefix: Option<(i32, QualifiedName)>,
    /// The left and right binding power for this operator used as an infix operator.
    /// and the function represented by this infix operator.
    pub infix: Option<(i32, i32, QualifiedName)>,
    /// The binding power for this operator used as a postfix operator.
    /// and the function represented by this postfix operator.
    pub postfix: Option<(i32, QualifiedName)>,
}

/// The reserved operators and keywords.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ReservedSymbol {
    /// `->`
    Arrow,
    /// `=>`
    DoubleArrow,
    /// `::`
    Scope,
    /// `:`
    Colon,
    /// `=`
    Assign,
    /// `,`
    Comma,
    /// `|`
    Pipe,
    /// `def`
    Def,
    /// `fn`
    Fn,
    /// `forall`
    Forall,
    /// `let`
    Let,
    /// `Type`
    Type,
    /// `Prop`
    Prop,
    /// `Region`
    Region,
}

impl Display for ReservedSymbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReservedSymbol::Arrow => write!(f, "->"),
            ReservedSymbol::DoubleArrow => write!(f, "=>"),
            ReservedSymbol::Scope => write!(f, "::"),
            ReservedSymbol::Colon => write!(f, ":"),
            ReservedSymbol::Assign => write!(f, "="),
            ReservedSymbol::Comma => write!(f, ","),
            ReservedSymbol::Pipe => write!(f, "|"),
            ReservedSymbol::Def => write!(f, "def"),
            ReservedSymbol::Fn => write!(f, "fn"),
            ReservedSymbol::Forall => write!(f, "forall"),
            ReservedSymbol::Let => write!(f, "let"),
            ReservedSymbol::Type => write!(f, "Type"),
            ReservedSymbol::Prop => write!(f, "Prop"),
            ReservedSymbol::Region => write!(f, "Region"),
        }
    }
}

/// A lexical token tree is string of input text, not enclosed in a comment or string literal, which
/// is not directly adjacent to any other non-space characters. Many of these are tokens, but some
/// token tree will need to be further split up into actual tokens. For instance, `<1>` is a
/// single token tree because it contains no spaces, but (unless `<1>` is defined as an operator
/// somewhere) it will then be converted into the tokens `<`, `1`, `>`.
///
/// A token tree is either a lexical token, a comment token, or a block enclosed in a matching pair of brackets.
/// Later, we may add string and char literals as extra variants to this enum.
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TokenTree {
    /// A token such as a variable name.
    Lexical { text: String, span: Span },
    /// A token used as an operator.
    Operator {
        text: String,
        info: OperatorInfo,
        span: Span,
    },
    /// A reserved symbol such as a language operator or a keyword.
    Reserved { symbol: ReservedSymbol, span: Span },
    /// A comment string.
    Comment { text: String, span: Span },
    /// A block enclosed in a matching pair of brackets.
    Block {
        bracket: Bracket,
        open: Span,
        close: Span,
        contents: Vec<TokenTree>,
    },
    /// The *start* of a new line.
    /// The amount of indentation at the start of this line is given.
    Newline { span: Span, indent: usize },
}

impl Display for TokenTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenTree::Lexical { text, .. } => write!(f, "'{text}'"),
            TokenTree::Operator { text, .. } => write!(f, "'{text}'"),
            TokenTree::Reserved { symbol, .. } => write!(f, "'{symbol}'"),
            TokenTree::Comment { .. } => write!(f, "comment"),
            TokenTree::Block { .. } => write!(f, "block"),
            TokenTree::Newline { .. } => write!(f, "new line"),
        }
    }
}

impl Spanned for TokenTree {
    fn span(&self) -> Span {
        match self {
            TokenTree::Lexical { span, .. } => *span,
            TokenTree::Operator { span, .. } => *span,
            TokenTree::Reserved { span, .. } => *span,
            TokenTree::Comment { span, .. } => *span,
            TokenTree::Block { open, close, .. } => Span {
                start: open.start,
                end: close.end,
            },
            TokenTree::Newline { span, .. } => *span,
        }
    }
}

/// Tokenises the input stream until the next character is `\r`, `\n`, or absent.
/// Returns the amount of leading whitespace characters on the line, then a list of things on the line.
fn tokenise_line(
    src: &SourceData,
    stream: &mut Peekable<impl Iterator<Item = (usize, char)>>,
) -> Dr<(usize, Vec<(String, Span)>)> {
    // Compute the leading whitespace of the line.
    let mut leading_whitespace = 0;
    while stream.next_if(|(_, c)| *c == ' ').is_some() {
        // This is a character of leading whitespace.
        leading_whitespace += 1;
    }

    // The main content of the line now follows.
    let mut tokens = Vec::new();
    let mut current_token = String::new();
    let mut current_token_span: Option<Span> = None;
    while let Some((index, c)) = stream.next_if(|(_, c)| *c != '\r' && *c != '\n') {
        // This is a character from the line.
        if c.is_whitespace() {
            if c == '\t' {
                return Dr::new_err(DynamicDiagnostic::new(TabError {
                    src: src.clone(),
                    span: Span {
                        start: index,
                        end: index + 1,
                    },
                }));
            }
            // The current token is finished, if indeed we just parsed one.
            if let Some(span) = current_token_span {
                tokens.push((std::mem::take(&mut current_token), span));
                current_token_span = None;
            }
        } else if ['(', ')', '[', ']', '{', '}'].contains(&c) {
            // This is a bracket character.
            // Bracket characters never mix with previous tokens.
            match current_token_span {
                Some(span) => {
                    // We just parsed a token.
                    tokens.push((std::mem::take(&mut current_token), span));
                    tokens.push((
                        c.into(),
                        Span {
                            start: index,
                            end: index + 1,
                        },
                    ));
                    current_token_span = None;
                }
                None => {
                    tokens.push((
                        c.into(),
                        Span {
                            start: index,
                            end: index + 1,
                        },
                    ));
                }
            }
        } else {
            // Append this character to the current token.
            // First, update the span information on the current token.
            match &mut current_token_span {
                Some(span) => {
                    span.end = index + 1;
                }
                None => {
                    // This was the first character in the current token.
                    current_token_span = Some(Span {
                        start: index,
                        end: index + 1,
                    });
                }
            }
            current_token.push(c);
        }
    }

    if let Some(span) = current_token_span {
        tokens.push((std::mem::take(&mut current_token), span));
    }

    Dr::new((leading_whitespace, tokens))
}

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq)]
#[error("tabs should be converted into spaces")]
#[help("explicit spaces are preferred to tab characters because the parser is whitespace-sensitive, and inconsistent use of tabs and spaces can cause ambiguity")]
struct TabError {
    #[source_code]
    src: SourceData,
    #[label("tab character was found here")]
    span: Span,
}

/// We opened a bracket that must be closed by a matching bracket.
#[derive(Debug)]
struct StackEntry {
    bracket: Bracket,
    span: Span,
}

struct Stack<'a> {
    src: &'a SourceData,
    /// The base list of token trees that we will return at the end.
    result: Vec<TokenTree>,
    stack: Vec<(StackEntry, Vec<TokenTree>)>,
}

impl<'a> Stack<'a> {
    fn push(&mut self, entry: StackEntry) {
        self.stack.push((entry, Vec::new()));
    }

    fn pop(&mut self) -> Option<(StackEntry, Vec<TokenTree>)> {
        self.stack.pop()
    }

    /// Push this token tree to the top stack entry.
    fn push_top(&mut self, tt: TokenTree) {
        match self.stack.last_mut() {
            Some((_, tokens)) => tokens.push(tt),
            None => self.result.push(tt),
        }
    }

    fn pop_bracket(&mut self, bracket: Bracket, span: Span) -> Dr<()> {
        match self.pop() {
            Some((
                StackEntry {
                    bracket: found_bracket,
                    span: found_span,
                },
                contents,
            )) => {
                if bracket == found_bracket {
                    // We combine the tokens in the stack into a single token tree.
                    self.push_top(TokenTree::Block {
                        bracket,
                        open: found_span,
                        close: span,
                        contents,
                    });
                    Dr::new(())
                } else {
                    Dr::new_err(DynamicDiagnostic::new(IncorrectBracket {
                        src: self.src.clone(),
                        span,
                        expected: found_bracket,
                        actual: bracket,
                    }))
                }
            }
            None => Dr::new_err(DynamicDiagnostic::new(UnmatchedClosingBracket {
                src: self.src.clone(),
                span,
            })),
        }
    }
}

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq)]
#[error("found incorrect bracket")]
struct IncorrectBracket {
    #[source_code]
    src: SourceData,
    #[label("expected a closing {expected}, but found a closing {actual}")]
    span: Span,
    expected: Bracket,
    actual: Bracket,
}

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq)]
#[error("found unmatched closing bracket")]
struct UnmatchedClosingBracket {
    #[source_code]
    src: SourceData,
    #[label("this closing bracket did not pair with an opening bracket")]
    span: Span,
}

/// Splits the input stream up into token trees.
/// The [`TokenTree::Operator`] and [`TokenTree::Reserved`] variants do not appear in the returned token trees;
/// the `Parser` manages splitting up the [`TokenTree::Lexical`] tokens into these.
pub fn tokenise(
    src: &SourceData,
    stream: impl Iterator<Item = char>,
) -> Dr<Vec<TokenTree>, DynamicDiagnostic, DynamicDiagnostic> {
    let mut stream = stream.enumerate().peekable();
    let mut diagnostics = Vec::new();

    // The stack of open brackets and indentations.
    let mut stack = Stack {
        src,
        result: Vec::new(),
        stack: Vec::new(),
    };

    let mut previous_newline_span = Span { start: 0, end: 0 };

    // Peek at the next character in the stream.
    loop {
        let (result, _) = tokenise_line(src, &mut stream).destructure();
        let (indent, tokens) = match result {
            Ok(result) => result,
            Err(err) => {
                diagnostics.push(err);
                break;
            }
        };

        stack.push_top(TokenTree::Newline {
            span: previous_newline_span,
            indent,
        });

        // If there are no tokens on the line, just ignore the line entirely.
        if tokens.first().is_none() {
            // Consume the newline character at the end of the line.
            let mut consumed_anything = false;
            while stream.next_if(|(_, c)| *c == '\r' || *c == '\n').is_some() {
                consumed_anything = true;
            }
            if consumed_anything {
                continue;
            } else {
                break;
            }
        };

        // Operate on each token on the line.
        for (token, span) in tokens {
            match token.as_str() {
                "(" => stack.push(StackEntry {
                    bracket: Bracket::Paren,
                    span,
                }),
                "[" => stack.push(StackEntry {
                    bracket: Bracket::Square,
                    span,
                }),
                "{" => stack.push(StackEntry {
                    bracket: Bracket::Brace,
                    span,
                }),
                ")" => {
                    if let (Err(err), _) = stack.pop_bracket(Bracket::Paren, span).destructure() {
                        diagnostics.push(err);
                    }
                }
                "]" => {
                    if let (Err(err), _) = stack.pop_bracket(Bracket::Square, span).destructure() {
                        diagnostics.push(err);
                    }
                }
                "}" => {
                    if let (Err(err), _) = stack.pop_bracket(Bracket::Brace, span).destructure() {
                        diagnostics.push(err);
                    }
                }
                _ => stack.push_top(TokenTree::Lexical { text: token, span }),
            }
        }

        // Consume the newline(s), or we're at the end of the file.
        let mut span: Option<Span> = None;
        while let Some((index, _)) = stream.next_if(|(_, c)| *c == '\r' || *c == '\n') {
            match &mut span {
                Some(span) => span.end = index + 1,
                None => {
                    span = Some(Span {
                        start: index,
                        end: index + 1,
                    })
                }
            }
        }
        match span {
            Some(span) => {
                previous_newline_span = Span {
                    start: span.end,
                    end: span.end + 1,
                }
            }
            None => {
                // We must be at the end of the file.
                break;
            }
        }
    }

    if diagnostics.is_empty() {
        // There were no errors emitted so far.
        if let Some((last, _)) = stack.stack.last() {
            diagnostics.push(DynamicDiagnostic::new(UnmatchedOpeningBracket {
                src: src.clone(),
                span: last.span,
            }))
        }

        if stream.next().is_some() {
            todo!()
        }
    }

    Dr::new(stack.result).with_many(diagnostics)
}

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq)]
#[error("found unmatched opening bracket")]
struct UnmatchedOpeningBracket {
    #[source_code]
    src: SourceData,
    #[label("this opening bracket did not pair with a closing bracket")]
    span: Span,
}
