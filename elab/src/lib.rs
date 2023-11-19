use std::collections::BTreeMap;

use diagnostic::{miette, Dr};
use files::{SourceData, Span};
use internment::Intern;
use parse::{
    kind::PKind,
    lex::QualifiedName,
    ty::{FunctionKind, PRegion, PType},
};
use thiserror::Error;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Metavariable(u32);

/// A kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Kind {
    /// The kind of types.
    Type,
    /// The kind of type constructors.
    Constructor {
        argument: Box<Kind>,
        result: Box<Kind>,
    },
}

/// A region.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Region {
    /// A region variable.
    Variable { name: Intern<String> },
    /// The static region.
    Static,
    /// The meet of two regions.
    Meet {
        left: Box<Region>,
        right: Box<Region>,
    },
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    /// A type variable.
    Variable { name: Intern<String> },
    /// A qualified name.
    QualifiedName { name: QualifiedName },
    /// The type of propositions.
    Prop,
    /// The type of borrowed values.
    Borrow {
        /// The region annotation, if one exists.
        region: Option<Region>,
        /// The type that we are borrowing.
        ty: Box<Type>,
    },
    /// The type of functions.
    Function {
        /// The way this function is handled.
        kind: FunctionKind,
        /// The argument type of the function.
        argument: Box<Type>,
        /// The region annotation, if one exists.
        region: Option<Region>,
        /// The return type of the function.
        result: Box<Type>,
    },
    /// An application of a polymorphic type.
    Apply { left: Box<Type>, right: Box<Type> },
    /// The type of values that are parametrised by type variables.
    Polymorphic {
        /// The type variable.
        variable: Intern<String>,
        variable_kind: Kind,
        /// The type of the value, which may be polymorphic over the type variable.
        result: Box<Type>,
    },
    /// The type of values that are parametrised by a region variable.
    Polyregion {
        /// The region variable.
        variable: Intern<String>,
        /// The type of the value, which may be polymorphic over the region variable.
        result: Box<Type>,
    },
    /// A metavariable.
    Metavariable { index: Metavariable },
}

/// A parsed term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A local variable.
    Variable { name: Intern<String> },
    /// A qualified name.
    QualifiedName { name: QualifiedName },
    /// The proposition that two values of the same type are equal.
    Equal { left: Box<Term>, right: Box<Term> },
    /// A borrowed value.
    Borrow {
        /// The value that we are borrowing.
        value: Box<Term>,
    },
    /// A lambda abstraction.
    Function {
        /// The way this function is handled.
        kind: FunctionKind,
        /// The argument of the function.
        argument: Intern<String>,
        /// The argument type, if it is given explicitly.
        argument_ty: Option<Type>,
        /// The return value of the function.
        result: Box<Term>,
    },
    /// A function application.
    Apply { left: Box<Term>, right: Box<Term> },
    /// A value that is parametrised by a type variable.
    Polymorphic {
        /// The type variable.
        variable: Intern<String>,
        variable_kind: Option<Kind>,
        /// The value, which may be polymorphic over the type variable.
        value: Box<Term>,
    },
    /// An instantiation of a polymorphic term.
    InstantiatePolymorphic { left: Box<Term>, right: Box<Term> },
    /// A value that is parametrised by a region variable.
    Polyregion {
        /// The region variable.
        variable: Intern<String>,
        /// The value, which may be polymorphic over the region variable.
        value: Box<Term>,
    },
    /// An instantiation of a region polymorphic term.
    InstantiatePolyregion { left: Box<Term>, right: Box<Term> },
}

/// An inference context describes the types currently assigned to each type variable.
pub struct InferContext {
    pub src: SourceData,
}

/// The set of type variables currently in scope.
#[derive(Default, Debug, Clone)]
pub struct Variables {
    type_variables: BTreeMap<Intern<String>, (Span, Kind)>,
}

impl Variables {
    pub fn format_type_variables(&self) -> Option<String> {
        if self.type_variables.is_empty() {
            None
        } else {
            Some(format!(
                "the type variables in scope are: {}",
                self.type_variables
                    .keys()
                    .map(|key| key.as_ref().to_owned())
                    .collect::<Vec<_>>()
                    .join(", "),
            ))
        }
    }
}

impl InferContext {
    pub fn elaborate_kind(&mut self, kind: &PKind) -> Kind {
        match kind {
            PKind::Type(_) => Kind::Type,
            PKind::Constructor { argument, result } => Kind::Constructor {
                argument: Box::new(self.elaborate_kind(argument)),
                result: Box::new(self.elaborate_kind(result)),
            },
        }
    }

    pub fn elaborate_region(
        &mut self,
        variables: &Variables,
        region: &PRegion,
    ) -> Dr<Region, ElabError> {
        todo!()
    }

    pub fn elaborate_type(&mut self, variables: &Variables, ty: &PType) -> Dr<Type, ElabError> {
        tracing::debug!("elaborating {ty}");
        match ty {
            PType::Variable { name, span } => {
                if name.module.is_empty() {
                    // Check if this is a type variable in scope.
                    if let Some((_, _)) = variables.type_variables.get(&name.name) {
                        return Dr::new(Type::Variable { name: name.name });
                    }
                }

                Dr::new_err(ElabError::ExpectedName {
                    src: self.src.clone(),
                    variable: name.name,
                    span: *span,
                    known: variables.format_type_variables(),
                })
            }
            PType::Prop(_) => todo!(),
            PType::Borrow { borrow, region, ty } => todo!(),
            PType::Function {
                kind,
                argument,
                region,
                result,
                ..
            } => self.elaborate_type(variables, argument).bind(|argument| {
                self.elaborate_type(variables, result).bind(|result| {
                    region
                        .as_ref()
                        .map_or_else(
                            || Dr::new(None),
                            |region| self.elaborate_region(variables, region).map(Some),
                        )
                        .map(|region| Type::Function {
                            kind: *kind,
                            argument: Box::new(argument),
                            region,
                            result: Box::new(result),
                        })
                })
            }),
            PType::Apply { left, right } => todo!(),
            PType::Polymorphic {
                binders, result, ..
            } => {
                let mut variables = variables.clone();
                let typed_binders = binders
                    .iter()
                    .map(|binder| {
                        (
                            binder,
                            binder
                                .variable_kind
                                .as_ref()
                                .map_or(Kind::Type, |kind| self.elaborate_kind(kind)),
                        )
                    })
                    .collect::<Vec<_>>();

                for (binder, kind) in &typed_binders {
                    variables
                        .type_variables
                        .insert(binder.variable, (binder.variable_span, kind.clone()));
                }

                self.elaborate_type(&variables, result).map(|result| {
                    typed_binders
                        .into_iter()
                        .rev()
                        .fold(result, |result, (binder, kind)| Type::Polymorphic {
                            variable: binder.variable,
                            variable_kind: kind,
                            result: Box::new(result),
                        })
                })
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

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq)]
pub enum ElabError {
    #[error("unknown type variable {variable}")]
    ExpectedName {
        #[source_code]
        src: SourceData,
        variable: Intern<String>,
        #[label("unknown type variable found here")]
        span: Span,
        #[help("type variables in scope are: {}")]
        known: Option<String>,
    },
}
