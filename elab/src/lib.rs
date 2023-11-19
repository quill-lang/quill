use std::{collections::BTreeMap, fmt::Display};

use diagnostic::{miette, Dr};
use files::{SourceData, Span};
use internment::Intern;
use parse::{
    kind::PKind,
    lex::QualifiedName,
    ty::{FunctionKind, PRegion, PType, PTypeBinder},
};
use thiserror::Error;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Metakind(u32);

impl Display for Metakind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?k{}", self.0)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Metavariable(u32);

impl Display for Metavariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{}", self.0)
    }
}

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
    /// A kind metavariable.
    Metakind { index: Metakind },
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

impl Kind {
    pub fn to_pkind(&self) -> PKind {
        match self {
            Kind::Type => PKind::Type(Span::default()),
            Kind::Constructor { argument, result } => PKind::Constructor {
                argument: Box::new(argument.to_pkind()),
                result: Box::new(result.to_pkind()),
            },
            Kind::Metakind { index } => PKind::Metakind {
                span: Span::default(),
                name: index.to_string(),
            },
        }
    }
}

impl Display for Kind {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_pkind())
    }
}

impl Region {
    pub fn to_pregion(&self) -> PRegion {
        match self {
            Region::Variable { name } => PRegion::Variable {
                span: Span::default(),
                name: *name,
            },
            Region::Static => PRegion::Static(Span::default()),
            Region::Meet { left, right } => PRegion::Meet {
                left: Box::new(left.to_pregion()),
                right: Box::new(right.to_pregion()),
            },
        }
    }
}

impl Display for Region {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_pregion())
    }
}

impl Type {
    pub fn to_ptype(&self) -> PType {
        match self {
            Type::Variable { name } => PType::Variable {
                name: QualifiedName {
                    module: Vec::new(),
                    name: *name,
                },
                span: Span::default(),
            },
            Type::QualifiedName { name } => PType::Variable {
                name: name.clone(),
                span: Span::default(),
            },
            Type::Prop => PType::Prop(Span::default()),
            Type::Borrow { region, ty } => PType::Borrow {
                borrow: Span::default(),
                region: region.as_ref().map(|region| region.to_pregion()),
                ty: Box::new(ty.to_ptype()),
            },
            Type::Function {
                kind,
                argument,
                region,
                result,
            } => PType::Function {
                kind: *kind,
                argument: Box::new(argument.to_ptype()),
                region: region.as_ref().map(|region| region.to_pregion()),
                arrow_token: Span::default(),
                result: Box::new(result.to_ptype()),
            },
            Type::Apply { left, right } => PType::Apply {
                left: Box::new(left.to_ptype()),
                right: Box::new(right.to_ptype()),
            },
            Type::Polymorphic {
                variable,
                variable_kind,
                result,
            } => PType::Polymorphic {
                token: Span::default(),
                binders: vec![PTypeBinder {
                    variable: *variable,
                    variable_span: Span::default(),
                    variable_kind: Some(variable_kind.to_pkind()),
                }],
                result: Box::new(result.to_ptype()),
            },
            Type::Polyregion { variable, result } => PType::Polyregion {
                token: Span::default(),
                variable: *variable,
                variable_span: Span::default(),
                result: Box::new(result.to_ptype()),
            },
            Type::Metavariable { index } => PType::Variable {
                name: QualifiedName {
                    module: Vec::new(),
                    name: index.to_string().into(),
                },
                span: Span::default(),
            },
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_ptype())
    }
}

pub struct Elaborator {
    pub src: SourceData,
    next_metakind: Metakind,
    next_metavariable: Metavariable,

    /// The value of each metakind.
    metakind_assignments: BTreeMap<Metakind, Kind>,
    /// The value of each metavariable.
    metavariable_assignments: BTreeMap<Metavariable, Type>,
}

impl Elaborator {
    pub fn new(src: SourceData) -> Self {
        Self {
            src,
            next_metakind: Metakind(0),
            next_metavariable: Metavariable(0),
            metakind_assignments: BTreeMap::new(),
            metavariable_assignments: BTreeMap::new(),
        }
    }

    pub fn new_raw_metakind(&mut self) -> Metakind {
        let result = self.next_metakind;
        self.next_metakind.0 += 1;
        result
    }

    pub fn new_metakind(&mut self) -> Kind {
        Kind::Metakind {
            index: self.new_raw_metakind(),
        }
    }

    pub fn new_raw_metavariable(&mut self) -> Metavariable {
        let result = self.next_metavariable;
        self.next_metavariable.0 += 1;
        result
    }

    pub fn new_metavariable(&mut self) -> Type {
        Type::Metavariable {
            index: self.new_raw_metavariable(),
        }
    }

    pub fn instantiate_metakinds(&self, kind: &mut Kind) {
        match kind {
            Kind::Type => {}
            Kind::Constructor { argument, result } => todo!(),
            Kind::Metakind { index } => {
                if let Some(replacement) = self.metakind_assignments.get(index) {
                    *kind = replacement.clone();
                    // This recursive call should never loop
                    // because of the occurs check performed when we add a metavariable assignment.
                    self.instantiate_metakinds(kind)
                }
            }
        }
    }

    pub fn instantiate_metavariables(&self, ty: &mut Type) {
        match ty {
            Type::Variable { .. } | Type::QualifiedName { .. } | Type::Prop => {},
            Type::Borrow { region, ty } => todo!(),
            Type::Function {
                kind,
                argument,
                region,
                result,
            } => {
                self.instantiate_metavariables(argument);
                self.instantiate_metavariables(result);
            },
            Type::Apply { left, right } => todo!(),
            Type::Polymorphic {
                variable_kind,
                result,
                ..
            } => {
                self.instantiate_metakinds(variable_kind);
                self.instantiate_metavariables(result);
            }
            Type::Polyregion { variable, result } => todo!(),
            Type::Metavariable { index } => {
                if let Some(replacement) = self.metavariable_assignments.get(index) {
                    *ty = replacement.clone();
                    // This recursive call should never loop
                    // because of the occurs check performed when we add a metavariable assignment.
                    self.instantiate_metavariables(ty)
                }
            }
        }
    }

    /// The left kind is the found kind, and the right kind is the expected kind.
    pub fn unify_kinds(&mut self, mut left: Kind, mut right: Kind) -> Dr<(), ElabError> {
        self.instantiate_metakinds(&mut left);
        self.instantiate_metakinds(&mut right);

        match (left, right) {
            (Kind::Type, Kind::Type) => Dr::new(()),
            (Kind::Type, Kind::Constructor { argument, result }) => todo!(),
            (Kind::Constructor { argument, result }, Kind::Type) => todo!(),
            (
                Kind::Constructor {
                    argument: left_argument,
                    result: left_result,
                },
                Kind::Constructor {
                    argument: right_argument,
                    result: right_result,
                },
            ) => todo!(),
            (Kind::Metakind { index }, right) => {
                // Unify the left and right types by making the metavariable expand to the known kind.
                self.metakind_assignments.insert(index, right);
                Dr::new(())
            }
            (left, Kind::Metakind { index }) => {
                // Unify the left and right types by making the metavariable expand to the known kind.
                self.metakind_assignments.insert(index, left);
                Dr::new(())
            }
        }
    }
}

/// The set of variables currently in scope.
#[derive(Default, Debug, Clone)]
pub struct Context {
    type_variables: BTreeMap<Intern<String>, (Span, Kind)>,
}

impl Context {
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

impl Type {
    /// Determine the kind of this type, assuming it is well-typed in the given context and contains no metavariables.
    pub fn kind(&self, context: &Context) -> Kind {
        match self {
            Type::Variable { name } => context
                .type_variables
                .get(name)
                .expect("type did not occur in context")
                .1
                .clone(),
            Type::QualifiedName { name } => todo!(),
            Type::Prop | Type::Borrow { .. } | Type::Function { .. } => Kind::Type,
            Type::Apply { left, right } => todo!(),
            Type::Polymorphic {
                variable,
                variable_kind,
                result,
            } => todo!(),
            Type::Polyregion { variable, result } => todo!(),
            Type::Metavariable { index } => todo!(),
        }
    }
}

impl Elaborator {
    pub fn elaborate_kind(&mut self, kind: &PKind) -> Kind {
        match kind {
            PKind::Type(_) => Kind::Type,
            PKind::Constructor { argument, result } => Kind::Constructor {
                argument: Box::new(self.elaborate_kind(argument)),
                result: Box::new(self.elaborate_kind(result)),
            },
            PKind::Metakind { span, name } => {
                unreachable!("metakinds cannot be used in source code")
            }
        }
    }

    pub fn elaborate_region(
        &mut self,
        context: &Context,
        region: &PRegion,
    ) -> Dr<Region, ElabError> {
        todo!()
    }

    pub fn elaborate_type(&mut self, context: &Context, ty: &PType) -> Dr<Type, ElabError> {
        match ty {
            PType::Variable { name, span } => {
                if name.module.is_empty() {
                    // Check if this is a type variable in scope.
                    if let Some((_, _)) = context.type_variables.get(&name.name) {
                        return Dr::new(Type::Variable { name: name.name });
                    }
                }

                Dr::new_err(ElabError::ExpectedName {
                    src: self.src.clone(),
                    variable: name.name,
                    span: *span,
                    known: context.format_type_variables(),
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
            } => self.elaborate_type(context, argument).bind(|argument| {
                self.elaborate_type(context, result).bind(|result| {
                    region
                        .as_ref()
                        .map_or_else(
                            || Dr::new(None),
                            |region| self.elaborate_region(context, region).map(Some),
                        )
                        .bind(|region| {
                            self.unify_kinds(argument.kind(context), Kind::Type)
                                .bind(|()| self.unify_kinds(result.kind(context), Kind::Type))
                                .map(|()| Type::Function {
                                    kind: *kind,
                                    argument: Box::new(argument),
                                    region,
                                    result: Box::new(result),
                                })
                        })
                })
            }),
            PType::Apply { left, right } => todo!(),
            PType::Polymorphic {
                binders, result, ..
            } => {
                let mut variables = context.clone();
                let typed_binders = binders
                    .iter()
                    .map(|binder| {
                        (
                            binder,
                            match &binder.variable_kind {
                                Some(kind) => self.elaborate_kind(kind),
                                None => self.new_metakind(),
                            },
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
