use std::collections::BTreeMap;

use internment::Intern;
use parse::{
    lex::QualifiedName,
    term::PTerm,
    ty::{FunctionKind, PType},
};

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Metavariable(u32);

/// A kind.
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
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
#[derive(Debug, PartialEq, Eq)]
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
        variable_kind: Option<Kind>,
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
#[derive(Debug, PartialEq, Eq)]
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
pub struct InferContext {}

impl InferContext {
    pub fn elaborate_type(
        &mut self,
        variables: &BTreeMap<Intern<String>, Type>,
        ty: PType,
    ) -> Type {
        tracing::debug!("elaborating {ty}");
        todo!()
    }
}
