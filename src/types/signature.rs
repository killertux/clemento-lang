use std::sync::atomic::{AtomicU64, Ordering};

use super::unit_type::{LiteralType, NumberType, UnitType};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type {
    pub pop_types: Vec<UnitType>,
    pub push_types: Vec<UnitType>,
    /// The side effects this signature performs. Effects are a compile-time-only
    /// dimension of a function's type: they never occupy the stack and have no
    /// runtime representation. An empty list means "pure".
    ///
    /// v1 shape rule: this is either all `Effect::Named` (a concrete set),
    /// exactly one `Effect::Var` (a polymorphic effect row), or exactly one
    /// `Effect::Wildcard` (`!*`, any effects). No mixing.
    pub effects: Vec<Effect>,
}

/// A side effect annotated in a signature with the `!` sigil (e.g. `!IO`).
/// Treated like a type with no value associated to it.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Effect {
    /// A concrete, declared effect, e.g. `!IO` → `["IO"]`, `!std::io::IO` →
    /// `["std", "io", "IO"]`. Resolved to its canonical path by the checker.
    Named(Vec<String>),
    /// An effect variable, e.g. `!a` — a polymorphic effect row that can be
    /// threaded from a function-value input to a combinator's output.
    Var(VarType),
    /// `!*` — the any-effects wildcard. Matches/accepts any effect set without
    /// binding; a function declaring it on its own output is possibly-effectful.
    Wildcard,
}

static VAR_TYPE: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct VarType {
    identifier: u64,
}

impl VarType {
    pub fn new() -> Self {
        let id = VAR_TYPE.fetch_add(1, Ordering::SeqCst);
        VarType { identifier: id }
    }
}

impl Type {
    pub fn new(pop_types: Vec<UnitType>, push_types: Vec<UnitType>) -> Self {
        Type {
            pop_types,
            push_types,
            effects: vec![],
        }
    }

    pub fn with_effects(
        pop_types: Vec<UnitType>,
        push_types: Vec<UnitType>,
        effects: Vec<Effect>,
    ) -> Self {
        Type {
            pop_types,
            push_types,
            effects,
        }
    }

    pub fn u8() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
        )
    }

    pub fn u16() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::U16))],
        )
    }

    pub fn u32() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::U32))],
        )
    }

    pub fn u64() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::U64))],
        )
    }

    pub fn u128() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::U128))],
        )
    }

    pub fn i8() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::I8))],
        )
    }

    pub fn i16() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::I16))],
        )
    }

    pub fn i32() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::I32))],
        )
    }

    pub fn i64() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::I64))],
        )
    }

    pub fn i128() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::I128))],
        )
    }
    pub fn f64() -> Self {
        Self::new(
            vec![],
            vec![UnitType::Literal(LiteralType::Number(NumberType::F64))],
        )
    }

    pub fn char() -> Self {
        Self::new(vec![], vec![UnitType::Literal(LiteralType::Char)])
    }

    pub(crate) fn empty() -> Self {
        Self::new(vec![], vec![])
    }
}
