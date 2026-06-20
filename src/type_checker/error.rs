use thiserror::Error;

use crate::lexer::Position;
use crate::parser::Pattern;
use crate::types::{Effect, Type, UnitType};

#[derive(Debug, Error)]
pub enum TypeCheckerError {
    #[error("Type conflict at {0}: expected {1}, got {2}")]
    TypeConflict(Position, Box<UnitType>, Box<UnitType>),
    #[error(
        "Symbol {0} not found at {1} with type stack {2}. Maybe it is defined after the current position"
    )]
    SymbolNotFound(String, Position, String),
    #[error(
        "Invalid top-level stack effect {0}. An imported module must be ( -> ); the entry file must be ( -> ) or ( -> I32)"
    )]
    InvalidModuleDefinition(Box<Type>),
    #[error("Missing import {0}")]
    MissingImport(String),
    #[error("Type not found {0:?}")]
    TypeNotFound(Vec<String>),
    #[error("Match cannot infer type at {0}")]
    MatchCannotInferType(Position),
    #[error("Invalid match type {0} at {1}")]
    InvalidMatchType(UnitType, Position),
    #[error("Match wildcard not at the end at {0}")]
    MatchWildcardNotAtTheEnd(Position),
    #[error("Invalid pattern {1} for type {0} at {2}")]
    InvalidPatternForType(Box<UnitType>, Box<Pattern>, Position),
    #[error("Missing wildcard match at {0}")]
    MissingWildcardMatch(Position),
    #[error("Invalid match body at {2}. Expected {0} but got {1}")]
    InvalidMatchBody(Box<Type>, Box<Type>, Position),
    #[error("Invalid match variant {0} at {1}")]
    InvalidMatchVariant(String, Position),
    #[error("Field {0} not found in variant {1}")]
    FieldNotFoundInVariant(String, String),
    #[error("Non-exhaustive match at {0}")]
    NonExhaustiveMatch(Position),
    #[error("`apply` expects a function value on top of the stack at {0}, but got {1}")]
    ApplyOnNonFunction(Position, String),
    #[error("Effect not found {0:?}. Declare it with `effect <Name>`")]
    EffectNotFound(Vec<String>),
    #[error("Effect conflict at {0}: expected effects [{e1}], got [{e2}]", e1 = fmt_effects(.1), e2 = fmt_effects(.2))]
    EffectConflict(Position, Vec<Effect>, Vec<Effect>),
    #[error("Undeclared effect {1} at {0}. The function performs it but does not declare it (declared: [{d}])", d = fmt_effects(.2))]
    UndeclaredEffect(Position, Effect, Vec<Effect>),
}

fn fmt_effects(effects: &[Effect]) -> String {
    effects
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join(" ")
}
