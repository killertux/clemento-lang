use inkwell::builder::BuilderError;
use thiserror::Error;

use crate::lexer::Position;
use crate::parser::ParserError;
use crate::type_checker::TypeCheckerError;
use crate::types::UnitType;

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error(transparent)]
    Parser(#[from] ParserError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    TypeChecker(#[from] TypeCheckerError),
    #[error("Failed to write LLVM IR to file: {0}")]
    WriteLLVMError(String),
    #[error("Stack underflow")]
    StackUnderflow,
    #[error("Builder error: {0}")]
    BuilderError(#[from] BuilderError),
    #[error("Failed to get function: {0}")]
    GetFunctionError(String),
    #[error("Undefined symbol: {0}")]
    UndefinedSymbol(String),
    #[error("Invalid stack for function {0}")]
    InvalidStackForFunction(String),
    #[error("Function call error")]
    FunctionCallError,
    #[error("Unexpected type")]
    UnexpectedType,
    #[error("If statement without function")]
    IfWithoutFunction,
    #[error("Invalid import type at {0}")]
    InvalidImportType(Position),
    #[error("Import not found")]
    ImportNotFound,
    #[error("Unsupported type")]
    UnsupportedType(UnitType),
    #[error("Unsupported pattern in match")]
    UnsupportedPattern,
    #[error("Custom type not found in scope")]
    TypeNotInScope,
    #[error("Variant {0} not found in custom type")]
    VariantNotFound(String),
    #[error(
        "Cannot take a reference to `{0}`: only user `def`s can be used as function values (builtins and constructors emit inline code)"
    )]
    CannotReferenceFunction(String),
    #[error(
        "Cannot determine a concrete type for function value `{0}`: its type still has unresolved type variables. Apply it (or annotate it) so its type can be inferred."
    )]
    UnresolvedFunctionValue(String),
}
