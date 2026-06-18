use thiserror::Error;

use crate::lexer::{LexerError, Position, TokenType};

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ParserError {
    #[error("Error importing file {0}: {1}")]
    ImportError(String, String),
    #[error(transparent)]
    LexerError(#[from] LexerError),
    #[error("Unexpected token {0:?} at {1}")]
    UnexpectedToken(TokenType, Position),
    #[error("Unexpected end of input at {0}")]
    UnexpectedEndOfInput(Position),
    #[error("Invalid generic type {0} at {1}. A generic type must be lowercase")]
    InvalidVarType(String, Position),
    #[error("Duplicate field {0} at {1}")]
    DuplicateField(String, Position),
    #[error("Duplicate variant {0} at {1}")]
    DuplicateVariant(String, Position),
}
