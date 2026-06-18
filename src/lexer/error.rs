use thiserror::Error;

use super::token::Position;

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum LexerError {
    #[error("Unexpected token {0} at {1}")]
    UnexpectedToken(String, Position),
    #[error("Unexpected end of input at {0}")]
    UnexpectedEndOfInput(Position),
    #[error("Invalid number {0} at {1}")]
    InvalidNumber(String, Position),
}
