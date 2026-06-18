use std::{
    fmt::{Display, Formatter},
    rc::Rc,
};

use crate::types::{LiteralType, NumberType, UnitType};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Position {
    line: usize,
    column: usize,
    path: Option<Rc<String>>,
}

impl Position {
    pub fn new(line: usize, column: usize, path: Option<Rc<String>>) -> Self {
        Position { line, column, path }
    }
}

impl Default for Position {
    fn default() -> Self {
        Position::new(1, 1, None)
    }
}

impl Display for Position {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match &self.path {
            Some(path) => write!(f, "{}:{}:{}", path, self.line, self.column),
            None => write!(f, "{}:{}", self.line, self.column),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenType {
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,
    RightArrow,
    LeftChevron,
    RightChevron,
    Backslash,
    Number(Number),
    String(String),
    Char(char),
    Symbol(String),
    SymbolWithPath(Vec<String>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Number {
    Integer(IntegerNumber),
    Float(String),
}

impl Number {
    pub fn to_unit_type(&self) -> UnitType {
        match self {
            Number::Integer(IntegerNumber::U8(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::U8))
            }
            Number::Integer(IntegerNumber::U16(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::U16))
            }
            Number::Integer(IntegerNumber::U32(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::U32))
            }
            Number::Integer(IntegerNumber::U64(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::U64))
            }
            Number::Integer(IntegerNumber::U128(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::U128))
            }
            Number::Integer(IntegerNumber::I8(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::I8))
            }
            Number::Integer(IntegerNumber::I16(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::I16))
            }
            Number::Integer(IntegerNumber::I32(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::I32))
            }
            Number::Integer(IntegerNumber::I64(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::I64))
            }
            Number::Integer(IntegerNumber::I128(_)) => {
                UnitType::Literal(LiteralType::Number(NumberType::I128))
            }
            Number::Float(_) => UnitType::Literal(LiteralType::Number(NumberType::F64)),
        }
    }
}

impl Display for Number {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Number::Integer(num) => write!(f, "{}", num),
            Number::Float(num) => write!(f, "{}", num),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntegerNumber {
    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),
    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
}

impl Display for IntegerNumber {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            IntegerNumber::I8(num) => write!(f, "{}i8", num),
            IntegerNumber::I16(num) => write!(f, "{}i16", num),
            IntegerNumber::I32(num) => write!(f, "{}i32", num),
            IntegerNumber::I64(num) => write!(f, "{}i64", num),
            IntegerNumber::I128(num) => write!(f, "{}i128", num),
            IntegerNumber::U8(num) => write!(f, "{}u8", num),
            IntegerNumber::U16(num) => write!(f, "{}u16", num),
            IntegerNumber::U32(num) => write!(f, "{}u32", num),
            IntegerNumber::U64(num) => write!(f, "{}u64", num),
            IntegerNumber::U128(num) => write!(f, "{}u128", num),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub token_type: TokenType,
    pub position: Position,
}
