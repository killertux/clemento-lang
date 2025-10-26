use std::{
    fmt::{Display, Formatter},
    iter::Peekable,
    rc::Rc,
    str::{Chars, FromStr},
};

use thiserror::Error;

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    line: usize,
    column: usize,
    path: Option<Rc<String>>,
}

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
    Number(Number),
    String(String),
    Boolean(bool),
    Symbol(String),
    SymbolWithPath(Vec<String>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Number {
    Integer(IntegerNumber),
    Float(String),
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

#[derive(Debug, Error, Clone, PartialEq, Eq)]
pub enum LexerError {
    #[error("Unexpected token {0} at {1}")]
    UnexpectedToken(String, Position),
    #[error("Unexpected end of input at {0}")]
    UnexpectedEndOfInput(Position),
    #[error("Invalid number {0} at {1}")]
    InvalidNumber(String, Position),
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str, path: Option<String>) -> Self {
        Lexer {
            input: input.chars().peekable(),
            line: 1,
            column: 0,
            path: path.map(Rc::new),
        }
    }

    fn lex(&mut self) -> Result<Option<Token>, LexerError> {
        match self.advance() {
            Some('"') => self.lex_string(),
            Some('(') => Ok(Some(self.create_token_here(TokenType::LeftParen))),
            Some(')') => Ok(Some(self.create_token_here(TokenType::RightParen))),
            Some('{') => Ok(Some(self.create_token_here(TokenType::LeftBrace))),
            Some('}') => Ok(Some(self.create_token_here(TokenType::RightBrace))),
            Some('[') => Ok(Some(self.create_token_here(TokenType::LeftBracket))),
            Some(']') => Ok(Some(self.create_token_here(TokenType::RightBracket))),
            Some('/') if self.input.peek().is_some_and(|c| *c == '/') => {
                self.lex_single_line_comment()
            }
            Some('/') if self.input.peek().is_some_and(|c| *c == '*') => {
                self.lex_multi_line_comment()
            }
            Some('-') if self.input.peek().is_some_and(|c| c.is_numeric()) => self.lex_number('-'),
            Some('-') if self.input.peek().is_some_and(|c| *c == '>') => {
                let position = Position::new(self.line, self.column, self.path.clone());
                assert!(self.advance() == Some('>'), "We checked for a '>' before");
                Ok(Some(Token {
                    token_type: TokenType::RightArrow,
                    position,
                }))
            }
            Some(x) if x.is_whitespace() => self.lex(),
            Some(x) if x.is_numeric() => self.lex_number(x),
            Some(x) => self.lex_symbol(x),
            None => Ok(None),
        }
    }

    fn advance(&mut self) -> Option<char> {
        self.column += 1;
        match self.input.next() {
            Some('\n') => {
                self.line += 1;
                self.column = 0;
                self.advance()
            }
            Some(c) => Some(c),
            None => None,
        }
    }

    fn create_token_here(&mut self, token_type: TokenType) -> Token {
        Token {
            token_type,
            position: Position::new(self.line, self.column, self.path.clone()),
        }
    }

    fn lex_string(&mut self) -> Result<Option<Token>, LexerError> {
        let mut string = String::new();
        let position = Position::new(self.line, self.column, self.path.clone());
        while let Some(c) = self.advance() {
            match c {
                '"' => {
                    return Ok(Some(Token {
                        token_type: TokenType::String(string),
                        position,
                    }));
                }
                '\\' => match self.advance() {
                    Some('\\') => string.push('\\'),
                    Some('"') => string.push('"'),
                    Some('n') => string.push('\n'),
                    Some('t') => string.push('\t'),
                    Some(c) => {
                        return Err(LexerError::UnexpectedToken(
                            format!("\\{}", c),
                            Position::new(self.line, self.column - 1, self.path.clone()),
                        ));
                    }
                    None => {
                        return Err(LexerError::UnexpectedEndOfInput(Position::new(
                            self.line,
                            self.column,
                            self.path.clone(),
                        )));
                    }
                },
                c => string.push(c),
            }
        }
        Err(LexerError::UnexpectedEndOfInput(Position::new(
            self.line,
            self.column,
            self.path.clone(),
        )))
    }

    fn lex_symbol(&mut self, x: char) -> Result<Option<Token>, LexerError> {
        let mut symbol = String::new();
        let position = Position::new(self.line, self.column, self.path.clone());
        symbol.push(x);
        while self.input.peek().map(|c| !is_separator(c)).unwrap_or(false) {
            if let Some(c) = self.advance() {
                symbol.push(c);
            } else {
                return Err(LexerError::UnexpectedEndOfInput(Position::new(
                    self.line,
                    self.column,
                    self.path.clone(),
                )));
            }
        }

        if symbol == "true" || symbol == "false" {
            return Ok(Some(Token {
                token_type: TokenType::Boolean(symbol == "true"),
                position,
            }));
        }
        if symbol.contains("::") {
            let parts: Vec<&str> = symbol.split("::").collect();
            let parts = parts.iter().map(|s| s.to_string()).collect();
            return Ok(Some(Token {
                token_type: TokenType::SymbolWithPath(parts),
                position,
            }));
        }

        Ok(Some(Token {
            token_type: TokenType::Symbol(symbol),
            position,
        }))
    }

    fn lex_number(&mut self, x: char) -> Result<Option<Token>, LexerError> {
        let mut number_as_string = String::new();
        let position = Position::new(self.line, self.column, self.path.clone());
        number_as_string.push(x);
        while self.input.peek().map(|c| !is_separator(c)).unwrap_or(false) {
            if let Some(c) = self.advance() {
                if c == '_' {
                    continue;
                }
                number_as_string.push(c);
            } else {
                return Err(LexerError::UnexpectedEndOfInput(Position::new(
                    self.line,
                    self.column,
                    self.path.clone(),
                )));
            }
        }

        let is_hex = number_as_string.starts_with("0x");
        if is_hex {
            let number = u64::from_str_radix(&number_as_string[2..], 16).map_err(|_| {
                LexerError::InvalidNumber(number_as_string.clone(), position.clone())
            })?;

            return Ok(Some(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(number))),
                position,
            }));
        }

        let is_float = number_as_string.contains('.');
        if is_float {
            let number = number_as_string
                .strip_suffix("f64")
                .unwrap_or(&number_as_string);
            let _number = f64::from_str(number)
                .map_err(|_| LexerError::InvalidNumber(number.to_string(), position.clone()))?;

            return Ok(Some(Token {
                token_type: TokenType::Number(Number::Float(number.to_string())),
                position,
            }));
        }

        Ok(Some(Token {
            token_type: TokenType::Number(Number::Integer(
                NumberTypeHint::from_str(&number_as_string)
                    .map(|hint| hint.parse(&number_as_string, position.clone()))
                    .unwrap_or_else(|| {
                        Ok(IntegerNumber::I64(
                            number_as_string.as_str().parse().map_err(|_| {
                                LexerError::InvalidNumber(number_as_string, position.clone())
                            })?,
                        ))
                    })?,
            )),
            position,
        }))
    }

    fn lex_single_line_comment(&mut self) -> Result<Option<Token>, LexerError> {
        while self.input.peek().is_some_and(|c| *c != '\n') {
            self.advance();
        }
        self.lex()
    }

    fn lex_multi_line_comment(&mut self) -> Result<Option<Token>, LexerError> {
        self.advance();
        while let Some(c) = self.advance() {
            if c == '*' && self.input.peek().is_some_and(|c| *c == '/') {
                break;
            }
        }
        self.advance();
        self.lex()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum NumberTypeHint {
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
}

impl NumberTypeHint {
    fn from_str(s: &str) -> Option<Self> {
        if s.ends_with("u8") {
            Some(NumberTypeHint::U8)
        } else if s.ends_with("u16") {
            Some(NumberTypeHint::U16)
        } else if s.ends_with("u32") {
            Some(NumberTypeHint::U32)
        } else if s.ends_with("u64") {
            Some(NumberTypeHint::U64)
        } else if s.ends_with("u128") {
            Some(NumberTypeHint::U128)
        } else if s.ends_with("i8") {
            Some(NumberTypeHint::I8)
        } else if s.ends_with("i16") {
            Some(NumberTypeHint::I16)
        } else if s.ends_with("i32") {
            Some(NumberTypeHint::I32)
        } else if s.ends_with("i64") {
            Some(NumberTypeHint::I64)
        } else if s.ends_with("i128") {
            Some(NumberTypeHint::I128)
        } else {
            None
        }
    }

    fn parse(&self, s: &str, position: Position) -> Result<IntegerNumber, LexerError> {
        let is_negative = s.starts_with('-');
        if is_negative
            && matches!(
                self,
                NumberTypeHint::U8
                    | NumberTypeHint::U16
                    | NumberTypeHint::U32
                    | NumberTypeHint::U64
                    | NumberTypeHint::U128
            )
        {
            return Err(LexerError::InvalidNumber(s.to_string(), position));
        }
        match self {
            NumberTypeHint::U8 => {
                Ok(IntegerNumber::U8(s[..s.len() - 2].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::U16 => {
                Ok(IntegerNumber::U16(s[..s.len() - 3].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::U32 => {
                Ok(IntegerNumber::U32(s[..s.len() - 3].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::U64 => {
                Ok(IntegerNumber::U64(s[..s.len() - 3].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::U128 => {
                Ok(IntegerNumber::U128(s[..s.len() - 4].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::I8 => {
                Ok(IntegerNumber::I8(s[..s.len() - 2].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::I16 => {
                Ok(IntegerNumber::I16(s[..s.len() - 3].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::I32 => {
                Ok(IntegerNumber::I32(s[..s.len() - 3].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::I64 => {
                Ok(IntegerNumber::I64(s[..s.len() - 3].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
            NumberTypeHint::I128 => {
                Ok(IntegerNumber::I128(s[..s.len() - 4].parse().map_err(
                    |_| LexerError::InvalidNumber(s.to_string(), position),
                )?))
            }
        }
    }
}

fn is_separator(c: &char) -> bool {
    c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | '{' | '}')
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.lex().transpose()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_symbol() {
        let input = "hello";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn multiple_symbols() {
        let input = "hello1 hello2\nhello3";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            [
                Token {
                    token_type: TokenType::Symbol("hello1".to_string()),
                    position: Position::new(1, 1, None)
                },
                Token {
                    token_type: TokenType::Symbol("hello2".to_string()),
                    position: Position::new(1, 8, None)
                },
                Token {
                    token_type: TokenType::Symbol("hello3".to_string()),
                    position: Position::new(2, 1, None)
                },
            ]
        );
    }

    #[test]
    fn lex_string() {
        let input = "\"hello\"";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::String("hello".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_complex_string() {
        let input = r#""\tHello\nWorld.\n\\Nice \"string\"\\""#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::String("\tHello\nWorld.\n\\Nice \"string\"\\".to_string()),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn not_closed_string() {
        let input = r#""Hello"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::UnexpectedEndOfInput(Position {
                line: 1,
                column: 7,
                path: None
            })))
        );
    }

    #[test]
    fn invalid_escape() {
        let input = r#""Hello \h""#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::UnexpectedToken(
                r#"\h"#.to_string(),
                Position {
                    line: 1,
                    column: 8,
                    path: None
                }
            )))
        );
    }

    #[test]
    fn lex_parentheses() {
        let input = r#"(Hello)"#;
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::LeftParen,
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("Hello".to_string()),
                    position: Position::new(1, 2, None),
                },
                Token {
                    token_type: TokenType::RightParen,
                    position: Position::new(1, 7, None),
                }
            ]
        );
    }

    #[test]
    fn lex_braces() {
        let input = r#"{Hello}"#;
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::LeftBrace,
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("Hello".to_string()),
                    position: Position::new(1, 2, None),
                },
                Token {
                    token_type: TokenType::RightBrace,
                    position: Position::new(1, 7, None),
                }
            ]
        );
    }

    #[test]
    fn lex_brackets() {
        let input = r#"[Hello]"#;
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::LeftBracket,
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("Hello".to_string()),
                    position: Position::new(1, 2, None),
                },
                Token {
                    token_type: TokenType::RightBracket,
                    position: Position::new(1, 7, None),
                }
            ]
        );
    }

    #[test]
    fn lex_right_arrow() {
        let input = r#"->"#;
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::RightArrow,
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_positive_integer() {
        let input = "42";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(42))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_negative_integer() {
        let input = "-123";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(-123))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_float() {
        let input = "3.14";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("3.14".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_negative_float() {
        let input = "-2.5";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("-2.5".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_hex_number() {
        let input = "0xFF";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(255))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_large_hex_number() {
        let input = "0x1A2B3C4D";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(439041101))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_number_with_underscores() {
        let input = "1_000_000";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(1000000))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_float_with_underscores() {
        let input = "1_000.5_5";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("1000.55".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_zero() {
        let input = "0";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(0))),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_zero_float() {
        let input = "0.0";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Number(Number::Float("0.0".to_string())),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_multiple_numbers() {
        let input = "42 -17 3.14 0xFF";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(42))),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(-17))),
                    position: Position::new(1, 4, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Float("3.14".to_string())),
                    position: Position::new(1, 8, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(255))),
                    position: Position::new(1, 13, None),
                }
            ]
        );
    }

    #[test]
    fn lex_invalid_hex() {
        let input = "0xGHI";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::InvalidNumber(
                "0xGHI".to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_invalid_float() {
        let input = "3.14.15";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::InvalidNumber(
                "3.14.15".to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_multiple_numbers_types() {
        let input = "42u8 42u16 42u32 42u64 42u128 42i8 42i16 42i32 42i64 42i128";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U8(42))),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U16(42))),
                    position: Position::new(1, 6, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U32(42))),
                    position: Position::new(1, 12, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U64(42))),
                    position: Position::new(1, 18, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::U128(42))),
                    position: Position::new(1, 24, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I8(42))),
                    position: Position::new(1, 31, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I16(42))),
                    position: Position::new(1, 36, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I32(42))),
                    position: Position::new(1, 42, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I64(42))),
                    position: Position::new(1, 48, None),
                },
                Token {
                    token_type: TokenType::Number(Number::Integer(IntegerNumber::I128(42))),
                    position: Position::new(1, 54, None),
                }
            ]
        );
    }

    #[test]
    fn lex_number_followed_by_symbol() {
        let input = "42hello";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Err(LexerError::InvalidNumber(
                "42hello".to_string(),
                Position::new(1, 1, None)
            )))
        );
    }

    #[test]
    fn lex_dash_without_number() {
        let input = "- hello";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Symbol("-".to_string()),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("hello".to_string()),
                    position: Position::new(1, 3, None),
                }
            ]
        );
    }

    #[test]
    fn lex_single_line_comment() {
        let input = "// this is a comment";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_single_line_comment_with_code_before() {
        let input = "hello // this is a comment";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_single_line_comment_with_code_after() {
        let input = "// this is a comment\nhello";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(2, 1, None),
            }]
        );
    }

    #[test]
    fn lex_multiple_single_line_comments() {
        let input = "// comment 1\n// comment 2\nhello\n// comment 3";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(3, 1, None),
            }]
        );
    }

    #[test]
    fn lex_single_line_comment_without_newline() {
        let input = "hello // comment at end of file";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("hello".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_multi_line_comment() {
        let input = "/* this is a multi-line comment */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_multi_line_comment_spanning_lines() {
        let input = "/* this is a\n   multi-line\n   comment */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_multi_line_comment_with_code_before() {
        let input = "hello /* comment */ world";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Symbol("hello".to_string()),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("world".to_string()),
                    position: Position::new(1, 21, None),
                }
            ]
        );
    }

    #[test]
    fn lex_multi_line_comment_with_asterisks_inside() {
        let input = "/* comment with * asterisks * inside */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_mixed_comments() {
        let input = "hello // single line\n/* multi\n   line */ world";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![
                Token {
                    token_type: TokenType::Symbol("hello".to_string()),
                    position: Position::new(1, 1, None),
                },
                Token {
                    token_type: TokenType::Symbol("world".to_string()),
                    position: Position::new(3, 12, None),
                }
            ]
        );
    }

    #[test]
    fn lex_slash_without_comment() {
        let input = "a/b";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("a/b".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_single_slash() {
        let input = "/";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(
            tokens,
            vec![Token {
                token_type: TokenType::Symbol("/".to_string()),
                position: Position::new(1, 1, None),
            }]
        );
    }

    #[test]
    fn lex_comments_with_special_characters() {
        let input =
            "// comment with symbols !@#$%^&*()\n/* comment with \"quotes\" and 'apostrophes' */";
        let lexer = Lexer::new(input, None);
        let tokens = lexer
            .collect::<Result<Vec<Token>, LexerError>>()
            .expect("Failed to collect tokens");
        assert_eq!(tokens, vec![]);
    }

    #[test]
    fn lex_boolean_true() {
        let input = "true";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Boolean(true),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_boolean_false() {
        let input = "false";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::Boolean(false),
                position: Position::new(1, 1, None),
            }))
        );
    }

    #[test]
    fn lex_symbol_with_path() {
        let input = "std::std::*";
        let mut lexer = Lexer::new(input, None);
        assert_eq!(
            lexer.next(),
            Some(Ok(Token {
                token_type: TokenType::SymbolWithPath(vec!["std".into(), "std".into(), "*".into()]),
                position: Position::new(1, 1, None),
            }))
        );
    }
}
