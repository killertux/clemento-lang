use std::{
    iter::Peekable,
    rc::Rc,
    str::{Chars, FromStr},
};

use super::error::LexerError;
use super::token::{IntegerNumber, Number, Position, Token, TokenType};

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
    line: usize,
    column: usize,
    path: Option<Rc<String>>,
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
            Some('\'') => self.lex_char(),
            Some('(') => Ok(Some(self.create_token_here(TokenType::LeftParen))),
            Some(')') => Ok(Some(self.create_token_here(TokenType::RightParen))),
            Some('{') => Ok(Some(self.create_token_here(TokenType::LeftBrace))),
            Some('}') => Ok(Some(self.create_token_here(TokenType::RightBrace))),
            Some('[') => Ok(Some(self.create_token_here(TokenType::LeftBracket))),
            Some(']') => Ok(Some(self.create_token_here(TokenType::RightBracket))),
            Some('<') => Ok(Some(self.create_token_here(TokenType::LeftChevron))),
            Some('>') => Ok(Some(self.create_token_here(TokenType::RightChevron))),
            // `\` introduces a function value: `\name` (reference) or `\{ ... }`
            // (anonymous quotation). It is always its own token.
            Some('\\') => Ok(Some(self.create_token_here(TokenType::Backslash))),
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

    fn lex_char(&mut self) -> Result<Option<Token>, LexerError> {
        let position = Position::new(self.line, self.column, self.path.clone());
        let value = match self.advance() {
            Some('\\') => match self.advance() {
                Some('\\') => '\\',
                Some('\'') => '\'',
                Some('"') => '"',
                Some('n') => '\n',
                Some('t') => '\t',
                Some('r') => '\r',
                Some('0') => '\0',
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
            Some('\'') => {
                return Err(LexerError::UnexpectedToken("''".into(), position));
            }
            Some(c) => c,
            None => return Err(LexerError::UnexpectedEndOfInput(position)),
        };
        match self.advance() {
            Some('\'') => Ok(Some(Token {
                token_type: TokenType::Char(value),
                position,
            })),
            Some(c) => Err(LexerError::UnexpectedToken(
                c.to_string(),
                Position::new(self.line, self.column, self.path.clone()),
            )),
            None => Err(LexerError::UnexpectedEndOfInput(position)),
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
                    Some('r') => string.push('\r'),
                    Some('0') => string.push('\0'),
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
            let hint = NumberTypeHint::from_str(&number_as_string);
            let digits = match hint {
                Some(h) => &number_as_string[2..number_as_string.len() - h.suffix_len()],
                None => &number_as_string[2..],
            };
            // Without a suffix, hex literals default to U64 (matching decimals' I64 default).
            let integer = match hint {
                Some(h) => h.parse_radix(digits, 16, &number_as_string, position.clone())?,
                None => IntegerNumber::U64(u64::from_str_radix(digits, 16).map_err(|_| {
                    LexerError::InvalidNumber(number_as_string.clone(), position.clone())
                })?),
            };

            return Ok(Some(Token {
                token_type: TokenType::Number(Number::Integer(integer)),
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
        // Entered with the opening `/` already consumed and `*` as the next char.
        self.advance(); // consume the opening `*`
        let mut depth = 1;
        while depth > 0 {
            match self.advance() {
                Some('/') if self.input.peek().is_some_and(|c| *c == '*') => {
                    self.advance(); // consume the `*` of a nested `/*`
                    depth += 1;
                }
                Some('*') if self.input.peek().is_some_and(|c| *c == '/') => {
                    self.advance(); // consume the closing `/`
                    depth -= 1;
                }
                Some(_) => {}
                None => break, // unterminated comment: stop gracefully
            }
        }
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

    /// Byte length of this hint's suffix (e.g. `u8` -> 2, `i128` -> 4).
    fn suffix_len(&self) -> usize {
        match self {
            NumberTypeHint::U8 | NumberTypeHint::I8 => 2,
            NumberTypeHint::U16
            | NumberTypeHint::U32
            | NumberTypeHint::U64
            | NumberTypeHint::I16
            | NumberTypeHint::I32
            | NumberTypeHint::I64 => 3,
            NumberTypeHint::U128 | NumberTypeHint::I128 => 4,
        }
    }

    /// Parses `digits` (already stripped of any type suffix) in the given radix
    /// into the integer type named by this hint.
    fn parse_radix(
        &self,
        digits: &str,
        radix: u32,
        original: &str,
        position: Position,
    ) -> Result<IntegerNumber, LexerError> {
        let err = || LexerError::InvalidNumber(original.to_string(), position.clone());
        Ok(match self {
            NumberTypeHint::U8 => {
                IntegerNumber::U8(u8::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::U16 => {
                IntegerNumber::U16(u16::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::U32 => {
                IntegerNumber::U32(u32::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::U64 => {
                IntegerNumber::U64(u64::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::U128 => {
                IntegerNumber::U128(u128::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::I8 => {
                IntegerNumber::I8(i8::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::I16 => {
                IntegerNumber::I16(i16::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::I32 => {
                IntegerNumber::I32(i32::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::I64 => {
                IntegerNumber::I64(i64::from_str_radix(digits, radix).map_err(|_| err())?)
            }
            NumberTypeHint::I128 => {
                IntegerNumber::I128(i128::from_str_radix(digits, radix).map_err(|_| err())?)
            }
        })
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
    c.is_whitespace() || matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | '<' | '>' | '\\')
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Result<Token, LexerError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.lex().transpose()
    }
}
