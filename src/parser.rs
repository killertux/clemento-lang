use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
    iter::Peekable,
    sync::atomic::{AtomicU64, Ordering},
};

use thiserror::Error;

use crate::lexer::{IntegerNumber, Lexer, LexerError, Number, Position, TokenType};

pub struct Parser<'a> {
    tokens: Peekable<Lexer<'a>>,
}

impl<'a> Parser<'a> {
    #[allow(dead_code)]
    pub fn new_from_str(input: &'a str) -> Self {
        let lexer = Lexer::new(input, None);
        let tokens = lexer.peekable();
        Self { tokens }
    }

    pub fn new_from_file(input: &'a str, path: String) -> Self {
        let lexer = Lexer::new(input, Some(path));
        let tokens = lexer.peekable();
        Self { tokens }
    }

    pub fn parse(&mut self) -> Result<Option<AstNode>, ParserError> {
        match self.tokens.next().transpose()? {
            Some(token) => match token.token_type {
                TokenType::Number(num) => Ok(Some(AstNode {
                    type_definition: Some(match &num {
                        Number::Integer(IntegerNumber::U8(_)) => Type::u8(),
                        Number::Integer(IntegerNumber::U16(_)) => Type::u16(),
                        Number::Integer(IntegerNumber::U32(_)) => Type::u32(),
                        Number::Integer(IntegerNumber::U64(_)) => Type::u64(),
                        Number::Integer(IntegerNumber::U128(_)) => Type::u128(),
                        Number::Integer(IntegerNumber::I8(_)) => Type::i8(),
                        Number::Integer(IntegerNumber::I16(_)) => Type::i16(),
                        Number::Integer(IntegerNumber::I32(_)) => Type::i32(),
                        Number::Integer(IntegerNumber::I64(_)) => Type::i64(),
                        Number::Integer(IntegerNumber::I128(_)) => Type::i128(),
                        Number::Float(_) => Type::f64(),
                    }),
                    node_type: AstNodeType::Number(num),
                    position: token.position,
                })),
                TokenType::String(string) => Ok(Some(AstNode {
                    node_type: AstNodeType::String(string),
                    position: token.position,
                    type_definition: Some(Type::string()),
                })),
                TokenType::Boolean(boolean) => Ok(Some(AstNode {
                    node_type: AstNodeType::Boolean(boolean),
                    position: token.position,
                    type_definition: Some(Type::boolean()),
                })),
                TokenType::LeftBrace => self.parse_block(token.position),
                TokenType::Symbol(symbol) => match symbol.as_str() {
                    "def" => self.parse_definition(token.position),
                    "if" => self.parse_if(token.position),
                    _ => Ok(Some(AstNode {
                        node_type: AstNodeType::Symbol(symbol),
                        position: token.position,
                        type_definition: None,
                    })),
                },
                TokenType::LeftParen => self.parse_type_definition(token.position),
                todo => todo!("{:?}", todo),
            },
            None => Ok(None),
        }
    }

    fn parse_definition(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let name_token = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        let TokenType::Symbol(name) = name_token.token_type else {
            return Err(ParserError::UnexpectedToken(
                name_token.token_type,
                position,
            ));
        };
        let body = self
            .parse()?
            .ok_or(ParserError::UnexpectedEndOfInput(name_token.position))?;
        Ok(Some(AstNode {
            node_type: AstNodeType::Definition(name, Box::new(body)),
            position,
            type_definition: None,
        }))
    }

    fn parse_block(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let mut nodes = Vec::new();
        while self
            .tokens
            .peek()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| !matches!(token.token_type, TokenType::RightBrace))
                    .unwrap_or(false)
            })
            .unwrap_or(false)
        {
            let node = self.parse()?;
            nodes.push(node.ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?);
        }
        let Some(node) = self.tokens.next().transpose()? else {
            return Err(ParserError::UnexpectedEndOfInput(position));
        };
        if !matches!(node.token_type, TokenType::RightBrace) {
            return Err(ParserError::UnexpectedToken(node.token_type, position));
        }
        Ok(Some(AstNode {
            node_type: AstNodeType::Block(nodes),
            position,
            type_definition: None,
        }))
    }

    fn parse_type_definition(
        &mut self,
        position: Position,
    ) -> Result<Option<AstNode>, ParserError> {
        let mut pop_types = Vec::new();
        let mut push_types = Vec::new();
        while self
            .tokens
            .peek()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| !matches!(token.token_type, TokenType::RightArrow))
                    .unwrap_or(false)
            })
            .unwrap_or(false)
        {
            let node = self.parse()?.and_then(parse_unit_type);
            pop_types.push(node.ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?);
        }
        let Some(_) = self.tokens.next() else {
            return Err(ParserError::UnexpectedEndOfInput(position.clone()));
        };
        while self
            .tokens
            .peek()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| !matches!(token.token_type, TokenType::RightParen))
                    .unwrap_or(false)
            })
            .unwrap_or(false)
        {
            let node = self.parse()?.and_then(parse_unit_type);
            push_types.push(node.ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?);
        }
        let Some(_) = self.tokens.next() else {
            return Err(ParserError::UnexpectedEndOfInput(position.clone()));
        };
        let node = self
            .parse()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;

        Ok(Some(AstNode {
            node_type: node.node_type,
            position: node.position,
            type_definition: Some(Type::new(pop_types, push_types)),
        }))
    }

    fn parse_if(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let true_body = self
            .parse()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        let mut false_body = None;
        if self.tokens.peek().map_or(false, |t| {
            t.as_ref()
                .map_or(false, |t| t.token_type == TokenType::Symbol("else".into()))
        }) {
            self.parse()?;
            false_body = Some(Box::new(
                self.parse()?
                    .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?,
            ));
        }

        Ok(Some(AstNode {
            node_type: AstNodeType::If(Box::new(true_body), false_body),
            position,
            type_definition: None,
        }))
    }
}

fn parse_unit_type(node: AstNode) -> Option<UnitType> {
    match node.node_type {
        AstNodeType::Symbol(symbol) => match symbol.as_str() {
            "String" => Some(UnitType::Literal(LiteralType::String)),
            "U8" => Some(UnitType::Literal(LiteralType::Number(NumberType::U8))),
            "U16" => Some(UnitType::Literal(LiteralType::Number(NumberType::U16))),
            "U32" => Some(UnitType::Literal(LiteralType::Number(NumberType::U32))),
            "U64" => Some(UnitType::Literal(LiteralType::Number(NumberType::U64))),
            "U128" => Some(UnitType::Literal(LiteralType::Number(NumberType::U128))),
            "I8" => Some(UnitType::Literal(LiteralType::Number(NumberType::I8))),
            "I16" => Some(UnitType::Literal(LiteralType::Number(NumberType::I16))),
            "I32" => Some(UnitType::Literal(LiteralType::Number(NumberType::I32))),
            "I64" => Some(UnitType::Literal(LiteralType::Number(NumberType::I64))),
            "I128" => Some(UnitType::Literal(LiteralType::Number(NumberType::I128))),
            "F64" => Some(UnitType::Literal(LiteralType::Number(NumberType::F64))),
            "Boolean" => Some(UnitType::Literal(LiteralType::Boolean)),
            _ => None,
        },
        _ => None,
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstNodeType<T> {
    Number(Number),
    String(String),
    Boolean(bool),
    Symbol(String),
    Definition(String, Box<T>),
    Block(Vec<T>),
    If(Box<T>, Option<Box<T>>),
}

impl<T> Display for AstNodeType<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNodeType::Number(number) => write!(f, "{}", number),
            AstNodeType::String(string) => write!(f, "\"{}\"", string),
            AstNodeType::Boolean(boolean) => write!(f, "{}", boolean),
            AstNodeType::Symbol(symbol) => write!(f, "{}", symbol),
            AstNodeType::Definition(symbol, body) => write!(f, "def {} {}\n", symbol, body),
            AstNodeType::If(true_body, Some(false_body)) => {
                write!(f, "if {} else {}", true_body, false_body)
            }
            AstNodeType::If(true_body, None) => {
                write!(f, "if {}", true_body)
            }
            AstNodeType::Block(nodes) => write!(
                f,
                "{{{}}}",
                nodes
                    .iter()
                    .map(|node| node.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AstNode {
    pub node_type: AstNodeType<AstNode>,
    pub position: Position,
    pub type_definition: Option<Type>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type {
    pub pop_types: Vec<UnitType>,
    pub push_types: Vec<UnitType>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum UnitType {
    Literal(LiteralType),
    Var(VarType),
    Type(Type),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LiteralType {
    Number(NumberType),
    String,
    Boolean,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum NumberType {
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
    F64,
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

pub struct VarTypeToCharContainer {
    map: HashMap<VarType, char>,
    current_char: char,
}

impl VarTypeToCharContainer {
    pub fn new() -> Self {
        VarTypeToCharContainer {
            map: HashMap::new(),
            current_char: 'a',
        }
    }

    pub fn get_string(&mut self, var_type: &VarType) -> String {
        if let Some(c) = self.map.get(var_type) {
            return c.to_string();
        }
        self.map.insert(var_type.clone(), self.current_char);
        let return_string = self.current_char.to_string();
        self.current_char = (self.current_char as u8 + 1) as char;
        return_string
    }
}

impl UnitType {
    pub fn to_consistent_string(&self, var_t: &mut VarTypeToCharContainer) -> String {
        match self {
            UnitType::Literal(LiteralType::Number(NumberType::U8)) => "U8".into(),
            UnitType::Literal(LiteralType::Number(NumberType::U16)) => "U16".into(),
            UnitType::Literal(LiteralType::Number(NumberType::U32)) => "U32".into(),
            UnitType::Literal(LiteralType::Number(NumberType::U64)) => "U64".into(),
            UnitType::Literal(LiteralType::Number(NumberType::U128)) => "U128".into(),
            UnitType::Literal(LiteralType::Number(NumberType::I8)) => "I8".into(),
            UnitType::Literal(LiteralType::Number(NumberType::I16)) => "I16".into(),
            UnitType::Literal(LiteralType::Number(NumberType::I32)) => "I32".into(),
            UnitType::Literal(LiteralType::Number(NumberType::I64)) => "I64".into(),
            UnitType::Literal(LiteralType::Number(NumberType::I128)) => "I128".into(),
            UnitType::Literal(LiteralType::Number(NumberType::F64)) => "F64".into(),
            UnitType::Literal(LiteralType::String) => "String".into(),
            UnitType::Literal(LiteralType::Boolean) => "Boolean".into(),
            UnitType::Var(var_type) => var_t.get_string(var_type),
            UnitType::Type(ty) => {
                format!("{}", ty)
            }
        }
    }
}

impl Display for UnitType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.to_consistent_string(&mut VarTypeToCharContainer::new())
        )
    }
}

impl Type {
    pub fn new(pop_types: Vec<UnitType>, push_types: Vec<UnitType>) -> Self {
        Type {
            pop_types,
            push_types,
        }
    }

    pub fn u8() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
        }
    }

    pub fn u16() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::U16))],
        }
    }

    pub fn u32() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::U32))],
        }
    }

    pub fn u64() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::U64))],
        }
    }

    pub fn u128() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::U128))],
        }
    }

    pub fn i8() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::I8))],
        }
    }

    pub fn i16() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::I16))],
        }
    }

    pub fn i32() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::I32))],
        }
    }

    pub fn i64() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::I64))],
        }
    }

    pub fn i128() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::I128))],
        }
    }
    pub fn f64() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Number(NumberType::F64))],
        }
    }

    pub fn string() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::String)],
        }
    }

    pub fn boolean() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Boolean)],
        }
    }

    pub(crate) fn empty() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![],
        }
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut var_t_container = VarTypeToCharContainer::new();
        write!(
            f,
            "({} -> {})",
            self.pop_types
                .iter()
                .map(|t| t.to_consistent_string(&mut var_t_container))
                .collect::<Vec<String>>()
                .join(", "),
            self.push_types
                .iter()
                .map(|t| t.to_consistent_string(&mut var_t_container))
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}

#[derive(Debug, PartialEq, Eq, Error)]
pub enum ParserError {
    #[error(transparent)]
    LexerError(#[from] LexerError),
    #[error("Unexpected token {0:?} at {1}")]
    UnexpectedToken(TokenType, Position),
    #[error("Unexpected end of input at {0}")]
    UnexpectedEndOfInput(Position),
}

impl<'a> Iterator for Parser<'a> {
    type Item = Result<AstNode, ParserError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.parse().transpose()
    }
}

#[cfg(test)]
mod tests {
    use crate::lexer::IntegerNumber;

    use super::*;

    #[test]
    fn test_parse_number() {
        let input = "5";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(5))),
                position: Position::new(1, 1, None),
                type_definition: Some(Type::i64()),
            }))
        );
    }

    #[test]
    fn test_parse_string() {
        let input = "\"Hello\"";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::String(String::from("Hello")),
                position: Position::new(1, 1, None),
                type_definition: Some(Type::string()),
            }))
        );
    }

    #[test]
    fn test_parse_symbol() {
        let input = "hello";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Symbol(String::from("hello")),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_definition() {
        let input = "def pi 3.14";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Definition(
                    "pi".into(),
                    Box::new(AstNode {
                        node_type: AstNodeType::Number(Number::Float("3.14".into())),
                        position: Position::new(1, 8, None),
                        type_definition: Some(Type::f64()),
                    })
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_incomplete_definition() {
        let input1 = "def";
        let input2 = "def pi";
        let err1 = Parser::new_from_str(input1).next();
        let err2 = Parser::new_from_str(input2).next();
        assert_eq!(
            err1,
            Some(Err(ParserError::UnexpectedEndOfInput(Position::new(
                1, 1, None
            )))),
        );
        assert_eq!(
            err2,
            Some(Err(ParserError::UnexpectedEndOfInput(Position::new(
                1, 5, None
            )))),
        );
    }

    #[test]
    fn test_parse_block() {
        let input = "{ hello }";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Block(vec![AstNode {
                    node_type: AstNodeType::Symbol(String::from("hello")),
                    position: Position::new(1, 3, None),
                    type_definition: None,
                }]),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_if_simple() {
        let input = "if true";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::Boolean(true),
                        position: Position::new(1, 4, None),
                        type_definition: Some(Type::boolean()),
                    }),
                    None
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_if_with_number() {
        let input = "if 42";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(42))),
                        position: Position::new(1, 4, None),
                        type_definition: Some(Type::i64()),
                    }),
                    None
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_if_with_block() {
        let input = "if { hello world }";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::Block(vec![
                            AstNode {
                                node_type: AstNodeType::Symbol(String::from("hello")),
                                position: Position::new(1, 6, None),
                                type_definition: None,
                            },
                            AstNode {
                                node_type: AstNodeType::Symbol(String::from("world")),
                                position: Position::new(1, 12, None),
                                type_definition: None,
                            }
                        ]),
                        position: Position::new(1, 4, None),
                        type_definition: None,
                    }),
                    None
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_if_else_simple() {
        let input = "if true else false";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::Boolean(true),
                        position: Position::new(1, 4, None),
                        type_definition: Some(Type::boolean()),
                    }),
                    Some(Box::new(AstNode {
                        node_type: AstNodeType::Boolean(false),
                        position: Position::new(1, 14, None),
                        type_definition: Some(Type::boolean()),
                    }))
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_if_else_with_numbers() {
        let input = "if 1 else 0";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(1))),
                        position: Position::new(1, 4, None),
                        type_definition: Some(Type::i64()),
                    }),
                    Some(Box::new(AstNode {
                        node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(0))),
                        position: Position::new(1, 11, None),
                        type_definition: Some(Type::i64()),
                    }))
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_if_else_with_blocks() {
        let input = "if { print \"true\" } else { print \"false\" }";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::Block(vec![
                            AstNode {
                                node_type: AstNodeType::Symbol(String::from("print")),
                                position: Position::new(1, 6, None),
                                type_definition: None,
                            },
                            AstNode {
                                node_type: AstNodeType::String(String::from("true")),
                                position: Position::new(1, 12, None),
                                type_definition: Some(Type::string()),
                            }
                        ]),
                        position: Position::new(1, 4, None),
                        type_definition: None,
                    }),
                    Some(Box::new(AstNode {
                        node_type: AstNodeType::Block(vec![
                            AstNode {
                                node_type: AstNodeType::Symbol(String::from("print")),
                                position: Position::new(1, 28, None),
                                type_definition: None,
                            },
                            AstNode {
                                node_type: AstNodeType::String(String::from("false")),
                                position: Position::new(1, 34, None),
                                type_definition: Some(Type::string()),
                            }
                        ]),
                        position: Position::new(1, 26, None),
                        type_definition: None,
                    }))
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_nested_if() {
        let input = "if if true else false else false";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::If(
                            Box::new(AstNode {
                                node_type: AstNodeType::Boolean(true),
                                position: Position::new(1, 7, None),
                                type_definition: Some(Type::boolean()),
                            }),
                            Some(Box::new(AstNode {
                                node_type: AstNodeType::Boolean(false),
                                position: Position::new(1, 17, None),
                                type_definition: Some(Type::boolean()),
                            }))
                        ),
                        position: Position::new(1, 4, None),
                        type_definition: None,
                    }),
                    Some(Box::new(AstNode {
                        node_type: AstNodeType::Boolean(false),
                        position: Position::new(1, 28, None),
                        type_definition: Some(Type::boolean()),
                    }))
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_if_incomplete() {
        let input = "if";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Err(ParserError::UnexpectedEndOfInput(Position::new(
                1, 1, None
            ))))
        );
    }

    #[test]
    fn test_parse_if_else_incomplete() {
        let input = "if true else";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Err(ParserError::UnexpectedEndOfInput(Position::new(
                1, 1, None
            ))))
        );
    }

    #[test]
    fn test_parse_if_with_string_body() {
        let input = "if \"hello\"";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::If(
                    Box::new(AstNode {
                        node_type: AstNodeType::String(String::from("hello")),
                        position: Position::new(1, 4, None),
                        type_definition: Some(Type::string()),
                    }),
                    None
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }
}
