use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
    fs::read_to_string,
    iter::Peekable,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use thiserror::Error;

use crate::lexer::{IntegerNumber, Lexer, LexerError, Number, Position, Token, TokenType};

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
                    "defx" => self.parse_external_definition(token.position),
                    "if" => self.parse_if(token.position),
                    "import" => self.parse_import(token.position),
                    _ => Ok(Some(AstNode {
                        node_type: AstNodeType::Symbol(symbol),
                        position: token.position,
                        type_definition: None,
                    })),
                },
                TokenType::LeftParen => self.parse_type_definition(token.position),
                TokenType::SymbolWithPath(path) => Ok(Some(AstNode {
                    node_type: AstNodeType::SymbolWithPath(path),
                    position: token.position,
                    type_definition: None,
                })),
                TokenType::RightParen
                | TokenType::RightBrace
                | TokenType::RightBracket
                | TokenType::RightArrow
                | TokenType::LeftBracket => Err(ParserError::UnexpectedToken(
                    token.token_type,
                    token.position,
                )),
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
        let ty = self.parse_type(&position)?;
        let node = self
            .parse()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;

        Ok(Some(AstNode {
            node_type: node.node_type,
            position: node.position,
            type_definition: Some(ty),
        }))
    }

    fn parse_type(&mut self, position: &Position) -> Result<Type, ParserError> {
        let mut pop_types = Vec::new();
        let mut push_types = Vec::new();
        let mut var_type_map: HashMap<String, VarType> = HashMap::new();
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
            let ty = self
                .tokens
                .next()
                .map(|token| parse_unit_type(token?, &mut var_type_map))
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
            pop_types.push(ty);
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
            let ty = self
                .tokens
                .next()
                .map(|token| parse_unit_type(token?, &mut var_type_map))
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
            push_types.push(ty);
        }
        let Some(_) = self.tokens.next() else {
            return Err(ParserError::UnexpectedEndOfInput(position.clone()));
        };
        let ty = Type::new(pop_types, push_types);
        Ok(ty)
    }

    fn parse_if(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let true_body = self
            .parse()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        let mut false_body = None;
        if self.tokens.peek().is_some_and(|t| {
            t.as_ref()
                .is_ok_and(|t| t.token_type == TokenType::Symbol("else".into()))
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

    fn parse_external_definition(
        &mut self,
        position: Position,
    ) -> Result<Option<AstNode>, ParserError> {
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
        let left_paren = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        let TokenType::LeftParen = left_paren.token_type else {
            return Err(ParserError::UnexpectedToken(
                left_paren.token_type,
                position,
            ));
        };
        let ty = self.parse_type(&position)?;
        Ok(Some(AstNode {
            node_type: AstNodeType::ExternalDefinition(name, ty),
            position,
            type_definition: None,
        }))
    }

    fn parse_import(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let symbol = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        let symbol = match symbol.token_type {
            TokenType::Symbol(symbol) => vec![symbol],
            TokenType::SymbolWithPath(symbol) => symbol,
            _ => return Err(ParserError::UnexpectedToken(symbol.token_type, position)),
        };

        let paths = if symbol.last().is_some_and(|last| last == "*") {
            let dir = PathBuf::from_iter(symbol.iter().take(symbol.len() - 1));
            let mut paths = Vec::new();
            for entry in std::fs::read_dir(&dir).map_err(|err| {
                ParserError::ImportError(dir.display().to_string(), err.to_string())
            })? {
                let entry = entry.map_err(|err| {
                    ParserError::ImportError(dir.display().to_string(), err.to_string())
                })?;
                if entry
                    .file_type()
                    .map_err(|err| {
                        ParserError::ImportError(dir.display().to_string(), err.to_string())
                    })?
                    .is_file()
                {
                    paths.push(entry.path().with_extension("clem"));
                }
            }
            paths
        } else {
            vec![PathBuf::from_iter(symbol.iter()).with_extension("clem")]
        };

        let mut nodes = Vec::new();
        for path in paths {
            let path_as_string = path.display().to_string();
            let file_content = read_to_string(&path)
                .map_err(|err| ParserError::ImportError(path_as_string.clone(), err.to_string()))?;

            let program = Parser::new_from_file(&file_content, path_as_string)
                .collect::<Result<Vec<AstNode>, ParserError>>()?;
            nodes.push(AstNode {
                node_type: AstNodeType::Block(program),
                position: Position::default(),
                type_definition: None,
            });
        }

        Ok(Some(AstNode {
            node_type: AstNodeType::Import(symbol, nodes),
            position,
            type_definition: None,
        }))
    }
}

fn parse_unit_type(
    token: Token,
    var_type_map: &mut HashMap<String, VarType>,
) -> Result<UnitType, ParserError> {
    match &token.token_type {
        TokenType::Symbol(symbol) => match symbol.as_str() {
            "String" => Ok(UnitType::Literal(LiteralType::String)),
            "U8" => Ok(UnitType::Literal(LiteralType::Number(NumberType::U8))),
            "U16" => Ok(UnitType::Literal(LiteralType::Number(NumberType::U16))),
            "U32" => Ok(UnitType::Literal(LiteralType::Number(NumberType::U32))),
            "U64" => Ok(UnitType::Literal(LiteralType::Number(NumberType::U64))),
            "U128" => Ok(UnitType::Literal(LiteralType::Number(NumberType::U128))),
            "I8" => Ok(UnitType::Literal(LiteralType::Number(NumberType::I8))),
            "I16" => Ok(UnitType::Literal(LiteralType::Number(NumberType::I16))),
            "I32" => Ok(UnitType::Literal(LiteralType::Number(NumberType::I32))),
            "I64" => Ok(UnitType::Literal(LiteralType::Number(NumberType::I64))),
            "I128" => Ok(UnitType::Literal(LiteralType::Number(NumberType::I128))),
            "F64" => Ok(UnitType::Literal(LiteralType::Number(NumberType::F64))),
            "Boolean" => Ok(UnitType::Literal(LiteralType::Boolean)),
            string => {
                if string == string.to_lowercase() {
                    if let Some(var) = var_type_map.get(string) {
                        Ok(UnitType::Var(var.clone()))
                    } else {
                        let var = VarType::new();
                        var_type_map.insert(string.to_string(), var.clone());
                        Ok(UnitType::Var(var))
                    }
                } else {
                    Err(ParserError::UnexpectedToken(
                        token.token_type,
                        token.position,
                    ))
                }
            }
        },
        _ => Err(ParserError::UnexpectedToken(
            token.token_type,
            token.position,
        )),
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstNodeType<T> {
    Number(Number),
    String(String),
    Boolean(bool),
    Symbol(String),
    SymbolWithPath(Vec<String>),
    Import(Vec<String>, Vec<T>),
    Definition(String, Box<T>),
    ExternalDefinition(String, Type),
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
            AstNodeType::SymbolWithPath(symbol) => write!(f, "{}", symbol.join("::")),
            AstNodeType::Definition(symbol, body) => writeln!(f, "def {} {}", symbol, body),
            AstNodeType::ExternalDefinition(symbol, ty) => writeln!(f, "defx {} {}", symbol, ty),
            AstNodeType::Import(symbol, _) => write!(f, "import {}", symbol.join("::")),
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
                .join(" "),
            self.push_types
                .iter()
                .map(|t| t.to_consistent_string(&mut var_t_container))
                .collect::<Vec<String>>()
                .join(" ")
        )
    }
}

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

    #[test]
    fn test_parse_external_definition() {
        let input = "defx println (String ->)";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::ExternalDefinition(
                    "println".into(),
                    Type::new(vec![UnitType::Literal(LiteralType::String)], vec![])
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }
}
