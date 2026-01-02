use std::{
    collections::{HashMap, HashSet},
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
    imports: HashSet<String>,
}

impl<'a> Parser<'a> {
    #[allow(dead_code)]
    pub fn new_from_str(input: &'a str) -> Self {
        let lexer = Lexer::new(input, None);
        let tokens = lexer.peekable();
        Self {
            tokens,
            imports: HashSet::new(),
        }
    }

    pub fn new_from_file(input: &'a str, path: String) -> Self {
        let lexer = Lexer::new(input, Some(path));
        let tokens = lexer.peekable();
        Self {
            tokens,
            imports: HashSet::new(),
        }
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
                TokenType::LeftBrace => self.parse_block(token.position),
                TokenType::Symbol(symbol) => match symbol.as_str() {
                    "def" => self.parse_definition(token.position, false),
                    "defp" => self.parse_definition(token.position, true),
                    "defx" => self.parse_external_definition(token.position),
                    "import" => self.parse_import(token.position),
                    "type" => self.parse_custom_type(token.position),
                    "match" => self.parse_match(token.position),
                    _ => Ok(Some(AstNode {
                        node_type: AstNodeType::Symbol(symbol),
                        position: token.position,
                        type_definition: None,
                    })),
                },
                TokenType::LeftParen => self.parse_type_annotation(token.position),
                TokenType::SymbolWithPath(path) => Ok(Some(AstNode {
                    node_type: AstNodeType::SymbolWithPath(path),
                    position: token.position,
                    type_definition: None,
                })),
                TokenType::LeftChevron => Err(ParserError::UnexpectedToken(
                    token.token_type,
                    token.position,
                )),
                TokenType::RightChevron => Err(ParserError::UnexpectedToken(
                    token.token_type,
                    token.position,
                )),
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

    fn parse_definition(
        &mut self,
        position: Position,
        is_private: bool,
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
        let body = self
            .parse()?
            .ok_or(ParserError::UnexpectedEndOfInput(name_token.position))?;
        Ok(Some(AstNode {
            node_type: AstNodeType::Definition {
                name: name.into(),
                is_private,
                body: Box::new(body),
            },
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

    fn parse_type_annotation(
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
                .map(|token| self.parse_unit_type(token?, &mut var_type_map, true))
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
                .map(|token| self.parse_unit_type(token?, &mut var_type_map, true))
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
            node_type: AstNodeType::ExternalDefinition(name.to_string(), ty),
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
        let mut functions = Vec::new();
        if self
            .tokens
            .peek()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| token.token_type == TokenType::LeftParen)
                    .unwrap_or(false)
            })
            .unwrap_or(false)
        {
            functions = self.parse_name_with_alias(position.clone())?;
        }
        let alias = self
            .tokens
            .next_if(|next| {
                next.as_ref()
                    .map(|next| next.token_type == TokenType::Symbol("as".into()))
                    .unwrap_or(false)
            })
            .transpose()?
            .map(|_| -> Result<String, ParserError> {
                let token = self
                    .tokens
                    .next()
                    .transpose()?
                    .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
                match token.token_type {
                    TokenType::Symbol(alias) => Ok(alias),
                    token_type => Err(ParserError::UnexpectedToken(token_type, token.position)),
                }
            })
            .transpose()?;
        let path = PathBuf::from_iter(symbol.iter()).with_extension("clem");
        let path_as_string = path.display().to_string();
        let name = symbol
            .last()
            .expect("A path will always have at least one element")
            .clone();
        let name = NameWithAlias {
            name: path_as_string,
            alias: alias.unwrap_or(name),
        };

        let node = {
            if self.imports.contains(&name.name) {
                Import {
                    name,
                    functions,
                    node: None,
                }
            } else {
                let file_content = read_to_string(&path)
                    .map_err(|err| ParserError::ImportError(name.name.clone(), err.to_string()))?;

                let program = Parser::new_from_file(&file_content, name.name.clone())
                    .collect::<Result<Vec<AstNode>, ParserError>>()?;

                self.imports.insert(name.name.clone());
                Import {
                    name,
                    functions,
                    node: Some(AstNode {
                        node_type: AstNodeType::Block(program),
                        position: Position::default(),
                        type_definition: None,
                    }),
                }
            }
        };

        Ok(Some(AstNode {
            node_type: AstNodeType::Import(symbol, Box::new(node)),
            position,
            type_definition: None,
        }))
    }

    fn parse_name_with_alias(
        &mut self,
        position: Position,
    ) -> Result<Vec<NameWithAlias>, ParserError> {
        let symbol = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        assert_token_type(&symbol, TokenType::LeftParen)?;
        let mut functions = Vec::new();
        loop {
            let symbol = self
                .tokens
                .next()
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
            if symbol.token_type == TokenType::RightParen {
                break;
            }

            match symbol.token_type {
                TokenType::Symbol(name) => {
                    let alias = self
                        .tokens
                        .next_if(|next| {
                            next.as_ref()
                                .map(|next| next.token_type == TokenType::Symbol("as".into()))
                                .unwrap_or(false)
                        })
                        .transpose()?
                        .map(|_| -> Result<String, ParserError> {
                            let token = self
                                .tokens
                                .next()
                                .transpose()?
                                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
                            match token.token_type {
                                TokenType::Symbol(alias) => Ok(alias),
                                token_type => {
                                    Err(ParserError::UnexpectedToken(token_type, token.position))
                                }
                            }
                        })
                        .transpose()?;
                    functions.push(NameWithAlias {
                        name: name.to_string(),
                        alias: alias.unwrap_or(name.to_string()),
                    });
                }
                _ => {
                    return Err(ParserError::UnexpectedToken(
                        symbol.token_type.clone(),
                        position,
                    ));
                }
            }
        }
        Ok(functions)
    }

    fn parse_custom_type(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let symbol = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        let TokenType::Symbol(type_name) = symbol.token_type else {
            return Err(ParserError::UnexpectedToken(
                symbol.token_type.clone(),
                symbol.position,
            ));
        };

        let mut var_types = Vec::new();
        if let Some(_) = self.tokens.next_if(|token| {
            token
                .as_ref()
                .map(|token| token.token_type == TokenType::LeftChevron)
                .unwrap_or(false)
        }) {
            loop {
                let symbol = self
                    .tokens
                    .next()
                    .transpose()?
                    .ok_or(ParserError::UnexpectedEndOfInput(symbol.position.clone()))?;
                if matches!(symbol.token_type, TokenType::RightChevron) {
                    break;
                }
                let TokenType::Symbol(var_type_name) = symbol.token_type else {
                    return Err(ParserError::UnexpectedToken(
                        symbol.token_type.clone(),
                        symbol.position,
                    ));
                };
                if var_type_name.to_lowercase() != var_type_name {
                    return Err(ParserError::InvalidVarType(
                        var_type_name.clone(),
                        symbol.position.clone(),
                    ));
                }
                var_types.push((var_type_name.clone(), VarType::new()));
            }
        }

        assert_token_type(
            &self
                .tokens
                .next()
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?,
            TokenType::LeftBrace,
        )?;
        let mut variants = Vec::new();
        loop {
            let symbol = self
                .tokens
                .next()
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
            if matches!(symbol.token_type, TokenType::RightBrace) {
                break;
            }
            let variant =
                self.parse_variant(symbol.clone(), &mut var_types.iter().cloned().collect())?;
            if variants.iter().any(|(name, _)| name == &variant.0) {
                return Err(ParserError::DuplicateVariant(
                    variant.0.clone(),
                    symbol.position.clone(),
                ));
            }
            variants.push(variant);
        }
        Ok(Some(AstNode {
            node_type: AstNodeType::CustomType {
                name: type_name.clone(),
                generics: var_types,
                variants: variants.clone(),
            },
            position,
            type_definition: Some(Type::empty()),
        }))
    }

    fn parse_variant(
        &mut self,
        symbol: Token,
        var_types: &mut HashMap<String, VarType>,
    ) -> Result<(String, Vec<(String, UnitType)>), ParserError> {
        let TokenType::Symbol(variant_name) = symbol.token_type else {
            return Err(ParserError::UnexpectedToken(
                symbol.token_type.clone(),
                symbol.position,
            ));
        };
        let mut fields: Vec<(String, UnitType)> = Vec::new();
        if let Some(_) = self.tokens.next_if(|token| {
            token
                .as_ref()
                .map(|token| token.token_type == TokenType::LeftParen)
                .unwrap_or(false)
        }) {
            loop {
                let symbol = self
                    .tokens
                    .next()
                    .transpose()?
                    .ok_or(ParserError::UnexpectedEndOfInput(symbol.position.clone()))?;
                if matches!(symbol.token_type, TokenType::RightParen) {
                    break;
                }
                let TokenType::Symbol(field_name) = symbol.token_type else {
                    return Err(ParserError::UnexpectedToken(
                        symbol.token_type.clone(),
                        symbol.position,
                    ));
                };
                if fields.iter().any(|field| field.0 == field_name) {
                    return Err(ParserError::DuplicateField(
                        field_name.clone(),
                        symbol.position,
                    ));
                }
                let symbol = self
                    .tokens
                    .next()
                    .transpose()?
                    .ok_or(ParserError::UnexpectedEndOfInput(symbol.position.clone()))?;
                let ty = self.parse_unit_type(symbol, var_types, false)?;
                fields.push((field_name, ty));
            }
        }
        Ok((variant_name, fields))
    }

    fn parse_unit_type(
        &mut self,
        token: Token,
        var_type_map: &mut HashMap<String, VarType>,
        allow_insert_new_var_type: bool,
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
                string => {
                    if string == string.to_lowercase() {
                        if let Some(var) = var_type_map.get(string) {
                            Ok(UnitType::Var(var.clone()))
                        } else if allow_insert_new_var_type {
                            let var = VarType::new();
                            var_type_map.insert(string.to_string(), var.clone());
                            Ok(UnitType::Var(var))
                        } else {
                            Err(ParserError::InvalidVarType(
                                string.to_string(),
                                token.position,
                            ))
                        }
                    } else {
                        let mut types = Vec::new();
                        if let Some(_) = self.tokens.next_if(|token| {
                            token
                                .as_ref()
                                .map(|token| token.token_type == TokenType::LeftChevron)
                                .unwrap_or(false)
                        }) {
                            loop {
                                let symbol = self.tokens.next().transpose()?.ok_or(
                                    ParserError::UnexpectedEndOfInput(token.position.clone()),
                                )?;
                                if matches!(symbol.token_type, TokenType::RightChevron) {
                                    break;
                                }
                                let ty = self.parse_unit_type(
                                    symbol,
                                    var_type_map,
                                    allow_insert_new_var_type,
                                )?;
                                types.push(ty);
                            }
                        }
                        Ok(UnitType::Custom {
                            name: vec![string.to_string()],
                            generic_types: types,
                        })
                    }
                }
            },
            TokenType::SymbolWithPath(symbol_with_path) => {
                let mut types = Vec::new();
                if let Some(_) = self.tokens.next_if(|token| {
                    token
                        .as_ref()
                        .map(|token| token.token_type == TokenType::LeftChevron)
                        .unwrap_or(false)
                }) {
                    loop {
                        let symbol = self
                            .tokens
                            .next()
                            .transpose()?
                            .ok_or(ParserError::UnexpectedEndOfInput(token.position.clone()))?;
                        if matches!(symbol.token_type, TokenType::RightChevron) {
                            break;
                        }
                        let ty =
                            self.parse_unit_type(symbol, var_type_map, allow_insert_new_var_type)?;
                        types.push(ty);
                    }
                }
                Ok(UnitType::Custom {
                    name: symbol_with_path.clone(),
                    generic_types: types,
                })
            }
            _ => Err(ParserError::UnexpectedToken(
                token.token_type,
                token.position,
            )),
        }
    }

    fn parse_match(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        assert_token_type(
            &self
                .tokens
                .next()
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?,
            TokenType::LeftBrace,
        )?;
        let mut cases = Vec::new();
        let mut last_position = position.clone();
        while self
            .tokens
            .peek()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| token.token_type != TokenType::RightBrace)
                    .unwrap_or(false)
            })
            .unwrap_or(false)
        {
            let pattern = self.parse_pattern(last_position)?;
            last_position = pattern.1;
            let token = self
                .tokens
                .next()
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(last_position))?;
            assert_token_type(&token, TokenType::RightArrow)?;
            last_position = token.position;
            let Some(body) = self.parse()? else {
                return Err(ParserError::UnexpectedEndOfInput(last_position));
            };
            last_position = body.position.clone();
            cases.push(Case {
                pattern: pattern.0,
                body: Box::new(body),
            });
        }
        assert_token_type(
            &self
                .tokens
                .next()
                .transpose()?
                .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?,
            TokenType::RightBrace,
        )?;
        Ok(Some(AstNode {
            node_type: AstNodeType::Match(cases),
            position,
            type_definition: None,
        }))
    }

    fn parse_pattern(&mut self, position: Position) -> Result<(Pattern, Position), ParserError> {
        let token = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        match token.token_type {
            TokenType::Number(number) => Ok((Pattern::Number(number), token.position)),
            TokenType::Symbol(symbol) if symbol == "*" => {
                if let Some(as_token) = self.tokens.next_if(|token| {
                    token
                        .as_ref()
                        .map(|token| matches!(&token.token_type, TokenType::Symbol(s) if s == "as"))
                        .unwrap_or(false)
                }) {
                    let as_token = as_token?;
                    let alias_token = self
                        .tokens
                        .next()
                        .transpose()?
                        .ok_or(ParserError::UnexpectedEndOfInput(as_token.position))?;
                    let TokenType::Symbol(alias) = alias_token.token_type else {
                        return Err(ParserError::UnexpectedToken(
                            alias_token.token_type.clone(),
                            alias_token.position.clone(),
                        ));
                    };
                    return Ok((Pattern::Wildcard(Some(alias)), alias_token.position));
                }
                Ok((Pattern::Wildcard(None), token.position))
            }
            TokenType::Symbol(symbol) => {
                let mut fields = Vec::new();
                if self
                    .tokens
                    .peek()
                    .map(|token| {
                        token
                            .as_ref()
                            .map(|token| token.token_type == TokenType::LeftParen)
                            .unwrap_or(false)
                    })
                    .unwrap_or(false)
                {
                    fields = self.parse_name_with_alias(token.position.clone())?;
                }
                Ok((
                    Pattern::Variant {
                        variant_name: vec![symbol],
                        fields,
                    },
                    token.position,
                ))
            }
            TokenType::SymbolWithPath(symbol) => {
                let mut fields = Vec::new();
                if self
                    .tokens
                    .peek()
                    .map(|token| {
                        token
                            .as_ref()
                            .map(|token| token.token_type == TokenType::LeftParen)
                            .unwrap_or(false)
                    })
                    .unwrap_or(false)
                {
                    fields = self.parse_name_with_alias(token.position.clone())?;
                }
                Ok((
                    Pattern::Variant {
                        variant_name: symbol,
                        fields,
                    },
                    token.position,
                ))
            }
            other => Err(ParserError::UnexpectedToken(other, token.position)),
        }
    }
}

fn assert_token_type(token: &Token, expected_type: TokenType) -> Result<(), ParserError> {
    if token.token_type == expected_type {
        Ok(())
    } else {
        Err(ParserError::UnexpectedToken(
            token.token_type.clone(),
            token.position.clone(),
        ))
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstNodeType<T> {
    Number(Number),
    String(String),
    Symbol(String),
    SymbolWithPath(Vec<String>),
    Import(Vec<String>, Box<Import<T>>),
    Definition {
        name: String,
        is_private: bool,
        body: Box<T>,
    },
    ExternalDefinition(String, Type),
    Block(Vec<T>),
    CustomType {
        name: String,
        generics: Vec<(String, VarType)>,
        variants: Vec<(String, Vec<(String, UnitType)>)>,
    },
    Match(Vec<Case<T>>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Case<T> {
    pub pattern: Pattern,
    pub body: Box<T>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Wildcard(Option<String>),
    Number(Number),
    Variant {
        variant_name: Vec<String>,
        fields: Vec<NameWithAlias>,
    },
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Wildcard(Some(name)) => write!(f, "* as {}", name),
            Pattern::Wildcard(None) => write!(f, "*"),
            Pattern::Number(number) => write!(f, "{}", number),
            Pattern::Variant {
                variant_name,
                fields,
            } => {
                if fields.is_empty() {
                    write!(f, "{}", variant_name.join("::"))
                } else {
                    write!(
                        f,
                        "{}({})",
                        variant_name.join("::"),
                        fields
                            .iter()
                            .map(|field| {
                                if field.name == field.alias {
                                    field.name.clone()
                                } else {
                                    format!("{} as {}", field.name, field.alias)
                                }
                            })
                            .collect::<Vec<String>>()
                            .join(" ")
                    )
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Import<T> {
    pub name: NameWithAlias,
    pub functions: Vec<NameWithAlias>,
    pub node: Option<T>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NameWithAlias {
    pub name: String,
    pub alias: String,
}

impl<T> Display for AstNodeType<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNodeType::Number(number) => write!(f, "{}", number),
            AstNodeType::String(string) => write!(f, "\"{}\"", string),
            AstNodeType::Symbol(symbol) => write!(f, "{}", symbol),
            AstNodeType::SymbolWithPath(symbol) => write!(f, "{}", symbol.join("::")),
            AstNodeType::Definition {
                name: symbol,
                is_private,
                body,
            } => {
                if *is_private {
                    writeln!(f, "defp {} {}", symbol, body)
                } else {
                    writeln!(f, "def {} {}", symbol, body)
                }
            }
            AstNodeType::ExternalDefinition(symbol, ty) => writeln!(f, "defx {} {}", symbol, ty),
            AstNodeType::Import(symbol, import) => {
                write!(f, "import {}", symbol.join("::"))?;
                if import.functions.len() > 0 {
                    write!(
                        f,
                        "({})",
                        import
                            .functions
                            .iter()
                            .map(|func| {
                                if func.name != func.alias {
                                    format!("{} as {}", func.name, func.alias)
                                } else {
                                    func.name.to_string()
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(" ")
                    )?;
                }
                if import.name.alias != symbol[symbol.len() - 1] {
                    write!(f, " as {}", import.name.alias)?;
                }
                Ok(())
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
            AstNodeType::CustomType {
                name,
                generics,
                variants,
            } => {
                write!(f, "type {}", name)?;
                if !generics.is_empty() {
                    write!(f, "<")?;

                    write!(
                        f,
                        "{}",
                        generics
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>()
                            .join(" ")
                    )?;
                    write!(f, ">")?;
                }
                write!(f, " {{")?;

                let mut variants_str = Vec::new();
                for (variant, fields) in variants {
                    let mut variant_str = variant.clone();
                    if !fields.is_empty() {
                        variant_str += "(";

                        for (field, ty) in fields {
                            variant_str += &format!("{} {}", field, ty);
                        }
                        variant_str += ")";
                    }
                    variants_str.push(variant_str);
                }
                write!(f, "{}", variants_str.join(" "))?;
                write!(f, "}}")
            }
            AstNodeType::Match(cases) => {
                write!(f, "match {{")?;

                let mut case_str = Vec::new();
                for case in cases {
                    match &case.pattern {
                        Pattern::Wildcard(name) => match name {
                            Some(name) => {
                                case_str.push(format!("* as {} => {}", name, case.body));
                            }
                            None => {
                                case_str.push(format!("* => {}", case.body));
                            }
                        },
                        Pattern::Number(number) => {
                            case_str.push(format!("{} => {}", number, case.body));
                        }
                        Pattern::Variant {
                            variant_name,
                            fields,
                        } => {
                            let mut variant_str = variant_name.join("::");
                            if !fields.is_empty() {
                                variant_str += "(";

                                let mut variants = Vec::new();
                                for name_with_alias in fields {
                                    if name_with_alias.name == name_with_alias.alias {
                                        variants.push(name_with_alias.name.clone());
                                    } else {
                                        variants.push(format!(
                                            "{} as {}",
                                            name_with_alias.name, name_with_alias.alias
                                        ));
                                    }
                                }
                                variant_str = format!("({})", variants.join(" "));
                            }
                            case_str.push(format!("{} => {}", variant_str, case.body));
                        }
                    }
                }
                write!(f, "{}", case_str.join(" "))?;
                write!(f, "}}")
            }
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

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum UnitType {
    Literal(LiteralType),
    Var(VarType),
    Custom {
        name: Vec<String>,
        generic_types: Vec<UnitType>,
    },
    Type(Type),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LiteralType {
    Number(NumberType),
    String,
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
            UnitType::Var(var_type) => var_t.get_string(var_type),
            UnitType::Custom {
                name,
                generic_types,
                ..
            } => {
                if generic_types.is_empty() {
                    name.join("::")
                } else {
                    format!(
                        "{}<{}>",
                        name.join("::"),
                        generic_types
                            .iter()
                            .map(|ty| ty.to_consistent_string(var_t))
                            .collect::<Vec<String>>()
                            .join(" ")
                    )
                }
            }
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
    #[error("Invalid generic type {0} at {1}. A generic type must be lowercase")]
    InvalidVarType(String, Position),
    #[error("Duplicate field {0} at {1}")]
    DuplicateField(String, Position),
    #[error("Duplicate variant {0} at {1}")]
    DuplicateVariant(String, Position),
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
                node_type: AstNodeType::Definition {
                    name: String::from("pi"),
                    is_private: false,
                    body: Box::new(AstNode {
                        node_type: AstNodeType::Number(Number::Float("3.14".into())),
                        position: Position::new(1, 8, None),
                        type_definition: Some(Type::f64()),
                    })
                },
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn test_parse_private_definition() {
        let input = "defp pi 3.14";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Definition {
                    name: String::from("pi"),
                    is_private: true,
                    body: Box::new(AstNode {
                        node_type: AstNodeType::Number(Number::Float("3.14".into())),
                        position: Position::new(1, 9, None),
                        type_definition: Some(Type::f64()),
                    })
                },
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

    #[test]
    fn parse_simple_import() {
        let input = "import std::stack";
        let mut parser = Parser::new_from_str(input);
        let token = parser.next().unwrap().unwrap();
        let AstNodeType::Import(_, import_node) = token.node_type.clone() else {
            panic!("Expected Import node type");
        };
        assert_eq!(
            token,
            AstNode {
                node_type: AstNodeType::Import(
                    vec!["std".into(), "stack".into()],
                    Box::new(Import {
                        name: NameWithAlias {
                            name: "std/stack.clem".into(),
                            alias: "stack".into()
                        },
                        functions: vec![],
                        node: import_node.node,
                    })
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }
        );
    }

    #[test]
    fn parse_simple_import_with_alias() {
        let input = "import std::stack as stack_op";
        let mut parser = Parser::new_from_str(input);
        let token = parser.next().unwrap().unwrap();
        let AstNodeType::Import(_, import_node) = token.node_type.clone() else {
            panic!("Expected Import node type");
        };
        assert_eq!(
            token,
            AstNode {
                node_type: AstNodeType::Import(
                    vec!["std".into(), "stack".into()],
                    Box::new(Import {
                        name: NameWithAlias {
                            name: "std/stack.clem".into(),
                            alias: "stack_op".into()
                        },
                        functions: vec![],
                        node: import_node.node,
                    })
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }
        );
    }

    #[test]
    fn parse_simple_import_with_functions() {
        let input = "import std::stack(dup pop)";
        let mut parser = Parser::new_from_str(input);
        let token = parser.next().unwrap().unwrap();
        let AstNodeType::Import(_, import_node) = token.node_type.clone() else {
            panic!("Expected Import node type");
        };
        assert_eq!(
            token,
            AstNode {
                node_type: AstNodeType::Import(
                    vec!["std".into(), "stack".into()],
                    Box::new(Import {
                        name: NameWithAlias {
                            name: "std/stack.clem".into(),
                            alias: "stack".into()
                        },
                        functions: vec![
                            NameWithAlias {
                                name: "dup".into(),
                                alias: "dup".into()
                            },
                            NameWithAlias {
                                name: "pop".into(),
                                alias: "pop".into()
                            }
                        ],
                        node: import_node.node,
                    })
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }
        );
    }

    #[test]
    fn parse_simple_import_with_functions_with_alias() {
        let input = "import std::stack(dup as dup_alias pop as pop_alias) as stack_alias";
        let mut parser = Parser::new_from_str(input);
        let token = parser.next().unwrap().unwrap();
        let AstNodeType::Import(_, import_node) = token.node_type.clone() else {
            panic!("Expected Import node type");
        };
        assert_eq!(
            token,
            AstNode {
                node_type: AstNodeType::Import(
                    vec!["std".into(), "stack".into()],
                    Box::new(Import {
                        name: NameWithAlias {
                            name: "std/stack.clem".into(),
                            alias: "stack_alias".into()
                        },
                        functions: vec![
                            NameWithAlias {
                                name: "dup".into(),
                                alias: "dup_alias".into()
                            },
                            NameWithAlias {
                                name: "pop".into(),
                                alias: "pop_alias".into()
                            }
                        ],
                        node: import_node.node,
                    })
                ),
                position: Position::new(1, 1, None),
                type_definition: None,
            }
        );
    }

    #[test]
    fn parse_boolean_type() {
        let input = "type Boolean { True False }";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::CustomType {
                    name: "Boolean".into(),
                    generics: Vec::new(),
                    variants: vec![("True".into(), vec![]), ("False".into(), vec![])]
                },
                position: Position::new(1, 1, None),
                type_definition: Some(Type::empty()),
            }))
        );
    }

    #[test]
    fn parse_option_type() {
        let input = "type Option<a> { Some(value a) None }";
        let mut parser = Parser::new_from_str(input);
        let node = parser.next();
        let generics = node
            .as_ref()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| {
                        let AstNodeType::CustomType { generics, .. } = &token.node_type else {
                            panic!("Unexpected token")
                        };
                        generics
                    })
                    .unwrap()
            })
            .unwrap();
        let var_type = generics.iter().find(|g| g.0 == "a").unwrap().clone().1;
        assert_eq!(
            node,
            Some(Ok(AstNode {
                node_type: AstNodeType::CustomType {
                    name: "Option".into(),
                    generics: vec![("a".into(), var_type.clone())],
                    variants: vec![
                        (
                            "Some".into(),
                            vec![("value".into(), UnitType::Var(var_type))]
                        ),
                        ("None".into(), vec![])
                    ]
                },
                position: Position::new(1, 1, None),
                type_definition: Some(Type::empty()),
            }))
        );
    }

    #[test]
    fn parse_result_type() {
        let input = "type Result<val err> { Ok(value val) Err(error err) }";
        let mut parser = Parser::new_from_str(input);
        let node = parser.next();
        let generics = node
            .as_ref()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| {
                        let AstNodeType::CustomType { generics, .. } = &token.node_type else {
                            panic!("Unexpected token")
                        };
                        generics
                    })
                    .unwrap()
            })
            .unwrap();
        let val = generics.iter().find(|g| g.0 == "val").unwrap().clone().1;
        let err = generics.iter().find(|g| g.0 == "err").unwrap().clone().1;
        assert_eq!(
            node,
            Some(Ok(AstNode {
                node_type: AstNodeType::CustomType {
                    name: "Result".into(),
                    generics: vec![
                        ("val".to_string(), val.clone()),
                        ("err".to_string(), err.clone())
                    ],
                    variants: vec![
                        ("Ok".into(), vec![("value".into(), UnitType::Var(val))]),
                        ("Err".into(), vec![("error".into(), UnitType::Var(err))])
                    ]
                },
                position: Position::new(1, 1, None),
                type_definition: Some(Type::empty()),
            }))
        );
    }

    #[test]
    fn parse_record() {
        let input = "type User { User(name String age U32) }";
        let mut parser = Parser::new_from_str(input);

        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::CustomType {
                    name: "User".into(),
                    generics: Vec::new(),
                    variants: vec![(
                        "User".into(),
                        vec![
                            ("name".into(), UnitType::Literal(LiteralType::String)),
                            (
                                "age".into(),
                                UnitType::Literal(LiteralType::Number(NumberType::U32))
                            )
                        ]
                    ),]
                },
                position: Position::new(1, 1, None),
                type_definition: Some(Type::empty()),
            }))
        );
    }

    #[test]
    fn parse_empty_match() {
        let input = "match {}";
        let mut parser = Parser::new_from_str(input);

        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Match(vec![]),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn parse_match_with_numbers() {
        let input = "match { 1 -> 2 3 -> { 4 } }";
        let mut parser = Parser::new_from_str(input);

        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Match(vec![
                    Case {
                        pattern: Pattern::Number(Number::Integer(IntegerNumber::I64(1))),
                        body: Box::new(AstNode {
                            node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(2))),
                            position: Position::new(1, 14, None),
                            type_definition: Some(Type::i64()),
                        })
                    },
                    Case {
                        pattern: Pattern::Number(Number::Integer(IntegerNumber::I64(3))),
                        body: Box::new(AstNode {
                            node_type: AstNodeType::Block(vec![AstNode {
                                node_type: AstNodeType::Number(Number::Integer(
                                    IntegerNumber::I64(4)
                                )),
                                position: Position::new(1, 23, None),
                                type_definition: Some(Type::i64()),
                            }]),
                            position: Position::new(1, 21, None),
                            type_definition: None,
                        })
                    }
                ]),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn parse_match_with_wildcard_and_no_alias() {
        let input = "match { * -> 1 }";
        let mut parser = Parser::new_from_str(input);

        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Match(vec![Case {
                    pattern: Pattern::Wildcard(None),
                    body: Box::new(AstNode {
                        node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(1))),
                        position: Position::new(1, 14, None),
                        type_definition: Some(Type::i64()),
                    })
                },]),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn parse_match_with_wildcard_with_alias() {
        let input = "match { * as n -> n }";
        let mut parser = Parser::new_from_str(input);

        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Match(vec![Case {
                    pattern: Pattern::Wildcard(Some("n".to_string())),
                    body: Box::new(AstNode {
                        node_type: AstNodeType::Symbol("n".to_string()),
                        position: Position::new(1, 19, None),
                        type_definition: None,
                    })
                },]),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn parse_match_boolean() {
        let input = "match { True -> 1 False -> 0 }";
        let mut parser = Parser::new_from_str(input);

        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Match(vec![
                    Case {
                        pattern: Pattern::Variant {
                            variant_name: vec!["True".into()],
                            fields: vec![]
                        },
                        body: Box::new(AstNode {
                            node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(1))),
                            position: Position::new(1, 17, None),
                            type_definition: Some(Type::i64()),
                        })
                    },
                    Case {
                        pattern: Pattern::Variant {
                            variant_name: vec!["False".into()],
                            fields: vec![]
                        },
                        body: Box::new(AstNode {
                            node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(0))),
                            position: Position::new(1, 28, None),
                            type_definition: Some(Type::i64()),
                        })
                    }
                ]),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }

    #[test]
    fn parse_match_result() {
        let input = "match { Ok(val) -> 1 Err(err as error) -> 0 }";
        let mut parser = Parser::new_from_str(input);

        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Match(vec![
                    Case {
                        pattern: Pattern::Variant {
                            variant_name: vec!["Ok".into()],
                            fields: vec![NameWithAlias {
                                name: "val".into(),
                                alias: "val".into()
                            }]
                        },
                        body: Box::new(AstNode {
                            node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(1))),
                            position: Position::new(1, 20, None),
                            type_definition: Some(Type::i64()),
                        })
                    },
                    Case {
                        pattern: Pattern::Variant {
                            variant_name: vec!["Err".into()],
                            fields: vec![NameWithAlias {
                                name: "err".into(),
                                alias: "error".into()
                            }]
                        },
                        body: Box::new(AstNode {
                            node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(0))),
                            position: Position::new(1, 43, None),
                            type_definition: Some(Type::i64()),
                        })
                    }
                ]),
                position: Position::new(1, 1, None),
                type_definition: None,
            }))
        );
    }
}
