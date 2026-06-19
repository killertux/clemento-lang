use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    iter::Peekable,
    path::PathBuf,
    rc::Rc,
};

mod ast;
mod error;

pub use ast::{AstNode, AstNodeType, Case, FieldPattern, Import, NameWithAlias, Pattern};
pub use error::ParserError;

use crate::lexer::{IntegerNumber, Lexer, Number, Position, Token, TokenType};
use crate::types::{LiteralType, NumberType, Type, UnitType, VarType};

pub struct Parser<'a> {
    tokens: Peekable<Lexer<'a>>,
    imports: HashSet<String>,
    /// Directories searched (in order, after the current directory) when
    /// resolving imported modules. Shared with the child parsers spawned while
    /// resolving each import.
    search_paths: Rc<[PathBuf]>,
    /// FFI C glue files discovered while resolving imports (a sibling `<name>.c`
    /// next to a resolved module). Shared with child parsers so a single list
    /// accumulates across the whole import graph; the driver links them all.
    c_sources: Rc<RefCell<Vec<PathBuf>>>,
}

impl<'a> Parser<'a> {
    #[allow(dead_code)]
    pub fn new_from_str(input: &'a str) -> Self {
        let lexer = Lexer::new(input, None);
        let tokens = lexer.peekable();
        Self {
            tokens,
            imports: HashSet::new(),
            search_paths: Rc::from(Vec::new()),
            c_sources: Rc::new(RefCell::new(Vec::new())),
        }
    }

    #[allow(dead_code)]
    pub fn new_from_file(input: &'a str, path: String) -> Self {
        Self::new_from_file_with(
            input,
            path,
            Rc::from(Vec::new()),
            Rc::new(RefCell::new(Vec::new())),
        )
    }

    /// Like [`new_from_file`], but threads the import search paths and the shared
    /// FFI C-source collector (so recursively-parsed imports share both).
    pub fn new_from_file_with(
        input: &'a str,
        path: String,
        search_paths: Rc<[PathBuf]>,
        c_sources: Rc<RefCell<Vec<PathBuf>>>,
    ) -> Self {
        let lexer = Lexer::new(input, Some(path));
        let tokens = lexer.peekable();
        Self {
            tokens,
            imports: HashSet::new(),
            search_paths,
            c_sources,
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
                TokenType::String(string) => {
                    // A string literal is sugar for a `List<Char>`: desugar to the
                    // same cons-list the `['a' 'b' ...]` literal would build.
                    let chars = string
                        .chars()
                        .map(|c| AstNode {
                            node_type: AstNodeType::Char(c),
                            position: token.position.clone(),
                            type_definition: Some(Type::char()),
                        })
                        .collect();
                    Ok(Some(build_cons_list(
                        chars,
                        token.position,
                        Some(UnitType::Literal(LiteralType::Char)),
                    )))
                }
                TokenType::Char(c) => Ok(Some(AstNode {
                    node_type: AstNodeType::Char(c),
                    position: token.position,
                    type_definition: Some(Type::char()),
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
                TokenType::Backslash => self.parse_function_value(token.position),
                TokenType::LeftBracket => self.parse_list(token.position),
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
                | TokenType::RightArrow => Err(ParserError::UnexpectedToken(
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
                name,
                is_private,
                body: Box::new(body),
            },
            position,
            type_definition: None,
        }))
    }

    fn parse_block(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let nodes = self.parse_block_body(position.clone())?;
        Ok(Some(AstNode {
            node_type: AstNodeType::Block(nodes),
            position,
            type_definition: None,
        }))
    }

    /// Collects the words of a `{ ... }` body, consuming the closing `}`. The
    /// opening `{` must already have been consumed by the caller. Shared by
    /// regular blocks and `\{ ... }` quotations.
    fn parse_block_body(&mut self, position: Position) -> Result<Vec<AstNode>, ParserError> {
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
        Ok(nodes)
    }

    /// Parses a function value following a `\`: either `\{ ... }` (an anonymous
    /// quotation) or `\name` / `\mod::name` (a reference to a named definition).
    fn parse_function_value(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let token = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        let node_type = match token.token_type {
            TokenType::LeftBrace => AstNodeType::Quotation(self.parse_block_body(token.position)?),
            TokenType::Symbol(symbol) => AstNodeType::FunctionRef(vec![symbol]),
            TokenType::SymbolWithPath(path) => AstNodeType::FunctionRef(path),
            other => return Err(ParserError::UnexpectedToken(other, token.position)),
        };
        Ok(Some(AstNode {
            node_type,
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
        let mut var_type_map: HashMap<String, VarType> = HashMap::new();
        self.parse_type_inner(position, &mut var_type_map)
    }

    /// Parses the body of a `( ... -> ... )` stack-effect type (the opening `(`
    /// must already be consumed). Takes the surrounding `var_type_map` so nested
    /// function types share type variables with the enclosing signature.
    fn parse_type_inner(
        &mut self,
        position: &Position,
        var_type_map: &mut HashMap<String, VarType>,
    ) -> Result<Type, ParserError> {
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
            let ty = self
                .tokens
                .next()
                .map(|token| self.parse_unit_type(token?, var_type_map, true))
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
                .map(|token| self.parse_unit_type(token?, var_type_map, true))
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

        let node = crate::imports::resolve_import(
            &mut self.imports,
            name,
            functions,
            &path,
            &self.search_paths,
            &self.c_sources,
        )?;

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
        if self
            .tokens
            .next_if(|token| {
                token
                    .as_ref()
                    .map(|token| token.token_type == TokenType::LeftChevron)
                    .unwrap_or(false)
            })
            .is_some()
        {
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
        if self
            .tokens
            .next_if(|token| {
                token
                    .as_ref()
                    .map(|token| token.token_type == TokenType::LeftParen)
                    .unwrap_or(false)
            })
            .is_some()
        {
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

    /// Parses an optional `<t1 t2 ...>` generic-argument list. Returns an empty
    /// vec when the next token is not a `<`.
    fn parse_generic_args(
        &mut self,
        position: &Position,
        var_type_map: &mut HashMap<String, VarType>,
        allow_insert_new_var_type: bool,
    ) -> Result<Vec<UnitType>, ParserError> {
        let mut types = Vec::new();
        if self
            .tokens
            .next_if(|token| {
                token
                    .as_ref()
                    .map(|token| token.token_type == TokenType::LeftChevron)
                    .unwrap_or(false)
            })
            .is_some()
        {
            loop {
                let symbol = self
                    .tokens
                    .next()
                    .transpose()?
                    .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
                if matches!(symbol.token_type, TokenType::RightChevron) {
                    break;
                }
                let ty = self.parse_unit_type(symbol, var_type_map, allow_insert_new_var_type)?;
                types.push(ty);
            }
        }
        Ok(types)
    }

    fn parse_unit_type(
        &mut self,
        token: Token,
        var_type_map: &mut HashMap<String, VarType>,
        allow_insert_new_var_type: bool,
    ) -> Result<UnitType, ParserError> {
        match &token.token_type {
            TokenType::Symbol(symbol) => match symbol.as_str() {
                // `String` is sugar for `List<Char>` (assumes `std::list` is imported as `list`).
                "String" => Ok(UnitType::Custom {
                    name: vec!["list".into(), "List".into()],
                    generic_types: vec![UnitType::Literal(LiteralType::Char)],
                }),
                "Char" => Ok(UnitType::Literal(LiteralType::Char)),
                // FFI raw-pointer types (see `LiteralType::CStr`/`Ptr`).
                "CStr" => Ok(UnitType::Literal(LiteralType::CStr)),
                "Ptr" => Ok(UnitType::Literal(LiteralType::Ptr)),
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
                        let types = self.parse_generic_args(
                            &token.position,
                            var_type_map,
                            allow_insert_new_var_type,
                        )?;
                        Ok(UnitType::Custom {
                            name: vec![string.to_string()],
                            generic_types: types,
                        })
                    }
                }
            },
            TokenType::SymbolWithPath(symbol_with_path) => {
                let types = self.parse_generic_args(
                    &token.position,
                    var_type_map,
                    allow_insert_new_var_type,
                )?;
                Ok(UnitType::Custom {
                    name: symbol_with_path.clone(),
                    generic_types: types,
                })
            }
            // A nested `( ... -> ... )` is a function type used as a value type,
            // e.g. the `(I64 -> I64)` parameter in `(I64 (I64 -> I64) -> I64)`.
            TokenType::LeftParen => {
                let ty = self.parse_type_inner(&token.position, var_type_map)?;
                Ok(UnitType::Type(ty))
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
                    fields = self
                        .parse_name_with_alias(token.position.clone())?
                        .into_iter()
                        .map(|nwa| FieldPattern {
                            field: nwa.name,
                            pattern: Pattern::Wildcard(Some(nwa.alias)),
                        })
                        .collect();
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
                    fields = self
                        .parse_name_with_alias(token.position.clone())?
                        .into_iter()
                        .map(|nwa| FieldPattern {
                            field: nwa.name,
                            pattern: Pattern::Wildcard(Some(nwa.alias)),
                        })
                        .collect();
                }
                Ok((
                    Pattern::Variant {
                        variant_name: symbol,
                        fields,
                    },
                    token.position,
                ))
            }
            TokenType::LeftBracket => {
                // List/char-list pattern sugar: `[a b ... tail]`, `['a' c]`, `[]`.
                // Each element is a binding (Symbol) or a char-literal match (Char).
                let mut elements = Vec::new();
                let mut tail = None;
                loop {
                    let element_token = self
                        .tokens
                        .next()
                        .transpose()?
                        .ok_or(ParserError::UnexpectedEndOfInput(token.position.clone()))?;
                    match element_token.token_type {
                        TokenType::RightBracket => break,
                        TokenType::Symbol(spread) if spread == "..." => {
                            let tail_token = self.tokens.next().transpose()?.ok_or(
                                ParserError::UnexpectedEndOfInput(element_token.position.clone()),
                            )?;
                            let TokenType::Symbol(name) = tail_token.token_type else {
                                return Err(ParserError::UnexpectedToken(
                                    tail_token.token_type,
                                    tail_token.position,
                                ));
                            };
                            tail = Some(name);
                            assert_token_type(
                                &self.tokens.next().transpose()?.ok_or(
                                    ParserError::UnexpectedEndOfInput(tail_token.position),
                                )?,
                                TokenType::RightBracket,
                            )?;
                            break;
                        }
                        TokenType::Symbol(name) => {
                            elements.push(Pattern::Wildcard(Some(name)));
                        }
                        TokenType::Char(c) => elements.push(Pattern::Char(c)),
                        other => {
                            return Err(ParserError::UnexpectedToken(
                                other,
                                element_token.position,
                            ));
                        }
                    }
                }
                Ok((
                    desugar_list_pattern(&elements, tail.as_deref()),
                    token.position,
                ))
            }
            TokenType::Char(c) => Ok((Pattern::Char(c), token.position)),
            TokenType::String(string) => {
                // String pattern: `"abc"` (exact) or `"ab" ... rest` (prefix).
                let elements: Vec<Pattern> = string.chars().map(Pattern::Char).collect();
                let mut tail = None;
                if self
                    .tokens
                    .next_if(|t| {
                        t.as_ref()
                            .map(|t| matches!(&t.token_type, TokenType::Symbol(s) if s == "..."))
                            .unwrap_or(false)
                    })
                    .is_some()
                {
                    let tail_token = self
                        .tokens
                        .next()
                        .transpose()?
                        .ok_or(ParserError::UnexpectedEndOfInput(token.position.clone()))?;
                    let TokenType::Symbol(name) = tail_token.token_type else {
                        return Err(ParserError::UnexpectedToken(
                            tail_token.token_type,
                            tail_token.position,
                        ));
                    };
                    tail = Some(name);
                }
                Ok((
                    desugar_list_pattern(&elements, tail.as_deref()),
                    token.position,
                ))
            }
            other => Err(ParserError::UnexpectedToken(other, token.position)),
        }
    }

    fn parse_list(&mut self, position: Position) -> Result<Option<AstNode>, ParserError> {
        let mut elements = Vec::new();
        while self
            .tokens
            .peek()
            .map(|token| {
                token
                    .as_ref()
                    .map(|token| token.token_type != TokenType::RightBracket)
                    .unwrap_or(false)
            })
            .unwrap_or(false)
        {
            elements.push(
                self.parse()?
                    .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?,
            );
        }
        let token = self
            .tokens
            .next()
            .transpose()?
            .ok_or(ParserError::UnexpectedEndOfInput(position.clone()))?;
        assert_token_type(&token, TokenType::RightBracket)?;
        Ok(Some(build_cons_list(elements, position, None)))
    }
}

/// Builds a `list::List` cons-list literal from `elements` (front-to-back),
/// terminated by `list::Empty`. Shared by the `[...]` list-literal sugar and the
/// `"..."` string-literal sugar (a `String` is a `List<Char>`). Assumes
/// `std::list` is imported as `list`.
fn build_cons_list(
    elements: Vec<AstNode>,
    position: Position,
    element_type_hint: Option<UnitType>,
) -> AstNode {
    let element_type = elements
        .first()
        .and_then(|node| {
            node.type_definition
                .as_ref()
                .map(|type_definition| type_definition.push_types[0].clone())
        })
        .or(element_type_hint);
    let type_definition = element_type.as_ref().map(|ty| {
        Type::new(
            vec![],
            vec![UnitType::Custom {
                name: vec!["list".into(), "List".into()],
                generic_types: vec![ty.clone()],
            }],
        )
    });
    let mut nodes = vec![AstNode {
        node_type: AstNodeType::SymbolWithPath(vec!["list".into(), "Empty".into()]),
        position: position.clone(),
        type_definition: type_definition.clone(),
    }];
    nodes.extend(elements.into_iter().rev().flat_map(|node| {
        vec![
            node,
            AstNode {
                node_type: AstNodeType::SymbolWithPath(vec!["list".into(), "List".into()]),
                position: position.clone(),
                type_definition: element_type.as_ref().map(|ty| {
                    Type::new(
                        vec![
                            UnitType::Custom {
                                name: vec!["list".into(), "List".into()],
                                generic_types: vec![ty.clone()],
                            },
                            ty.clone(),
                        ],
                        vec![UnitType::Custom {
                            name: vec!["list".into(), "List".into()],
                            generic_types: vec![ty.clone()],
                        }],
                    )
                }),
            },
        ]
    }));
    AstNode {
        node_type: AstNodeType::Block(nodes),
        position: position.clone(),
        type_definition,
    }
}

/// Desugars a list pattern (`[e0 e1 ... tail]`) into nested `list::List` /
/// `list::Empty` variant patterns, binding each element to its name and the tail
/// (if present) to the remaining list. Mirrors the `[...]` literal sugar in
/// `parse_list` and assumes `std::list` is imported as `list`.
///
/// Each element is a sub-pattern (a `Wildcard(Some(name))` binding or a
/// `Char`/number-literal match); the tail (if present) binds the remaining list.
///
/// - `[]`            -> `list::Empty`
/// - `[... t]`       -> bind whole list to `t`
/// - `[a 'b' ... t]` -> `list::List(element a, next list::List(element 'b', next t))`
/// - `[a b]`         -> `list::List(element a, next list::List(element b, next list::Empty))`
fn desugar_list_pattern(elements: &[Pattern], tail: Option<&str>) -> Pattern {
    match elements.split_first() {
        None => match tail {
            None => Pattern::Variant {
                variant_name: vec!["list".into(), "Empty".into()],
                fields: vec![],
            },
            Some(tail) => Pattern::Wildcard(Some(tail.to_string())),
        },
        Some((head, rest)) => Pattern::Variant {
            variant_name: vec!["list".into(), "List".into()],
            fields: vec![
                FieldPattern {
                    field: "element".into(),
                    pattern: head.clone(),
                },
                FieldPattern {
                    field: "next".into(),
                    pattern: desugar_list_pattern(rest, tail),
                },
            ],
        },
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
        // A string literal desugars to a `List<Char>` cons-list (a Block).
        let input = "\"Hi\"";
        let mut parser = Parser::new_from_str(input);
        let node = parser.next().unwrap().unwrap();
        assert!(matches!(node.node_type, AstNodeType::Block(_)));
        assert_eq!(
            node.type_definition,
            Some(Type::new(
                vec![],
                vec![UnitType::Custom {
                    name: vec!["list".into(), "List".into()],
                    generic_types: vec![UnitType::Literal(LiteralType::Char)],
                }]
            ))
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
    fn test_parse_function_ref() {
        let mut parser = Parser::new_from_str("\\double");
        let node = parser.next().unwrap().unwrap();
        assert_eq!(
            node.node_type,
            AstNodeType::FunctionRef(vec!["double".into()])
        );
    }

    #[test]
    fn test_parse_function_ref_with_path() {
        let mut parser = Parser::new_from_str("\\std::double");
        let node = parser.next().unwrap().unwrap();
        assert_eq!(
            node.node_type,
            AstNodeType::FunctionRef(vec!["std".into(), "double".into()])
        );
    }

    #[test]
    fn test_parse_quotation() {
        let mut parser = Parser::new_from_str("\\{ 1i64 + }");
        let node = parser.next().unwrap().unwrap();
        let AstNodeType::Quotation(nodes) = node.node_type else {
            panic!("expected a quotation, got {:?}", node.node_type);
        };
        assert_eq!(nodes.len(), 2);
        assert_eq!(nodes[1].node_type, AstNodeType::Symbol("+".into()));
    }

    #[test]
    fn test_parse_nested_function_type_annotation() {
        // The `(I64 -> I64)` parameter is a function type used as a value type.
        let mut parser = Parser::new_from_str("(I64 (I64 -> I64) -> I64) f");
        let node = parser.next().unwrap().unwrap();
        let i64 = UnitType::Literal(LiteralType::Number(NumberType::I64));
        assert_eq!(
            node.type_definition,
            Some(Type::new(
                vec![
                    i64.clone(),
                    UnitType::Type(Type::new(vec![i64.clone()], vec![i64.clone()])),
                ],
                vec![i64],
            ))
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
                    Type::new(
                        vec![UnitType::Custom {
                            name: vec!["list".into(), "List".into()],
                            generic_types: vec![UnitType::Literal(LiteralType::Char)],
                        }],
                        vec![]
                    )
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
                            (
                                "name".into(),
                                UnitType::Custom {
                                    name: vec!["list".into(), "List".into()],
                                    generic_types: vec![UnitType::Literal(LiteralType::Char)],
                                }
                            ),
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
                            fields: vec![FieldPattern {
                                field: "val".into(),
                                pattern: Pattern::Wildcard(Some("val".into()))
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
                            fields: vec![FieldPattern {
                                field: "err".into(),
                                pattern: Pattern::Wildcard(Some("error".into()))
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

    #[test]
    fn parse_empty_list() {
        let input = "[]";
        let mut parser = Parser::new_from_str(input);
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Block(vec![AstNode {
                    node_type: AstNodeType::SymbolWithPath(vec!["list".into(), "Empty".into()]),
                    position: Position::new(1, 1, None),
                    type_definition: None
                }]),
                position: Position::new(1, 1, None),
                type_definition: None
            }))
        );
    }

    #[test]
    fn parse_list() {
        let input = "[1 2 3]";
        let mut parser = Parser::new_from_str(input);
        let list_type = UnitType::Custom {
            name: vec!["list".into(), "List".into()],
            generic_types: vec![UnitType::Literal(LiteralType::Number(NumberType::I64))],
        };
        assert_eq!(
            parser.next(),
            Some(Ok(AstNode {
                node_type: AstNodeType::Block(vec![
                    AstNode {
                        node_type: AstNodeType::SymbolWithPath(vec!["list".into(), "Empty".into()]),
                        position: Position::new(1, 1, None),
                        type_definition: Some(Type::new(vec![], vec![list_type.clone()]))
                    },
                    AstNode {
                        node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(3))),
                        position: Position::new(1, 6, None),
                        type_definition: Some(Type::new(
                            vec![],
                            vec![UnitType::Literal(LiteralType::Number(NumberType::I64))]
                        ))
                    },
                    AstNode {
                        node_type: AstNodeType::SymbolWithPath(vec!["list".into(), "List".into()]),
                        position: Position::new(1, 1, None),
                        type_definition: Some(Type::new(
                            vec![
                                list_type.clone(),
                                UnitType::Literal(LiteralType::Number(NumberType::I64))
                            ],
                            vec![list_type.clone()]
                        ))
                    },
                    AstNode {
                        node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(2))),
                        position: Position::new(1, 4, None),
                        type_definition: Some(Type::new(
                            vec![],
                            vec![UnitType::Literal(LiteralType::Number(NumberType::I64))]
                        ))
                    },
                    AstNode {
                        node_type: AstNodeType::SymbolWithPath(vec!["list".into(), "List".into()]),
                        position: Position::new(1, 1, None),
                        type_definition: Some(Type::new(
                            vec![
                                list_type.clone(),
                                UnitType::Literal(LiteralType::Number(NumberType::I64))
                            ],
                            vec![list_type.clone()]
                        ))
                    },
                    AstNode {
                        node_type: AstNodeType::Number(Number::Integer(IntegerNumber::I64(1))),
                        position: Position::new(1, 2, None),
                        type_definition: Some(Type::new(
                            vec![],
                            vec![UnitType::Literal(LiteralType::Number(NumberType::I64))]
                        ))
                    },
                    AstNode {
                        node_type: AstNodeType::SymbolWithPath(vec!["list".into(), "List".into()]),
                        position: Position::new(1, 1, None),
                        type_definition: Some(Type::new(
                            vec![
                                list_type.clone(),
                                UnitType::Literal(LiteralType::Number(NumberType::I64))
                            ],
                            vec![list_type.clone()]
                        ))
                    }
                ]),
                position: Position::new(1, 1, None),
                type_definition: Some(Type::new(vec![], vec![list_type.clone()]))
            }))
        );
    }

    /// Parses a single-arm `match` and returns that arm's (desugared) pattern.
    fn first_match_pattern(src: &str) -> Pattern {
        let mut parser = Parser::new_from_str(src);
        let node = parser.next().expect("a node").expect("no parse error");
        let AstNodeType::Match(cases) = node.node_type else {
            panic!("expected a match node");
        };
        cases.into_iter().next().expect("one case").pattern
    }

    fn list_variant(fields: Vec<FieldPattern>) -> Pattern {
        Pattern::Variant {
            variant_name: vec!["list".into(), "List".into()],
            fields,
        }
    }

    fn list_empty() -> Pattern {
        Pattern::Variant {
            variant_name: vec!["list".into(), "Empty".into()],
            fields: vec![],
        }
    }

    fn field(name: &str, pattern: Pattern) -> FieldPattern {
        FieldPattern {
            field: name.into(),
            pattern,
        }
    }

    fn bind(name: &str) -> Pattern {
        Pattern::Wildcard(Some(name.into()))
    }

    #[test]
    fn list_pattern_empty() {
        assert_eq!(first_match_pattern("match { [] -> 1i64 }"), list_empty());
    }

    #[test]
    fn list_pattern_single_is_exact() {
        // `[a]` is exact-length: element bound, tail must be Empty.
        assert_eq!(
            first_match_pattern("match { [a] -> 1i64 }"),
            list_variant(vec![
                field("element", bind("a")),
                field("next", list_empty()),
            ])
        );
    }

    #[test]
    fn list_pattern_two_exact() {
        assert_eq!(
            first_match_pattern("match { [a b] -> 1i64 }"),
            list_variant(vec![
                field("element", bind("a")),
                field(
                    "next",
                    list_variant(vec![
                        field("element", bind("b")),
                        field("next", list_empty()),
                    ])
                ),
            ])
        );
    }

    #[test]
    fn list_pattern_head_tail() {
        assert_eq!(
            first_match_pattern("match { [head ... tail] -> 1i64 }"),
            list_variant(vec![
                field("element", bind("head")),
                field("next", bind("tail")),
            ])
        );
    }

    #[test]
    fn list_pattern_two_plus_tail() {
        assert_eq!(
            first_match_pattern("match { [a b ... rest] -> 1i64 }"),
            list_variant(vec![
                field("element", bind("a")),
                field(
                    "next",
                    list_variant(vec![
                        field("element", bind("b")),
                        field("next", bind("rest")),
                    ])
                ),
            ])
        );
    }

    #[test]
    fn list_pattern_tail_only_binds_whole_list() {
        assert_eq!(
            first_match_pattern("match { [... all] -> 1i64 }"),
            bind("all")
        );
    }

    #[test]
    fn char_literal_pattern() {
        assert_eq!(
            first_match_pattern("match { 'a' -> 1i64 }"),
            Pattern::Char('a')
        );
    }

    #[test]
    fn string_pattern_exact() {
        // "ab" -> list::List('a', next list::List('b', next list::Empty))
        assert_eq!(
            first_match_pattern("match { \"ab\" -> 1i64 }"),
            list_variant(vec![
                field("element", Pattern::Char('a')),
                field(
                    "next",
                    list_variant(vec![
                        field("element", Pattern::Char('b')),
                        field("next", list_empty()),
                    ])
                ),
            ])
        );
    }

    #[test]
    fn string_pattern_prefix() {
        // "a" ... rest -> list::List('a', next rest)
        assert_eq!(
            first_match_pattern("match { \"a\" ... rest -> 1i64 }"),
            list_variant(vec![
                field("element", Pattern::Char('a')),
                field("next", bind("rest")),
            ])
        );
    }

    #[test]
    fn char_list_pattern_mixed() {
        // ['a' c ... rest] mixes a char-literal match and bindings.
        assert_eq!(
            first_match_pattern("match { ['a' c ... rest] -> 1i64 }"),
            list_variant(vec![
                field("element", Pattern::Char('a')),
                field(
                    "next",
                    list_variant(vec![
                        field("element", bind("c")),
                        field("next", bind("rest")),
                    ])
                ),
            ])
        );
    }
}
