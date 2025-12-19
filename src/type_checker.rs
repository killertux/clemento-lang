use std::{cell::RefCell, collections::HashMap, fmt::Display, rc::Rc};

use thiserror::Error;

use crate::{
    lexer::{IntegerNumber, Number, Position},
    parser::{
        AstNode, AstNodeType, Import, LiteralType, NumberType, Type, UnitType, VarType,
        VarTypeToCharContainer,
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AstNodeWithType {
    pub node_type: AstNodeType<AstNodeWithType>,
    pub position: Position,
    pub type_definition: Type,
}

impl Display for AstNodeWithType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.type_definition, self.node_type)
    }
}

impl AstNodeWithType {
    pub fn new(
        node_type: AstNodeType<AstNodeWithType>,
        position: Position,
        type_definition: Type,
    ) -> Self {
        Self {
            node_type,
            position,
            type_definition,
        }
    }
}

pub struct TypeChecker {
    imports: HashMap<String, TypeScope>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            imports: HashMap::new(),
        }
    }

    pub fn type_check(
        &mut self,
        program: AstNode,
        check_for_main: bool,
    ) -> Result<(AstNodeWithType, TypeScope), TypeCheckerError> {
        let mut scope = TypeScope::empty();
        let AstNodeType::Block(nodes) = program.node_type else {
            return Err(TypeCheckerError::InvalidModuleDefinition(Box::new(
                Type::empty(),
            )));
        };

        let (block_type_check_result, nodes_with_types) =
            self.type_check_block(&mut scope, Vec::new(), nodes, check_for_main)?;
        if block_type_check_result != Type::empty() {
            return Err(TypeCheckerError::InvalidModuleDefinition(Box::new(
                block_type_check_result,
            )));
        }
        Ok((
            AstNodeWithType::new(
                AstNodeType::Block(nodes_with_types),
                program.position,
                block_type_check_result,
            ),
            scope,
        ))
    }

    fn type_check_block(
        &mut self,
        scope: &mut TypeScope,
        mut type_stack: Vec<UnitType>,
        program: Vec<AstNode>,
        check_for_main: bool,
    ) -> Result<(Type, Vec<AstNodeWithType>), TypeCheckerError> {
        let mut node_results = Vec::new();
        let mut pop_type_stack: Vec<UnitType> = Vec::new();
        let mut local_stack: Vec<UnitType> = Vec::new();
        for node in program {
            let node = self.infer_type_definition(scope, type_stack.clone(), node)?;
            let type_definition = &node.type_definition;
            let pop_size = type_definition.pop_types.len();
            if pop_size > type_stack.len() {
                let new_types = &type_definition.pop_types[0..(pop_size - type_stack.len())];
                type_stack = [new_types.to_vec(), type_stack.clone()].concat();
            }
            if pop_size > local_stack.len() {
                let new_types = &type_definition.pop_types[0..(pop_size - local_stack.len())];
                pop_type_stack = [new_types.to_vec(), pop_type_stack.clone()].concat();
                local_stack = [new_types.to_vec(), local_stack.clone()].concat();
            }
            let push_types = validate_and_get_push_types(
                &type_stack,
                type_definition.clone(),
                node.position.clone(),
            )?;
            type_stack.truncate(type_stack.len() - pop_size);
            type_stack.extend(push_types.clone().into_iter());
            local_stack.truncate(local_stack.len() - pop_size);
            local_stack.extend(push_types.into_iter());
            node_results.push(node);
        }

        if check_for_main && let Some(main) = scope.get_definition(vec!["main".to_string()], false)
        {
            let valid_main_definitions = [
                Type::new(vec![], vec![]),
                Type::new(
                    vec![],
                    vec![UnitType::Literal(LiteralType::Number(NumberType::I32))],
                ),
            ];
            if !valid_main_definitions.contains(&main) {
                return Err(TypeCheckerError::InvalidMainDefinition(Box::new(main)));
            }
        }
        let block_type = Type::new(pop_type_stack, local_stack);
        Ok((block_type, node_results))
    }

    fn infer_type_definition(
        &mut self,
        scope: &mut TypeScope,
        type_stack: Vec<UnitType>,
        node: AstNode,
    ) -> Result<AstNodeWithType, TypeCheckerError> {
        let type_stack = match &node.type_definition {
            Some(ty) => ty.pop_types.clone(),
            None => type_stack,
        };
        let inferred_type = match node.node_type {
            AstNodeType::Number(Number::Integer(IntegerNumber::U8(n))) => Ok(AstNodeWithType::new(
                AstNodeType::Number(Number::Integer(IntegerNumber::U8(n))),
                node.position.clone(),
                Type::u8(),
            )),
            AstNodeType::Number(Number::Integer(IntegerNumber::U16(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::U16(n))),
                    node.position.clone(),
                    Type::u16(),
                ))
            }
            AstNodeType::Number(Number::Integer(IntegerNumber::U32(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::U32(n))),
                    node.position.clone(),
                    Type::u32(),
                ))
            }
            AstNodeType::Number(Number::Integer(IntegerNumber::U64(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::U64(n))),
                    node.position.clone(),
                    Type::u64(),
                ))
            }
            AstNodeType::Number(Number::Integer(IntegerNumber::U128(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::U128(n))),
                    node.position.clone(),
                    Type::u128(),
                ))
            }
            AstNodeType::Number(Number::Integer(IntegerNumber::I8(n))) => Ok(AstNodeWithType::new(
                AstNodeType::Number(Number::Integer(IntegerNumber::I8(n))),
                node.position.clone(),
                Type::i8(),
            )),
            AstNodeType::Number(Number::Integer(IntegerNumber::I16(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::I16(n))),
                    node.position.clone(),
                    Type::i16(),
                ))
            }
            AstNodeType::Number(Number::Integer(IntegerNumber::I32(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::I32(n))),
                    node.position.clone(),
                    Type::i32(),
                ))
            }
            AstNodeType::Number(Number::Integer(IntegerNumber::I64(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::I64(n))),
                    node.position.clone(),
                    Type::i64(),
                ))
            }
            AstNodeType::Number(Number::Integer(IntegerNumber::I128(n))) => {
                Ok(AstNodeWithType::new(
                    AstNodeType::Number(Number::Integer(IntegerNumber::I128(n))),
                    node.position.clone(),
                    Type::i128(),
                ))
            }
            AstNodeType::Number(Number::Float(n)) => Ok(AstNodeWithType::new(
                AstNodeType::Number(Number::Float(n)),
                node.position.clone(),
                Type::f64(),
            )),
            AstNodeType::String(s) => Ok(AstNodeWithType::new(
                AstNodeType::String(s),
                node.position.clone(),
                Type::string(),
            )),
            AstNodeType::Boolean(bool) => Ok(AstNodeWithType::new(
                AstNodeType::Boolean(bool),
                node.position.clone(),
                Type::boolean(),
            )),
            AstNodeType::SymbolWithPath(symbol) => {
                let type_definition = scope.get_definition(symbol.clone(), false).ok_or(
                    TypeCheckerError::SymbolNotFound(symbol.join("::"), node.position.clone(), {
                        let mut var_t_container = VarTypeToCharContainer::new();
                        format!(
                            "<...{}>",
                            type_stack[type_stack.len().saturating_sub(5)..]
                                .iter()
                                .map(|t| t.to_consistent_string(&mut var_t_container))
                                .collect::<Vec<String>>()
                                .join(",")
                        )
                    }),
                )?;
                validate_type_against_type_stack(
                    &type_stack,
                    &type_definition,
                    node.position.clone(),
                )?;
                Ok(AstNodeWithType::new(
                    AstNodeType::SymbolWithPath(symbol),
                    node.position.clone(),
                    substitute_types(&type_stack, type_definition, node.position.clone())?,
                ))
            }
            AstNodeType::Symbol(symbol) => {
                let type_definition = scope.get_definition(vec![symbol.clone()], false).ok_or(
                    TypeCheckerError::SymbolNotFound(symbol.clone(), node.position.clone(), {
                        let mut var_t_container = VarTypeToCharContainer::new();
                        format!(
                            "<...{}>",
                            type_stack[type_stack.len().saturating_sub(5)..]
                                .iter()
                                .map(|t| t.to_consistent_string(&mut var_t_container))
                                .collect::<Vec<String>>()
                                .join(",")
                        )
                    }),
                )?;
                validate_type_against_type_stack(
                    &type_stack,
                    &type_definition,
                    node.position.clone(),
                )?;
                Ok(AstNodeWithType::new(
                    AstNodeType::Symbol(symbol),
                    node.position.clone(),
                    substitute_types(&type_stack, type_definition, node.position.clone())?,
                ))
            }
            AstNodeType::Block(nodes) => {
                let mut scope = TypeScope::with_parent(scope.clone());
                let (ty, nodes) =
                    self.type_check_block(&mut scope, type_stack.clone(), nodes, false)?;
                Ok(AstNodeWithType::new(
                    AstNodeType::Block(nodes),
                    node.position.clone(),
                    substitute_types(&type_stack, ty, node.position.clone())?,
                ))
            }
            AstNodeType::Definition {
                name: symbol,
                is_private,
                body,
            } => {
                let body = if let Some(ty) = body.type_definition.as_ref() {
                    // We use this to allow recursive types. We should probably create a better implementation latter
                    scope.insert_definition(symbol.clone(), ty.clone(), is_private);
                    let body = self.infer_type_definition(scope, Vec::new(), *body)?;
                    body
                } else {
                    let body = self.infer_type_definition(scope, Vec::new(), *body)?;
                    scope.insert_definition(
                        symbol.clone(),
                        body.type_definition.clone(),
                        is_private,
                    );
                    body
                };
                Ok(AstNodeWithType::new(
                    AstNodeType::Definition {
                        name: symbol,
                        is_private,
                        body: Box::new(body),
                    },
                    node.position.clone(),
                    Type::empty(),
                ))
            }
            AstNodeType::ExternalDefinition(symbol, ty) => {
                scope.insert_definition(symbol.clone(), ty.clone(), false);
                Ok(AstNodeWithType::new(
                    AstNodeType::ExternalDefinition(symbol, ty),
                    node.position.clone(),
                    Type::empty(),
                ))
            }
            AstNodeType::Import(_path, import_node) => {
                let result_node = if let Some(nodes) = import_node.node {
                    let result = self.type_check(nodes, false)?;
                    scope.insert_import(import_node.name.alias.clone(), result.1);
                    for function in &import_node.functions {
                        scope.insert_function_import(
                            function.alias.clone(),
                            function.name.clone(),
                            import_node.name.alias.clone(),
                        );
                    }

                    Import {
                        name: import_node.name,
                        functions: import_node.functions,
                        node: Some(result.0),
                    }
                } else {
                    let imported_scope = self.imports.get(&import_node.name.name).ok_or(
                        TypeCheckerError::MissingImport(import_node.name.alias.clone()),
                    )?;
                    scope.insert_import(import_node.name.alias.clone(), imported_scope.clone());
                    for function in &import_node.functions {
                        scope.insert_function_import(
                            function.alias.clone(),
                            function.name.clone(),
                            import_node.name.alias.clone(),
                        );
                    }
                    Import {
                        name: import_node.name,
                        functions: import_node.functions,
                        node: None,
                    }
                };

                Ok(AstNodeWithType::new(
                    AstNodeType::Import(_path, Box::new(result_node)),
                    node.position.clone(),
                    Type::empty(),
                ))
            }
            AstNodeType::If(true_body, false_body) => {
                let type_stack_without_last_element =
                    &type_stack[..type_stack.len().saturating_sub(1)].to_vec();
                let mut true_body = self.infer_type_definition(
                    scope,
                    type_stack_without_last_element.clone(),
                    *true_body,
                )?;
                true_body.type_definition = substitute_types(
                    type_stack_without_last_element,
                    true_body.type_definition,
                    node.position.clone(),
                )?;
                if let Some(false_body) = false_body {
                    let mut false_body = self.infer_type_definition(
                        scope,
                        type_stack_without_last_element.clone(),
                        *false_body,
                    )?;
                    false_body.type_definition = substitute_types(
                        type_stack_without_last_element,
                        false_body.type_definition,
                        node.position.clone(),
                    )?;

                    let true_push_types = validate_and_get_push_types(
                        type_stack_without_last_element,
                        true_body.type_definition.clone(),
                        true_body.position.clone(),
                    )?;
                    let false_push_types = validate_and_get_push_types(
                        type_stack_without_last_element,
                        false_body.type_definition.clone(),
                        false_body.position.clone(),
                    )?;

                    let true_type =
                        Type::new(true_body.type_definition.pop_types.clone(), true_push_types);
                    let false_type = Type::new(
                        false_body.type_definition.pop_types.clone(),
                        false_push_types,
                    );

                    if true_type.pop_types.len() != false_type.pop_types.len()
                        || true_type.push_types != false_type.push_types
                    {
                        return Err(TypeCheckerError::InvalidIfElseBody(
                            node.position.clone(),
                            Box::new(true_type),
                            Box::new(false_type),
                        ));
                    }

                    let mut pop_type = true_type.pop_types;
                    pop_type.push(UnitType::Literal(LiteralType::Boolean));

                    Ok(AstNodeWithType::new(
                        AstNodeType::If(Box::new(true_body), Some(Box::new(false_body))),
                        node.position.clone(),
                        Type::new(pop_type, true_type.push_types),
                    ))
                } else {
                    if true_body.type_definition.pop_types
                        != true_body
                            .type_definition
                            .push_types
                            .iter()
                            .rev()
                            .cloned()
                            .collect::<Vec<_>>()
                    {
                        return Err(TypeCheckerError::InvalidIfBody(
                            node.position.clone(),
                            Box::new(true_body.type_definition),
                        ));
                    }
                    let mut pop_types = true_body.type_definition.pop_types.clone();
                    pop_types.push(UnitType::Literal(LiteralType::Boolean));
                    let push_types = true_body.type_definition.push_types.clone();
                    Ok(AstNodeWithType::new(
                        AstNodeType::If(Box::new(true_body), None),
                        node.position.clone(),
                        Type::new(pop_types, push_types),
                    ))
                }
            }
        }?;
        Ok(match node.type_definition.clone() {
            Some(ty) => {
                let push_types = validate_and_get_push_types(
                    &type_stack,
                    inferred_type.type_definition.clone(),
                    node.position.clone(),
                )?;
                if push_types != ty.push_types
                    || inferred_type.type_definition.pop_types.len() != ty.pop_types.len()
                {
                    return Err(TypeCheckerError::TypeConflict(
                        node.position.clone(),
                        Box::new(UnitType::Type(ty.clone())),
                        Box::new(UnitType::Type(inferred_type.type_definition.clone())),
                    ));
                }
                AstNodeWithType::new(inferred_type.node_type, node.position, ty)
            }
            None => inferred_type,
        })
    }
}

fn validate_and_get_push_types(
    type_stack: &[UnitType],
    type_definition: Type,
    position: Position,
) -> Result<Vec<UnitType>, TypeCheckerError> {
    let variable_substitution =
        validate_type_against_type_stack(type_stack, &type_definition, position)?;

    Ok(type_definition
        .push_types
        .into_iter()
        .map(|ty| match ty {
            UnitType::Var(var) => variable_substitution
                .get(&var)
                .cloned()
                .unwrap_or(UnitType::Var(var)),
            other => other,
        })
        .collect())
}

fn substitute_types(
    type_stack: &[UnitType],
    type_definition: Type,
    position: Position,
) -> Result<Type, TypeCheckerError> {
    let variable_substitution =
        validate_type_against_type_stack(type_stack, &type_definition, position)?;

    Ok(Type::new(
        type_definition
            .pop_types
            .into_iter()
            .map(|ty| match ty {
                UnitType::Var(var) => variable_substitution
                    .get(&var)
                    .cloned()
                    .unwrap_or(UnitType::Var(var)),
                other => other,
            })
            .collect(),
        type_definition
            .push_types
            .into_iter()
            .map(|ty| match ty {
                UnitType::Var(var) => variable_substitution
                    .get(&var)
                    .cloned()
                    .unwrap_or(UnitType::Var(var)),
                other => other,
            })
            .collect(),
    ))
}

pub fn validate_type_against_type_stack(
    type_stack: &[UnitType],
    type_definition: &Type,
    position: Position,
) -> Result<HashMap<VarType, UnitType>, TypeCheckerError> {
    let mut variable_substitution: HashMap<VarType, UnitType> = HashMap::new();
    let stack_pop_types = &type_stack[type_stack
        .len()
        .saturating_sub(type_definition.pop_types.len())..];
    for (i, ty) in stack_pop_types.iter().enumerate() {
        match (ty, &type_definition.pop_types[i]) {
            (UnitType::Literal(lit1), UnitType::Literal(lit2)) if lit1 == lit2 => {}
            (UnitType::Literal(lit), UnitType::Var(var)) => {
                let existent =
                    variable_substitution.insert(var.clone(), UnitType::Literal(lit.clone()));
                if let Some(existent) = existent
                    && existent != UnitType::Literal(lit.clone())
                {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        Box::new(existent),
                        Box::new(UnitType::Literal(lit.clone())),
                    ));
                }
            }
            (UnitType::Type(ty1), UnitType::Type(ty2)) => {
                if ty1 != ty2 {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        Box::new(UnitType::Type(ty1.clone())),
                        Box::new(UnitType::Type(ty2.clone())),
                    ));
                }
            }
            (UnitType::Type(ty), UnitType::Var(var)) | (UnitType::Var(var), UnitType::Type(ty)) => {
                let existent =
                    variable_substitution.insert(var.clone(), UnitType::Type(ty.clone()));
                if let Some(existent) = existent
                    && existent != UnitType::Type(ty.clone())
                {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        Box::new(existent),
                        Box::new(UnitType::Type(ty.clone())),
                    ));
                }
            }
            (UnitType::Var(var1), UnitType::Var(var2)) => {
                let existent =
                    variable_substitution.insert(var1.clone(), UnitType::Var(var2.clone()));
                if let Some(existent) = existent
                    && existent != UnitType::Var(var2.clone())
                {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        Box::new(existent),
                        Box::new(UnitType::Var(var2.clone())),
                    ));
                }
            }
            (other1, other2) => {
                return Err(TypeCheckerError::TypeConflict(
                    position,
                    Box::new(other2.clone()),
                    Box::new(other1.clone()),
                ));
            }
        }
    }
    Ok(variable_substitution)
}

#[derive(Debug, Error)]
pub enum TypeCheckerError {
    #[error("Type conflict at {0}: expected {1}, got {2}")]
    TypeConflict(Position, Box<UnitType>, Box<UnitType>),
    #[error(
        "Symbol {0} not found at {1} with type stack {2}. Maybe it is defined after the current position"
    )]
    SymbolNotFound(String, Position, String),
    #[error("Invalid main definition {0}")]
    InvalidMainDefinition(Box<Type>),
    #[error("Invalid module definition {0}. It should always be (->)")]
    InvalidModuleDefinition(Box<Type>),
    #[error("Invalid if body at {0}. If cannot change the type stack. It tried to change to {1}")]
    InvalidIfBody(Position, Box<Type>),
    #[error(
        "Invalid if else body at {0}.If and else bodies need to pop and push the same types. {1} != {2}"
    )]
    InvalidIfElseBody(Position, Box<Type>, Box<Type>),
    #[error("Missing import {0}")]
    MissingImport(String),
}

#[derive(Debug, Clone)]
pub struct TypeScope {
    inner: Rc<RefCell<InnerTypeScope>>,
}

#[derive(Debug, Clone)]
struct InnerTypeScope {
    parent: Option<TypeScope>,
    imported: HashMap<String, TypeScope>,
    imported_functions: HashMap<String, (String, String)>,
    definitions: HashMap<String, (Type, bool)>,
}

impl TypeScope {
    fn with_parent(parent: TypeScope) -> TypeScope {
        TypeScope {
            inner: Rc::new(RefCell::new(InnerTypeScope {
                parent: Some(parent),
                imported: HashMap::new(),
                imported_functions: HashMap::new(),
                definitions: HashMap::new(),
            })),
        }
    }

    fn insert_definition(&mut self, symbol: String, definition: Type, is_private: bool) {
        let mut inner = self.inner.borrow_mut();
        inner.definitions.insert(symbol, (definition, is_private));
    }

    fn insert_import(&mut self, symbol: String, scope: TypeScope) {
        let mut inner = self.inner.borrow_mut();
        inner.imported.insert(symbol, scope);
    }

    fn insert_function_import(
        &mut self,
        function_alias: String,
        function_name: String,
        module: String,
    ) {
        let mut inner = self.inner.borrow_mut();
        inner
            .imported_functions
            .insert(function_alias, (function_name, module));
    }

    fn get_definition(&self, mut symbol: Vec<String>, filter_private: bool) -> Option<Type> {
        match symbol.len() {
            1 => {
                let inner = self.inner.borrow();
                let last = symbol
                    .last()
                    .expect("We checked for the symbol size")
                    .clone();
                if let Some(from_definitions) =
                    inner
                        .definitions
                        .get(&last)
                        .cloned()
                        .and_then(|definitions| {
                            let (def, is_private) = definitions;
                            if is_private && filter_private {
                                None
                            } else {
                                Some(def)
                            }
                        })
                {
                    return Some(from_definitions);
                }
                if let Some(imported_functions) = inner.imported_functions.get(&last) {
                    return self.get_definition(
                        vec![imported_functions.1.clone(), imported_functions.0.clone()],
                        filter_private,
                    );
                }
                if let Some(parent) = inner.parent.as_ref() {
                    return parent.get_definition(symbol, filter_private);
                }
                None
            }
            0 => None,
            _ => {
                let inner = self.inner.borrow();
                let first = symbol.remove(0);
                if let Some(from_imports) = inner.imported.get(&first) {
                    return from_imports.get_definition(symbol, filter_private);
                }
                if let Some(parent) = inner.parent.as_ref() {
                    symbol.insert(0, first);
                    return parent.get_definition(symbol, filter_private);
                }

                None
            }
        }
    }

    fn empty() -> TypeScope {
        TypeScope {
            inner: Rc::new(RefCell::new(InnerTypeScope {
                parent: None,
                imported: HashMap::new(),
                imported_functions: HashMap::new(),
                definitions: HashMap::new(),
            })),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        lexer::Position,
        parser::{AstNode, AstNodeType, Parser, ParserError},
        type_checker::TypeChecker,
    };

    use super::TypeCheckerError;

    fn parse_and_type_check(
        contents: &str,
        check_for_main: bool,
    ) -> Result<String, TypeCheckerError> {
        let program = Parser::new_from_str(&contents)
            .collect::<Result<Vec<AstNode>, ParserError>>()
            .unwrap();
        TypeChecker::new()
            .type_check(
                AstNode {
                    node_type: AstNodeType::Block(program),
                    position: Position::default(),
                    type_definition: None,
                },
                check_for_main,
            )
            .map(|ast_node| ast_node.0.to_string())
    }

    #[test]
    fn basic_number_literals() {
        let contents = "import std::stack(drop) 42u8 drop 100u16 drop 1000u32 drop";
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) import std::stack(drop) ( -> U8) 42u8 (U8 -> ) drop ( -> U16) 100u16 (U16 -> ) drop ( -> U32) 1000u32 (U32 -> ) drop}"
        );
    }

    #[test]
    fn signed_number_literals() {
        let contents = "import std::stack(drop) -42i8 drop -100i16 drop -1000i32 drop";
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) import std::stack(drop) ( -> I8) -42i8 (I8 -> ) drop ( -> I16) -100i16 (I16 -> ) drop ( -> I32) -1000i32 (I32 -> ) drop}"
        )
    }

    #[test]
    fn float_and_string_literals() {
        let contents = r#"import std::stack 3.14 stack::drop "hello world" stack::drop"#;
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) import std::stack ( -> F64) 3.14 (F64 -> ) stack::drop ( -> String) \"hello world\" (String -> ) stack::drop}"
        );
    }

    #[test]
    fn simple_block() {
        let contents = "import std::stack(drop) { 42u8 \"test\" stack::drop drop }";
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) import std::stack(drop) ( -> ) {( -> U8) 42u8 ( -> String) \"test\" (String -> ) stack::drop (U8 -> ) drop}}"
        );
    }

    #[test]
    fn simple_definition() {
        let contents = r#"def hello { "Hello, World!" }"#;
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) def hello ( -> String) {( -> String) \"Hello, World!\"}\n}"
        );
    }

    #[test]
    fn if_without_else() {
        let contents = r#"
            import std::stack

            def main {
                true if { 42u8 stack::drop }
            }
        "#;
        let program = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            program,
            "( -> ) {( -> ) import std::stack ( -> ) def main ( -> ) {( -> Boolean) true (Boolean -> ) if ( -> ) {( -> U8) 42u8 (U8 -> ) stack::drop}}\n}"
        );
    }

    #[test]
    fn if_with_else_same_types() {
        let contents = r#"
            import std::stack

            def main {
                true if { 42u8 } else { 24u8 } stack::drop
            }
        "#;
        let program = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            program,
            "( -> ) {( -> ) import std::stack ( -> ) def main ( -> ) {( -> Boolean) true (Boolean -> U8) if ( -> U8) {( -> U8) 42u8} else ( -> U8) {( -> U8) 24u8} (U8 -> ) stack::drop}\n}"
        );
    }

    #[test]
    fn symbol_not_found_error() {
        let contents = "unknown_symbol";
        let error = parse_and_type_check(contents, false)
            .unwrap_err()
            .to_string();

        assert_eq!(
            error,
            "Symbol unknown_symbol not found at 1:1 with type stack <...>. Maybe it is defined after the current position"
        );
    }

    #[test]
    fn invalid_if_body_error() {
        let contents = r#"true if { 42u8 }"#;
        let error = parse_and_type_check(contents, false)
            .unwrap_err()
            .to_string();

        assert_eq!(
            error,
            "Invalid if body at 1:6. If cannot change the type stack. It tried to change to ( -> U8)"
        );
    }

    #[test]
    fn invalid_if_else_body_different_types() {
        let contents = r#"
            def main {
                true if { 42u8 } else { "hello" } print
            }
        "#;
        let error = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(
            error,
            "Invalid if else body at 3:22.If and else bodies need to pop and push the same types. ( -> U8) != ( -> String)"
        );
    }

    #[test]
    fn valid_main_function() {
        let contents = r#"def main { }"#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(result, "( -> ) {( -> ) def main ( -> ) {}\n}");
    }

    #[test]
    fn valid_main_function_with_i32_return() {
        let contents = r#"def main (-> I32) { 0i32 }"#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            result,
            "( -> ) {( -> ) def main ( -> I32) {( -> I32) 0i32}\n}"
        );
    }

    #[test]
    fn invalid_main_function_wrong_return_type() {
        let contents = r#"def main (-> String) { "hello" }"#;
        let error = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(error, "Invalid main definition ( -> String)");
    }

    #[test]
    fn builtin_functions_work() {
        let contents = r#"
            import std::stack(drop)

            def main {
                42u8 drop
                "hello" drop
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            result,
            "( -> ) {( -> ) import std::stack(drop) ( -> ) def main ( -> ) {( -> U8) 42u8 (U8 -> ) drop ( -> String) \"hello\" (String -> ) drop}\n}"
        );
    }

    #[test]
    fn arithmetic_operations() {
        let contents = r#"
import std::number::i32(+ -)
import std::stack(drop)

def main {
    5i32 3i32 +
    10i32 2i32 -
    15i32 3i32 + drop drop drop
}"#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            result,
            "( -> ) {( -> ) import std::number::i32(+ -) ( -> ) import std::stack(drop) ( -> ) def main ( -> ) {( -> I32) 5i32 ( -> I32) 3i32 (I32 I32 -> I32) + ( -> I32) 10i32 ( -> I32) 2i32 (I32 I32 -> I32) - ( -> I32) 15i32 ( -> I32) 3i32 (I32 I32 -> I32) + (I32 -> ) drop (I32 -> ) drop (I32 -> ) drop}\n}"
        );
    }

    #[test]
    fn nested_blocks() {
        let contents = r#"
            import std::stack

            def main {
                { { 42u8 stack::drop } }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            result,
            "( -> ) {( -> ) import std::stack ( -> ) def main ( -> ) {( -> ) {( -> ) {( -> U8) 42u8 (U8 -> ) stack::drop}}}\n}"
        );
    }

    #[test]
    fn complex_stack_manipulation() {
        let contents = r#"
            import std::stack(dup drop swap)
            def main {
                1u8 2u8
                dup drop
                swap drop drop
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            result,
            "( -> ) {( -> ) import std::stack(dup drop swap) ( -> ) def main ( -> ) {( -> U8) 1u8 ( -> U8) 2u8 (U8 -> U8 U8) dup (U8 -> ) drop (U8 U8 -> U8 U8) swap (U8 -> ) drop (U8 -> ) drop}\n}"
        );
    }

    #[test]
    fn type_conflict_error() {
        let contents = r#"
            import std::stack(dup drop)
            def test (U8 -> U8) { dup drop }
            def main {
                42i32 test  # This should fail - trying to pass I32 where U8 expected
            }
        "#;
        let error = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(error, "Type conflict at 5:23: expected U8, got I32");
    }

    #[test]
    fn nested_def() {
        let contents = r#"
            import std::stack(drop)
            def test {
                def test1 { drop }
                10i32 test1
            }
            def main {
                test
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) import std::stack(drop) ( -> ) def test ( -> ) {( -> ) def test1 (a -> ) {(a -> ) drop}\n ( -> I32) 10i32 (I32 -> ) test1}\n ( -> ) def main ( -> ) {( -> ) test}\n}"
        );
    }
}
