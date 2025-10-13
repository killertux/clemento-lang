use std::{collections::HashMap, fmt::Display};

use thiserror::Error;

use crate::{
    lexer::{IntegerNumber, Number, Position},
    parser::{AstNode, AstNodeType, LiteralType, NumberType, Type, UnitType, VarType},
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

pub fn type_check<'a>(
    program: AstNode,
    check_for_main: bool,
) -> Result<AstNodeWithType, TypeCheckerError> {
    let scope = TypeScope::root();
    let AstNodeType::Block(nodes) = program.node_type else {
        return Err(TypeCheckerError::InvalidModuleDefinition(Type::empty()));
    };

    let (block_type_check_result, nodes_with_types) =
        type_check_block(&scope, Vec::new(), nodes, check_for_main)?;
    if block_type_check_result != Type::empty() {
        return Err(TypeCheckerError::InvalidModuleDefinition(
            block_type_check_result,
        ));
    }
    Ok(AstNodeWithType::new(
        AstNodeType::Block(nodes_with_types),
        program.position,
        block_type_check_result,
    ))
}

fn type_check_block<'a>(
    scope: &TypeScope,
    mut type_stack: Vec<UnitType>,
    program: Vec<AstNode>,
    check_for_main: bool,
) -> Result<(Type, Vec<AstNodeWithType>), TypeCheckerError> {
    let mut node_results = Vec::new();
    let mut scope = TypeScope::with_parent(scope);
    let mut pop_type_stack: Vec<UnitType> = Vec::new();
    let mut local_stack: Vec<UnitType> = Vec::new();
    for node in program {
        let node = infer_type_definition(&mut scope, type_stack.clone(), node)?;
        let type_definition = &node.type_definition;
        let pop_size = type_definition.pop_types.len();
        if pop_size > type_stack.len() {
            let new_types = &type_definition.pop_types[0..(pop_size - type_stack.len())];
            type_stack = vec![new_types.to_vec(), type_stack.clone()].concat();
        }
        if pop_size > local_stack.len() {
            let new_types = &type_definition.pop_types[0..(pop_size - local_stack.len())];
            pop_type_stack = vec![new_types.to_vec(), local_stack.clone()].concat();
            local_stack = vec![new_types.to_vec(), local_stack.clone()].concat();
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

    if check_for_main {
        match scope.get_definition("main") {
            Some(main) => {
                let valid_main_definitions = vec![
                    Type::new(vec![], vec![]),
                    Type::new(
                        vec![],
                        vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
                    ),
                ];
                if !valid_main_definitions.contains(&main) {
                    return Err(TypeCheckerError::InvalidMainDefinition(main));
                }
            }
            None => {}
        }
    }
    let block_type = Type::new(pop_type_stack, local_stack);
    Ok((block_type, node_results))
}

fn validate_and_get_push_types(
    type_stack: &[UnitType],
    type_definition: Type,
    position: Position,
) -> Result<Vec<UnitType>, TypeCheckerError> {
    let mut variable_substitution: HashMap<VarType, UnitType> = HashMap::new();
    let stack_pop_types = &type_stack[(type_stack.len() - type_definition.pop_types.len())..];
    for (i, ty) in type_definition.pop_types.iter().enumerate() {
        match (&stack_pop_types[i], ty) {
            (UnitType::Literal(lit1), UnitType::Literal(lit2)) if lit1 == lit2 => {}
            (UnitType::Literal(lit), UnitType::Var(var))
            | (UnitType::Var(var), UnitType::Literal(lit)) => {
                let existent =
                    variable_substitution.insert(var.clone(), UnitType::Literal(lit.clone()));
                if let Some(existent) = existent
                    && existent != UnitType::Literal(lit.clone())
                {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        existent,
                        UnitType::Literal(lit.clone()),
                    ));
                }
            }
            (UnitType::Type(ty1), UnitType::Type(ty2)) => {
                if ty1 != ty2 {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        UnitType::Type(ty1.clone()),
                        UnitType::Type(ty2.clone()),
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
                        existent,
                        UnitType::Type(ty.clone()),
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
                        existent,
                        UnitType::Var(var2.clone()),
                    ));
                }
            }
            (other1, other2) => {
                return Err(TypeCheckerError::TypeConflict(
                    position,
                    other2.clone(),
                    other1.clone(),
                ));
            }
        }
    }

    return Ok(type_definition
        .push_types
        .into_iter()
        .map(|ty| match ty {
            UnitType::Var(var) => variable_substitution
                .get(&var)
                .cloned()
                .unwrap_or(UnitType::Var(var)),
            other => other,
        })
        .collect());
}

fn infer_type_definition(
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
        AstNodeType::Number(Number::Integer(IntegerNumber::U16(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::U16(n))),
            node.position.clone(),
            Type::u16(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::U32(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::U32(n))),
            node.position.clone(),
            Type::u32(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::U64(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::U64(n))),
            node.position.clone(),
            Type::u64(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::U128(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::U128(n))),
            node.position.clone(),
            Type::u128(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::I8(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::I8(n))),
            node.position.clone(),
            Type::i8(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::I16(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::I16(n))),
            node.position.clone(),
            Type::i16(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::I32(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::I32(n))),
            node.position.clone(),
            Type::i32(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::I64(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::I64(n))),
            node.position.clone(),
            Type::i64(),
        )),
        AstNodeType::Number(Number::Integer(IntegerNumber::I128(n))) => Ok(AstNodeWithType::new(
            AstNodeType::Number(Number::Integer(IntegerNumber::I128(n))),
            node.position.clone(),
            Type::i128(),
        )),
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
        AstNodeType::Symbol(symbol) => {
            let type_definition =
                scope
                    .get_definition(&symbol)
                    .ok_or(TypeCheckerError::SymbolNotFound(
                        symbol.clone(),
                        node.position.clone(),
                    ))?;
            Ok(AstNodeWithType::new(
                AstNodeType::Symbol(symbol),
                node.position.clone(),
                type_definition,
            ))
        }
        AstNodeType::Block(nodes) => {
            let (ty, nodes) = type_check_block(scope, type_stack.clone(), nodes, false)?;
            Ok(AstNodeWithType::new(
                AstNodeType::Block(nodes),
                node.position.clone(),
                ty,
            ))
        }
        AstNodeType::Definition(symbol, body) => {
            let body = infer_type_definition(scope, type_stack.clone(), *body)?;
            scope
                .definitions
                .insert(symbol.clone(), body.type_definition.clone());
            Ok(AstNodeWithType::new(
                AstNodeType::Definition(symbol, Box::new(body)),
                node.position.clone(),
                Type::empty(),
            ))
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
                    UnitType::Type(ty.clone()),
                    UnitType::Type(Type::new(
                        ty.pop_types,
                        inferred_type.type_definition.push_types,
                    )),
                ));
            }
            AstNodeWithType::new(inferred_type.node_type, node.position, ty)
        }
        None => inferred_type,
    })
}

#[derive(Debug, Error)]
pub enum TypeCheckerError {
    #[error("Type conflict at {0}: expected {1}, got {2}")]
    TypeConflict(Position, UnitType, UnitType),
    #[error("Symbol {0} not found at {1}. Maybe it is defined after the current position")]
    SymbolNotFound(String, Position),
    #[error("Invalid main definition {0}")]
    InvalidMainDefinition(Type),
    #[error("Invalid module definition {0}. It should always be (->)")]
    InvalidModuleDefinition(Type),
}

struct TypeScope<'a> {
    parent: Option<&'a TypeScope<'a>>,
    definitions: HashMap<String, Type>,
}

impl<'a> TypeScope<'a> {
    fn with_parent(parent: &'a TypeScope<'a>) -> TypeScope<'a> {
        TypeScope {
            parent: Some(parent),
            definitions: HashMap::new(),
        }
    }

    fn root() -> Self {
        TypeScope {
            parent: None,
            definitions: HashMap::from([
                (
                    "println".into(),
                    Type::new(vec![UnitType::Literal(LiteralType::String)], vec![]),
                ),
                ("dup".into(), {
                    let var = VarType::new();
                    Type::new(
                        vec![UnitType::Var(var.clone())],
                        vec![UnitType::Var(var.clone()), UnitType::Var(var)],
                    )
                }),
                ("swap".into(), {
                    let var1 = VarType::new();
                    let var2 = VarType::new();
                    Type::new(
                        vec![UnitType::Var(var1.clone()), UnitType::Var(var2.clone())],
                        vec![UnitType::Var(var2.clone()), UnitType::Var(var1.clone())],
                    )
                }),
            ]),
        }
    }

    fn get_definition(&self, symbol: &str) -> Option<Type> {
        let Some(definition) = self.definitions.get(symbol).cloned() else {
            if let Some(parent) = &self.parent {
                return parent.get_definition(symbol);
            }
            return None;
        };
        Some(definition)
    }
}
