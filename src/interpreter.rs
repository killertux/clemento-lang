use std::{
    cell::RefCell, collections::HashMap, fmt::Debug, fs::read_to_string, path::Path, rc::Rc,
};

use thiserror::Error;

use crate::{
    internal_functions::{InternalFunction, builtins_functions},
    lexer::{IntegerNumber, Number, Position},
    parser::{AstNode, AstNodeType, Parser, ParserError, Type, UnitType, VarType},
    type_checker::{AstNodeWithType, TypeCheckerError, type_check},
};

pub fn interpret(file: impl AsRef<Path>) -> Result<u8, RuntimeError> {
    let path_as_string = file.as_ref().display().to_string();
    let file_content = read_to_string(file.as_ref())?;

    let scope = Scope::root();
    let mut stack: Vec<Value> = Vec::new();

    let program = Parser::new_from_file(&file_content, path_as_string)
        .collect::<Result<Vec<AstNode>, ParserError>>()?;
    let program = type_check(
        AstNode {
            node_type: AstNodeType::Block(program),
            position: Position::default(),
            type_definition: None,
        },
        true,
    )?;
    let AstNodeType::Block(nodes) = program.node_type else {
        unreachable!()
    };
    execute_scope(scope.clone(), &mut stack, nodes.into_iter())?;
    if scope.has_main() {
        scope.call_main(&mut stack)?;
    }
    if stack.len() != 0 {
        return match stack[0] {
            Value::IntegerNumber(IntegerNumber::U8(number)) => Ok(number),
            _ => Err(RuntimeError::Unexpected(
                "Wrong param in the stack at the end of the program".into(),
            )),
        };
    }
    Ok(0)
}

fn execute_scope(
    scope: Scope,
    stack: &mut Vec<Value>,
    nodes: impl Iterator<Item = AstNodeWithType>,
) -> Result<(), RuntimeError> {
    for node in nodes {
        match node.node_type {
            AstNodeType::Number(_) => stack.push(try_into_value(&scope, node)?),
            AstNodeType::String(_) => stack.push(try_into_value(&scope, node)?),
            AstNodeType::Definition(name, body) => {
                let ty = body.type_definition.clone();
                scope.add_definition(name, scope.clone(), try_into_value(&scope, *body)?, ty);
            }
            AstNodeType::Block(block) => {
                execute_scope(Scope::with_parent(scope.clone()), stack, block.into_iter())?;
            }
            AstNodeType::Symbol(symbol) => {
                scope.call_symbol(symbol.as_str(), node.type_definition, node.position, stack)?
            }
        }
    }
    Ok(())
}

fn try_into_value(scope: &Scope, node: AstNodeWithType) -> Result<Value, RuntimeError> {
    match node.node_type {
        AstNodeType::Number(Number::Integer(number)) => Ok(Value::IntegerNumber(number)),
        AstNodeType::Number(Number::Float(number)) => {
            Ok(Value::FloatNumber(number.parse().map_err(|_| {
                RuntimeError::Unexpected("Unexpected not valid float".into())
            })?))
        }
        AstNodeType::String(string) => Ok(Value::String(string)),
        AstNodeType::Block(block) => Ok(Value::Block(block)),
        AstNodeType::Symbol(symbol) => Ok(scope
            .get_symbol(symbol.as_str(), node.type_definition, node.position)?
            .0),
        _ => Err(RuntimeError::Unexpected("Unexpected node type".into())),
    }
}

#[derive(Clone)]
pub struct Scope {
    internal_scope: Rc<RefCell<InternalScope>>,
}

#[derive(Clone)]
struct InternalScope {
    definitions_map: HashMap<String, Vec<(Value, Type, Scope)>>,
    parent: Option<Scope>,
}

impl Scope {
    pub fn empty() -> Self {
        Scope {
            internal_scope: Rc::new(RefCell::new(InternalScope {
                definitions_map: HashMap::new(),
                parent: None,
            })),
        }
    }

    pub fn with_parent(parent: Scope) -> Self {
        Scope {
            internal_scope: Rc::new(RefCell::new(InternalScope {
                definitions_map: HashMap::new(),
                parent: Some(parent),
            })),
        }
    }

    pub fn root() -> Self {
        let builtin_functions = builtins_functions();
        let scope = Scope {
            internal_scope: Rc::new(RefCell::new(InternalScope {
                definitions_map: HashMap::new(),
                parent: None,
            })),
        };

        for builtin_function in builtin_functions {
            let ty = builtin_function.ty.clone();
            scope.add_definition(
                builtin_function.name.clone(),
                Scope::empty(),
                Value::InternalFunction(builtin_function),
                ty,
            );
        }
        scope
    }

    pub fn add_definition(&self, name: String, scope: Scope, value: Value, ty: Type) {
        self.internal_scope
            .borrow_mut()
            .definitions_map
            .entry(name)
            .or_default()
            .push((value, ty, scope));
    }

    pub fn get_symbol(
        &self,
        name: &str,
        ty: Type,
        position: Position,
    ) -> Result<(Value, Scope), RuntimeError> {
        let borrow = self.internal_scope.borrow();
        let Some(definition) = borrow.definitions_map.get(name) else {
            if let Some(parent) = borrow.parent.clone() {
                return parent.get_symbol(name, ty, position);
            } else {
                return Err(RuntimeError::SymbolNotFound(name.to_string(), position));
            }
        };
        for (value, def_ty, scope) in definition {
            if match_types(&ty.pop_types, &def_ty.pop_types) {
                return Ok((value.clone(), scope.clone()));
            }
        }
        if let Some(parent) = borrow.parent.clone() {
            return parent.get_symbol(name, ty, position);
        }
        Err(RuntimeError::SymbolNotFound(name.to_string(), position))
    }

    pub fn call_symbol(
        &self,
        name: &str,
        ty: Type,
        position: Position,
        stack: &mut Vec<Value>,
    ) -> Result<(), RuntimeError> {
        let (value, scope) = self.get_symbol(name, ty, position)?;
        value.clone().execute(scope.clone(), stack)
    }

    pub fn call_main(&self, stack: &mut Vec<Value>) -> Result<(), RuntimeError> {
        let main_type = {
            let borrow = self.internal_scope.borrow();
            let Some(main) = borrow.definitions_map.get("main") else {
                return Err(RuntimeError::SymbolNotFound(
                    "main".to_string(),
                    Position::default(),
                ));
            };
            main[0].1.clone()
        };
        let (value, scope) = self.get_symbol("main", main_type, Position::default())?;
        value.clone().execute(scope.clone(), stack)
    }

    pub fn has_main(&self) -> bool {
        self.internal_scope
            .borrow()
            .definitions_map
            .contains_key("main")
    }
}

fn match_types(left: &[UnitType], right: &[UnitType]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut var_type_map: HashMap<VarType, UnitType> = HashMap::new();
    for (left, right) in left.into_iter().zip(right.into_iter()) {
        let match_ty = match (left, right) {
            (UnitType::Literal(a), UnitType::Literal(b)) => a == b,
            (UnitType::Var(a), UnitType::Var(b)) => var_type_map
                .insert(a.clone(), UnitType::Var(b.clone()))
                .map_or(true, |previous| previous == UnitType::Var(b.clone())),
            (type_left, UnitType::Var(a)) => {
                let previous = var_type_map.insert(a.clone(), type_left.clone());
                previous.map(|p| p == *type_left).unwrap_or(true)
            }
            _ => false,
        };
        if !match_ty {
            return false;
        }
    }
    true
}

#[derive(Clone)]
pub enum Value {
    IntegerNumber(IntegerNumber),
    FloatNumber(f64),
    String(String),
    Block(Vec<AstNodeWithType>),
    InternalFunction(InternalFunction),
}

impl Value {
    pub fn execute(self, scope: Scope, stack: &mut Vec<Value>) -> Result<(), RuntimeError> {
        match self {
            Value::IntegerNumber(_) | Value::FloatNumber(_) | Value::String(_) => stack.push(self),
            Value::Block(nodes) => execute_scope(scope, stack, nodes.into_iter())?,
            Value::InternalFunction(function) => {
                let args = stack.split_off(stack.len() - function.arity);
                if args.len() != function.arity {
                    return Err(RuntimeError::StackUnderflow);
                }
                let result = (function.function)(args)?;
                stack.extend(result);
            }
        }
        Ok(())
    }
}

impl Debug for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::IntegerNumber(number) => write!(f, "{:?}", number),
            Value::FloatNumber(number) => write!(f, "{}", number),
            Value::String(string) => write!(f, "{}", string),
            Value::Block(nodes) => write!(f, "{:?}", nodes),
            Value::InternalFunction(_) => write!(f, "<internal function>"),
        }
    }
}

#[derive(Debug, Error)]
pub enum RuntimeError {
    #[error(transparent)]
    TypeCheckerError(#[from] TypeCheckerError),
    #[error(transparent)]
    ParserError(#[from] ParserError),
    #[error(transparent)]
    IOError(#[from] std::io::Error),
    #[error("Symbol not found: {0} at {1}")]
    SymbolNotFound(String, Position),
    #[error("Unexpected error: {0}")]
    Unexpected(String),
    #[error("Stack underflow")]
    StackUnderflow,
}
