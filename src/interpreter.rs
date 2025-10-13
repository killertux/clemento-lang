use std::{
    cell::RefCell, collections::HashMap, fmt::Debug, fs::read_to_string, path::Path, rc::Rc,
};

use thiserror::Error;

use crate::{
    lexer::{IntegerNumber, Number, Position},
    parser::{AstNode, AstNodeType, Parser, ParserError},
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
        scope.call_symbol("main", Position::default(), &mut stack)?;
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
                scope.add_definition(name, scope.clone(), try_into_value(&scope, *body)?);
            }
            AstNodeType::Block(block) => {
                execute_scope(Scope::with_parent(scope.clone()), stack, block.into_iter())?;
            }
            AstNodeType::Symbol(symbol) => {
                scope.call_symbol(symbol.as_str(), node.position, stack)?
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
        AstNodeType::Symbol(symbol) => Ok(scope.get_symbol(symbol.as_str(), node.position)?.0),
        _ => Err(RuntimeError::Unexpected("Unexpected node type".into())),
    }
}

#[derive(Clone)]
pub struct Scope {
    internal_scope: Rc<RefCell<InternalScope>>,
}

#[derive(Clone)]
struct InternalScope {
    definitions_map: HashMap<String, (Value, Scope)>,
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
        Scope {
            internal_scope: Rc::new(RefCell::new(InternalScope {
                definitions_map: HashMap::from([
                    (
                        "println".to_string(),
                        (
                            Value::InternalFunction(InternalFunction {
                                n_params: 1,
                                function: Rc::new(Box::new(|args| {
                                    if let Some(arg) = args.first() {
                                        match arg {
                                            Value::IntegerNumber(num) => println!("{}", num),
                                            Value::FloatNumber(num) => println!("{}", num),
                                            Value::String(string) => println!("{}", string),
                                            _ => println!("Unknown type"),
                                        }
                                    }
                                    Ok(Vec::new())
                                })),
                            }),
                            Scope::empty(),
                        ),
                    ),
                    (
                        "dup".to_string(),
                        (
                            Value::InternalFunction(InternalFunction {
                                n_params: 1,
                                function: Rc::new(Box::new(|args| {
                                    Ok(vec![args[0].clone(), args[0].clone()])
                                })),
                            }),
                            Scope::empty(),
                        ),
                    ),
                    (
                        "swap".to_string(),
                        (
                            Value::InternalFunction(InternalFunction {
                                n_params: 2,
                                function: Rc::new(Box::new(|args| {
                                    Ok(vec![args[1].clone(), args[0].clone()])
                                })),
                            }),
                            Scope::empty(),
                        ),
                    ),
                ]),
                parent: None,
            })),
        }
    }

    pub fn add_definition(&self, name: String, scope: Scope, value: Value) {
        self.internal_scope
            .borrow_mut()
            .definitions_map
            .insert(name, (value, scope));
    }

    pub fn get_symbol(
        &self,
        name: &str,
        position: Position,
    ) -> Result<(Value, Scope), RuntimeError> {
        let borrow = self.internal_scope.borrow();
        let Some((value, scope)) = borrow.definitions_map.get(name) else {
            if let Some(parent) = borrow.parent.clone() {
                return parent.get_symbol(name, position);
            } else {
                return Err(RuntimeError::SymbolNotFound(name.to_string(), position));
            }
        };
        Ok((value.clone(), scope.clone()))
    }

    pub fn call_symbol(
        &self,
        name: &str,
        position: Position,
        stack: &mut Vec<Value>,
    ) -> Result<(), RuntimeError> {
        let (value, scope) = self.get_symbol(name, position)?;
        value.clone().execute(scope.clone(), stack)
    }

    pub fn has_main(&self) -> bool {
        self.internal_scope
            .borrow()
            .definitions_map
            .contains_key("main")
    }
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
                let args = stack.split_off(stack.len() - function.n_params);
                if args.len() != function.n_params {
                    return Err(RuntimeError::StackUnderflow);
                }
                let result = (function.function)(args)?;
                stack.extend(result);
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
pub struct InternalFunction {
    n_params: usize,
    function: Rc<Box<dyn Fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>>>,
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
