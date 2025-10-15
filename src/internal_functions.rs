use std::rc::Rc;

use crate::{
    interpreter::{RuntimeError, Value},
    lexer::IntegerNumber,
    parser::{LiteralType, NumberType, Type, UnitType, VarType},
};

#[derive(Clone)]
pub struct InternalFunction {
    pub arity: usize,
    pub name: String,
    pub ty: Type,
    pub function: Rc<Box<dyn Fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>>>,
}

pub fn builtins_functions() -> Vec<InternalFunction> {
    let all_integer_types = vec![
        UnitType::Literal(LiteralType::Number(NumberType::U8)),
        UnitType::Literal(LiteralType::Number(NumberType::U16)),
        UnitType::Literal(LiteralType::Number(NumberType::U32)),
        UnitType::Literal(LiteralType::Number(NumberType::U64)),
        UnitType::Literal(LiteralType::Number(NumberType::U128)),
        UnitType::Literal(LiteralType::Number(NumberType::I8)),
        UnitType::Literal(LiteralType::Number(NumberType::I16)),
        UnitType::Literal(LiteralType::Number(NumberType::I32)),
        UnitType::Literal(LiteralType::Number(NumberType::I64)),
        UnitType::Literal(LiteralType::Number(NumberType::I128)),
    ];

    let mut all_number_types = all_integer_types.clone();
    all_number_types.push(UnitType::Literal(LiteralType::Number(NumberType::F64)));

    let mut all_literal_types = all_number_types.clone();
    all_literal_types.push(UnitType::Literal(LiteralType::String));

    [
        pop1_push0(
            &all_literal_types,
            "print".into(),
            Rc::new(
                Box::new(|args: Vec<Value>| -> Result<Vec<Value>, RuntimeError> {
                    match &args[0] {
                        Value::IntegerNumber(IntegerNumber::U8(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U16(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U32(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U64(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U128(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I8(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I16(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I32(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I64(n)) => print!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I128(n)) => print!("{}", n),
                        Value::FloatNumber(n) => print!("{}", n),
                        Value::String(s) => print!("{}", s),
                        _ => {
                            return Err(RuntimeError::Unexpected(format!(
                                "Unexpected value for print param {:?}",
                                args[0]
                            )));
                        }
                    }
                    Ok(vec![])
                }) as Box<dyn Fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>>,
            ),
        ),
        pop1_push0(
            &all_literal_types,
            "println".into(),
            Rc::new(
                Box::new(|args: Vec<Value>| -> Result<Vec<Value>, RuntimeError> {
                    match &args[0] {
                        Value::IntegerNumber(IntegerNumber::U8(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U16(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U32(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U64(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::U128(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I8(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I16(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I32(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I64(n)) => println!("{}", n),
                        Value::IntegerNumber(IntegerNumber::I128(n)) => println!("{}", n),
                        Value::FloatNumber(n) => println!("{}", n),
                        Value::String(s) => println!("{}", s),
                        _ => {
                            return Err(RuntimeError::Unexpected(format!(
                                "Unexpected value for println param {:?}",
                                args[0]
                            )));
                        }
                    }
                    Ok(vec![])
                }) as Box<dyn Fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>>,
            ),
        ),
        vec![InternalFunction {
            arity: 1,
            name: "dup".into(),
            ty: {
                let var = VarType::new();
                Type::new(
                    vec![UnitType::Var(var.clone())],
                    vec![UnitType::Var(var.clone()), UnitType::Var(var.clone())],
                )
            },
            function: Rc::new(Box::new(|args| Ok(vec![args[0].clone(), args[0].clone()]))),
        }],
        vec![InternalFunction {
            arity: 2,
            name: "swap".into(),
            ty: {
                let var1 = VarType::new();
                let var2 = VarType::new();
                Type::new(
                    vec![UnitType::Var(var1.clone()), UnitType::Var(var2.clone())],
                    vec![UnitType::Var(var2.clone()), UnitType::Var(var1.clone())],
                )
            },
            function: Rc::new(Box::new(|args| Ok(vec![args[1].clone(), args[0].clone()]))),
        }],
        vec![InternalFunction {
            arity: 3,
            name: "rot".into(),
            ty: {
                let var1 = VarType::new();
                let var2 = VarType::new();
                let var3 = VarType::new();
                Type::new(
                    vec![
                        UnitType::Var(var1.clone()),
                        UnitType::Var(var2.clone()),
                        UnitType::Var(var3.clone()),
                    ],
                    vec![
                        UnitType::Var(var2.clone()),
                        UnitType::Var(var3.clone()),
                        UnitType::Var(var1.clone()),
                    ],
                )
            },
            function: Rc::new(Box::new(|args| {
                Ok(vec![args[1].clone(), args[2].clone(), args[0].clone()])
            })),
        }],
        vec![InternalFunction {
            arity: 1,
            name: "drop".into(),
            ty: Type::new(vec![UnitType::Var(VarType::new())], vec![]),
            function: Rc::new(Box::new(|_args| Ok(vec![]))),
        }],
        vec![InternalFunction {
            arity: 2,
            name: "&&".into(),
            ty: {
                Type::new(
                    vec![
                        UnitType::Literal(LiteralType::Boolean),
                        UnitType::Literal(LiteralType::Boolean),
                    ],
                    vec![UnitType::Literal(LiteralType::Boolean)],
                )
            },
            function: Rc::new(Box::new(|args| match (&args[0], &args[1]) {
                (Value::Boolean(b1), Value::Boolean(b2)) => Ok(vec![Value::Boolean(*b1 && *b2)]),
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in && function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        }],
        pop2_push1(
            &all_number_types,
            None,
            "+".into(),
            Rc::new(Box::new(|args: Vec<Value>| match (&args[0], &args[1]) {
                (
                    Value::IntegerNumber(IntegerNumber::U8(n1)),
                    Value::IntegerNumber(IntegerNumber::U8(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U8(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U16(n1)),
                    Value::IntegerNumber(IntegerNumber::U16(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U16(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U32(n1)),
                    Value::IntegerNumber(IntegerNumber::U32(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U32(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U64(n1)),
                    Value::IntegerNumber(IntegerNumber::U64(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U64(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U128(n1)),
                    Value::IntegerNumber(IntegerNumber::U128(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U128(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I8(n1)),
                    Value::IntegerNumber(IntegerNumber::I8(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I8(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I16(n1)),
                    Value::IntegerNumber(IntegerNumber::I16(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I16(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I32(n1)),
                    Value::IntegerNumber(IntegerNumber::I32(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I32(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I64(n1)),
                    Value::IntegerNumber(IntegerNumber::I64(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I64(n1 + n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I128(n1)),
                    Value::IntegerNumber(IntegerNumber::I128(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I128(n1 + n2))]),
                (Value::FloatNumber(n1), Value::FloatNumber(n2)) => {
                    Ok(vec![Value::FloatNumber(n1 + n2)])
                }
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in + function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        ),
        pop2_push1(
            &all_number_types,
            None,
            "-".into(),
            Rc::new(Box::new(|args: Vec<Value>| match (&args[0], &args[1]) {
                (
                    Value::IntegerNumber(IntegerNumber::U8(n1)),
                    Value::IntegerNumber(IntegerNumber::U8(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U8(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U16(n1)),
                    Value::IntegerNumber(IntegerNumber::U16(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U16(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U32(n1)),
                    Value::IntegerNumber(IntegerNumber::U32(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U32(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U64(n1)),
                    Value::IntegerNumber(IntegerNumber::U64(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U64(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U128(n1)),
                    Value::IntegerNumber(IntegerNumber::U128(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U128(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I8(n1)),
                    Value::IntegerNumber(IntegerNumber::I8(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I8(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I16(n1)),
                    Value::IntegerNumber(IntegerNumber::I16(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I16(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I32(n1)),
                    Value::IntegerNumber(IntegerNumber::I32(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I32(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I64(n1)),
                    Value::IntegerNumber(IntegerNumber::I64(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I64(n1 - n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I128(n1)),
                    Value::IntegerNumber(IntegerNumber::I128(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I128(n1 - n2))]),
                (Value::FloatNumber(n1), Value::FloatNumber(n2)) => {
                    Ok(vec![Value::FloatNumber(n1 - n2)])
                }
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in - function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        ),
        pop2_push1(
            &all_number_types,
            None,
            "%".into(),
            Rc::new(Box::new(|args: Vec<Value>| match (&args[0], &args[1]) {
                (
                    Value::IntegerNumber(IntegerNumber::U8(n1)),
                    Value::IntegerNumber(IntegerNumber::U8(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U8(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U16(n1)),
                    Value::IntegerNumber(IntegerNumber::U16(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U16(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U32(n1)),
                    Value::IntegerNumber(IntegerNumber::U32(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U32(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U64(n1)),
                    Value::IntegerNumber(IntegerNumber::U64(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U64(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::U128(n1)),
                    Value::IntegerNumber(IntegerNumber::U128(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::U128(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I8(n1)),
                    Value::IntegerNumber(IntegerNumber::I8(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I8(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I16(n1)),
                    Value::IntegerNumber(IntegerNumber::I16(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I16(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I32(n1)),
                    Value::IntegerNumber(IntegerNumber::I32(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I32(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I64(n1)),
                    Value::IntegerNumber(IntegerNumber::I64(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I64(n1 % n2))]),
                (
                    Value::IntegerNumber(IntegerNumber::I128(n1)),
                    Value::IntegerNumber(IntegerNumber::I128(n2)),
                ) => Ok(vec![Value::IntegerNumber(IntegerNumber::I128(n1 % n2))]),
                (Value::FloatNumber(n1), Value::FloatNumber(n2)) => {
                    Ok(vec![Value::FloatNumber(n1 % n2)])
                }
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in - function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        ),
        pop2_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            ">".into(),
            Rc::new(Box::new(|args: Vec<Value>| match (&args[0], &args[1]) {
                (
                    Value::IntegerNumber(IntegerNumber::U8(n1)),
                    Value::IntegerNumber(IntegerNumber::U8(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U16(n1)),
                    Value::IntegerNumber(IntegerNumber::U16(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U32(n1)),
                    Value::IntegerNumber(IntegerNumber::U32(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U64(n1)),
                    Value::IntegerNumber(IntegerNumber::U64(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U128(n1)),
                    Value::IntegerNumber(IntegerNumber::U128(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I8(n1)),
                    Value::IntegerNumber(IntegerNumber::I8(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I16(n1)),
                    Value::IntegerNumber(IntegerNumber::I16(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I32(n1)),
                    Value::IntegerNumber(IntegerNumber::I32(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I64(n1)),
                    Value::IntegerNumber(IntegerNumber::I64(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I128(n1)),
                    Value::IntegerNumber(IntegerNumber::I128(n2)),
                ) => Ok(vec![Value::Boolean(n1 > n2)]),
                (Value::FloatNumber(n1), Value::FloatNumber(n2)) => {
                    Ok(vec![Value::Boolean(n1 > n2)])
                }
                (Value::String(n1), Value::String(n2)) => Ok(vec![Value::Boolean(n1 > n2)]),
                (Value::Boolean(n1), Value::Boolean(n2)) => Ok(vec![Value::Boolean(n1 > n2)]),
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in > function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        ),
        pop2_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            "<".into(),
            Rc::new(Box::new(|args: Vec<Value>| match (&args[0], &args[1]) {
                (
                    Value::IntegerNumber(IntegerNumber::U8(n1)),
                    Value::IntegerNumber(IntegerNumber::U8(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U16(n1)),
                    Value::IntegerNumber(IntegerNumber::U16(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U32(n1)),
                    Value::IntegerNumber(IntegerNumber::U32(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U64(n1)),
                    Value::IntegerNumber(IntegerNumber::U64(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U128(n1)),
                    Value::IntegerNumber(IntegerNumber::U128(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I8(n1)),
                    Value::IntegerNumber(IntegerNumber::I8(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I16(n1)),
                    Value::IntegerNumber(IntegerNumber::I16(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I32(n1)),
                    Value::IntegerNumber(IntegerNumber::I32(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I64(n1)),
                    Value::IntegerNumber(IntegerNumber::I64(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I128(n1)),
                    Value::IntegerNumber(IntegerNumber::I128(n2)),
                ) => Ok(vec![Value::Boolean(n1 < n2)]),
                (Value::FloatNumber(n1), Value::FloatNumber(n2)) => {
                    Ok(vec![Value::Boolean(n1 < n2)])
                }
                (Value::String(n1), Value::String(n2)) => Ok(vec![Value::Boolean(n1 < n2)]),
                (Value::Boolean(n1), Value::Boolean(n2)) => Ok(vec![Value::Boolean(n1 < n2)]),
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in < function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        ),
        pop2_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            "=".into(),
            Rc::new(Box::new(|args: Vec<Value>| match (&args[0], &args[1]) {
                (
                    Value::IntegerNumber(IntegerNumber::U8(n1)),
                    Value::IntegerNumber(IntegerNumber::U8(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U16(n1)),
                    Value::IntegerNumber(IntegerNumber::U16(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U32(n1)),
                    Value::IntegerNumber(IntegerNumber::U32(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U64(n1)),
                    Value::IntegerNumber(IntegerNumber::U64(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U128(n1)),
                    Value::IntegerNumber(IntegerNumber::U128(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I8(n1)),
                    Value::IntegerNumber(IntegerNumber::I8(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I16(n1)),
                    Value::IntegerNumber(IntegerNumber::I16(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I32(n1)),
                    Value::IntegerNumber(IntegerNumber::I32(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I64(n1)),
                    Value::IntegerNumber(IntegerNumber::I64(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I128(n1)),
                    Value::IntegerNumber(IntegerNumber::I128(n2)),
                ) => Ok(vec![Value::Boolean(n1 == n2)]),
                (Value::FloatNumber(n1), Value::FloatNumber(n2)) => {
                    Ok(vec![Value::Boolean(n1 == n2)])
                }
                (Value::String(n1), Value::String(n2)) => Ok(vec![Value::Boolean(n1 == n2)]),
                (Value::Boolean(n1), Value::Boolean(n2)) => Ok(vec![Value::Boolean(n1 == n2)]),
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in == function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        ),
        pop2_push1(
            &all_integer_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            "!=".into(),
            Rc::new(Box::new(|args: Vec<Value>| match (&args[0], &args[1]) {
                (
                    Value::IntegerNumber(IntegerNumber::U8(n1)),
                    Value::IntegerNumber(IntegerNumber::U8(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U16(n1)),
                    Value::IntegerNumber(IntegerNumber::U16(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U32(n1)),
                    Value::IntegerNumber(IntegerNumber::U32(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U64(n1)),
                    Value::IntegerNumber(IntegerNumber::U64(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::U128(n1)),
                    Value::IntegerNumber(IntegerNumber::U128(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I8(n1)),
                    Value::IntegerNumber(IntegerNumber::I8(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I16(n1)),
                    Value::IntegerNumber(IntegerNumber::I16(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I32(n1)),
                    Value::IntegerNumber(IntegerNumber::I32(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I64(n1)),
                    Value::IntegerNumber(IntegerNumber::I64(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (
                    Value::IntegerNumber(IntegerNumber::I128(n1)),
                    Value::IntegerNumber(IntegerNumber::I128(n2)),
                ) => Ok(vec![Value::Boolean(n1 != n2)]),
                (Value::FloatNumber(n1), Value::FloatNumber(n2)) => {
                    Ok(vec![Value::Boolean(n1 != n2)])
                }
                (Value::String(n1), Value::String(n2)) => Ok(vec![Value::Boolean(n1 != n2)]),
                (Value::Boolean(n1), Value::Boolean(n2)) => Ok(vec![Value::Boolean(n1 != n2)]),
                (other1, other2) => Err(RuntimeError::Unexpected(format!(
                    "Unexpected types used in < function. {:?} {:?}",
                    other1, other2
                ))),
            })),
        ),
    ]
    .concat()
}

fn pop1_push0(
    types: &[UnitType],
    name: String,
    function: Rc<Box<dyn Fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>>>,
) -> Vec<InternalFunction> {
    let mut result = Vec::new();
    for ty in types {
        result.push(InternalFunction {
            arity: 1,
            name: name.clone(),
            ty: Type::new(vec![ty.clone()], vec![]),
            function: function.clone(),
        });
    }
    result
}

fn pop2_push1(
    pop_types: &[UnitType],
    push_type: Option<UnitType>,
    name: String,
    function: Rc<Box<dyn Fn(Vec<Value>) -> Result<Vec<Value>, RuntimeError>>>,
) -> Vec<InternalFunction> {
    let mut result = Vec::new();
    for ty in pop_types {
        result.push(InternalFunction {
            arity: 2,
            name: name.clone(),
            ty: Type::new(
                vec![ty.clone(), ty.clone()],
                vec![push_type.clone().unwrap_or(ty.clone())],
            ),
            function: function.clone(),
        });
    }
    result
}
