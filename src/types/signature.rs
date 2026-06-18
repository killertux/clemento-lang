use std::sync::atomic::{AtomicU64, Ordering};

use super::unit_type::{LiteralType, NumberType, UnitType};

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Type {
    pub pop_types: Vec<UnitType>,
    pub push_types: Vec<UnitType>,
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

    pub fn char() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![UnitType::Literal(LiteralType::Char)],
        }
    }

    pub(crate) fn empty() -> Self {
        Self {
            pop_types: vec![],
            push_types: vec![],
        }
    }
}
