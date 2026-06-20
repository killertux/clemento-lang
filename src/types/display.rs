use std::{
    collections::HashMap,
    fmt::{Display, Formatter},
};

use super::signature::{Effect, Type, VarType};
use super::unit_type::{LiteralType, NumberType, UnitType};

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
            UnitType::Literal(LiteralType::Char) => "Char".into(),
            UnitType::Literal(LiteralType::CStr) => "CStr".into(),
            UnitType::Literal(LiteralType::Ptr) => "Ptr".into(),
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

impl Display for Type {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut var_t_container = VarTypeToCharContainer::new();
        let push = self
            .push_types
            .iter()
            .map(|t| t.to_consistent_string(&mut var_t_container))
            .collect::<Vec<String>>()
            .join(" ");
        let effects = self
            .effects
            .iter()
            .map(|e| e.to_consistent_string(&mut var_t_container))
            .collect::<Vec<String>>()
            .join(" ");
        let output = match (push.is_empty(), effects.is_empty()) {
            (_, true) => push,
            (true, false) => effects,
            (false, false) => format!("{push} {effects}"),
        };
        write!(
            f,
            "({} -> {})",
            self.pop_types
                .iter()
                .map(|t| t.to_consistent_string(&mut var_t_container))
                .collect::<Vec<String>>()
                .join(" "),
            output,
        )
    }
}

impl Effect {
    pub fn to_consistent_string(&self, var_t: &mut VarTypeToCharContainer) -> String {
        match self {
            Effect::Named(name) => format!("!{}", name.join("::")),
            Effect::Var(var_type) => format!("!{}", var_t.get_string(var_type)),
            Effect::Wildcard => "!*".into(),
        }
    }
}

impl Display for Effect {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.to_consistent_string(&mut VarTypeToCharContainer::new())
        )
    }
}
