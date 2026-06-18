use super::signature::VarType;
use super::unit_type::UnitType;

#[derive(Debug, Clone)]
pub struct CustomType {
    pub name: Vec<String>,
    pub generics: Vec<(String, VarType)>,
    pub variants: Vec<(String, Vec<(String, UnitType)>)>,
}
