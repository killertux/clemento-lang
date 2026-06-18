use std::collections::HashMap;

use crate::lexer::Position;
use crate::types::{Type, UnitType, VarType};

use super::{TypeCheckerError, TypeScope};

pub(super) fn replace_custom_unit_type(
    scope: &mut TypeScope,
    ty: UnitType,
) -> Result<UnitType, TypeCheckerError> {
    match ty {
        UnitType::Custom {
            name,
            generic_types,
        } => {
            let Some(ty) = scope.get_type(name.clone()) else {
                return Err(TypeCheckerError::TypeNotFound(name));
            };
            if ty.generics.len() != generic_types.len() {
                return Err(TypeCheckerError::TypeNotFound(name));
            }
            Ok(UnitType::Custom {
                name: ty.name,
                generic_types: generic_types
                    .into_iter()
                    .map(|ty| replace_custom_unit_type(scope, ty))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        other => Ok(other),
    }
}

pub(super) fn substitute_types(
    type_stack: &[UnitType],
    type_definition: Type,
    position: Position,
) -> Result<Type, TypeCheckerError> {
    let variable_substitution = validate_types_and_return_variable_substitution(
        type_stack,
        &type_definition.pop_types,
        position,
    )?;

    Ok(apply_substitution(&variable_substitution, type_definition))
}

fn apply_substitution(
    variable_substitution: &HashMap<VarType, UnitType>,
    type_definition: Type,
) -> Type {
    Type::new(
        type_definition
            .pop_types
            .into_iter()
            .map(|ty| substitute_unit_type(variable_substitution, ty))
            .collect(),
        type_definition
            .push_types
            .into_iter()
            .map(|ty| substitute_unit_type(variable_substitution, ty))
            .collect(),
    )
}

pub(super) fn substitute_unit_type(
    variable_substitution: &HashMap<VarType, UnitType>,
    ty: UnitType,
) -> UnitType {
    match ty {
        UnitType::Var(var) => variable_substitution
            .get(&var)
            .cloned()
            .unwrap_or(UnitType::Var(var)),
        UnitType::Custom {
            name,
            generic_types,
        } => UnitType::Custom {
            name,
            generic_types: generic_types
                .into_iter()
                .map(|generic_type| match generic_type {
                    UnitType::Var(var) => variable_substitution
                        .get(&var)
                        .cloned()
                        .unwrap_or(UnitType::Var(var)),
                    other => other,
                })
                .collect(),
        },
        other => other,
    }
}

pub(super) fn validate_types_and_return_variable_substitution(
    type_stack_1: &[UnitType],
    type_stack_2: &[UnitType],
    position: Position,
) -> Result<HashMap<VarType, UnitType>, TypeCheckerError> {
    let mut variable_substitution: HashMap<VarType, UnitType> = HashMap::new();
    let stack_pop_types = &type_stack_1[type_stack_1.len().saturating_sub(type_stack_2.len())..];
    for (i, ty) in stack_pop_types.iter().enumerate() {
        match (ty, &type_stack_2[i]) {
            (UnitType::Literal(lit1), UnitType::Literal(lit2)) if lit1 == lit2 => {}
            // Binding a type variable to a literal — either order (unification is
            // symmetric; the actual value may be on either side).
            (UnitType::Literal(lit), UnitType::Var(var))
            | (UnitType::Var(var), UnitType::Literal(lit)) => {
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
            (
                UnitType::Custom {
                    name,
                    generic_types,
                },
                UnitType::Var(var),
            )
            | (
                UnitType::Var(var),
                UnitType::Custom {
                    name,
                    generic_types,
                },
            ) => {
                let ty = UnitType::Custom {
                    name: name.clone(),
                    generic_types: generic_types.clone(),
                };
                let existent = variable_substitution.insert(var.clone(), ty.clone());
                if let Some(existent) = existent
                    && existent != ty
                {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        Box::new(existent),
                        Box::new(ty),
                    ));
                }
            }
            (
                UnitType::Custom {
                    name: name1,
                    generic_types: generic_types1,
                },
                UnitType::Custom {
                    name: name2,
                    generic_types: generic_types2,
                },
            ) => {
                if name1 != name2 {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        Box::new(UnitType::Custom {
                            name: name1.clone(),
                            generic_types: generic_types1.clone(),
                        }),
                        Box::new(UnitType::Custom {
                            name: name2.clone(),
                            generic_types: generic_types2.clone(),
                        }),
                    ));
                }
                if generic_types1.len() != generic_types2.len() {
                    return Err(TypeCheckerError::TypeConflict(
                        position,
                        Box::new(UnitType::Custom {
                            name: name1.clone(),
                            generic_types: generic_types1.clone(),
                        }),
                        Box::new(UnitType::Custom {
                            name: name2.clone(),
                            generic_types: generic_types2.clone(),
                        }),
                    ));
                }

                variable_substitution.extend(validate_types_and_return_variable_substitution(
                    generic_types1,
                    generic_types2,
                    position.clone(),
                )?);
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
