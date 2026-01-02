use std::{cell::RefCell, collections::HashMap, fmt::Display, rc::Rc};

use thiserror::Error;

use crate::{
    lexer::{IntegerNumber, Number, Position},
    parser::{
        AstNode, AstNodeType, Case, Import, LiteralType, NumberType, Pattern, Type, UnitType,
        VarType, VarTypeToCharContainer,
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
    type_definitions: HashMap<Vec<String>, CustomType>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            imports: HashMap::new(),
            type_definitions: HashMap::new(),
        }
    }

    pub fn type_check(
        &mut self,
        program: AstNode,
        check_for_main: bool,
        module_path: Vec<String>,
    ) -> Result<(AstNodeWithType, TypeScope), TypeCheckerError> {
        let mut scope = TypeScope::empty();
        let AstNodeType::Block(nodes) = program.node_type else {
            return Err(TypeCheckerError::InvalidModuleDefinition(Box::new(
                Type::empty(),
            )));
        };

        let (block_type_check_result, nodes_with_types) =
            self.type_check_block(&mut scope, Vec::new(), nodes, check_for_main, module_path)?;
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
        module_path: Vec<String>,
    ) -> Result<(Type, Vec<AstNodeWithType>), TypeCheckerError> {
        let mut node_results = Vec::new();
        let mut pop_type_stack: Vec<UnitType> = Vec::new();
        let mut local_stack: Vec<UnitType> = Vec::new();
        for node in program {
            let node =
                self.infer_type_definition(scope, type_stack.clone(), node, module_path.clone())?;
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
            let push_types =
                substitute_types(&type_stack, type_definition.clone(), node.position.clone())?
                    .push_types;
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
        mut node: AstNode,
        module_path: Vec<String>,
    ) -> Result<AstNodeWithType, TypeCheckerError> {
        node.type_definition = match node.type_definition {
            Some(ty) => Some(self.replace_custom_type(scope, ty.clone())?),
            None => None,
        };
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
                validate_types_and_return_variable_substitution(
                    &type_stack,
                    &type_definition.pop_types,
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
                validate_types_and_return_variable_substitution(
                    &type_stack,
                    &type_definition.pop_types,
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
                let (ty, nodes) = self.type_check_block(
                    &mut scope,
                    type_stack.clone(),
                    nodes,
                    false,
                    module_path,
                )?;
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
                    let ty = self.replace_custom_type(scope, ty.clone())?;
                    scope.insert_definition(symbol.clone(), ty, is_private);
                    let body = self.infer_type_definition(scope, Vec::new(), *body, module_path)?;
                    body
                } else {
                    let body = self.infer_type_definition(scope, Vec::new(), *body, module_path)?;
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
                let ty = self.replace_custom_type(scope, ty.clone())?;
                scope.insert_definition(symbol.clone(), ty.clone(), false);
                Ok(AstNodeWithType::new(
                    AstNodeType::ExternalDefinition(symbol, ty),
                    node.position.clone(),
                    Type::empty(),
                ))
            }
            AstNodeType::Import(path, import_node) => {
                let result_node = if let Some(nodes) = import_node.node {
                    // let mut module_path = module_path.clone();
                    // module_path.extend(path.clone());
                    let result = self.type_check(nodes, false, path.clone())?;
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
                    AstNodeType::Import(path, Box::new(result_node)),
                    node.position.clone(),
                    Type::empty(),
                ))
            }

            AstNodeType::CustomType {
                name,
                generics,
                variants,
            } => {
                let mut name_with_path = module_path.clone();
                name_with_path.push(name.clone());
                scope.insert_type_definition(
                    name_with_path.clone(),
                    generics.clone(),
                    variants.clone(),
                );
                self.type_definitions.insert(
                    name_with_path.clone(),
                    CustomType {
                        name: name_with_path.clone(),
                        generics: generics.clone(),
                        variants: variants.clone(),
                    },
                );
                for variant in variants.iter() {
                    scope.insert_definition(
                        variant.0.clone(),
                        Type::new(
                            variant.1.iter().map(|(_, ty)| ty.clone()).collect(),
                            vec![UnitType::Custom {
                                name: name_with_path.clone(),
                                generic_types: generics
                                    .iter()
                                    .map(|g| UnitType::Var(g.1.clone()))
                                    .collect(),
                            }],
                        ),
                        false,
                    );
                }

                Ok(AstNodeWithType::new(
                    AstNodeType::CustomType {
                        name,
                        generics,
                        variants,
                    },
                    node.position.clone(),
                    Type::empty(),
                ))
            }
            AstNodeType::Match(cases) => self.type_check_match(
                scope,
                cases,
                &type_stack,
                node.position.clone(),
                module_path,
            ),
        }?;
        Ok(match node.type_definition.clone() {
            Some(ty) => {
                let push_types = substitute_types(
                    &type_stack,
                    inferred_type.type_definition.clone(),
                    node.position.clone(),
                )?
                .push_types;

                if validate_types_and_return_variable_substitution(
                    &ty.push_types,
                    &push_types,
                    node.position.clone(),
                )
                .is_err()
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

    fn replace_custom_type(
        &self,
        scope: &mut TypeScope,
        ty: Type,
    ) -> Result<Type, TypeCheckerError> {
        let pop_types = ty
            .pop_types
            .into_iter()
            .map(|ty| match ty {
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
                        generic_types,
                    })
                }
                other => Ok(other),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let push_types = ty
            .push_types
            .into_iter()
            .map(|ty| match ty {
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
                        generic_types,
                    })
                }
                other => Ok(other),
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Type::new(pop_types, push_types))
    }

    fn type_check_match(
        &mut self,
        scope: &mut TypeScope,
        cases: Vec<Case<AstNode>>,
        type_stack: &[UnitType],
        position: Position,
        module_path: Vec<String>,
    ) -> Result<AstNodeWithType, TypeCheckerError> {
        let match_type = type_stack
            .last()
            .cloned()
            .ok_or(TypeCheckerError::MatchCannotInferType(position.clone()))?;
        if cases
            .iter()
            .position(|case| matches!(case.pattern, Pattern::Wildcard(_)))
            .map(|pos| pos != cases.len() - 1)
            .unwrap_or(false)
        {
            return Err(TypeCheckerError::MatchWildcardNotAtTheEnd(position));
        }
        let type_stack_without_last_element =
            &type_stack[..type_stack.len().saturating_sub(1)].to_vec();
        let mut pattern_body_type = None;
        match &match_type {
            UnitType::Literal(LiteralType::Number(_)) => {
                let len = cases.len();
                let mut result_cases = Vec::with_capacity(len);
                for (pos, case) in cases.clone().into_iter().enumerate() {
                    if pos == len - 1 && !matches!(case.pattern, Pattern::Wildcard(_)) {
                        return Err(TypeCheckerError::MissingWildcardMatch(position));
                    }
                    match &case.pattern {
                        Pattern::Number(number_pattern) => {
                            if match_type != number_pattern.to_unit_type() {
                                return Err(TypeCheckerError::InvalidPatternForType(
                                    match_type.clone(),
                                    Pattern::Number(number_pattern.clone()),
                                    position.clone(),
                                ));
                            }
                            let mut body_type = self.infer_type_definition(
                                scope,
                                type_stack_without_last_element.clone(),
                                *case.body,
                                module_path.clone(),
                            )?;
                            body_type.type_definition = substitute_types(
                                type_stack_without_last_element,
                                body_type.type_definition,
                                position.clone(),
                            )?;
                            match pattern_body_type {
                                Some(existing) => {
                                    if existing != body_type.type_definition {
                                        return Err(TypeCheckerError::InvalidMatchBody(
                                            existing,
                                            body_type.type_definition,
                                            position.clone(),
                                        ));
                                    }
                                }
                                None => {}
                            }
                            result_cases.push(Case {
                                pattern: case.pattern,
                                body: Box::new(body_type.clone()),
                            });
                            pattern_body_type = Some(body_type.type_definition);
                        }
                        Pattern::Wildcard(name) => {
                            let mut scope = TypeScope::with_parent(scope.clone());
                            if let Some(name) = name {
                                scope.insert_definition(
                                    name.clone(),
                                    Type::new(vec![], vec![match_type.clone()]),
                                    false,
                                );
                            }
                            let mut body_type = self.infer_type_definition(
                                &mut scope,
                                type_stack_without_last_element.clone(),
                                *case.body,
                                module_path.clone(),
                            )?;
                            body_type.type_definition = substitute_types(
                                type_stack_without_last_element,
                                body_type.type_definition,
                                position.clone(),
                            )?;
                            match pattern_body_type {
                                Some(existing) => {
                                    if existing != body_type.type_definition {
                                        return Err(TypeCheckerError::InvalidMatchBody(
                                            existing,
                                            body_type.type_definition,
                                            position.clone(),
                                        ));
                                    }
                                }
                                None => {}
                            }
                            result_cases.push(Case {
                                pattern: case.pattern,
                                body: Box::new(body_type.clone()),
                            });
                            pattern_body_type = Some(body_type.type_definition);
                        }
                        other => {
                            return Err(TypeCheckerError::InvalidPatternForType(
                                match_type.clone(),
                                other.clone(),
                                position.clone(),
                            ));
                        }
                    }
                }
                Ok(AstNodeWithType {
                    node_type: AstNodeType::Match(result_cases),
                    position: position.clone(),
                    type_definition: Type::new(
                        pattern_body_type
                            .clone()
                            .map(|mut t| {
                                t.pop_types.extend_from_slice(&[match_type.clone()]);
                                t.pop_types
                            })
                            .unwrap_or(vec![match_type]),
                        pattern_body_type.map(|t| t.push_types).unwrap_or(vec![]),
                    ),
                })
            }
            UnitType::Custom {
                name,
                generic_types,
            } => {
                let Some(custom_type) = self.type_definitions.get(name) else {
                    return Err(TypeCheckerError::TypeNotFound(name.clone()));
                };
                let generics_map: HashMap<VarType, UnitType> = custom_type
                    .generics
                    .iter()
                    .map(|g| g.1.clone())
                    .zip(generic_types.iter().cloned())
                    .collect();
                let mut variants: HashMap<String, Vec<(String, UnitType)>> =
                    custom_type.variants.iter().cloned().collect();
                let mut result_cases = Vec::with_capacity(cases.len());
                for case in cases.clone().into_iter() {
                    match &case.pattern {
                        Pattern::Variant {
                            variant_name,
                            fields,
                        } => {
                            let Some(variant_constructor) =
                                scope.get_definition(variant_name.clone(), true)
                            else {
                                return Err(TypeCheckerError::TypeNotFound(variant_name.clone()));
                            };
                            let UnitType::Custom { .. } = variant_constructor.push_types[0].clone()
                            else {
                                return Err(TypeCheckerError::TypeNotFound(variant_name.clone()));
                            };
                            if !variants.contains_key(&variant_name[variant_name.len() - 1]) {
                                return Err(TypeCheckerError::InvalidMatchVariant(
                                    variant_name.join("::"),
                                    position.clone(),
                                ));
                            }
                            let fields_with_types = variants
                                .remove(&variant_name[variant_name.len() - 1])
                                .expect("We checked that the variant exists")
                                .into_iter()
                                .map(|field| {
                                    (
                                        field.0,
                                        match field.1 {
                                            UnitType::Var(v) => generics_map
                                                .get(&v)
                                                .cloned()
                                                .unwrap_or(UnitType::Var(v)),
                                            other => other,
                                        },
                                    )
                                })
                                .collect::<HashMap<_, _>>();
                            let mut scope = TypeScope::with_parent(scope.clone());
                            for field in fields {
                                let field_ty = fields_with_types.get(&field.name).ok_or(
                                    TypeCheckerError::FieldNotFoundInVariant(
                                        field.name.clone(),
                                        variant_name.join("::"),
                                    ),
                                )?;
                                scope.insert_definition(
                                    field.alias.clone(),
                                    Type::new(vec![], vec![field_ty.clone()]),
                                    false,
                                );
                            }
                            let mut body_type = self.infer_type_definition(
                                &mut scope,
                                type_stack_without_last_element.clone(),
                                *case.body,
                                module_path.clone(),
                            )?;
                            body_type.type_definition = substitute_types(
                                type_stack_without_last_element,
                                body_type.type_definition,
                                position.clone(),
                            )?;
                            match pattern_body_type {
                                Some(existing) => {
                                    if existing != body_type.type_definition {
                                        return Err(TypeCheckerError::InvalidMatchBody(
                                            existing,
                                            body_type.type_definition,
                                            position.clone(),
                                        ));
                                    }
                                }
                                None => {}
                            }
                            result_cases.push(Case {
                                pattern: case.pattern,
                                body: Box::new(body_type.clone()),
                            });
                            pattern_body_type = Some(body_type.type_definition);
                        }
                        Pattern::Wildcard(alias) => {
                            let mut scope = TypeScope::with_parent(scope.clone());
                            if let Some(alias) = alias {
                                scope.insert_definition(
                                    alias.clone(),
                                    Type::new(vec![], vec![match_type.clone()]),
                                    false,
                                );
                            }
                            let mut body_type = self.infer_type_definition(
                                &mut scope,
                                type_stack_without_last_element.clone(),
                                *case.body,
                                module_path.clone(),
                            )?;
                            body_type.type_definition = substitute_types(
                                type_stack_without_last_element,
                                body_type.type_definition,
                                position.clone(),
                            )?;

                            variants.clear();
                            match pattern_body_type {
                                Some(existing) => {
                                    if existing != body_type.type_definition {
                                        return Err(TypeCheckerError::InvalidMatchBody(
                                            existing,
                                            body_type.type_definition,
                                            position.clone(),
                                        ));
                                    }
                                }
                                None => {}
                            }
                            result_cases.push(Case {
                                pattern: case.pattern,
                                body: Box::new(body_type.clone()),
                            });
                            pattern_body_type = Some(body_type.type_definition);
                        }
                        other => {
                            return Err(TypeCheckerError::InvalidPatternForType(
                                match_type.clone(),
                                other.clone(),
                                position.clone(),
                            ));
                        }
                    }
                }
                if variants.len() != 0 {
                    return Err(TypeCheckerError::NonExhaustiveMatch(position.clone()));
                }
                Ok(AstNodeWithType {
                    node_type: AstNodeType::Match(result_cases),
                    position: position.clone(),
                    type_definition: Type::new(
                        pattern_body_type
                            .clone()
                            .map(|mut t| {
                                t.pop_types.extend_from_slice(&[match_type.clone()]);
                                t.pop_types
                            })
                            .unwrap_or(vec![match_type]),
                        pattern_body_type.map(|t| t.push_types).unwrap_or(vec![]),
                    ),
                })
            }
            other => Err(TypeCheckerError::InvalidMatchType(other.clone(), position)),
        }
    }
}

fn substitute_types(
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
            .map(|ty| match ty {
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
            })
            .collect(),
    )
}

pub fn validate_types_and_return_variable_substitution(
    type_stack_1: &[UnitType],
    type_stack_2: &[UnitType],
    position: Position,
) -> Result<HashMap<VarType, UnitType>, TypeCheckerError> {
    let mut variable_substitution: HashMap<VarType, UnitType> = HashMap::new();
    let stack_pop_types = &type_stack_1[type_stack_1.len().saturating_sub(type_stack_2.len())..];
    for (i, ty) in stack_pop_types.iter().enumerate() {
        match (ty, &type_stack_2[i]) {
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
            (
                UnitType::Custom {
                    name,
                    generic_types,
                },
                UnitType::Var(var),
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

                variable_substitution.extend(
                    validate_types_and_return_variable_substitution(
                        generic_types1,
                        generic_types2,
                        position.clone(),
                    )?
                    .into_iter(),
                );
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
    #[error("Missing import {0}")]
    MissingImport(String),
    #[error("Type not found {0:?}")]
    TypeNotFound(Vec<String>),
    #[error("Match cannot infer type at {0}")]
    MatchCannotInferType(Position),
    #[error("Invalid match type {0} at {1}")]
    InvalidMatchType(UnitType, Position),
    #[error("Match wildcard not at the end at {0}")]
    MatchWildcardNotAtTheEnd(Position),
    #[error("Invalid pattern {1} for type {0} at {2}")]
    InvalidPatternForType(UnitType, Pattern, Position),
    #[error("Missing wildcard match at {0}")]
    MissingWildcardMatch(Position),
    #[error("Invalid match body at {2}. Expected {0} but got {1}")]
    InvalidMatchBody(Type, Type, Position),
    #[error("Invalid match variant {0} at {1}")]
    InvalidMatchVariant(String, Position),
    #[error("Field {0} not found in variant {1}")]
    FieldNotFoundInVariant(String, String),
    #[error("Non-exhaustive match at {0}")]
    NonExhaustiveMatch(Position),
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
    type_definitions: HashMap<String, CustomType>,
}

#[derive(Debug, Clone)]
pub struct CustomType {
    pub name: Vec<String>,
    pub generics: Vec<(String, VarType)>,
    pub variants: Vec<(String, Vec<(String, UnitType)>)>,
}

impl TypeScope {
    fn with_parent(parent: TypeScope) -> TypeScope {
        TypeScope {
            inner: Rc::new(RefCell::new(InnerTypeScope {
                parent: Some(parent),
                imported: HashMap::new(),
                imported_functions: HashMap::new(),
                definitions: HashMap::new(),
                type_definitions: HashMap::new(),
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
                type_definitions: HashMap::new(),
            })),
        }
    }

    fn insert_type_definition(
        &self,
        name: Vec<String>,
        generics: Vec<(String, VarType)>,
        variants: Vec<(String, Vec<(String, UnitType)>)>,
    ) {
        let mut inner = self.inner.borrow_mut();
        inner.type_definitions.insert(
            name.last()
                .expect("A type should always have a name")
                .clone(),
            CustomType {
                name,
                generics,
                variants,
            },
        );
    }

    fn get_type(&self, mut name: Vec<String>) -> Option<CustomType> {
        match name.len() {
            0 => None,
            1 => {
                let inner = self.inner.borrow();
                let last = name.last().expect("We checked for the name size").clone();
                if let Some(from_definitions) = inner
                    .type_definitions
                    .get(&last)
                    .cloned()
                    .and_then(|type_definition| Some(type_definition))
                {
                    return Some(from_definitions);
                }
                if let Some(imported_functions) = inner.imported_functions.get(&last) {
                    return self.get_type(vec![
                        imported_functions.1.clone(),
                        imported_functions.0.clone(),
                    ]);
                }
                if let Some(parent) = inner.parent.as_ref() {
                    return parent.get_type(name);
                }
                None
            }
            _ => {
                let inner = self.inner.borrow();
                let first = name.remove(0);
                if let Some(from_imports) = inner.imported.get(&first) {
                    return from_imports.get_type(name);
                }
                if let Some(parent) = inner.parent.as_ref() {
                    name.insert(0, first);
                    return parent.get_type(name);
                }

                None
            }
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
                vec![],
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

    #[test]
    fn boolean_type() {
        let contents = r#"
            type Bool {
                True False
            }

            def test ( -> Bool Bool) {
                True False
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Bool {True False} ( -> ) def test ( -> Bool Bool) {( -> Bool) True ( -> Bool) False}\n}"
        );
    }

    #[test]
    fn option_type() {
        let contents = r#"
            type Option<a> {
                Some(val a) None
            }

            def test ( -> Option<I64> Option<I64>) {
                42 Some None
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> Option<I64> Option<I64>) {( -> I64) 42i64 (I64 -> Option<I64>) Some ( -> Option<a>) None}\n}"
        );
    }

    #[test]
    fn empty_match() {
        let contents = r#"
            def main {
                10 match {}
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) def main ( -> ) {( -> I64) 10i64 (I64 -> ) match {}}\n}"
        );
    }

    #[test]
    fn match_number() {
        let contents = r#"
            def test {
                10 match { 0 -> "zero" 1 -> "one" * -> "big number" }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) def test ( -> String) {( -> I64) 10i64 (I64 -> String) match {0i64 => ( -> String) \"zero\" 1i64 => ( -> String) \"one\" * => ( -> String) \"big number\"}}\n}"
        );
    }

    #[test]
    fn match_without_stack_value() {
        let contents = r#"
            def test {
                match { }
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(result, "Match cannot infer type at 3:17");
    }

    #[test]
    fn match_number_wildcard_not_last() {
        let contents = r#"
            def test {
                10 match { * -> "wildcard" 1 -> "one" }
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(result, "Match wildcard not at the end at 3:20");
    }

    #[test]
    fn match_number_with_no_wildcard() {
        let contents = r#"
            def test {
                10 match { 1 -> "one" }
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(result, "Missing wildcard match at 3:20");
    }

    #[test]
    fn match_with_different_bodies() {
        let contents = r#"
            def test {
                10 match { 1 -> "one" * -> 10 }
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(
            result,
            "Invalid match body at 3:20. Expected ( -> String) but got ( -> I64)"
        );
    }

    #[test]
    fn match_with_correct_bodies_with_var() {
        let contents = r#"
            import std::stack

            def test {
                5 10 match { 1 -> stack::dup * -> stack::dup }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) import std::stack ( -> ) def test ( -> I64 I64) {( -> I64) 5i64 ( -> I64) 10i64 (I64 I64 -> I64 I64) match {1i64 => (I64 -> I64 I64) stack::dup * => (I64 -> I64 I64) stack::dup}}\n}"
        );
    }

    #[test]
    fn match_with_boolean() {
        let contents = r#"
            type Boolean {
                True False
            }

            def test {
                True match { True -> "True" False -> "False" }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Boolean {True False} ( -> ) def test ( -> String) {( -> Boolean) True (Boolean -> String) match {True => ( -> String) \"True\" False => ( -> String) \"False\"}}\n}"
        );
    }

    #[test]
    fn match_option() {
        let contents = r#"
            type Option<a> {
                Some(val a) None
            }

            def test {
                "Hi" Some match { Some(val) -> val None -> "None" }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> String) {( -> String) \"Hi\" (String -> Option<String>) Some (Option<String> -> String) match {(val) => ( -> String) val None => ( -> String) \"None\"}}\n}"
        );
    }

    #[test]
    fn match_option_with_wildcard() {
        let contents = r#"
            type Option<a> {
                Some(val a) None
            }

            def test {
                "Hi" Some match { * -> "Option" }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> String) {( -> String) \"Hi\" (String -> Option<String>) Some (Option<String> -> String) match {* => ( -> String) \"Option\"}}\n}"
        );
    }

    #[test]
    fn match_option_with_wildcard_2() {
        let contents = r#"
            type Option<a> {
                Some(val a) None
            }

            def test {
                "Hi" Some match { Some -> "Some"  * -> "Option" }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> String) {( -> String) \"Hi\" (String -> Option<String>) Some (Option<String> -> String) match {Some => ( -> String) \"Some\" * => ( -> String) \"Option\"}}\n}"
        );
    }

    #[test]
    fn match_option_with_wildcard_with_alias() {
        let contents = r#"
            type Option<a> {
                Some(val a) None
            }

            def test {
                "Hi" Some match { Some -> { "Some" Some }  * as rest -> rest }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> Option<String>) {( -> String) \"Hi\" (String -> Option<String>) Some (Option<String> -> Option<String>) match {Some => ( -> Option<String>) {( -> String) \"Some\" (String -> Option<String>) Some} * as rest => ( -> Option<String>) rest}}\n}"
        );
    }

    #[test]
    fn non_exhaustive_match() {
        let contents = r#"
            type Option<a> {
                Some(val a) None
            }

            def test {
                "Hi" Some match { Some -> "Some" }
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(result, "Non-exhaustive match at 7:27");
    }

    #[test]
    fn match_result() {
        let contents = r#"
            type Result<a b> {
                Ok(val a) Err(val b)
            }

            def test {
                "Hi" (String -> Result<String String>) Ok match { Ok(val as value) -> value Err(val as error) -> error }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Result<a b> {Ok(val a) Err(val a)} ( -> ) def test ( -> String) {( -> String) \"Hi\" (String -> Result<String String>) Ok (Result<String String> -> String) match {(val as value) => ( -> String) value (val as error) => ( -> String) error}}\n}"
        );
    }

    #[test]
    fn match_result_without_value() {
        let contents = r#"
            type Result<a b> {
                Ok(val a) Err(val b)
            }

            def test {
                "Hi" (String -> Result<String String>) Ok match { Ok -> "Ok" Err -> "Err" }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) type Result<a b> {Ok(val a) Err(val a)} ( -> ) def test ( -> String) {( -> String) \"Hi\" (String -> Result<String String>) Ok (Result<String String> -> String) match {Ok => ( -> String) \"Ok\" Err => ( -> String) \"Err\"}}\n}"
        );
    }

    #[test]
    fn different_types_with_same_name() {
        let contents = r#"
            import std::option
            import std::stack(drop)

            type Option<a> {
                Some(val a) None
            }

            def test1 (option::Option<I64> -> ) {
                drop
            }

            def test2 (Option<I64> -> ) {
                drop
            }

            def test {
                42 option::Some test1 42 Some test2
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) import std::option ( -> ) import std::stack(drop) ( -> ) type Option<a> {Some(val a) None} ( -> ) def test1 (std::option::Option<I64> -> ) {(std::option::Option<I64> -> ) drop}\n ( -> ) def test2 (Option<I64> -> ) {(Option<I64> -> ) drop}\n ( -> ) def test ( -> ) {( -> I64) 42i64 (I64 -> std::option::Option<I64>) option::Some (std::option::Option<I64> -> ) test1 ( -> I64) 42i64 (I64 -> Option<I64>) Some (Option<I64> -> ) test2}\n}"
        );
    }

    #[test]
    fn different_types_with_same_name_should_fail_1() {
        let contents = r#"
            import std::option
            import std::stack(drop)

            type Option<a> {
                Some(val a) None
            }

            def test_option (option::Option<I64> -> ) {
                drop
            }

            def test {
                42 Some test_option
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(
            result,
            "Type conflict at 14:25: expected Option<I64>, got std::option::Option<I64>"
        );
    }

    #[test]
    fn different_types_with_same_name_should_fail_2() {
        let contents = r#"
            import std::option
            import std::stack(drop)

            type Option<a> {
                Some(val a) None
            }

            def test_option (Option<I64> -> ) {
                drop
            }

            def test {
                42 option::Some test_option
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(
            result,
            "Type conflict at 14:33: expected std::option::Option<I64>, got Option<I64>"
        );
    }
}
