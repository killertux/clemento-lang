use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
    fmt::Display,
    rc::Rc,
};

mod error;
mod unify;

pub use error::TypeCheckerError;
use unify::{
    apply_substitution, replace_custom_unit_type, substitute_types, substitute_unit_type,
    validate_types_and_return_variable_substitution,
};

use crate::{
    lexer::{IntegerNumber, Number, Position},
    parser::{AstNode, AstNodeType, Case, FieldPattern, Import, Pattern},
    types::{CustomType, LiteralType, NumberType, Type, UnitType, VarType, VarTypeToCharContainer},
};

/// Replaces every type variable in `ty` with a fresh one, consistently (the same
/// source variable maps to the same fresh variable via `remap`). Used so each
/// occurrence of a function-value reference gets independent variables — two
/// `\dup` references must not share `a`, or applying them at different types
/// would spuriously conflict.
fn freshen_type(ty: &Type, remap: &mut HashMap<VarType, VarType>) -> Type {
    Type::new(
        ty.pop_types
            .iter()
            .map(|u| freshen_unit(u, remap))
            .collect(),
        ty.push_types
            .iter()
            .map(|u| freshen_unit(u, remap))
            .collect(),
    )
}

fn freshen_unit(unit: &UnitType, remap: &mut HashMap<VarType, VarType>) -> UnitType {
    match unit {
        UnitType::Var(var) => UnitType::Var(
            remap
                .entry(var.clone())
                .or_insert_with(VarType::new)
                .clone(),
        ),
        UnitType::Custom {
            name,
            generic_types,
        } => UnitType::Custom {
            name: name.clone(),
            generic_types: generic_types
                .iter()
                .map(|g| freshen_unit(g, remap))
                .collect(),
        },
        UnitType::Type(inner) => UnitType::Type(freshen_type(inner, remap)),
        UnitType::Literal(_) => unit.clone(),
    }
}

/// Rewrites every `type_definition` in an AST subtree with `subst`, recursing
/// into nested blocks/quotations/match arms. Used to back-substitute the
/// apply-site bindings into a definition body (and to freshen quotation bodies).
fn apply_subst_to_node(node: &mut AstNodeWithType, subst: &HashMap<VarType, UnitType>) {
    node.type_definition = apply_substitution(subst, node.type_definition.clone());
    match &mut node.node_type {
        AstNodeType::Block(nodes) | AstNodeType::Quotation(nodes) => {
            for n in nodes {
                apply_subst_to_node(n, subst);
            }
        }
        AstNodeType::Match(cases) => {
            for case in cases {
                apply_subst_to_node(&mut case.body, subst);
            }
        }
        AstNodeType::Definition { body, .. } => apply_subst_to_node(body, subst),
        _ => {}
    }
}

/// Closes transitive chains in a substitution (`a -> b`, `b -> I64` becomes
/// `a -> I64`) so a single back-substitution pass fully concretizes. Capped to
/// avoid looping on `a -> b`, `b -> a` cycles.
fn resolve_substitution(map: &mut HashMap<VarType, UnitType>) {
    for _ in 0..map.len() + 1 {
        let mut changed = false;
        let keys: Vec<VarType> = map.keys().cloned().collect();
        for key in keys {
            let value = map.get(&key).cloned().expect("key came from the map");
            let resolved = substitute_unit_type(map, value.clone());
            if resolved != value {
                map.insert(key, resolved);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

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
    /// Accumulates the type-variable bindings discovered while checking the
    /// current definition's body (mostly at `apply` sites). After the body is
    /// checked it is back-substituted into the body so function-value
    /// references/quotations whose concrete type is pinned only by a downstream
    /// `apply` become concrete. Saved/restored per definition.
    function_value_subst: HashMap<VarType, UnitType>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            imports: HashMap::new(),
            type_definitions: HashMap::new(),
            function_value_subst: HashMap::new(),
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

        let (block_type_check_result, nodes_with_types) = self.type_check_block(
            &mut scope,
            Vec::new(),
            nodes,
            check_for_main,
            module_path,
            false,
        )?;
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
        // When true, bindings learned across the block are applied back to its
        // inferred signature so under-flowed inputs are resolved to concrete
        // types. Only quotations need this (their inferred signature *is* a
        // first-class value type that must not leak free variables); ordinary
        // blocks leave it off, because `match`-arm consistency compares arm
        // types by exact equality and relies on inputs keeping their original
        // (alpha-equivalent) variables across arms.
        resolve_inferred_inputs: bool,
    ) -> Result<(Type, Vec<AstNodeWithType>), TypeCheckerError> {
        let mut node_results = Vec::new();
        let mut pop_type_stack: Vec<UnitType> = Vec::new();
        let mut local_stack: Vec<UnitType> = Vec::new();
        // Bindings learned across the whole block. A word can constrain a type
        // variable that an earlier word introduced as an inferred input (e.g.
        // `\{ dup from_cstr }`: `dup` under-flows, making its operand an input
        // variable, then `from_cstr` pins that variable to `CStr`). We collect
        // every such binding and apply it once to the block's signature at the
        // end, so inferred inputs are resolved instead of leaking out as free
        // variables. We deliberately do NOT rewrite the working stacks mid-loop:
        // that would change variable identities the rest of inference (notably
        // `match`-arm consistency) relies on.
        let mut accumulated_subst: HashMap<VarType, UnitType> = HashMap::new();
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
            if resolve_inferred_inputs {
                accumulated_subst.extend(validate_types_and_return_variable_substitution(
                    &type_stack,
                    &type_definition.pop_types,
                    node.position.clone(),
                )?);
            }
            let push_types =
                substitute_types(&type_stack, type_definition.clone(), node.position.clone())?
                    .push_types;
            type_stack.truncate(type_stack.len() - pop_size);
            type_stack.extend(push_types.clone());
            local_stack.truncate(local_stack.len() - pop_size);
            local_stack.extend(push_types);
            node_results.push(node);
        }
        let (pop_type_stack, local_stack) = if resolve_inferred_inputs {
            resolve_substitution(&mut accumulated_subst);
            (
                pop_type_stack
                    .into_iter()
                    .map(|ty| substitute_unit_type(&accumulated_subst, ty))
                    .collect(),
                local_stack
                    .into_iter()
                    .map(|ty| substitute_unit_type(&accumulated_subst, ty))
                    .collect(),
            )
        } else {
            (pop_type_stack, local_stack)
        };

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
            AstNodeType::Char(c) => Ok(AstNodeWithType::new(
                AstNodeType::Char(c),
                node.position.clone(),
                Type::char(),
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
            // `apply` is a builtin whose stack effect depends on the function
            // value sitting on top of the stack, so it cannot be an ordinary
            // fixed-signature definition: pop the function value, then apply its
            // own signature (pop its inputs, push its outputs).
            AstNodeType::Symbol(symbol) if symbol == "apply" => {
                let Some(UnitType::Type(sig)) = type_stack.last().cloned() else {
                    let got = type_stack
                        .last()
                        .map(|t| t.to_string())
                        .unwrap_or_else(|| "an empty stack".to_string());
                    return Err(TypeCheckerError::ApplyOnNonFunction(
                        node.position.clone(),
                        got,
                    ));
                };
                // The function value occupies the top of the stack; its inputs
                // sit just below it. Unify the function's input types against
                // those actual values — this is what pins a polymorphic function
                // value's type (e.g. `\dup` applied to an I64 binds `a := I64`).
                // We intentionally do NOT unify the function value against itself
                // (that yields only useless `v := v` self-bindings).
                let args = &type_stack[..type_stack.len() - 1];
                let subst = validate_types_and_return_variable_substitution(
                    args,
                    &sig.pop_types,
                    node.position.clone(),
                )?;
                self.function_value_subst.extend(subst.clone());

                let mut pop_types = sig.pop_types.clone();
                pop_types.push(UnitType::Type(sig.clone()));
                let apply_ty = Type::new(pop_types, sig.push_types.clone());
                Ok(AstNodeWithType::new(
                    AstNodeType::Symbol(symbol),
                    node.position.clone(),
                    apply_substitution(&subst, apply_ty),
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
                    false,
                )?;
                Ok(AstNodeWithType::new(
                    AstNodeType::Block(nodes),
                    node.position.clone(),
                    substitute_types(&type_stack, ty, node.position.clone())?,
                ))
            }
            AstNodeType::FunctionRef(symbol) => {
                let sig = scope.get_definition(symbol.clone(), false).ok_or(
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
                // Give this occurrence its own type variables; if the reference
                // is generic its concrete type is resolved later from the
                // `apply` sites that consume it (or from monomorphization of the
                // enclosing generic definition).
                let mut remap = HashMap::new();
                let sig = freshen_type(&sig, &mut remap);
                Ok(AstNodeWithType::new(
                    AstNodeType::FunctionRef(symbol),
                    node.position.clone(),
                    Type::new(vec![], vec![UnitType::Type(sig)]),
                ))
            }
            AstNodeType::Quotation(nodes) => {
                // A quotation is type-checked against an EMPTY stack: its inputs
                // are inferred from its own body (under-flowed operands become
                // parameters), never borrowed from the ambient stack.
                let mut quotation_scope = TypeScope::with_parent(scope.clone());
                let (sig, mut nodes) = self.type_check_block(
                    &mut quotation_scope,
                    Vec::new(),
                    nodes,
                    false,
                    module_path,
                    // Resolve under-flowed inputs to concrete types so the
                    // quotation's value type carries no free variables.
                    true,
                )?;
                // Freshen the inferred variables (consistently across the sig and
                // the body) so two quotation occurrences don't alias variables,
                // and so variables bound by unrelated calls don't leak in.
                let mut remap = HashMap::new();
                let sig = freshen_type(&sig, &mut remap);
                let remap: HashMap<VarType, UnitType> = remap
                    .into_iter()
                    .map(|(from, to)| (from, UnitType::Var(to)))
                    .collect();
                if !remap.is_empty() {
                    for node in &mut nodes {
                        apply_subst_to_node(node, &remap);
                    }
                }
                Ok(AstNodeWithType::new(
                    AstNodeType::Quotation(nodes),
                    node.position.clone(),
                    Type::new(vec![], vec![UnitType::Type(sig)]),
                ))
            }
            AstNodeType::Definition {
                name: symbol,
                is_private,
                body,
            } => {
                // Each definition body has its own pool of function-value
                // bindings; save the enclosing one (definitions can nest).
                let saved_subst = std::mem::take(&mut self.function_value_subst);
                let mut body = if let Some(ty) = body.type_definition.as_ref() {
                    // We use this to allow recursive types. We should probably create a better implementation latter
                    let ty = self.replace_custom_type(scope, ty.clone())?;
                    scope.insert_definition(symbol.clone(), ty, is_private);

                    self.infer_type_definition(scope, Vec::new(), *body, module_path)?
                } else {
                    let body = self.infer_type_definition(scope, Vec::new(), *body, module_path)?;
                    scope.insert_definition(
                        symbol.clone(),
                        body.type_definition.clone(),
                        is_private,
                    );
                    body
                };
                // Back-substitute the bindings discovered from `apply`/call sites
                // into the body, concretizing function-value references and
                // quotations whose type was only pinned downstream.
                let mut subst = std::mem::replace(&mut self.function_value_subst, saved_subst);
                if !subst.is_empty() {
                    resolve_substitution(&mut subst);
                    apply_subst_to_node(&mut body, &subst);
                }
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
                let variants = variants
                    .into_iter()
                    .map(|variant| {
                        Ok((
                            variant.0,
                            variant
                                .1
                                .into_iter()
                                .map(|field| {
                                    Ok((field.0, replace_custom_unit_type(scope, field.1)?))
                                })
                                .collect::<Result<Vec<(String, UnitType)>, TypeCheckerError>>()?,
                        ))
                    })
                    .collect::<Result<Vec<(String, Vec<(String, UnitType)>)>, TypeCheckerError>>(
                    )?;
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
            .map(|ty| replace_custom_unit_type(scope, ty))
            .collect::<Result<Vec<_>, _>>()?;
        let push_types = ty
            .push_types
            .into_iter()
            .map(|ty| replace_custom_unit_type(scope, ty))
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
                                    Box::new(match_type.clone()),
                                    Box::new(Pattern::Number(number_pattern.clone())),
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
                            check_branch_body_consistency(
                                &pattern_body_type,
                                &body_type.type_definition,
                                &position,
                            )?;
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
                            check_branch_body_consistency(
                                &pattern_body_type,
                                &body_type.type_definition,
                                &position,
                            )?;
                            result_cases.push(Case {
                                pattern: case.pattern,
                                body: Box::new(body_type.clone()),
                            });
                            pattern_body_type = Some(body_type.type_definition);
                        }
                        other => {
                            return Err(TypeCheckerError::InvalidPatternForType(
                                Box::new(match_type.clone()),
                                Box::new(other.clone()),
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
                                t.pop_types
                                    .extend_from_slice(std::slice::from_ref(&match_type));
                                t.pop_types
                            })
                            .unwrap_or(vec![match_type]),
                        pattern_body_type.map(|t| t.push_types).unwrap_or(vec![]),
                    ),
                })
            }
            UnitType::Custom { .. } => {
                let mut result_cases = Vec::with_capacity(cases.len());
                for case in cases.clone().into_iter() {
                    if !matches!(case.pattern, Pattern::Variant { .. } | Pattern::Wildcard(_)) {
                        return Err(TypeCheckerError::InvalidPatternForType(
                            Box::new(match_type.clone()),
                            Box::new(case.pattern.clone()),
                            position.clone(),
                        ));
                    }
                    // Bind the pattern's variables (recursing into nested patterns)
                    // against the matched type.
                    let mut scope = TypeScope::with_parent(scope.clone());
                    bind_pattern(
                        &mut scope,
                        &self.type_definitions,
                        &match_type,
                        &case.pattern,
                        &position,
                    )?;
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
                    check_branch_body_consistency(
                        &pattern_body_type,
                        &body_type.type_definition,
                        &position,
                    )?;
                    result_cases.push(Case {
                        pattern: case.pattern,
                        body: Box::new(body_type.clone()),
                    });
                    pattern_body_type = Some(body_type.type_definition);
                }
                // Exhaustiveness: a fresh catch-all arm must be redundant (usefulness check).
                let top_patterns: Vec<Pattern> = cases.iter().map(|c| c.pattern.clone()).collect();
                if pattern_is_useful(
                    &self.type_definitions,
                    &top_patterns,
                    &match_type,
                    &position,
                )? {
                    return Err(TypeCheckerError::NonExhaustiveMatch(position.clone()));
                }
                Ok(AstNodeWithType {
                    node_type: AstNodeType::Match(result_cases),
                    position: position.clone(),
                    type_definition: Type::new(
                        pattern_body_type
                            .clone()
                            .map(|mut t| {
                                t.pop_types
                                    .extend_from_slice(std::slice::from_ref(&match_type));
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

/// Ensures every arm of a `match` produces the same stack effect. The first
/// arm seeds `pattern_body_type`; later arms must match it.
fn check_branch_body_consistency(
    pattern_body_type: &Option<Type>,
    body_type: &Type,
    position: &Position,
) -> Result<(), TypeCheckerError> {
    if let Some(existing) = pattern_body_type
        && existing != body_type
    {
        return Err(TypeCheckerError::InvalidMatchBody(
            Box::new(existing.clone()),
            Box::new(body_type.clone()),
            position.clone(),
        ));
    }
    Ok(())
}

type TypeDefinitions = HashMap<Vec<String>, CustomType>;

/// Recursively binds a pattern's variables into `scope` against value type `ty`.
/// Leaf `Wildcard(Some(v))` binds `v`; nested `Variant` recurses into the matched
/// variant's (generic-substituted) field types.
fn bind_pattern(
    scope: &mut TypeScope,
    type_definitions: &TypeDefinitions,
    ty: &UnitType,
    pattern: &Pattern,
    position: &Position,
) -> Result<(), TypeCheckerError> {
    match pattern {
        Pattern::Wildcard(Some(alias)) => {
            scope.insert_definition(alias.clone(), Type::new(vec![], vec![ty.clone()]), false);
            Ok(())
        }
        Pattern::Wildcard(None) => Ok(()),
        Pattern::Number(_) => match ty {
            UnitType::Literal(LiteralType::Number(_)) => Ok(()),
            _ => Err(TypeCheckerError::InvalidPatternForType(
                Box::new(ty.clone()),
                Box::new(pattern.clone()),
                position.clone(),
            )),
        },
        Pattern::Char(_) => match ty {
            UnitType::Literal(LiteralType::Char) => Ok(()),
            _ => Err(TypeCheckerError::InvalidPatternForType(
                Box::new(ty.clone()),
                Box::new(pattern.clone()),
                position.clone(),
            )),
        },
        Pattern::Variant {
            variant_name,
            fields,
        } => {
            let variant = variant_name.last().map(|s| s.as_str()).unwrap_or_default();
            let (field_order, field_types) =
                variant_fields_of(type_definitions, ty, variant, position)?;
            for field in fields {
                let idx = field_order.iter().position(|f| f == &field.field).ok_or(
                    TypeCheckerError::FieldNotFoundInVariant(
                        field.field.clone(),
                        variant_name.join("::"),
                    ),
                )?;
                bind_pattern(
                    scope,
                    type_definitions,
                    &field_types[idx],
                    &field.pattern,
                    position,
                )?;
            }
            Ok(())
        }
    }
}

/// Returns a variant's field names (declaration order) and their generic-substituted
/// types for the custom type `ty` (which must be `UnitType::Custom`).
fn variant_fields_of(
    type_definitions: &TypeDefinitions,
    ty: &UnitType,
    variant: &str,
    position: &Position,
) -> Result<(Vec<String>, Vec<UnitType>), TypeCheckerError> {
    let UnitType::Custom {
        name,
        generic_types,
    } = ty
    else {
        return Err(TypeCheckerError::InvalidMatchType(
            ty.clone(),
            position.clone(),
        ));
    };
    let custom_type = type_definitions
        .get(name)
        .ok_or_else(|| TypeCheckerError::TypeNotFound(name.clone()))?;
    let generics_map: HashMap<VarType, UnitType> = custom_type
        .generics
        .iter()
        .map(|g| g.1.clone())
        .zip(generic_types.iter().cloned())
        .collect();
    let (_, fields) = custom_type
        .variants
        .iter()
        .find(|(n, _)| n == variant)
        .ok_or_else(|| {
            TypeCheckerError::InvalidMatchVariant(variant.to_string(), position.clone())
        })?;
    let field_order = fields.iter().map(|(n, _)| n.clone()).collect();
    let field_types = fields
        .iter()
        .map(|(_, t)| substitute_unit_type(&generics_map, t.clone()))
        .collect();
    Ok((field_order, field_types))
}

/// Whether a `match`'s arms leave any value uncovered: builds a single-column
/// matrix from the arms' patterns and asks whether a fresh wildcard row is still
/// useful (Maranget's usefulness algorithm). `true` ⇒ non-exhaustive.
fn pattern_is_useful(
    type_definitions: &TypeDefinitions,
    top_patterns: &[Pattern],
    scrutinee_ty: &UnitType,
    position: &Position,
) -> Result<bool, TypeCheckerError> {
    let matrix: Vec<Vec<Pattern>> = top_patterns.iter().map(|p| vec![p.clone()]).collect();
    is_useful(
        type_definitions,
        &matrix,
        &[Pattern::Wildcard(None)],
        std::slice::from_ref(scrutinee_ty),
        position,
    )
}

fn sub_patterns_in_order(fields: &[FieldPattern], field_order: &[String]) -> Vec<Pattern> {
    field_order
        .iter()
        .map(|fname| {
            fields
                .iter()
                .find(|f| &f.field == fname)
                .map(|f| f.pattern.clone())
                .unwrap_or(Pattern::Wildcard(None))
        })
        .collect()
}

/// Specializes a pattern matrix by `variant`: keeps rows whose first column matches
/// the variant (expanding its sub-patterns in `field_order`) or is a wildcard
/// (expanding to wildcards); drops rows for other constructors.
fn specialize_matrix(
    matrix: &[Vec<Pattern>],
    variant: &str,
    field_order: &[String],
) -> Vec<Vec<Pattern>> {
    let mut out = Vec::new();
    for row in matrix {
        let (head, rest) = row.split_first().expect("matrix rows are non-empty");
        match head {
            Pattern::Variant {
                variant_name,
                fields,
            } if variant_name.last().map(|s| s.as_str()) == Some(variant) => {
                let mut new_row = sub_patterns_in_order(fields, field_order);
                new_row.extend_from_slice(rest);
                out.push(new_row);
            }
            Pattern::Wildcard(_) => {
                let mut new_row = vec![Pattern::Wildcard(None); field_order.len()];
                new_row.extend_from_slice(rest);
                out.push(new_row);
            }
            _ => {}
        }
    }
    out
}

/// The default matrix: rows whose first column is a wildcard, with that column removed.
fn default_matrix(matrix: &[Vec<Pattern>]) -> Vec<Vec<Pattern>> {
    matrix
        .iter()
        .filter_map(|row| {
            let (head, rest) = row.split_first().expect("matrix rows are non-empty");
            matches!(head, Pattern::Wildcard(_)).then(|| rest.to_vec())
        })
        .collect()
}

/// Maranget's usefulness: is `q` useful w.r.t. `matrix` over column `types`?
/// (Used only with all-wildcard `q` for exhaustiveness.)
fn is_useful(
    type_definitions: &TypeDefinitions,
    matrix: &[Vec<Pattern>],
    q: &[Pattern],
    types: &[UnitType],
    position: &Position,
) -> Result<bool, TypeCheckerError> {
    if types.is_empty() {
        return Ok(matrix.is_empty());
    }
    let t0 = &types[0];
    match &q[0] {
        Pattern::Variant {
            variant_name,
            fields,
        } => {
            let variant = variant_name.last().map(|s| s.as_str()).unwrap_or_default();
            let (field_order, field_types) =
                variant_fields_of(type_definitions, t0, variant, position)?;
            let spec = specialize_matrix(matrix, variant, &field_order);
            let mut q2 = sub_patterns_in_order(fields, &field_order);
            q2.extend_from_slice(&q[1..]);
            let mut new_types = field_types;
            new_types.extend_from_slice(&types[1..]);
            is_useful(type_definitions, &spec, &q2, &new_types, position)
        }
        Pattern::Number(_) | Pattern::Char(_) => {
            let default = default_matrix(matrix);
            is_useful(type_definitions, &default, &q[1..], &types[1..], position)
        }
        Pattern::Wildcard(_) => {
            // A custom type has a complete signature iff every variant appears in column 0.
            let complete_variants = match t0 {
                UnitType::Custom { name, .. } => {
                    let custom_type = type_definitions
                        .get(name)
                        .ok_or_else(|| TypeCheckerError::TypeNotFound(name.clone()))?;
                    let all: Vec<String> = custom_type
                        .variants
                        .iter()
                        .map(|(n, _)| n.clone())
                        .collect();
                    let present: HashSet<String> = matrix
                        .iter()
                        .filter_map(|row| match row.first() {
                            Some(Pattern::Variant { variant_name, .. }) => {
                                variant_name.last().cloned()
                            }
                            _ => None,
                        })
                        .collect();
                    if !all.is_empty() && all.iter().all(|v| present.contains(v)) {
                        Some(all)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            match complete_variants {
                // Complete: useful iff useful under some variant's specialization.
                Some(all) => {
                    for variant in &all {
                        let (field_order, field_types) =
                            variant_fields_of(type_definitions, t0, variant, position)?;
                        let spec = specialize_matrix(matrix, variant, &field_order);
                        let mut q2 = vec![Pattern::Wildcard(None); field_order.len()];
                        q2.extend_from_slice(&q[1..]);
                        let mut new_types = field_types;
                        new_types.extend_from_slice(&types[1..]);
                        if is_useful(type_definitions, &spec, &q2, &new_types, position)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
                // Incomplete (or infinite, e.g. numbers/strings/generics): recurse on the default matrix.
                None => {
                    let default = default_matrix(matrix);
                    is_useful(type_definitions, &default, &q[1..], &types[1..], position)
                }
            }
        }
    }
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
                if let Some(from_definitions) = inner.type_definitions.get(&last).cloned() {
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
        let program = Parser::new_from_str(contents)
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
        let contents = r#"import std::list
import std::stack 3.14 stack::drop "hello world" stack::drop"#;
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) import std::list ( -> ) import std::stack ( -> F64) 3.14 (F64 -> ) stack::drop ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'd' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'r' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'w' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) ' ' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'h' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> ) stack::drop}"
        );
    }

    #[test]
    fn simple_block() {
        let contents = r#"import std::list
import std::stack(drop) { 42u8 "test" stack::drop drop }"#;
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) import std::list ( -> ) import std::stack(drop) ( -> ) {( -> U8) 42u8 ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 't' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 's' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 't' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> ) stack::drop (U8 -> ) drop}}"
        );
    }

    #[test]
    fn simple_definition() {
        let contents = r#"import std::list
def hello { "Hello, World!" }"#;
        let program = parse_and_type_check(contents, false).unwrap();

        assert_eq!(
            program,
            "( -> ) {( -> ) import std::list ( -> ) def hello ( -> std::list::List<Char>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) '!' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'd' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'r' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'W' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) ' ' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) ',' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'H' (std::list::List<Char> Char -> std::list::List<Char>) list::List}}\n}"
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
        let contents = r#"import std::list
def main (-> String) { "hello" }"#;
        let error = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(error, "Invalid main definition ( -> std::list::List<Char>)");
    }

    #[test]
    fn builtin_functions_work() {
        let contents = r#"import std::list

            import std::stack(drop)

            def main {
                42u8 drop
                "hello" drop
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(
            result,
            "( -> ) {( -> ) import std::list ( -> ) import std::stack(drop) ( -> ) def main ( -> ) {( -> U8) 42u8 (U8 -> ) drop ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'h' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> ) drop}\n}"
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
        let contents = r#"import std::list

            def test {
                10 match { 0 -> "zero" 1 -> "one" * -> "big number" }
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) import std::list ( -> ) def test ( -> std::list::List<Char>) {( -> I64) 10i64 (I64 -> std::list::List<Char>) match {0i64 => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'r' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'z' (std::list::List<Char> Char -> std::list::List<Char>) list::List} 1i64 => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'n' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List} * => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'r' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'b' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'm' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'u' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'n' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) ' ' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'g' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'b' (std::list::List<Char> Char -> std::list::List<Char>) list::List}}}\n}"
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
        let contents = r#"import std::list

            def test {
                10 match { 1 -> "one" * -> 10 }
            }
        "#;
        let result = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(
            result,
            "Invalid match body at 4:20. Expected ( -> std::list::List<Char>) but got ( -> I64)"
        );
    }

    #[test]
    fn function_ref_and_apply_type_check() {
        let contents = r#"
            import std::number::i64

            def double (I64 -> I64) { 2i64 i64::* }
            def test (I64 -> I64) { \double apply }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn quotation_infers_function_type() {
        let contents = r#"
            import std::number::i64

            def test (I64 -> I64) { \{ 1i64 i64::+ } apply }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn quotation_under_flow_infers_inputs() {
        // `\{ 1i64 i64::+ }` under-flows by one operand, which becomes its input:
        // the quotation has type `(I64 -> I64)`, inferred against an empty stack
        // (not the ambient one).
        let contents = r#"
            import std::number::i64

            def test { \{ 1i64 i64::+ } }
        "#;
        let result = parse_and_type_check(contents, false).expect("type checks");
        assert!(
            result.contains("(I64 -> I64)"),
            "expected the quotation to infer (I64 -> I64): {}",
            result
        );
    }

    #[test]
    fn quotation_input_resolved_from_later_body_word() {
        // A quotation whose under-flowed input is only pinned to a concrete type
        // by a *later* word in its body must still infer a closed type — no free
        // variable may leak. Here `dup` under-flows (introducing an input
        // variable) and `swap`/`free_cstr` later constrain it to `CStr`, so the
        // quotation is `(CStr -> String)`.
        let contents = r#"
            import std::stack(dup swap)
            import std::list

            defx from_cstr (CStr -> String)
            defx free_cstr (CStr ->)

            def test { \{ dup from_cstr swap free_cstr } }
        "#;
        let result = parse_and_type_check(contents, false).expect("type checks");
        assert!(
            result.contains("(CStr -> "),
            "expected the quotation's input to resolve to CStr, not a free var: {}",
            result
        );
    }

    #[test]
    fn quotation_with_late_resolved_input_passed_to_generic_higher_order() {
        // The same quotation, handed to a *generic* higher-order definition that
        // applies it internally. The quotation must already carry a concrete
        // type here (the `apply` is inside `with`, generic over its own var, so
        // it can't pin the quotation's input). Regression for the
        // "unresolved type variables" codegen error.
        let contents = r#"
            import std::stack(dup swap)
            import std::list

            defx mkcstr ( -> CStr)
            defx from_cstr (CStr -> String)
            defx free_cstr (CStr ->)
            defx use_str (String ->)

            def with (a (a -> b) -> b) { apply }

            def main ( -> ) {
                mkcstr \{ dup from_cstr swap free_cstr } with use_str
            }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn builtin_reference_type_checks() {
        // `\i64::+` references a builtin as a value; applying it consumes two I64.
        let contents = r#"
            import std::number::i64

            def test (I64 I64 -> I64) { \i64::+ apply }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn generic_higher_order_def_type_checks() {
        // A generic higher-order def: takes a value and a function over it.
        let contents = r#"
            import std::number::i64

            def double (I64 -> I64) { 2i64 i64::* }
            def with (a (a -> a) -> a) { apply }
            def test (I64 -> I64) { \double with }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn generic_def_constructs_generic_value() {
        // A generic definition that builds a generic value with the nullary
        // (`Empty`) and binary (`List`) constructors.
        let contents = r#"
            import std::list

            def copy (list::List<a> -> list::List<a>) {
                match {
                    [] -> { list::Empty }
                    [head ... tail] -> { tail copy head list::List }
                }
            }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn generic_higher_order_map_type_checks() {
        // Generic construction together with a function-value parameter and
        // `apply` — this is the case the function-type self-binding fix unblocked.
        let contents = r#"
            import std::list
            import std::stack(swap dup drop)

            def map (list::List<a> (a -> a) -> list::List<a>) {
                swap
                match {
                    [] -> { drop list::Empty }
                    [head ... tail] -> {
                        dup tail swap map
                        swap head swap apply
                        list::List
                    }
                }
            }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn apply_on_non_function_fails() {
        let contents = r#"
            def test (I64 -> I64) { apply }
        "#;
        let result = parse_and_type_check(contents, false)
            .unwrap_err()
            .to_string();
        assert!(
            result.contains("`apply` expects a function value"),
            "unexpected error: {}",
            result
        );
    }

    #[test]
    fn polymorphic_function_value_resolves_from_apply() {
        // `\dup` is generic (`a -> a a`); applying it to an I64 pins it.
        let contents = r#"
            import std::stack
            import std::number::i64

            def test (I64 -> I64 I64) { \stack::dup apply }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
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
        let contents = r#"import std::list

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
            "( -> ) {( -> ) import std::list ( -> ) type Boolean {True False} ( -> ) def test ( -> std::list::List<Char>) {( -> Boolean) True (Boolean -> std::list::List<Char>) match {True => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'u' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'r' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'T' (std::list::List<Char> Char -> std::list::List<Char>) list::List} False => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 's' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'l' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'a' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'F' (std::list::List<Char> Char -> std::list::List<Char>) list::List}}}\n}"
        );
    }

    #[test]
    fn match_option() {
        let contents = r#"import std::list

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
            "( -> ) {( -> ) import std::list ( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> std::list::List<Char>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'H' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> Option<std::list::List<Char>>) Some (Option<std::list::List<Char>> -> std::list::List<Char>) match {Some(val) => ( -> std::list::List<Char>) val None => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'n' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'N' (std::list::List<Char> Char -> std::list::List<Char>) list::List}}}\n}"
        );
    }

    #[test]
    fn match_option_with_wildcard() {
        let contents = r#"import std::list

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
            "( -> ) {( -> ) import std::list ( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> std::list::List<Char>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'H' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> Option<std::list::List<Char>>) Some (Option<std::list::List<Char>> -> std::list::List<Char>) match {* => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'n' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 't' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'p' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'O' (std::list::List<Char> Char -> std::list::List<Char>) list::List}}}\n}"
        );
    }

    #[test]
    fn match_option_with_wildcard_2() {
        let contents = r#"import std::list

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
            "( -> ) {( -> ) import std::list ( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> std::list::List<Char>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'H' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> Option<std::list::List<Char>>) Some (Option<std::list::List<Char>> -> std::list::List<Char>) match {Some => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'm' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'S' (std::list::List<Char> Char -> std::list::List<Char>) list::List} * => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'n' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 't' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'p' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'O' (std::list::List<Char> Char -> std::list::List<Char>) list::List}}}\n}"
        );
    }

    #[test]
    fn match_option_with_wildcard_with_alias() {
        let contents = r#"import std::list

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
            "( -> ) {( -> ) import std::list ( -> ) type Option<a> {Some(val a) None} ( -> ) def test ( -> Option<std::list::List<Char>>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'H' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> Option<std::list::List<Char>>) Some (Option<std::list::List<Char>> -> Option<std::list::List<Char>>) match {Some => ( -> Option<std::list::List<Char>>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'e' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'm' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'o' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'S' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> Option<std::list::List<Char>>) Some} * as rest => ( -> Option<std::list::List<Char>>) rest}}\n}"
        );
    }

    #[test]
    fn non_exhaustive_match() {
        let contents = r#"import std::list

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

        assert_eq!(result, "Non-exhaustive match at 8:27");
    }

    #[test]
    fn match_result() {
        let contents = r#"import std::list

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
            "( -> ) {( -> ) import std::list ( -> ) type Result<a b> {Ok(val a) Err(val a)} ( -> ) def test ( -> std::list::List<Char>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'H' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> Result<std::list::List<Char> std::list::List<Char>>) Ok (Result<std::list::List<Char> std::list::List<Char>> -> std::list::List<Char>) match {Ok(val as value) => ( -> std::list::List<Char>) value Err(val as error) => ( -> std::list::List<Char>) error}}\n}"
        );
    }

    #[test]
    fn match_result_without_value() {
        let contents = r#"import std::list

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
            "( -> ) {( -> ) import std::list ( -> ) type Result<a b> {Ok(val a) Err(val a)} ( -> ) def test ( -> std::list::List<Char>) {( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'i' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'H' (std::list::List<Char> Char -> std::list::List<Char>) list::List} (std::list::List<Char> -> Result<std::list::List<Char> std::list::List<Char>>) Ok (Result<std::list::List<Char> std::list::List<Char>> -> std::list::List<Char>) match {Ok => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'k' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'O' (std::list::List<Char> Char -> std::list::List<Char>) list::List} Err => ( -> std::list::List<Char>) {( -> std::list::List<Char>) list::Empty ( -> Char) 'r' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'r' (std::list::List<Char> Char -> std::list::List<Char>) list::List ( -> Char) 'E' (std::list::List<Char> Char -> std::list::List<Char>) list::List}}}\n}"
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

    #[test]
    fn list_match_head_tail_is_exhaustive() {
        let contents = r#"
            import std::list

            def test {
                [1i64 2i64 3i64] match {
                    [] -> 0i64
                    [head ... tail] -> head
                }
            }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn list_match_with_exact_and_open_is_exhaustive() {
        let contents = r#"
            import std::list

            def test {
                [1i64 2i64 3i64] match {
                    [] -> 0i64
                    [only] -> only
                    [a b ... rest] -> a
                }
            }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn list_match_exact_only_is_non_exhaustive() {
        // `[]` + `[a b]` leaves length-1 and length-3+ lists uncovered.
        let contents = r#"
            import std::list

            def test {
                [1i64 2i64] match {
                    [] -> 0i64
                    [a b] -> a
                }
            }
        "#;
        let err = parse_and_type_check(contents, false)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("Non-exhaustive"),
            "expected non-exhaustive, got: {err}"
        );
    }

    #[test]
    fn list_match_missing_empty_is_non_exhaustive() {
        let contents = r#"
            import std::list

            def test {
                [1i64] match {
                    [head ... tail] -> head
                }
            }
        "#;
        let err = parse_and_type_check(contents, false)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("Non-exhaustive"),
            "expected non-exhaustive, got: {err}"
        );
    }

    #[test]
    fn list_match_wildcard_is_exhaustive() {
        let contents = r#"
            import std::list

            def test {
                [1i64 2i64] match {
                    [a b] -> a
                    * as other -> 0i64
                }
            }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn string_match_exact_only_is_non_exhaustive() {
        // Matching only the exact string "hi" leaves every other string uncovered.
        let contents = r#"
            import std::list
            import std::number::i64
            def test { "hi" match { "hi" -> 1i64 } }
        "#;
        let err = parse_and_type_check(contents, false)
            .unwrap_err()
            .to_string();
        assert!(
            err.contains("Non-exhaustive"),
            "expected non-exhaustive, got: {err}"
        );
    }

    #[test]
    fn string_match_with_empty_and_tail_is_exhaustive() {
        let contents = r#"
            import std::list
            import std::number::i64
            def test { "hi" match { "" -> 0i64 [c ... rest] -> 1i64 } }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }
}
