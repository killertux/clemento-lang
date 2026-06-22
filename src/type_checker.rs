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
    Substitution, apply_substitution, replace_custom_type, replace_custom_unit_type,
    substitute_effects, substitute_types, substitute_unit_type,
    validate_types_and_return_variable_substitution,
};

use crate::{
    lexer::{IntegerNumber, Number, Position},
    parser::{AstNode, AstNodeType, Case, FieldPattern, Import, Pattern},
    types::{
        CustomType, Effect, LiteralType, NumberType, Type, UnitType, VarType,
        VarTypeToCharContainer,
    },
};

/// Replaces every type variable in `ty` with a fresh one, consistently (the same
/// source variable maps to the same fresh variable via `remap`). Used so each
/// occurrence of a function-value reference gets independent variables — two
/// `\dup` references must not share `a`, or applying them at different types
/// would spuriously conflict.
fn freshen_type(ty: &Type, remap: &mut HashMap<VarType, VarType>) -> Type {
    Type::with_effects(
        ty.pop_types
            .iter()
            .map(|u| freshen_unit(u, remap))
            .collect(),
        ty.push_types
            .iter()
            .map(|u| freshen_unit(u, remap))
            .collect(),
        ty.effects
            .iter()
            .map(|e| freshen_effect(e, remap))
            .collect(),
    )
}

/// Gives each effect *variable* (`!a`) a fresh identity per function-value
/// occurrence, consistently with the type-variable freshening in `freshen_unit`.
fn freshen_effect(effect: &Effect, remap: &mut HashMap<VarType, VarType>) -> Effect {
    match effect {
        Effect::Var(var) => Effect::Var(
            remap
                .entry(var.clone())
                .or_insert_with(VarType::new)
                .clone(),
        ),
        other => other.clone(),
    }
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
fn apply_subst_to_node(node: &mut AstNodeWithType, subst: &Substitution) {
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
fn resolve_substitution(subst: &mut Substitution) {
    let total = subst.types.len() + subst.effects.len();
    for _ in 0..total + 1 {
        let mut changed = false;
        let keys: Vec<VarType> = subst.types.keys().cloned().collect();
        for key in keys {
            let value = subst
                .types
                .get(&key)
                .cloned()
                .expect("key came from the map");
            let resolved = substitute_unit_type(subst, value.clone());
            if resolved != value {
                subst.types.insert(key, resolved);
                changed = true;
            }
        }
        // Effect rows can reference other effect variables; close those too.
        let effect_keys: Vec<VarType> = subst.effects.keys().cloned().collect();
        for key in effect_keys {
            let value = subst
                .effects
                .get(&key)
                .cloned()
                .expect("key came from the map");
            let resolved = substitute_effects(subst, value.clone());
            if resolved != value {
                subst.effects.insert(key, resolved);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Unions two effect rows (dedup). A `!*` wildcard absorbs everything, so the
/// result collapses to `[Wildcard]` whenever one is present.
fn merge_effects(mut acc: Vec<Effect>, more: Vec<Effect>) -> Vec<Effect> {
    for e in more {
        if !acc.contains(&e) {
            acc.push(e);
        }
    }
    if acc.contains(&Effect::Wildcard) {
        return vec![Effect::Wildcard];
    }
    acc
}

/// Checks that every effect a body actually performs (`inferred`) is permitted by
/// its `declared` effect row. A declared `!*` permits anything.
fn check_effects_declared(
    inferred: &[Effect],
    declared: &[Effect],
    position: &Position,
) -> Result<(), TypeCheckerError> {
    if declared.contains(&Effect::Wildcard) {
        return Ok(());
    }
    for effect in inferred {
        if !declared.contains(effect) {
            return Err(TypeCheckerError::UndeclaredEffect(
                position.clone(),
                effect.clone(),
                declared.to_vec(),
            ));
        }
    }
    Ok(())
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

/// Distinguishes the top-level block being type-checked. The **entry** file is
/// run as the program, so it may leave a value on the stack: `( -> )` (exit 0)
/// or `( -> I32)` (the exit code). An **imported module** is a pure namespace
/// and must be `( -> )`. Nested blocks/bodies are unrestricted (eager defs there
/// are local let-bindings) and are not tagged — only the outermost block of a
/// `type_check` call carries this.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScopeKind {
    Entry,
    Module,
}

pub struct TypeChecker {
    imports: HashMap<String, TypeScope>,
    type_definitions: HashMap<Vec<String>, CustomType>,
    /// Accumulates the type-variable bindings discovered while checking the
    /// current definition's body (mostly at `apply` sites). After the body is
    /// checked it is back-substituted into the body so function-value
    /// references/quotations whose concrete type is pinned only by a downstream
    /// `apply` become concrete. Saved/restored per definition.
    function_value_subst: Substitution,
    /// One-shot scope for the *next* block to type-check into, instead of a fresh
    /// child. Set by an eager namespace def so its body's nested defs are
    /// retained (as the def's members) rather than discarded; consumed by the
    /// very next `Block` arm. `None` everywhere else.
    pending_block_scope: Option<TypeScope>,
}

impl TypeChecker {
    pub fn new() -> Self {
        Self {
            imports: HashMap::new(),
            type_definitions: HashMap::new(),
            function_value_subst: Substitution::new(),
            pending_block_scope: None,
        }
    }

    pub fn type_check(
        &mut self,
        program: AstNode,
        scope_kind: ScopeKind,
        module_path: Vec<String>,
    ) -> Result<(AstNodeWithType, TypeScope), TypeCheckerError> {
        let mut scope = TypeScope::empty();
        let AstNodeType::Block(nodes) = program.node_type else {
            return Err(TypeCheckerError::InvalidModuleDefinition(Box::new(
                Type::empty(),
            )));
        };

        let (block_type_check_result, mut nodes_with_types) =
            self.type_check_block(&mut scope, Vec::new(), nodes, module_path, false)?;
        // Back-substitute bindings discovered at top-level `apply`/call sites into
        // the top-level nodes, so function values pinned only downstream (e.g.
        // `\dup` consumed by a later `apply`) lose their free type variables.
        // Inside a `def` body this happens in the Definition arm; the entry/module
        // top level (which now runs program code directly) needs it here too.
        let mut subst = std::mem::take(&mut self.function_value_subst);
        if !subst.is_empty() {
            resolve_substitution(&mut subst);
            for node in &mut nodes_with_types {
                apply_subst_to_node(node, &subst);
            }
        }
        // The entry file runs as the program: it may leave nothing (exit 0) or a
        // single I32 (exit code), and — being the program — it is where effects
        // are discharged, so any effect row is allowed. An imported module is a
        // pure namespace: `( -> )` with NO effects. The latter is exactly what
        // lets a module hold arbitrary (but provably pure) instructions, not just
        // definitions.
        let pop_empty = block_type_check_result.pop_types.is_empty();
        let push = &block_type_check_result.push_types;
        let valid = match scope_kind {
            ScopeKind::Entry => {
                pop_empty
                    && (push.is_empty()
                        || push.as_slice()
                            == [UnitType::Literal(LiteralType::Number(NumberType::I32))])
            }
            ScopeKind::Module => {
                pop_empty && push.is_empty() && block_type_check_result.effects.is_empty()
            }
        };
        if !valid {
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
        let mut accumulated_subst = Substitution::new();
        // The union of every node's effects — the block's overall effect row.
        let mut block_effects: Vec<Effect> = Vec::new();
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
            let substituted =
                substitute_types(&type_stack, type_definition.clone(), node.position.clone())?;
            let push_types = substituted.push_types;
            // Accumulate this node's (now-substituted) effects into the block's
            // effect row — this is how effects propagate up to the enclosing
            // function/program.
            block_effects = merge_effects(block_effects, substituted.effects);
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

        // Resolve any effect variables the block accumulated against the
        // bindings discovered while checking it.
        if resolve_inferred_inputs {
            block_effects = substitute_effects(&accumulated_subst, block_effects);
        }
        let block_type = Type::with_effects(pop_type_stack, local_stack, block_effects);
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
                // Instantiate with fresh variables for this call (see the
                // `Symbol` arm); a qualified call to a generic definition needs
                // per-use type variables just the same.
                let type_definition = freshen_type(&type_definition, &mut HashMap::new());
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
                // Applying a function value performs that value's effects, so
                // `apply` carries the applied signature's effect row upward.
                let apply_ty =
                    Type::with_effects(pop_types, sig.push_types.clone(), sig.effects.clone());
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

                // Instantiate the definition's signature with fresh type
                // variables for this call. Without this, a generic builtin or
                // function (e.g. `rot (a b c -> b c a)`) shares one set of vars
                // across every call site; binding a stack value's variable to
                // such a shared var can alias it to the builtin's, and a later
                // reuse then collides — producing spurious conflicts / cycles
                // (e.g. `fold`'s accumulator getting tangled with `rot`'s vars).
                // `FunctionRef` already freshens; ordinary calls must too.
                let type_definition = freshen_type(&type_definition, &mut HashMap::new());
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
                // An eager namespace def pre-seeds the scope to retain its members.
                let mut scope = self
                    .pending_block_scope
                    .take()
                    .unwrap_or_else(|| TypeScope::with_parent(scope.clone()));
                let (ty, nodes) = self.type_check_block(
                    &mut scope,
                    type_stack.clone(),
                    nodes,
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
                // `remap` may carry both type-variable and effect-variable
                // renamings (`VarType`s are globally unique, so an entry is
                // exclusively one or the other); populate both maps — applying a
                // type-var renaming to effects, or vice versa, is a harmless no-op.
                let remap = Substitution {
                    types: remap
                        .iter()
                        .map(|(from, to)| (from.clone(), UnitType::Var(to.clone())))
                        .collect(),
                    effects: remap
                        .iter()
                        .map(|(from, to)| (from.clone(), vec![Effect::Var(to.clone())]))
                        .collect(),
                };
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
                is_lazy,
                body,
            } => {
                // Each definition body has its own pool of function-value
                // bindings; save the enclosing one (definitions can nest).
                let saved_subst = std::mem::take(&mut self.function_value_subst);
                let (mut body, def_type) = if is_lazy {
                    // Lazy function def (`def f \{ ... }` / `def f \g`, unwrapped
                    // to a block by the parser). Identical to the historical
                    // behaviour: the body is checked against an EMPTY stack to
                    // infer the function signature `(ins -> outs)`, the name is
                    // stored as that callable, and defining it changes nothing on
                    // the surrounding stack (`( -> )`).
                    let body = if let Some(ty) = body.type_definition.as_ref() {
                        // Pre-insert the annotated signature so the body may recurse.
                        // (The body's effects are checked against this annotation in
                        // the general annotation path of `infer_type_definition`.)
                        let ty = self.replace_custom_type(scope, ty.clone())?;
                        scope.insert_definition(symbol.clone(), ty, is_private);
                        self.infer_type_definition(scope, Vec::new(), *body, module_path)?
                    } else {
                        let body =
                            self.infer_type_definition(scope, Vec::new(), *body, module_path)?;
                        scope.insert_definition(
                            symbol.clone(),
                            body.type_definition.clone(),
                            is_private,
                        );
                        body
                    };
                    (body, Type::empty())
                } else {
                    // Eager value def (`def x { ... }`). The body runs once
                    // against the CURRENT stack; its outputs are captured into the
                    // name and removed from the stack. So the name resolves to a
                    // nullary `( -> outs)` (referencing it re-pushes the outputs),
                    // and the def statement itself consumes the body's inputs and
                    // pushes nothing: `(ins -> )`.
                    //
                    // When the body is a block, the def is also a *namespace*: pre-
                    // seed a retained `member_scope` so its nested defs survive as
                    // the def's members (`name::member`, see `get_definition`).
                    // Registering it BEFORE checking the body lets a qualified
                    // self-reference (`math::double` inside `math`) resolve, and the
                    // normal `infer_type_definition` path keeps annotation handling.
                    if matches!(body.node_type, AstNodeType::Block(_)) {
                        let member_scope = TypeScope::with_parent(scope.clone());
                        scope.insert_member(symbol.clone(), member_scope.clone());
                        self.pending_block_scope = Some(member_scope);
                    }
                    let body =
                        self.infer_type_definition(scope, type_stack.clone(), *body, module_path)?;
                    let body_ty = body.type_definition.clone();
                    scope.insert_definition(
                        symbol.clone(),
                        Type::new(vec![], body_ty.push_types.clone()),
                        is_private,
                    );
                    // The eager body runs once at this point, so the def statement
                    // performs the body's effects (they propagate to the enclosing
                    // block); the captured name itself is a pure `( -> outs)`.
                    (
                        body,
                        Type::with_effects(body_ty.pop_types, vec![], body_ty.effects),
                    )
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
                        is_lazy,
                        body: Box::new(body),
                    },
                    node.position.clone(),
                    def_type,
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
                    let result = self.type_check(nodes, ScopeKind::Module, path.clone())?;
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
            AstNodeType::EffectDefinition(name) => {
                let mut canonical = module_path.clone();
                canonical.push(name.clone());
                scope.insert_effect(canonical);
                Ok(AstNodeWithType::new(
                    AstNodeType::EffectDefinition(name),
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
                let substituted = substitute_types(
                    &type_stack,
                    inferred_type.type_definition.clone(),
                    node.position.clone(),
                )?;
                let push_types = substituted.push_types;

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
                // Every effect the body actually performs must be permitted by the
                // declared effect row (`!*` permits anything). The node's type then
                // carries the *declared* effects — what callers see.
                check_effects_declared(&substituted.effects, &ty.effects, &node.position)?;
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
        replace_custom_type(scope, ty)
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
        // Union of every arm's effects — the match's overall effect row.
        let mut match_effects: Vec<Effect> = Vec::new();
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
                            let refined = check_branch_body_consistency(
                                &pattern_body_type,
                                &body_type.type_definition,
                                &position,
                            )?;
                            result_cases.push(Case {
                                pattern: case.pattern,
                                body: Box::new(body_type.clone()),
                            });
                            match_effects = merge_effects(
                                match_effects,
                                body_type.type_definition.effects.clone(),
                            );
                            pattern_body_type = Some(refined);
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
                            let refined = check_branch_body_consistency(
                                &pattern_body_type,
                                &body_type.type_definition,
                                &position,
                            )?;
                            result_cases.push(Case {
                                pattern: case.pattern,
                                body: Box::new(body_type.clone()),
                            });
                            match_effects = merge_effects(
                                match_effects,
                                body_type.type_definition.effects.clone(),
                            );
                            pattern_body_type = Some(refined);
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
                    type_definition: Type::with_effects(
                        pattern_body_type
                            .clone()
                            .map(|mut t| {
                                t.pop_types
                                    .extend_from_slice(std::slice::from_ref(&match_type));
                                t.pop_types
                            })
                            .unwrap_or(vec![match_type]),
                        pattern_body_type.map(|t| t.push_types).unwrap_or(vec![]),
                        match_effects,
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
                    let refined = check_branch_body_consistency(
                        &pattern_body_type,
                        &body_type.type_definition,
                        &position,
                    )?;
                    result_cases.push(Case {
                        pattern: case.pattern,
                        body: Box::new(body_type.clone()),
                    });
                    match_effects =
                        merge_effects(match_effects, body_type.type_definition.effects.clone());
                    pattern_body_type = Some(refined);
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
                    type_definition: Type::with_effects(
                        pattern_body_type
                            .clone()
                            .map(|mut t| {
                                t.pop_types
                                    .extend_from_slice(std::slice::from_ref(&match_type));
                                t.pop_types
                            })
                            .unwrap_or(vec![match_type]),
                        pattern_body_type.map(|t| t.push_types).unwrap_or(vec![]),
                        match_effects,
                    ),
                })
            }
            other => Err(TypeCheckerError::InvalidMatchType(other.clone(), position)),
        }
    }
}

/// Reconciles a `match` arm's type with the running common type of the arms seen
/// so far, returning the refined common type. The first arm seeds it; each later
/// arm must be **unifiable** with it.
///
/// Arms need only have a common instance, not byte-identical types: an arm
/// inferred through a generic call (a recursive generic function, a constructor
/// like `Some`) gets independent type-variable identities, and an arm that
/// returns the scrutinee unchanged (`touch`) is fully polymorphic in its input —
/// these are all reconciled by the most-general unifier. (Arms may differ in
/// effects; those are unioned into the match's effect row separately.)
fn check_branch_body_consistency(
    pattern_body_type: &Option<Type>,
    body_type: &Type,
    position: &Position,
) -> Result<Type, TypeCheckerError> {
    let Some(existing) = pattern_body_type else {
        return Ok(body_type.clone());
    };
    unify_branch_types(existing, body_type).ok_or_else(|| {
        TypeCheckerError::InvalidMatchBody(
            Box::new(existing.clone()),
            Box::new(body_type.clone()),
            position.clone(),
        )
    })
}

/// The most general unifier of two arm types, with the resulting substitution
/// applied — the common type both arms inhabit. `None` if they are incompatible.
/// Effects are dropped (tracked separately by the match).
fn unify_branch_types(a: &Type, b: &Type) -> Option<Type> {
    if a.pop_types.len() != b.pop_types.len() || a.push_types.len() != b.push_types.len() {
        return None;
    }
    let mut subst: HashMap<VarType, UnitType> = HashMap::new();
    for (x, y) in a
        .pop_types
        .iter()
        .zip(&b.pop_types)
        .chain(a.push_types.iter().zip(&b.push_types))
    {
        if !unify_unit(x, y, &mut subst) {
            return None;
        }
    }
    let subst = Substitution::from_types(subst);
    Some(Type::new(
        a.pop_types
            .iter()
            .cloned()
            .map(|t| substitute_unit_type(&subst, t))
            .collect(),
        a.push_types
            .iter()
            .cloned()
            .map(|t| substitute_unit_type(&subst, t))
            .collect(),
    ))
}

/// Robinson unification of two unit types, accumulating bindings into `subst`.
fn unify_unit(a: &UnitType, b: &UnitType, subst: &mut HashMap<VarType, UnitType>) -> bool {
    let a = resolve_var(a, subst);
    let b = resolve_var(b, subst);
    match (&a, &b) {
        (UnitType::Var(x), UnitType::Var(y)) if x == y => true,
        (UnitType::Var(x), other) | (other, UnitType::Var(x)) => {
            if occurs_in(x, other) {
                return false;
            }
            subst.insert(x.clone(), other.clone());
            true
        }
        (UnitType::Literal(x), UnitType::Literal(y)) => x == y,
        (
            UnitType::Custom {
                name: n1,
                generic_types: g1,
            },
            UnitType::Custom {
                name: n2,
                generic_types: g2,
            },
        ) => {
            n1 == n2
                && g1.len() == g2.len()
                && g1.iter().zip(g2).all(|(x, y)| unify_unit(x, y, subst))
        }
        (UnitType::Type(t1), UnitType::Type(t2)) => {
            t1.pop_types.len() == t2.pop_types.len()
                && t1.push_types.len() == t2.push_types.len()
                && t1
                    .pop_types
                    .iter()
                    .zip(&t2.pop_types)
                    .chain(t1.push_types.iter().zip(&t2.push_types))
                    .all(|(x, y)| unify_unit(x, y, subst))
        }
        _ => false,
    }
}

/// Follows variable bindings to a representative (shallow — only the head).
fn resolve_var(ty: &UnitType, subst: &HashMap<VarType, UnitType>) -> UnitType {
    let mut current = ty.clone();
    while let UnitType::Var(var) = &current {
        match subst.get(var) {
            Some(next) => current = next.clone(),
            None => break,
        }
    }
    current
}

/// Occurs-check: does variable `var` appear inside `ty`? Prevents infinite types.
fn occurs_in(var: &VarType, ty: &UnitType) -> bool {
    match ty {
        UnitType::Var(x) => x == var,
        UnitType::Custom { generic_types, .. } => generic_types.iter().any(|g| occurs_in(var, g)),
        UnitType::Type(t) => t
            .pop_types
            .iter()
            .chain(&t.push_types)
            .any(|u| occurs_in(var, u)),
        UnitType::Literal(_) => false,
    }
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
    let generics_map = Substitution::from_types(
        custom_type
            .generics
            .iter()
            .map(|g| g.1.clone())
            .zip(generic_types.iter().cloned())
            .collect(),
    );
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
    /// Declared effects (`effect IO`), keyed by their last name segment and
    /// mapping to the canonical fully-qualified path (e.g. `IO` →
    /// `["std", "io", "IO"]`). Resolved like `type_definitions`.
    effect_definitions: HashMap<String, Vec<String>>,
    /// Member namespaces: the retained body scope of an eager namespace def
    /// (`def std { def string { ... } }`), keyed by the def's name. Navigated by
    /// `::` (see `get_definition`). Distinct from `imported` so file imports keep
    /// their current (privacy-free) qualified access, while member access enforces
    /// privacy.
    members: HashMap<String, TypeScope>,
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
                effect_definitions: HashMap::new(),
                members: HashMap::new(),
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

    /// Registers the retained body scope of an eager namespace def as a member,
    /// reachable via `name::member`.
    fn insert_member(&mut self, symbol: String, scope: TypeScope) {
        let mut inner = self.inner.borrow_mut();
        inner.members.insert(symbol, scope);
    }

    /// Registers a declared effect by its canonical fully-qualified path.
    fn insert_effect(&self, canonical: Vec<String>) {
        let mut inner = self.inner.borrow_mut();
        inner.effect_definitions.insert(
            canonical
                .last()
                .expect("An effect always has a name")
                .clone(),
            canonical,
        );
    }

    /// Resolves an effect reference to its canonical path, navigating imports and
    /// members exactly like `get_definition`. Returns `None` if undeclared.
    fn get_effect(&self, mut name: Vec<String>) -> Option<Vec<String>> {
        match name.len() {
            0 => None,
            1 => {
                let inner = self.inner.borrow();
                let last = name.last().expect("We checked for the name size").clone();
                if let Some(canonical) = inner.effect_definitions.get(&last).cloned() {
                    return Some(canonical);
                }
                if let Some(imported_functions) = inner.imported_functions.get(&last) {
                    return self.get_effect(vec![
                        imported_functions.1.clone(),
                        imported_functions.0.clone(),
                    ]);
                }
                if let Some(parent) = inner.parent.as_ref() {
                    return parent.get_effect(name);
                }
                None
            }
            _ => {
                let inner = self.inner.borrow();
                let first = name.remove(0);
                if let Some(from_imports) = inner.imported.get(&first) {
                    return from_imports.get_effect(name);
                }
                if let Some(member_scope) = inner.members.get(&first) {
                    return member_scope.get_effect(name);
                }
                if let Some(parent) = inner.parent.as_ref() {
                    name.insert(0, first);
                    return parent.get_effect(name);
                }
                None
            }
        }
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
                // Member-namespace navigation (`first::rest`). Reject if `first`
                // itself is a private member the caller cannot name; then recurse
                // into the member scope forcing `filter_private` — crossing into a
                // namespace means we are outside its internals, so its `defp`
                // members stay hidden (the terminal single-segment lookup rejects).
                if let Some(member_scope) = inner.members.get(&first) {
                    let first_private = inner
                        .definitions
                        .get(&first)
                        .map(|(_, is_private)| *is_private)
                        .unwrap_or(false);
                    if first_private && filter_private {
                        return None;
                    }
                    return member_scope.get_definition(symbol, true);
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
                effect_definitions: HashMap::new(),
                members: HashMap::new(),
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

    use super::{ScopeKind, TypeCheckerError};

    fn parse_and_type_check(contents: &str, is_entry: bool) -> Result<String, TypeCheckerError> {
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
                if is_entry {
                    ScopeKind::Entry
                } else {
                    ScopeKind::Module
                },
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
    fn valid_empty_entry() {
        // No `main`: the entry file's top-level block is the program. An empty
        // program is `( -> )` (exit 0).
        let contents = r#""#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(result, "( -> ) {}");
    }

    #[test]
    fn valid_entry_with_i32_exit() {
        // A single I32 left at the top level is the process exit code.
        let contents = r#"0i32"#;
        let result = parse_and_type_check(contents, true).unwrap();
        assert_eq!(result, "( -> I32) {( -> I32) 0i32}");
    }

    #[test]
    fn invalid_entry_non_i32_result() {
        // The entry file may only leave nothing or an I32; a leftover String is
        // rejected.
        let contents = r#"import std::list
"hello""#;
        let error = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(
            error,
            "Invalid top-level stack effect ( -> std::list::List<Char>). An imported module must be ( -> ); the entry file must be ( -> ) or ( -> I32)"
        );
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
            def test (U8 -> U8) \{ dup drop }
            42i32 test
        "#;
        let error = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();

        assert_eq!(error, "Type conflict at 4:19: expected U8, got I32");
    }

    #[test]
    fn nested_def() {
        let contents = r#"
            import std::stack(drop)
            def test \{
                def test1 \{ drop }
                10i32 test1
            }
            test
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) import std::stack(drop) ( -> ) def test \\{ ( -> ) {( -> ) def test1 \\{ (a -> ) {(a -> ) drop} }\n ( -> I32) 10i32 (I32 -> ) test1} }\n ( -> ) test}"
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

            def double (I64 -> I64) \{ 2i64 i64::* }
            def test (I64 -> I64) \{ \double apply }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn quotation_infers_function_type() {
        let contents = r#"
            import std::number::i64

            def test (I64 -> I64) \{ \{ 1i64 i64::+ } apply }
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

            def with (a (a -> b) -> b) \{ apply }

            mkcstr \{ dup from_cstr swap free_cstr } with use_str
        "#;
        let result = parse_and_type_check(contents, true);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn builtin_reference_type_checks() {
        // `\i64::+` references a builtin as a value; applying it consumes two I64.
        let contents = r#"
            import std::number::i64

            def test (I64 I64 -> I64) \{ \i64::+ apply }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn generic_higher_order_def_type_checks() {
        // A generic higher-order def: takes a value and a function over it.
        let contents = r#"
            import std::number::i64

            def double (I64 -> I64) \{ 2i64 i64::* }
            def with (a (a -> a) -> a) \{ apply }
            def test (I64 -> I64) \{ \double with }
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

            def copy (list::List<a> -> list::List<a>) \{
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

            def map (list::List<a> (a -> a) -> list::List<a>) \{
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

            def test (I64 -> I64 I64) \{ \stack::dup apply }
        "#;
        let result = parse_and_type_check(contents, false);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn eager_def_binds_value_and_consumes_stack() {
        // `doubled` runs `2i64 *` once against the current stack (consuming the
        // `5i64`), binds the result, and re-pushes it on reference.
        let contents = r#"
            import std::number::i64(* to_string)
            import std::io(println)

            5i64 def doubled { 2i64 * } doubled to_string println
        "#;
        let result = parse_and_type_check(contents, true);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn eager_def_in_module_consuming_stack_is_rejected() {
        // At module scope every def must be `( -> )`; an eager def that consumes
        // an input has type `(I64 -> )`, leaving the module non-`( -> )`.
        let contents = r#"
            import std::number::i64(*)
            def doubled { 2i64 * }
        "#;
        let error = parse_and_type_check(contents, false)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("Invalid top-level stack effect"),
            "unexpected error: {}",
            error
        );
    }

    #[test]
    fn eager_def_can_capture_a_function_value() {
        // `def k { \double }` captures the function *value* (not calling it);
        // referencing `k` pushes it, then `apply` runs it.
        let contents = r#"
            import std::number::i64(*)
            import std::stack(drop)

            def double (I64 -> I64) \{ 2i64 * }
            def k { \double }
            5i64 k apply drop
        "#;
        let result = parse_and_type_check(contents, true);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn namespace_member_navigation() {
        // An eager namespace def exposes its nested defs as `::`-navigable members.
        let contents = r#"
            import std::number::i64(*)
            import std::stack(drop)

            def math {
                def double (I64 -> I64) \{ 2i64 * }
            }
            5i64 math::double drop
        "#;
        let result = parse_and_type_check(contents, true);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn namespace_deep_nesting_and_self_reference() {
        // Arbitrary nesting depth, plus a member calling a qualified
        // self-reference (`math::double` from inside `math`) and an outer import.
        let contents = r#"
            import std::number::i64(*)
            import std::stack(drop)

            def math {
                def double (I64 -> I64) \{ 2i64 * }
                def geometry {
                    def perimeter (I64 -> I64) \{ math::double }
                }
            }
            5i64 math::geometry::perimeter drop
        "#;
        let result = parse_and_type_check(contents, true);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn namespace_private_member_hidden() {
        // A `defp` member is not navigable via `::` from outside.
        let contents = r#"
            import std::number::i64(+)
            import std::stack(drop)

            def m {
                defp secret (I64 -> I64) \{ 1i64 + }
            }
            5i64 m::secret drop
        "#;
        let error = parse_and_type_check(contents, true)
            .unwrap_err()
            .to_string();
        assert!(
            error.contains("m::secret not found"),
            "expected a not-found error for the private member: {}",
            error
        );
    }

    #[test]
    fn namespace_public_member_visible() {
        // The same shape with `def` (public) resolves.
        let contents = r#"
            import std::number::i64(+)
            import std::stack(drop)

            def m {
                def pub (I64 -> I64) \{ 1i64 + }
            }
            5i64 m::pub drop
        "#;
        let result = parse_and_type_check(contents, true);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn namespace_member_function_ref() {
        // `\m::f` references a member as a function value, applied via `apply`.
        let contents = r#"
            import std::number::i64(*)
            import std::stack(drop)

            def m {
                def double (I64 -> I64) \{ 2i64 * }
            }
            5i64 \m::double apply drop
        "#;
        let result = parse_and_type_check(contents, true);
        assert!(result.is_ok(), "{:?}", result);
    }

    #[test]
    fn lazy_def_is_callable() {
        // The `\` form keeps the historical function behaviour: referencing the
        // name runs the body.
        let contents = r#"
            import std::number::i64(*)
            import std::stack(drop)

            def double (I64 -> I64) \{ 2i64 * }
            5i64 double drop
        "#;
        let result = parse_and_type_check(contents, true);
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

            def test1 (option::Option<I64> -> ) \{
                drop
            }

            def test2 (Option<I64> -> ) \{
                drop
            }

            def test \{
                42 option::Some test1 42 Some test2
            }
        "#;
        let result = parse_and_type_check(contents, true).unwrap();

        assert_eq!(
            result,
            "( -> ) {( -> ) import std::option ( -> ) import std::stack(drop) ( -> ) type Option<a> {Some(val a) None} ( -> ) def test1 \\{ (std::option::Option<I64> -> ) {(std::option::Option<I64> -> ) drop} }\n ( -> ) def test2 \\{ (Option<I64> -> ) {(Option<I64> -> ) drop} }\n ( -> ) def test \\{ ( -> ) {( -> I64) 42i64 (I64 -> std::option::Option<I64>) option::Some (std::option::Option<I64> -> ) test1 ( -> I64) 42i64 (I64 -> Option<I64>) Some (Option<I64> -> ) test2} }\n}"
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

            def test_option (option::Option<I64> -> ) \{
                drop
            }

            def test \{
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

            def test_option (Option<I64> -> ) \{
                drop
            }

            def test \{
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

    // --------------------------------------------------------------- effects

    #[test]
    fn declared_effect_is_accepted() {
        // A function that performs IO and declares `!io::IO` type-checks.
        let contents = r#"
            import std::list
            import std::io(println)
            def shout (String -> !io::IO) \{ println }
            "hi" shout
            0i32
        "#;
        assert!(parse_and_type_check(contents, true).is_ok());
    }

    #[test]
    fn undeclared_effect_is_rejected() {
        // Calling an effectful function without declaring its effect is an error.
        let contents = r#"
            import std::list
            import std::io(println)
            def shout (String -> ) \{ println }
            "hi" shout
            0i32
        "#;
        assert!(matches!(
            parse_and_type_check(contents, true),
            Err(TypeCheckerError::UndeclaredEffect(..))
        ));
    }

    #[test]
    fn module_performing_io_is_rejected() {
        // A module is pure: an effectful top-level instruction is rejected.
        let contents = r#"
            import std::list
            import std::io(println)
            "side effect" println
        "#;
        assert!(matches!(
            parse_and_type_check(contents, false),
            Err(TypeCheckerError::InvalidModuleDefinition(..))
        ));
    }

    #[test]
    fn module_with_pure_instruction_is_allowed() {
        // The relaxation: a module may now hold non-definition instructions, as
        // long as they are pure (no stack change, no effects).
        let contents = r#"
            import std::stack(drop)
            1u8 drop
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn effectful_function_into_pure_param_is_rejected() {
        // Strict/sound: an effectful `(String -> !IO)` value cannot satisfy a
        // pure `(String -> )` parameter.
        let contents = r#"
            import std::list
            import std::io(println)
            def use_pure (String (String -> ) -> ) \{ apply }
            "x" \println use_pure
            0i32
        "#;
        assert!(matches!(
            parse_and_type_check(contents, true),
            Err(TypeCheckerError::EffectConflict(..))
        ));
    }

    #[test]
    fn effect_variable_threads_callee_effects() {
        // `!e` is bound to the argument's effects and threaded to the output, so
        // applying an effectful function makes the call effectful.
        let contents = r#"
            import std::list
            import std::io(println)
            def run (String (String -> !e) -> !e) \{ apply }
            "x" \println run
            0i32
        "#;
        let result = parse_and_type_check(contents, true).expect("should type-check");
        assert!(
            result.contains("!std::io::IO"),
            "expected the threaded IO effect, got: {result}"
        );
    }

    #[test]
    fn wildcard_param_accepts_effectful_function() {
        // `!*` accepts a function value carrying any effects.
        let contents = r#"
            import std::list
            import std::io(println)
            def run_any (String (String -> !*) -> !*) \{ apply }
            "x" \println run_any
            0i32
        "#;
        assert!(parse_and_type_check(contents, true).is_ok());
    }

    #[test]
    fn pure_function_into_effect_polymorphic_param_stays_pure() {
        // Passing a pure function to an `!e` combinator leaves the call pure.
        let contents = r#"
            import std::list
            import std::stack(drop)
            def run (String (String -> ) -> ) \{ apply }
            def consume (String -> ) \{ drop }
            "x" \consume run
        "#;
        let result = parse_and_type_check(contents, false).expect("should type-check");
        assert!(!result.contains('!'), "expected no effects, got: {result}");
    }

    #[test]
    fn undeclared_effect_name_is_rejected() {
        // Referencing an effect that was never declared with `effect` is an error.
        let contents = r#"
            import std::number::i64
            def f (I64 -> !Bogus) \{ }
            0i32
        "#;
        assert!(matches!(
            parse_and_type_check(contents, true),
            Err(TypeCheckerError::EffectNotFound(..))
        ));
    }

    #[test]
    fn effect_declaration_type_checks() {
        // `effect IO` is a valid pure declaration.
        let contents = r#"
            effect IO
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn match_arms_with_alpha_equivalent_generic_results() {
        // Each arm produces `Option<a>`, but through different generic paths
        // (`Some` vs the recursive `id`), so the arm types are alpha-equivalent
        // but not byte-identical. Match-arm consistency must accept them.
        let contents = r#"
            import std::list
            import std::option(Option None Some)
            import std::stack(drop)
            def id (Option<a> -> Option<a>) \{
                match {
                    Some(value) -> { value Some }
                    None        -> { None }
                }
            }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn match_arms_unify_identity_and_rebuild() {
        // One arm returns the scrutinee unchanged (`touch` → `(X -> X)`), the
        // other drops it and rebuilds (`(Y -> Option<Z>)`). The arms are not
        // alpha-equivalent but do unify to `(Option<w> -> Option<w>)`, so the
        // match must accept them. This is the shape of an AVL-map tree rotation.
        let contents = r#"
            import std::list
            import std::option(Option None Some)
            import std::stack(dup drop touch)
            defp f (Option<a> -> Option<a>) \{
                dup match {
                    Some(value) -> touch
                    None        -> { drop None }
                }
            }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn match_arms_with_genuinely_different_types_still_conflict() {
        // Unification must not be *too* lenient: arms producing incompatible
        // types (I64 vs a String) still conflict.
        let contents = r#"
            import std::list
            import std::option(Option None Some)
            import std::number::i64
            def f (Option<a> -> ) \{
                match {
                    Some(value) -> { 0i64 }
                    None        -> { "no" }
                }
            }
        "#;
        assert!(matches!(
            parse_and_type_check(contents, false),
            Err(TypeCheckerError::InvalidMatchBody(..))
        ));
    }

    #[test]
    fn unifier_reconciles_a_variable_constrained_twice() {
        // Calling `same (a a -> a)` requires both arguments to share a type. When
        // they arrive as two distinct variables (`b`, `c`), the unifier must
        // reconcile them (`b := c`) instead of reporting "expected a, got a".
        let contents = r#"
            import std::stack(swap drop)
            defp same (a a -> a) \{ swap drop }
            defp mk (b c -> a) \{ same }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }

    #[test]
    fn unifier_still_rejects_incompatible_constraints() {
        // Reconciliation must not mask real conflicts: a variable forced to be
        // both an I64 and a Char still fails.
        let contents = r#"
            import std::list
            import std::number::i64
            import std::stack(swap drop)
            defp same (a a -> a) \{ swap drop }
            defp bad ( -> a) \{ 0i64 'x' same }
        "#;
        assert!(parse_and_type_check(contents, false).is_err());
    }

    #[test]
    fn higher_order_recursive_fold_type_checks() {
        // A `fold` over a list with an accumulator function: it `dup`s the
        // function value and reuses generic stack builtins (`rot`) twice. Each
        // call site must instantiate its signature with fresh type variables;
        // otherwise the accumulator's type gets aliased to a shared builtin
        // variable and a later reuse collides (an infinite type / conflict).
        let contents = r#"
            import std::stack(dup drop rot rotr swap touch)
            type Lst<a> {
                Nil
                Cons(rest Lst<a> head a)
            }
            defp myfold (Lst<a> b (b a -> b) -> b) \{
                rot match {
                    Nil -> { drop touch }
                    Cons(rest head) -> {
                        dup rot swap head swap apply
                        swap rest rotr myfold
                    }
                }
            }
        "#;
        assert!(parse_and_type_check(contents, false).is_ok());
    }
}
