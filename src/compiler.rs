use std::{
    cell::RefCell,
    collections::HashMap,
    fs::read_to_string,
    path::{Path, PathBuf},
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
};

use inkwell::{
    AddressSpace, AtomicOrdering, AtomicRMWBinOp,
    builder::Builder,
    context::Context,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, StructType},
    values::{
        AggregateValue, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FunctionValue,
        PointerValue,
    },
};
mod error;

pub use error::CompilerError;

use crate::{
    internal_functions::builtins_functions,
    lexer::{IntegerNumber, Number, Position},
    parser::{AstNode, AstNodeType, FieldPattern, Parser, ParserError, Pattern},
    type_checker::{AstNodeWithType, ScopeKind, TypeChecker},
    types::{CustomType, LiteralType, NumberType, Type, UnitType, VarType},
};

pub struct CompilerContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub imports: HashMap<String, Scope<'ctx>>,
    pub type_definitions: HashMap<Vec<String>, CustomType>,
    pub global_strings: HashMap<String, PointerValue<'ctx>>,
    /// Set while a (non-`main`) definition's body is being compiled: identifies
    /// the function currently in scope for self-tail-call rewriting. A self-call
    /// that matches `function_name` and is in tail position becomes a branch back
    /// to `loop_header` (storing fresh args into `param_slots`) instead of a real
    /// `call`+`ret`, so direct recursion runs in constant stack. Saved/restored
    /// around nested definition compilation.
    tail_ctx: Option<TailContext<'ctx>>,
    /// Whether the node about to be compiled sits in tail position (its result is
    /// the enclosing function's result). Consumed at the call site in
    /// `call_function`; only meaningful together with `tail_ctx`.
    tail_position: bool,
    /// Owned values (currently: `match` scrutinees) whose drop the surrounding
    /// code defers until *after* the arm body — in normal flow that drop runs at
    /// the `match`'s merge block. A self-tail-call back-edge skips the merge, so
    /// before branching it must replay these drops itself, or the scrutinee leaks
    /// once per iteration. Innermost-last; only populated for arms in tail
    /// position (the only ones that can produce a back-edge).
    tail_cleanups: Vec<(UnitType, BasicValueEnum<'ctx>)>,
}

/// Self-tail-call target for the function whose body is currently compiling.
/// Mutual / cross-function tail calls are out of scope (they need real backend
/// tail calls); only direct self-recursion is lowered to a loop here.
#[derive(Clone)]
struct TailContext<'ctx> {
    function_name: String,
    param_slots: Vec<PointerValue<'ctx>>,
    loop_header: inkwell::basic_block::BasicBlock<'ctx>,
}

/// Compiles a `.clem` source file to LLVM IR, returning the path to the emitted
/// `.ll` file along with any FFI C glue files discovered while resolving imports
/// (a sibling `<name>.c` next to each resolved module). The caller links those.
pub fn compile(
    file: impl AsRef<Path>,
    search_paths: &[PathBuf],
) -> Result<(PathBuf, Vec<PathBuf>), CompilerError> {
    let path_as_string = file.as_ref().display().to_string();
    let file_content = read_to_string(file.as_ref())?;

    let c_sources = Rc::new(RefCell::new(Vec::new()));
    let program = Parser::new_from_file_with(
        &file_content,
        path_as_string,
        Rc::from(search_paths.to_vec()),
        c_sources.clone(),
    )
    .collect::<Result<Vec<AstNode>, ParserError>>()?;
    let program = TypeChecker::new().type_check(
        AstNode {
            node_type: AstNodeType::Block(program),
            position: Position::default(),
            type_definition: None,
        },
        ScopeKind::Entry,
        vec![],
    )?;
    let context = Context::create();
    let mut stack = Stack::new();

    let scope = Scope::empty();
    let mut compiler_context = CompilerContext::new(&context);

    // The entry file has no `main`: its top-level block *is* the program. Emit an
    // LLVM `main` whose body is that block (executable words run in source order;
    // lazy defs register callables; eager defs bind values). The block's type is
    // `( -> )` (exit 0) or `( -> I32)` (the value left on the stack is the exit
    // code), enforced by the type checker.
    let main_type = compiler_context.context.i32_type().fn_type(&[], false);
    let main_function = compiler_context
        .module
        .add_function("main", main_type, None);
    let entry_block = compiler_context
        .context
        .append_basic_block(main_function, "entry");
    compiler_context.builder.position_at_end(entry_block);
    compiler_context.tail_ctx = None;
    compiler_context.tail_position = false;

    compiler_context.compile_ast(scope, &mut stack, program.0, vec![])?;

    match stack.pop() {
        Some(value) => {
            compiler_context.builder.build_return(Some(&value.1))?;
        }
        None => {
            compiler_context.builder.build_return(Some(
                &compiler_context
                    .context
                    .i32_type()
                    .const_zero()
                    .as_basic_value_enum(),
            ))?;
        }
    }

    let mut output_path = file.as_ref().to_path_buf();
    output_path.set_extension("ll");
    compiler_context
        .module
        .print_to_file(&output_path)
        .map_err(|err| CompilerError::WriteLLVMError(err.to_string()))?;
    let discovered_c_sources = Rc::try_unwrap(c_sources)
        .map(RefCell::into_inner)
        .unwrap_or_else(|rc| rc.borrow().clone());
    Ok((output_path, discovered_c_sources))
}

impl<'ctx> CompilerContext<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        let module = context.create_module("std");
        let builder = context.create_builder();

        Self {
            context,
            module,
            builder,
            imports: HashMap::new(),
            type_definitions: HashMap::new(),
            global_strings: HashMap::new(),
            tail_ctx: None,
            tail_position: false,
            tail_cleanups: Vec::new(),
        }
    }

    /// True when the block the builder is currently positioned in already has a
    /// terminator — e.g. a self-tail-call just rewrote this path into a back-edge,
    /// so callers must not emit a fall-through branch or a `ret` after it.
    fn current_block_terminated(&self) -> bool {
        self.builder
            .get_insert_block()
            .and_then(|b| b.get_terminator())
            .is_some()
    }

    /// Allocates `size` bytes from the slab pool (`clem_alloc`) instead of `malloc`.
    pub fn build_pool_alloc(
        &self,
        size: inkwell::values::IntValue<'ctx>,
    ) -> Result<PointerValue<'ctx>, CompilerError> {
        let clem_alloc = self
            .module
            .get_function("clem_alloc")
            .ok_or(CompilerError::GetFunctionError("clem_alloc".into()))?;
        Ok(self
            .builder
            .build_call(clem_alloc, &[size.into()], "alloc")?
            .try_as_basic_value()
            .left()
            .ok_or(CompilerError::FunctionCallError)?
            .into_pointer_value())
    }

    /// Returns a node to the slab pool (`clem_free`) instead of `free`.
    pub fn build_pool_free(&self, ptr: PointerValue<'ctx>) -> Result<(), CompilerError> {
        let clem_free = self
            .module
            .get_function("clem_free")
            .ok_or(CompilerError::GetFunctionError("clem_free".into()))?;
        self.builder.build_call(clem_free, &[ptr.into()], "")?;
        Ok(())
    }

    pub fn drop_value(
        &self,
        ty: UnitType,
        value: BasicValueEnum<'ctx>,
    ) -> Result<(), CompilerError> {
        let ref_count_type = self.context.i64_type();
        match ty {
            UnitType::Custom {
                name,
                generic_types,
            } => {
                let ref_count_struct = self.base_custom_type();
                let ptr = value.into_pointer_value();

                let rc_field_ptr =
                    self.builder
                        .build_struct_gep(ref_count_struct, ptr, 0, "ref_count")?;
                // Atomically decrement the refcount. `old` is the value *before* the
                // subtraction; Release ordering ensures any writes through this owner
                // happen-before the decrement other owners observe.
                let old = self.builder.build_atomicrmw(
                    AtomicRMWBinOp::Sub,
                    rc_field_ptr,
                    ref_count_type.const_int(1, false),
                    AtomicOrdering::Release,
                )?;
                // We were the last owner iff the count was 1 before decrementing.
                let condition = self.builder.build_int_compare(
                    inkwell::IntPredicate::NE,
                    old,
                    ref_count_type.const_int(1, false),
                    "if_cond",
                )?;

                let current_function = self
                    .builder
                    .get_insert_block()
                    .ok_or(CompilerError::IfWithoutFunction)?
                    .get_parent()
                    .ok_or(CompilerError::IfWithoutFunction)?;
                let with_more_references = self
                    .context
                    .append_basic_block(current_function, "with_more_references");
                let merge_block = self.context.append_basic_block(current_function, "merge");
                let free_rc = self.context.append_basic_block(current_function, "free_rc");
                self.builder
                    .build_conditional_branch(condition, with_more_references, free_rc)?;

                // The atomicrmw already wrote the decremented count, so this path just
                // continues without freeing.
                self.builder.position_at_end(with_more_references);
                self.builder.build_unconditional_branch(merge_block)?;

                self.builder.position_at_end(free_rc);
                // Acquire fence: pair with the Release decrements above so every prior
                // owner's writes are visible before we read the payload and free it.
                self.builder.build_fence(AtomicOrdering::Acquire, 0, "")?;
                let variant_type = self.context.i8_type();

                let variant_ptr =
                    self.builder
                        .build_struct_gep(ref_count_struct, ptr, 1, "variant")?;
                let variant = self
                    .builder
                    .build_load(variant_type, variant_ptr, "get_variant")?
                    .into_int_value();
                let Some(ty) = self.get_type(name) else {
                    return Err(CompilerError::UnexpectedType);
                };
                let mut blocks = Vec::new();
                let variant_merge_block =
                    self.context.append_basic_block(current_function, "merge");
                for (index, _) in ty.variants.iter().enumerate() {
                    let block = self.context.append_basic_block(current_function, "variant");
                    blocks.push((self.context.i8_type().const_int(index as u64, false), block));
                }
                self.builder
                    .build_switch(variant, variant_merge_block, &blocks)?;
                let generics_map = ty
                    .generics
                    .iter()
                    .map(|generic| generic.1.clone())
                    .zip(generic_types.iter().cloned())
                    .collect::<HashMap<_, _>>();
                for (index, variant) in ty.variants.into_iter().enumerate() {
                    let (_, block) = blocks[index];
                    self.builder.position_at_end(block);
                    let variant_type =
                        custom_type_variant_struct(variant, generics_map.clone(), self)?;
                    if variant_type.count_fields() > 0 {
                        let payload_ptr = self.builder.build_struct_gep(
                            ref_count_struct,
                            ptr,
                            2,
                            "payload_ptr",
                        )?;

                        for field in 0..variant_type.count_fields() {
                            match variant_type.get_field_type_at_index(field) {
                                Some(BasicTypeEnum::PointerType(pointer_ty)) => {
                                    let field_ptr = self.builder.build_struct_gep(
                                        variant_type,
                                        payload_ptr,
                                        field,
                                        "field",
                                    )?;
                                    let field_value = self.builder.build_load(
                                        BasicTypeEnum::PointerType(pointer_ty),
                                        field_ptr,
                                        "field_value",
                                    )?;
                                    self.build_pool_free(field_value.into_pointer_value())?;
                                }
                                Some(_) => {}
                                None => {}
                            }
                        }
                    }
                    self.builder
                        .build_unconditional_branch(variant_merge_block)?;
                }
                self.builder.position_at_end(variant_merge_block);

                self.build_pool_free(ptr)?;
                self.builder.build_unconditional_branch(merge_block)?;
                self.builder.position_at_end(merge_block);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    /// Releases one reference to a heap node, freeing **only the node itself**
    /// (never its fields) when the count reaches zero.
    ///
    /// Used on self-tail-call back-edges, which bypass the `match` merge where the
    /// scrutinee is normally dropped. The full `drop_value` recursively frees a
    /// node's child pointers, but a child may have been bound out of the scrutinee
    /// and threaded into the next iteration — e.g. `tail` in a list fold — so
    /// freeing it here would be a use-after-free once the loop reloads it. Freeing
    /// just the node avoids that. The trade-off: a sole-owned child (one not
    /// threaded forward) is leaked, which matches the reference-counting runtime's
    /// existing limitation around recursive types (it has no runtime deep-drop).
    fn build_rc_release_node_only(
        &self,
        ty: UnitType,
        value: BasicValueEnum<'ctx>,
    ) -> Result<(), CompilerError> {
        let UnitType::Custom { .. } = ty else {
            return Ok(());
        };
        let ptr = value.into_pointer_value();
        let rc_type = self.context.i64_type();
        let base = self.base_custom_type();
        let rc_ptr = self.builder.build_struct_gep(base, ptr, 0, "rc")?;
        let old = self.builder.build_atomicrmw(
            AtomicRMWBinOp::Sub,
            rc_ptr,
            rc_type.const_int(1, false),
            AtomicOrdering::Release,
        )?;
        let is_last = self.builder.build_int_compare(
            inkwell::IntPredicate::EQ,
            old,
            rc_type.const_int(1, false),
            "tc_last_ref",
        )?;
        let current_function = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?
            .get_parent()
            .ok_or(CompilerError::IfWithoutFunction)?;
        let free_block = self.context.append_basic_block(current_function, "tc_free");
        let cont_block = self.context.append_basic_block(current_function, "tc_cont");
        self.builder
            .build_conditional_branch(is_last, free_block, cont_block)?;
        self.builder.position_at_end(free_block);
        self.builder.build_fence(AtomicOrdering::Acquire, 0, "")?;
        self.build_pool_free(ptr)?;
        self.builder.build_unconditional_branch(cont_block)?;
        self.builder.position_at_end(cont_block);
        Ok(())
    }

    pub fn clone_value(
        &self,
        ty: UnitType,
        value: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match ty {
            UnitType::Custom { .. } => {
                let ptr = value.into_pointer_value();
                let ref_count_type = self.context.i64_type();
                let ref_count_struct = self.base_custom_type();

                let rc_field_ptr =
                    self.builder
                        .build_struct_gep(ref_count_struct, ptr, 0, "ref_count")?;
                // Atomically bump the refcount. Monotonic (Relaxed) is sufficient:
                // incrementing only needs the count itself to be race-free, with no
                // ordering against the referent's data.
                self.builder.build_atomicrmw(
                    AtomicRMWBinOp::Add,
                    rc_field_ptr,
                    ref_count_type.const_int(1, false),
                    AtomicOrdering::Monotonic,
                )?;
                Ok(BasicValueEnum::PointerValue(ptr))
            }
            _ => Ok(value),
        }
    }

    /// Lifts a `\{ ... }` quotation into a fresh top-level LLVM function with the
    /// inferred signature `sig`, compiles its body, and returns the function so
    /// the caller can push its pointer. Quotations are anonymous (never
    /// self-recursive) and capture nothing — they operate purely on the stack.
    fn compile_quotation(
        &mut self,
        scope: Scope<'ctx>,
        sig: Type,
        nodes: Vec<AstNodeWithType>,
        position: Position,
        module_path: Vec<String>,
    ) -> Result<FunctionValue<'ctx>, CompilerError> {
        let current_block = self.builder.get_insert_block();
        let function_type = self.get_llvm_function_type(&sig)?;
        let name = format!("quot_{}", QUOT_ID.fetch_add(1, Ordering::Relaxed));
        let function = self.module.add_function(&name, function_type, None);

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let mut stack = Stack::new();
        for (pop_type, arg) in sig.pop_types.iter().cloned().zip(function.get_param_iter()) {
            stack.push((pop_type, arg));
        }

        // Anonymous quotations are never self-recursive: no tail loop. Save and
        // restore the enclosing function's tail context (we may be lifting this
        // quotation from inside another function's body).
        let prev_tail_ctx = self.tail_ctx.take();
        let prev_tail_position = self.tail_position;
        let prev_tail_cleanups = std::mem::take(&mut self.tail_cleanups);
        self.tail_position = false;

        let body = AstNodeWithType::new(AstNodeType::Block(nodes), position, sig.clone());
        let result = self.compile_ast(scope, &mut stack, body, module_path);

        self.tail_ctx = prev_tail_ctx;
        self.tail_position = prev_tail_position;
        self.tail_cleanups = prev_tail_cleanups;
        result?;

        if !self.current_block_terminated() {
            self.emit_function_return(function_type, &mut stack, &name)?;
        }

        if let Some(block) = current_block {
            self.builder.position_at_end(block);
        }
        Ok(function)
    }

    /// Packs the remaining stack into the function's `ret` (single value, packed
    /// struct for multiple results, or `void`). Shared by quotation lifting and
    /// builtin-wrapper generation; the caller must have checked the block isn't
    /// already terminated.
    fn emit_function_return(
        &self,
        function_type: inkwell::types::FunctionType<'ctx>,
        stack: &mut Stack<'ctx>,
        name: &str,
    ) -> Result<(), CompilerError> {
        match function_type.get_return_type() {
            Some(BasicTypeEnum::StructType(return_type)) => {
                let return_val = stack.remove_all();
                let mut struct_val = return_type.get_undef().as_aggregate_value_enum();
                for (index, value) in return_val.into_iter().enumerate() {
                    struct_val = self.builder.build_insert_value(
                        struct_val,
                        value.1,
                        index as u32,
                        &format!("ret_{}", index),
                    )?;
                }
                self.builder
                    .build_return(Some(&struct_val.as_basic_value_enum()))?;
            }
            Some(return_type) => {
                let return_val = stack.remove_all();
                if return_val.len() != 1 {
                    return Err(CompilerError::InvalidStackForFunction(name.to_string()));
                }
                let return_val = return_val[0].clone().1;
                if return_val.get_type() != return_type {
                    return Err(CompilerError::InvalidStackForFunction(name.to_string()));
                }
                self.builder.build_return(Some(&return_val))?;
            }
            None => {
                if !stack.is_empty() {
                    return Err(CompilerError::InvalidStackForFunction(name.to_string()));
                }
                self.builder.build_return(None)?;
            }
        }
        Ok(())
    }

    /// Builds a real LLVM function wrapping a builtin's inline IR-emitter at a
    /// concrete signature, so `\+`, `\swap`, etc. can be used as function values.
    /// The wrapper seeds a temporary stack with its parameters, runs the builtin
    /// closure (which emits the IR inline), and returns the result(s).
    fn materialize_builtin_wrapper(
        &mut self,
        name: &str,
        sig: Type,
        inline: &DefinitionType<'ctx>,
    ) -> Result<FunctionValue<'ctx>, CompilerError> {
        let current_block = self.builder.get_insert_block();
        let function_type = self.get_llvm_function_type(&sig)?;
        let mangled = format!(
            "builtinwrap_{}_{}__{}",
            name,
            sig.pop_types
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join("_"),
            sig.push_types
                .iter()
                .map(|t| t.to_string())
                .collect::<Vec<_>>()
                .join("_")
        );
        let function = self.module.add_function(&mangled, function_type, None);

        let entry = self.context.append_basic_block(function, "entry");
        self.builder.position_at_end(entry);

        let mut stack = Stack::new();
        for (pop_type, arg) in sig.pop_types.iter().cloned().zip(function.get_param_iter()) {
            stack.push((pop_type, arg));
        }

        inline(self, &mut stack)?;

        if !self.current_block_terminated() {
            self.emit_function_return(function_type, &mut stack, &mangled)?;
        }

        if let Some(block) = current_block {
            self.builder.position_at_end(block);
        }
        Ok(function)
    }

    fn compile_ast(
        &mut self,
        scope: Scope<'ctx>,
        stack: &mut Stack<'ctx>,
        program: AstNodeWithType,
        module_path: Vec<String>,
    ) -> Result<(), CompilerError> {
        match program.node_type {
            AstNodeType::Number(number) => self.compile_number(stack, number),
            AstNodeType::Char(c) => self.compile_char(stack, c),
            AstNodeType::Symbol(symbol) => {
                // `apply` is the builtin that runs a function value off the stack;
                // it is not a real definition, so dispatch it directly.
                if symbol == "apply" {
                    apply_function(self, stack)?;
                } else {
                    // `tail_position` stays set across the call so `call_function`
                    // can see it; clear it afterwards so it never leaks to a
                    // sibling word.
                    let ty = concretize_call_type(&program.type_definition, stack);
                    scope.call_symbol(vec![symbol], self, ty, stack)?;
                }
                self.tail_position = false;
                Ok(())
            }
            AstNodeType::SymbolWithPath(symbol) => {
                let ty = concretize_call_type(&program.type_definition, stack);
                scope.call_symbol(symbol, self, ty, stack)?;
                self.tail_position = false;
                Ok(())
            }
            AstNodeType::Block(nodes) => {
                let scope = Scope::with_parent(scope);
                // Only the last word of a tail-positioned block is itself in tail
                // position; earlier words run for their stack effect.
                let outer_tail = self.tail_position;
                let last = nodes.len().saturating_sub(1);
                for (index, node) in nodes.into_iter().enumerate() {
                    self.tail_position = outer_tail && index == last;
                    self.compile_ast(scope.clone(), stack, node, module_path.clone())?;
                    // A self-tail-call rewrote this point into a back-edge: the
                    // block is terminated, so nothing further on this path runs.
                    if self.current_block_terminated() {
                        break;
                    }
                }
                self.tail_position = false;

                // Release eager bindings introduced in this block. Skipped when a
                // tail-call already terminated the block (the back-edge bypasses
                // this, matching the existing tail-loop leak trade-off).
                if !self.current_block_terminated() {
                    scope.release_owned_values(self)?;
                }

                Ok(())
            }
            AstNodeType::FunctionRef(symbol) => {
                // The type checker resolved this to `( -> Type(sig))`: materialize
                // the named definition at `sig` and push its pointer as a value.
                let UnitType::Type(sig) = program.type_definition.push_types[0].clone() else {
                    return Err(CompilerError::UnexpectedType);
                };
                if type_contains_var(&sig) {
                    return Err(CompilerError::UnresolvedFunctionValue(
                        format!("\\{}", symbol.join("::")),
                        program.position,
                    ));
                }
                let function = scope.materialize_symbol(symbol, self, sig.clone())?;
                let pointer = function.as_global_value().as_pointer_value();
                stack.push((UnitType::Type(sig), pointer.as_basic_value_enum()));
                self.tail_position = false;
                Ok(())
            }
            AstNodeType::Quotation(nodes) => {
                let UnitType::Type(sig) = program.type_definition.push_types[0].clone() else {
                    return Err(CompilerError::UnexpectedType);
                };
                if type_contains_var(&sig) {
                    return Err(CompilerError::UnresolvedFunctionValue(
                        "\\{ ... }".to_string(),
                        program.position.clone(),
                    ));
                }
                let function = self.compile_quotation(
                    Scope::with_parent(scope),
                    sig.clone(),
                    nodes,
                    program.position,
                    module_path,
                )?;
                let pointer = function.as_global_value().as_pointer_value();
                stack.push((UnitType::Type(sig), pointer.as_basic_value_enum()));
                self.tail_position = false;
                Ok(())
            }
            AstNodeType::Definition {
                name: symbol,
                is_lazy,
                body,
                ..
            } => {
                if is_lazy {
                    // Lazy function def: register a callable (today's behaviour).
                    self.compile_definition(scope, &symbol, *body, module_path)
                } else {
                    // Eager value def: run the body once against the current stack
                    // and capture its output(s) into the name. The body consumes
                    // its inputs from the stack; we pop the produced outputs and
                    // bind them so later references re-push (cloned) copies.
                    //
                    // If the body is a block that declares nested defs, the def is
                    // also a *namespace*: we compile its body into a retained
                    // `member_scope` (so the nested defs' closures capture it) and
                    // register it as members for `name::member` navigation. We do
                    // NOT release `member_scope` — like an import, a namespace's
                    // bindings live for the program (const-like).
                    let n_outputs = body.type_definition.push_types.len();
                    self.tail_position = false;
                    let body = *body;
                    if let AstNodeType::Block(nodes) = body.node_type {
                        let member_scope = Scope::with_parent(scope.clone());
                        // Register the member scope BEFORE compiling the body so a
                        // qualified self-reference (`math::double` inside `math`)
                        // resolves, and the nested defs' closures capture it.
                        scope.add_member(symbol.clone(), member_scope.clone());
                        for node in nodes {
                            self.tail_position = false;
                            self.compile_ast(
                                member_scope.clone(),
                                stack,
                                node,
                                module_path.clone(),
                            )?;
                            if self.current_block_terminated() {
                                break;
                            }
                        }
                    } else {
                        self.compile_ast(scope.clone(), stack, body, module_path)?;
                    }
                    let mut values = Vec::with_capacity(n_outputs);
                    for _ in 0..n_outputs {
                        values.push(stack.pop().ok_or(CompilerError::StackUnderflow)?);
                    }
                    values.reverse();
                    scope.add_owned_values(symbol, values);
                    self.tail_position = false;
                    Ok(())
                }
            }
            AstNodeType::ExternalDefinition(symbol, ty) => {
                for function in builtins_functions(self) {
                    if function.name == symbol && match_types(&ty.pop_types, &function.ty.pop_types)
                    {
                        let fun = function.function.clone();
                        scope.add_function_definition(
                            function.name.as_str(),
                            Box::new(
                                move |ty: Type,
                                      _: &mut CompilerContext<'ctx>,
                                      definitions: DefinitionInstances<'ctx>|
                                      -> Result<(), CompilerError> {
                                    let mut definitions = definitions.borrow_mut();
                                    definitions.push((ty, fun.clone(), None));
                                    Ok(())
                                },
                            ),
                        );
                        return Ok(());
                    }
                }
                let function_type = self.get_llvm_function_type(&ty)?;
                self.module.add_function(&symbol, function_type, None);
                scope.add_external_definition(symbol, ty);
                Ok(())
            }
            AstNodeType::Import(path, import_node) => {
                let import_scope = if let Some(nodes) = import_node.node {
                    let AstNodeType::Block(nodes) = nodes.node_type else {
                        return Err(CompilerError::InvalidImportType(program.position));
                    };
                    let import_scope = Scope::empty();
                    // let mut module_path = module_path.clone();
                    // module_path.extend(path);
                    for node in nodes {
                        self.compile_ast(import_scope.clone(), stack, node, path.clone())?;
                    }

                    self.imports
                        .insert(import_node.name.name, import_scope.clone());
                    import_scope
                } else {
                    self.imports
                        .get(&import_node.name.name)
                        .ok_or(CompilerError::ImportNotFound)?
                        .clone()
                };
                for function_import in import_node.functions {
                    scope.add_function_import(
                        function_import.alias,
                        function_import.name,
                        import_node.name.alias.clone(),
                    );
                }

                scope.add_import(import_node.name.alias, import_scope);
                Ok(())
            }
            AstNodeType::CustomType {
                name,
                generics,
                variants,
            } => {
                let mut module_path = module_path.clone();
                module_path.push(name);
                self.type_definitions.insert(
                    module_path.clone(),
                    CustomType {
                        name: module_path,
                        generics: generics.clone(),
                        variants: variants.clone(),
                    },
                );

                for (index, variant) in variants.into_iter().enumerate() {
                    scope.add_function_definition(
                        variant.0.clone().as_str(),
                        Box::new(
                            move |ty: Type,
                                  _: &mut CompilerContext<'ctx>,
                                  definitions: DefinitionInstances<'ctx>|
                                  -> Result<(), CompilerError> {
                                let mut definitions = definitions.borrow_mut();
                                definitions.push((ty.clone(), Rc::new(Box::new(move |compiler_context: &mut CompilerContext<'ctx>,
                                      stack: &mut Stack<'ctx>|
                                      -> Result<(), CompilerError> {
                                        let base_struct = compiler_context.base_custom_type();
                                        let values = stack.pop_n(ty.pop_types.len());
                                        // Build the heap payload layout from the actual field
                                        // values' LLVM types rather than from the (possibly still
                                        // generic) field types. This lets a generic definition
                                        // construct a generic value: the value carries a concrete
                                        // type even when the constructor's static type variable
                                        // was never monomorphized. The match/drop paths rebuild
                                        // the same layout from the concrete type, so they agree.
                                        let variant_struct = compiler_context.context.struct_type(
                                            &values
                                                .iter()
                                                .map(|value| value.1.get_type())
                                                .collect::<Vec<_>>(),
                                            true,
                                        );
                                        let obj_size = base_struct
                                            .size_of()
                                            .expect("size_of works");
                                        let payload_size = variant_struct
                                            .size_of()
                                            .expect("size_of works");
                                        let total_size = compiler_context.builder.build_int_add(
                                            obj_size,
                                            payload_size,
                                            "obj_alloc_size",
                                        )?;

                                        let struct_val = compiler_context.build_pool_alloc(total_size)?;
                                        let rc_ptr = compiler_context.builder.build_struct_gep(base_struct, struct_val, 0, "rc")?;
                                        let field_ptr = compiler_context.builder.build_struct_gep(base_struct, struct_val, 1, "variant")?;
                                        compiler_context.builder.build_store(rc_ptr, compiler_context.context.i64_type().const_int(1, false))?;
                                        compiler_context.builder.build_store(field_ptr, compiler_context.context.i8_type().const_int(index as u64, false))?;
                                        let payload_ptr = compiler_context.builder.build_struct_gep(base_struct, struct_val, 2, "payload")?;
                                        (0..(variant_struct.count_fields() as usize)).try_for_each(|field_index| -> Result<(), CompilerError> {
                                            let field_ptr = compiler_context.builder.build_struct_gep(variant_struct, payload_ptr, field_index as u32, &format!("field_{}", field_index))?;
                                            compiler_context.builder.build_store(field_ptr, values[field_index].1)?;
                                            Ok(())
                                        })?;
                                        stack.push((ty.push_types[0].clone(), struct_val.into()));
                                        Ok(())
                                })), None));
                                Ok(())
                            },
                        ),
                    );
                }

                Ok(())
            }
            // Effects are a compile-time-only concept (the type checker is the
            // only gate); an `effect` declaration produces no code.
            AstNodeType::EffectDefinition(_) => Ok(()),
            AstNodeType::Match(cases) => {
                self.compile_match(scope, cases, stack, module_path, program.type_definition)
            }
        }
    }

    /// A char literal lowers to its Unicode scalar (code point) as an i32.
    fn compile_char(&self, stack: &mut Stack<'ctx>, c: char) -> Result<(), CompilerError> {
        stack.push((
            UnitType::Literal(LiteralType::Char),
            self.context
                .i32_type()
                .const_int(c as u64, false)
                .as_basic_value_enum(),
        ));
        Ok(())
    }

    fn compile_number(&self, stack: &mut Stack<'ctx>, number: Number) -> Result<(), CompilerError> {
        let (unit_type, llvm_number) = self.number_to_llvm_number(number);
        stack.push((unit_type, llvm_number));
        Ok(())
    }

    fn number_to_llvm_number(&self, number: Number) -> (UnitType, BasicValueEnum<'ctx>) {
        match number {
            Number::Integer(IntegerNumber::U8(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                self.context
                    .i8_type()
                    .const_int_arbitrary_precision(&[n as u64])
                    .into(),
            ),
            Number::Integer(IntegerNumber::U16(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                self.context
                    .i16_type()
                    .const_int_arbitrary_precision(&[n as u64])
                    .into(),
            ),
            Number::Integer(IntegerNumber::U32(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                self.context
                    .i32_type()
                    .const_int_arbitrary_precision(&[n as u64])
                    .into(),
            ),
            Number::Integer(IntegerNumber::U64(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                self.context
                    .i64_type()
                    .const_int_arbitrary_precision(&[n])
                    .into(),
            ),
            Number::Integer(IntegerNumber::U128(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                self.context
                    .i128_type()
                    .const_int_arbitrary_precision(&[
                        u64::from_le_bytes(
                            n.to_le_bytes()[..8]
                                .try_into()
                                .expect("We know that we have the correct number of bytes"),
                        ),
                        u64::from_le_bytes(
                            n.to_le_bytes()[8..]
                                .try_into()
                                .expect("We know that we have the correct number of bytes"),
                        ),
                    ])
                    .into(),
            ),
            Number::Integer(IntegerNumber::I8(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                self.context
                    .i8_type()
                    .const_int_arbitrary_precision(&[n as u64])
                    .into(),
            ),
            Number::Integer(IntegerNumber::I16(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                self.context
                    .i16_type()
                    .const_int_arbitrary_precision(&[n as u64])
                    .into(),
            ),
            Number::Integer(IntegerNumber::I32(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                self.context
                    .i32_type()
                    .const_int_arbitrary_precision(&[n as u64])
                    .into(),
            ),
            Number::Integer(IntegerNumber::I64(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                self.context
                    .i64_type()
                    .const_int_arbitrary_precision(&[n as u64])
                    .into(),
            ),
            Number::Integer(IntegerNumber::I128(n)) => (
                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                self.context
                    .i128_type()
                    .const_int_arbitrary_precision(&[
                        u64::from_le_bytes(
                            n.to_le_bytes()[..8]
                                .try_into()
                                .expect("We know that we have the correct number of bytes"),
                        ),
                        u64::from_le_bytes(
                            n.to_le_bytes()[8..]
                                .try_into()
                                .expect("We know that we have the correct number of bytes"),
                        ),
                    ])
                    .into(),
            ),
            Number::Float(float) => (
                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                self.context
                    .f64_type()
                    .const_float(
                        float
                            .parse()
                            .expect("We checked that this is a valid float in the lexer"),
                    )
                    .into(),
            ),
        }
    }

    fn compile_definition(
        &mut self,
        scope: Scope<'ctx>,
        symbol: &str,
        body: AstNodeWithType,
        module_path: Vec<String>,
    ) -> Result<(), CompilerError> {
        let cloned_scope = scope.clone();
        let symbol_name = symbol.to_string();
        let id = scope.id();

        scope.add_function_definition(
            symbol,
            Box::new(
                move |ty: Type,
                      context: &mut CompilerContext<'ctx>,
                      definitions: DefinitionInstances<'ctx>| {
                    let cloned_scope = cloned_scope.clone();
                    let mut body = body.clone();
                    // Concretize the generic body for this monomorphic instance:
                    // match the def's (possibly generic) signature against the
                    // concrete `ty` and rewrite every node's type. This is what
                    // makes generic defs — and function-value parameters typed
                    // `(a -> a)` — usable at a concrete type.
                    let mut generics_map = HashMap::new();
                    for (template, concrete) in body
                        .type_definition
                        .pop_types
                        .iter()
                        .zip(ty.pop_types.iter())
                    {
                        bind_generics(template, concrete, &mut generics_map);
                    }
                    for (template, concrete) in body
                        .type_definition
                        .push_types
                        .iter()
                        .zip(ty.push_types.iter())
                    {
                        bind_generics(template, concrete, &mut generics_map);
                    }
                    if !generics_map.is_empty() {
                        substitute_ast_types(&mut body, &generics_map);
                    }
                    let current_block = context.builder.get_insert_block();

                    let function_type = context.get_llvm_function_type(&ty)?;
                    let function_name = format!(
                        "{}_{}_{}__{}",
                        symbol_name,
                        id,
                        ty.pop_types
                            .iter()
                            .map(|t| t.to_string())
                            .collect::<Vec<_>>()
                            .join("_"),
                        ty.push_types
                            .iter()
                            .map(|t| t.to_string())
                            .collect::<Vec<_>>()
                            .join("_")
                    );

                    let function = context
                        .module
                        .add_function(&function_name, function_type, None);
                    // Kept for the tail-call context; `function_name` itself is
                    // moved into the call closure below.
                    let tail_function_name = function_name.clone();
                    let symbol_name_cloned = symbol_name.clone();
                    {
                        let mut definitions = definitions.borrow_mut();
                        definitions.push((
                            ty.clone(),
                            Rc::new(Box::new(
                                move |compiler_context: &mut CompilerContext<'ctx>,
                                      stack: &mut Stack<'ctx>|
                                      -> Result<(), CompilerError> {
                                    call_function(
                                        compiler_context,
                                        stack,
                                        symbol_name_cloned.clone(),
                                        function_name.clone(),
                                        ty.clone(),
                                    )
                                },
                            )),
                            Some(function),
                        ));
                    }
                    let new_scope = Scope::with_parent(cloned_scope);

                    // Give each parameter a stack slot seeded with the incoming
                    // argument, then fall into a loop header. A self-tail-call is
                    // lowered to "store fresh args into these slots; branch back to
                    // the header", reusing this frame so direct recursion runs in
                    // constant stack regardless of the optimization level.
                    let entry = context.context.append_basic_block(function, "entry");
                    let loop_header = context.context.append_basic_block(function, "tail_loop");
                    context.builder.position_at_end(entry);

                    let mut param_slots = Vec::new();
                    let mut reload = Vec::new();
                    for (pop_type, arg) in body
                        .type_definition
                        .pop_types
                        .clone()
                        .into_iter()
                        .zip(function.get_param_iter())
                    {
                        let llvm_type = arg.get_type();
                        let slot = context.builder.build_alloca(llvm_type, "param_slot")?;
                        context.builder.build_store(slot, arg)?;
                        param_slots.push(slot);
                        reload.push((pop_type, llvm_type, slot));
                    }
                    context.builder.build_unconditional_branch(loop_header)?;
                    context.builder.position_at_end(loop_header);

                    let mut stack = Stack::new();
                    for (pop_type, llvm_type, slot) in &reload {
                        let value = context.builder.build_load(*llvm_type, *slot, "param")?;
                        stack.push((pop_type.clone(), value));
                    }

                    // Activate self-tail-call rewriting for this function's body,
                    // saving/restoring any enclosing function's context (definition
                    // bodies can be compiled nested — a `defp` first called from
                    // inside another function's match arm). In particular
                    // `tail_cleanups` MUST reset, or this function's back-edge would
                    // try to release the enclosing function's scrutinee.
                    let prev_tail_ctx = context.tail_ctx.take();
                    let prev_tail_position = context.tail_position;
                    let prev_tail_cleanups = std::mem::take(&mut context.tail_cleanups);
                    context.tail_ctx = Some(TailContext {
                        function_name: tail_function_name,
                        param_slots,
                        loop_header,
                    });
                    context.tail_position = true;

                    let compile_result =
                        context.compile_ast(new_scope, &mut stack, body, module_path.clone());

                    context.tail_ctx = prev_tail_ctx;
                    context.tail_position = prev_tail_position;
                    context.tail_cleanups = prev_tail_cleanups;
                    compile_result?;

                    // The body may have ended on a back-edge (e.g. an infinite tail
                    // loop), terminating the current block; only emit a return when
                    // the path actually falls through to one.
                    if context.current_block_terminated() {
                        if let Some(block) = current_block {
                            context.builder.position_at_end(block);
                        }
                        return Ok(());
                    }

                    match function_type.get_return_type() {
                        Some(BasicTypeEnum::StructType(return_type)) => {
                            let return_val = stack.remove_all();
                            let mut struct_val = return_type.get_undef().as_aggregate_value_enum();
                            for (index, value) in return_val.into_iter().enumerate() {
                                struct_val = context.builder.build_insert_value(
                                    struct_val,
                                    value.1,
                                    index as u32,
                                    &format!("ret_{}", index),
                                )?;
                            }
                            context
                                .builder
                                .build_return(Some(&struct_val.as_basic_value_enum()))?;
                        }
                        Some(return_type) => {
                            let return_val = stack.remove_all();
                            if return_val.len() != 1 {
                                return Err(CompilerError::InvalidStackForFunction(
                                    symbol_name.to_string(),
                                ));
                            }
                            let return_val = return_val[0].clone().1;

                            if return_val.get_type() != return_type {
                                return Err(CompilerError::InvalidStackForFunction(
                                    symbol_name.to_string(),
                                ));
                            }
                            context.builder.build_return(Some(&return_val))?;
                        }
                        None => {
                            if !stack.is_empty() {
                                return Err(CompilerError::InvalidStackForFunction(
                                    symbol_name.clone(),
                                ));
                            }
                            context.builder.build_return(None)?;
                        }
                    }

                    if let Some(block) = current_block {
                        context.builder.position_at_end(block);
                    }

                    Ok(())
                },
            ),
        );

        Ok(())
    }

    fn get_llvm_function_type(
        &self,
        type_def: &Type,
    ) -> Result<inkwell::types::FunctionType<'ctx>, CompilerError> {
        let mut param_types = Vec::new();

        for pop_type in &type_def.pop_types {
            param_types.push(BasicMetadataTypeEnum::from(
                self.unit_type_to_llvm_type(pop_type)?,
            ));
        }

        if type_def.push_types.is_empty() {
            return Ok(self.context.void_type().fn_type(&param_types, false));
        }
        Ok(self.get_return_type(type_def)?.fn_type(&param_types, false))
    }

    fn get_return_type(&self, type_def: &Type) -> Result<BasicTypeEnum<'ctx>, CompilerError> {
        if type_def.push_types.len() == 1 {
            return self.unit_type_to_llvm_type(&type_def.push_types[0]);
        }

        let mut return_types = Vec::new();
        for push_type in &type_def.push_types {
            return_types.push(self.unit_type_to_llvm_type(push_type)?);
        }
        Ok(self
            .context
            .struct_type(&return_types, true)
            .as_basic_type_enum())
    }

    fn unit_type_to_llvm_type(
        &self,
        unit_type: &UnitType,
    ) -> Result<BasicTypeEnum<'ctx>, CompilerError> {
        match unit_type {
            UnitType::Literal(lit_type) => match lit_type {
                LiteralType::Number(num_type) => match num_type {
                    NumberType::U8 | NumberType::I8 => Ok(self.context.i8_type().into()),
                    NumberType::U16 | NumberType::I16 => Ok(self.context.i16_type().into()),
                    NumberType::U32 | NumberType::I32 => Ok(self.context.i32_type().into()),
                    NumberType::U64 | NumberType::I64 => Ok(self.context.i64_type().into()),
                    NumberType::U128 | NumberType::I128 => Ok(self.context.i128_type().into()),
                    NumberType::F64 => Ok(self.context.f64_type().into()),
                },
                LiteralType::Char => Ok(self.context.i32_type().into()),
                // Raw C pointers (`char*` / `void*`) cross FFI as opaque pointers.
                LiteralType::CStr | LiteralType::Ptr => {
                    Ok(self.context.ptr_type(AddressSpace::default()).into())
                }
            },
            // An unconstrained generic that survived monomorphization (e.g. the
            // value type of an empty `Map<I64, v>` that is never populated). No
            // concrete value of this type is ever produced, so the code handling
            // it is dead — we only need a consistent, valid lowering. Use an
            // opaque pointer, the same representation as boxed/`Custom` values.
            UnitType::Var(_) => Ok(self.context.ptr_type(AddressSpace::default()).into()),
            // A function value is an opaque code pointer.
            UnitType::Type(_) => Ok(self.context.ptr_type(AddressSpace::default()).into()),
            UnitType::Custom { .. } => Ok(self.context.ptr_type(AddressSpace::default()).into()),
        }
    }

    pub fn build_global_string(
        &mut self,
        string: String,
    ) -> Result<PointerValue<'ctx>, CompilerError> {
        match self.global_strings.get(&string) {
            Some(value) => Ok(*value),
            None => {
                let value = self.builder.build_global_string_ptr(&string, "str")?;
                let pointer = value.as_pointer_value();
                self.global_strings.insert(string, pointer);
                Ok(pointer)
            }
        }
    }

    /// Writes a Unicode scalar (`cp`, an i32 code point) to stdout as UTF-8,
    /// emitting 1–4 bytes via `putchar`. This is the one string-output primitive;
    /// the stdlib walks a `List<Char>` calling `char::print` for each element.
    pub fn emit_print_char(
        &self,
        cp: inkwell::values::IntValue<'ctx>,
    ) -> Result<(), CompilerError> {
        self.emit_print_char_with(cp, "putchar")
    }

    /// As [`emit_print_char`], but emits each UTF-8 byte through the named libc
    /// per-byte writer (`putchar` for stdout, `clem_putchar_err` for stderr).
    /// Both have signature `i32 (i32)`.
    pub fn emit_print_char_with(
        &self,
        cp: inkwell::values::IntValue<'ctx>,
        put_function: &str,
    ) -> Result<(), CompilerError> {
        let i32_type = self.context.i32_type();
        let putchar = self
            .module
            .get_function(put_function)
            .ok_or_else(|| CompilerError::GetFunctionError(put_function.into()))?;
        let function = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?
            .get_parent()
            .ok_or(CompilerError::IfWithoutFunction)?;

        let one = self.context.append_basic_block(function, "utf8_1");
        let multi = self.context.append_basic_block(function, "utf8_multi");
        let two = self.context.append_basic_block(function, "utf8_2");
        let three_plus = self.context.append_basic_block(function, "utf8_3p");
        let three = self.context.append_basic_block(function, "utf8_3");
        let four = self.context.append_basic_block(function, "utf8_4");
        let done = self.context.append_basic_block(function, "utf8_done");

        let c = |v: u64| i32_type.const_int(v, false);
        // `cp >> shift` (logical) then `low6 | mask`, producing a continuation/lead byte.
        let shifted =
            |cp: inkwell::values::IntValue<'ctx>, shift: u64| -> Result<_, CompilerError> {
                Ok(self.builder.build_right_shift(cp, c(shift), false, "sh")?)
            };
        let put = |byte: inkwell::values::IntValue<'ctx>| -> Result<(), CompilerError> {
            self.builder
                .build_call(putchar, &[byte.into()], "putchar")?;
            Ok(())
        };
        let or = |a, b, name| self.builder.build_or(a, b, name);
        let and = |a, b, name| self.builder.build_and(a, b, name);

        // cp < 0x80 ?
        let lt_80 =
            self.builder
                .build_int_compare(inkwell::IntPredicate::ULT, cp, c(0x80), "lt80")?;
        self.builder.build_conditional_branch(lt_80, one, multi)?;

        // 1-byte: the code point itself.
        self.builder.position_at_end(one);
        put(cp)?;
        self.builder.build_unconditional_branch(done)?;

        self.builder.position_at_end(multi);
        let lt_800 =
            self.builder
                .build_int_compare(inkwell::IntPredicate::ULT, cp, c(0x800), "lt800")?;
        self.builder
            .build_conditional_branch(lt_800, two, three_plus)?;

        // 2-byte: 110xxxxx 10xxxxxx
        self.builder.position_at_end(two);
        put(or(c(0xC0), shifted(cp, 6)?, "b0")?)?;
        put(or(c(0x80), and(cp, c(0x3F), "lo")?, "b1")?)?;
        self.builder.build_unconditional_branch(done)?;

        self.builder.position_at_end(three_plus);
        let lt_10000 = self.builder.build_int_compare(
            inkwell::IntPredicate::ULT,
            cp,
            c(0x10000),
            "lt10000",
        )?;
        self.builder
            .build_conditional_branch(lt_10000, three, four)?;

        // 3-byte: 1110xxxx 10xxxxxx 10xxxxxx
        self.builder.position_at_end(three);
        put(or(c(0xE0), shifted(cp, 12)?, "b0")?)?;
        put(or(c(0x80), and(shifted(cp, 6)?, c(0x3F), "m")?, "b1")?)?;
        put(or(c(0x80), and(cp, c(0x3F), "lo")?, "b2")?)?;
        self.builder.build_unconditional_branch(done)?;

        // 4-byte: 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
        self.builder.position_at_end(four);
        put(or(c(0xF0), shifted(cp, 18)?, "b0")?)?;
        put(or(c(0x80), and(shifted(cp, 12)?, c(0x3F), "m1")?, "b1")?)?;
        put(or(c(0x80), and(shifted(cp, 6)?, c(0x3F), "m2")?, "b2")?)?;
        put(or(c(0x80), and(cp, c(0x3F), "lo")?, "b3")?)?;
        self.builder.build_unconditional_branch(done)?;

        self.builder.position_at_end(done);
        Ok(())
    }

    /// Compiles a custom-type `match` as a decision tree over the pattern matrix
    /// (Maranget-style). `value_columns` are the values currently being matched;
    /// each row carries the remaining column patterns, the leaf bindings gathered
    /// so far, and the body. The builder is positioned at this node's entry block;
    /// every emitted leaf branches to `merge_block` (recording its pushed values
    /// for the phi) and any unmatched value falls through to `default_block`.
    // The arguments thread the decision-tree state through recursion; bundling
    // them into a struct would obscure more than it clarifies.
    #[allow(clippy::too_many_arguments)]
    fn compile_rows(
        &mut self,
        scope: &Scope<'ctx>,
        value_columns: &[(UnitType, BasicValueEnum<'ctx>)],
        rows: Vec<MatchRow<'ctx>>,
        stack: &Stack<'ctx>,
        module_path: &[String],
        merge_block: inkwell::basic_block::BasicBlock<'ctx>,
        default_block: inkwell::basic_block::BasicBlock<'ctx>,
        values_and_blocks: &mut Vec<(
            Vec<(UnitType, BasicValueEnum<'ctx>)>,
            inkwell::basic_block::BasicBlock<'ctx>,
        )>,
        // Tail position of the enclosing match: leaf arm bodies inherit it so a
        // self-tail-call inside an arm lowers to a loop back-edge.
        outer_tail: bool,
    ) -> Result<(), CompilerError> {
        let Some(first) = rows.first() else {
            // No row can match here: fall through.
            self.builder.build_unconditional_branch(default_block)?;
            return Ok(());
        };

        // If the highest-priority row has no constructor left to test, it matches:
        // bind its columns + accumulated bindings and compile its body (a leaf).
        let Some(col) = first
            .patterns
            .iter()
            .position(|p| !matches!(p, Pattern::Wildcard(_)))
        else {
            let scope = scope.clone();
            for (i, pattern) in first.patterns.iter().enumerate() {
                if let Pattern::Wildcard(Some(name)) = pattern {
                    let (ty, value) = &value_columns[i];
                    scope.add_value(
                        name.clone(),
                        (ty.clone(), self.clone_value(ty.clone(), *value)?),
                    );
                }
            }
            for (name, (ty, value)) in &first.bindings {
                scope.add_value(
                    name.clone(),
                    (ty.clone(), self.clone_value(ty.clone(), *value)?),
                );
            }
            let n_push_types = first.body.type_definition.push_types.len();
            let mut temp_stack = stack.clone();
            self.tail_position = outer_tail;
            self.compile_ast(
                scope,
                &mut temp_stack,
                first.body.clone(),
                module_path.to_vec(),
            )?;
            // Skip the merge edge if a tail-call already terminated this arm with a
            // back-edge to the loop header.
            if !self.current_block_terminated() {
                self.builder.build_unconditional_branch(merge_block)?;
                let bb = self
                    .builder
                    .get_insert_block()
                    .ok_or(CompilerError::IfWithoutFunction)?;
                values_and_blocks.push((temp_stack.pop_n(n_push_types), bb));
            }
            return Ok(());
        };

        // Scalar literal (Char/Number) column: discriminate by value (int switch).
        if matches!(first.patterns[col], Pattern::Char(_) | Pattern::Number(_)) {
            return self.compile_literal_rows(
                scope,
                value_columns,
                rows,
                col,
                stack,
                module_path,
                merge_block,
                default_block,
                values_and_blocks,
                outer_tail,
            );
        }

        // Discriminate on column `col` (a custom-typed value).
        let (col_ty, col_value) = value_columns[col].clone();
        let UnitType::Custom {
            name,
            generic_types,
        } = &col_ty
        else {
            return Err(CompilerError::UnsupportedPattern);
        };
        let custom_type = self
            .get_type(name.clone())
            .ok_or(CompilerError::TypeNotInScope)?;
        let generics_map = custom_type
            .generics
            .iter()
            .map(|generic| generic.1.clone())
            .zip(generic_types.iter().cloned())
            .collect::<HashMap<_, _>>();

        // Constructors explicitly tested in this column, in first-appearance order.
        let mut constructors: Vec<String> = Vec::new();
        for row in &rows {
            if let Pattern::Variant { variant_name, .. } = &row.patterns[col]
                && let Some(c) = variant_name.last()
                && !constructors.contains(c)
            {
                constructors.push(c.clone());
            }
        }

        let current_function = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?
            .get_parent()
            .ok_or(CompilerError::IfWithoutFunction)?;
        let switch_default = self
            .context
            .append_basic_block(current_function, "match_default");

        let base = self.base_custom_type();
        let match_ptr = col_value.into_pointer_value();
        let disc_ptr = self
            .builder
            .build_struct_gep(base, match_ptr, 1, "variant")?;
        let discriminant = self
            .builder
            .build_load(self.context.i8_type(), disc_ptr, "variant_load")?
            .into_int_value();

        let mut switch_arms = Vec::new();
        for c in &constructors {
            let index = custom_type
                .variants
                .iter()
                .position(|v| &v.0 == c)
                .ok_or_else(|| CompilerError::VariantNotFound(c.clone()))?;
            let block = self
                .context
                .append_basic_block(current_function, &format!("case_{}", c));
            switch_arms.push((index, c.clone(), block));
        }
        self.builder.build_switch(
            discriminant,
            switch_default,
            &switch_arms
                .iter()
                .map(|(index, _, block)| {
                    (
                        self.context.i8_type().const_int(*index as u64, false),
                        *block,
                    )
                })
                .collect::<Vec<_>>(),
        )?;

        // Each tested constructor: destructure its fields and recurse with the
        // column replaced by the variant's field columns.
        for (_, c, block) in &switch_arms {
            self.builder.position_at_end(*block);
            let variant = custom_type
                .variants
                .iter()
                .find(|v| &v.0 == c)
                .expect("constructor exists")
                .clone();
            let payload_ptr = self
                .builder
                .build_struct_gep(base, match_ptr, 2, "payload_ptr")?;
            let variant_struct =
                custom_type_variant_struct(variant.clone(), generics_map.clone(), self)?;

            let mut field_values = Vec::new();
            for (field_index, (_, field_ty)) in variant.1.iter().enumerate() {
                let resolved_ty = substitute_unit(field_ty, &generics_map);
                let field_ptr = self.builder.build_struct_gep(
                    variant_struct,
                    payload_ptr,
                    field_index as u32,
                    "field_ptr",
                )?;
                let field_value = self.builder.build_load(
                    variant_struct
                        .get_field_type_at_index(field_index as u32)
                        .expect("field exists"),
                    field_ptr,
                    "field_value",
                )?;
                field_values.push((resolved_ty, field_value));
            }

            let specialized = specialize_rows(&rows, col, c, &variant, &col_ty, col_value);
            let mut new_columns = value_columns.to_vec();
            let tail = new_columns.split_off(col + 1);
            new_columns.pop();
            new_columns.extend(field_values);
            new_columns.extend(tail);

            self.compile_rows(
                scope,
                &new_columns,
                specialized,
                stack,
                module_path,
                merge_block,
                switch_default,
                values_and_blocks,
                outer_tail,
            )?;
        }

        // The default: rows whose column `col` is a wildcard match any remaining
        // constructor (binding the whole value if named).
        self.builder.position_at_end(switch_default);
        let defaulted = default_rows(&rows, col, &col_ty, col_value);
        let mut default_columns = value_columns.to_vec();
        default_columns.remove(col);
        self.compile_rows(
            scope,
            &default_columns,
            defaulted,
            stack,
            module_path,
            merge_block,
            default_block,
            values_and_blocks,
            outer_tail,
        )
    }

    /// Like `compile_rows`, but for a column holding a scalar literal (`Char` or
    /// number): discriminates the value with an integer `switch` (one block per
    /// distinct literal, default for wildcard rows). Literal columns have no
    /// sub-fields, so matching just drops the column (binding the value for a
    /// wildcard row).
    #[allow(clippy::too_many_arguments)]
    fn compile_literal_rows(
        &mut self,
        scope: &Scope<'ctx>,
        value_columns: &[(UnitType, BasicValueEnum<'ctx>)],
        rows: Vec<MatchRow<'ctx>>,
        col: usize,
        stack: &Stack<'ctx>,
        module_path: &[String],
        merge_block: inkwell::basic_block::BasicBlock<'ctx>,
        default_block: inkwell::basic_block::BasicBlock<'ctx>,
        values_and_blocks: &mut Vec<(
            Vec<(UnitType, BasicValueEnum<'ctx>)>,
            inkwell::basic_block::BasicBlock<'ctx>,
        )>,
        outer_tail: bool,
    ) -> Result<(), CompilerError> {
        let (col_ty, col_value) = value_columns[col].clone();
        let scrutinee = col_value.into_int_value();

        // Drops column `col`; for a wildcard pattern, records its binding.
        let without_col = |row: &MatchRow<'ctx>, bind_value: bool| -> MatchRow<'ctx> {
            let mut patterns = row.patterns.clone();
            let removed = patterns.remove(col);
            let mut bindings = row.bindings.clone();
            if bind_value && let Pattern::Wildcard(Some(name)) = removed {
                bindings.push((name, (col_ty.clone(), col_value)));
            }
            MatchRow {
                patterns,
                bindings,
                body: row.body.clone(),
            }
        };

        // Distinct literal values tested in this column (first-appearance order).
        let mut literals: Vec<u64> = Vec::new();
        for row in &rows {
            if let Some(k) = literal_key(&row.patterns[col])
                && !literals.contains(&k)
            {
                literals.push(k);
            }
        }

        let function = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?
            .get_parent()
            .ok_or(CompilerError::IfWithoutFunction)?;
        let switch_default = self.context.append_basic_block(function, "lit_default");

        let mut arms = Vec::new();
        for &lit in &literals {
            let block = self.context.append_basic_block(function, "lit_case");
            arms.push((scrutinee.get_type().const_int(lit, false), block, lit));
        }
        self.builder.build_switch(
            scrutinee,
            switch_default,
            &arms.iter().map(|(c, b, _)| (*c, *b)).collect::<Vec<_>>(),
        )?;

        for (_, block, lit) in &arms {
            self.builder.position_at_end(*block);
            // Rows matching this literal (drop col, no binding) or wildcards
            // (drop col, bind the value).
            let specialized: Vec<MatchRow<'ctx>> = rows
                .iter()
                .filter_map(|row| match &row.patterns[col] {
                    Pattern::Wildcard(_) => Some(without_col(row, true)),
                    p if literal_key(p) == Some(*lit) => Some(without_col(row, false)),
                    _ => None,
                })
                .collect();
            let mut columns = value_columns.to_vec();
            columns.remove(col);
            self.compile_rows(
                scope,
                &columns,
                specialized,
                stack,
                module_path,
                merge_block,
                switch_default,
                values_and_blocks,
                outer_tail,
            )?;
        }

        self.builder.position_at_end(switch_default);
        let defaulted: Vec<MatchRow<'ctx>> = rows
            .iter()
            .filter(|row| matches!(row.patterns[col], Pattern::Wildcard(_)))
            .map(|row| without_col(row, true))
            .collect();
        let mut columns = value_columns.to_vec();
        columns.remove(col);
        self.compile_rows(
            scope,
            &columns,
            defaulted,
            stack,
            module_path,
            merge_block,
            default_block,
            values_and_blocks,
            outer_tail,
        )
    }

    fn compile_match(
        &mut self,
        scope: Scope<'ctx>,
        cases: Vec<crate::parser::Case<AstNodeWithType>>,
        stack: &mut Stack<'ctx>,
        module_path: Vec<String>,
        match_type: Type,
    ) -> Result<(), CompilerError> {
        let Some(match_value) = stack.pop() else {
            return Err(CompilerError::StackUnderflow);
        };
        // If the whole match is in tail position, so is every arm body (each arm's
        // last word is the function's result). Stash that intent and clear the live
        // flag so the discriminant/switch scaffolding below never trips it; we
        // re-arm it right before compiling each arm body.
        let outer_tail = self.tail_position;
        self.tail_position = false;
        let current_function = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?
            .get_parent()
            .ok_or(CompilerError::IfWithoutFunction)?;
        let merge_block = self.context.append_basic_block(current_function, "merge");
        match match_value.0.clone() {
            UnitType::Literal(LiteralType::Number(_)) => {
                let mut case_blocks = Vec::new();
                let mut values_and_blocks = Vec::new();
                for (index, _) in cases.iter().enumerate() {
                    case_blocks.push(
                        self.context
                            .append_basic_block(current_function, &format!("case_{}", index)),
                    );
                }
                let switch_cases = cases
                    .iter()
                    .map(|case| match &case.pattern {
                        Pattern::Number(n) => {
                            Ok(self.number_to_llvm_number(n.clone()).1.into_int_value())
                        }
                        _ => Err(CompilerError::UnsupportedPattern),
                    })
                    .zip(case_blocks[0..case_blocks.len() - 1].iter().cloned())
                    .map(|(value, block)| Ok((value?, block)))
                    .collect::<Result<Vec<_>, CompilerError>>()?;
                self.builder.build_switch(
                    match_value.1.into_int_value(),
                    case_blocks[case_blocks.len() - 1],
                    switch_cases.as_slice(),
                )?;
                for (index, case) in cases.into_iter().enumerate() {
                    let mut temp_stack = stack.clone();
                    match case.pattern {
                        Pattern::Number(_) => {
                            self.builder.position_at_end(case_blocks[index]);
                            let n_push_types = case.body.type_definition.push_types.len();
                            self.tail_position = outer_tail;
                            self.compile_ast(
                                scope.clone(),
                                &mut temp_stack,
                                *case.body,
                                module_path.clone(),
                            )?;
                            // Skip the merge edge if a tail-call already terminated
                            // this arm with a back-edge to the loop header.
                            if !self.current_block_terminated() {
                                self.builder.build_unconditional_branch(merge_block)?;
                                let bb = self
                                    .builder
                                    .get_insert_block()
                                    .ok_or(CompilerError::IfWithoutFunction)?;
                                values_and_blocks.push((temp_stack.pop_n(n_push_types), bb));
                            }
                        }
                        Pattern::Wildcard(name) => {
                            self.builder.position_at_end(case_blocks[index]);
                            let n_push_types = case.body.type_definition.push_types.len();
                            let scope = scope.clone();
                            if let Some(name) = name {
                                scope.add_value(name, match_value.clone());
                            }
                            self.tail_position = outer_tail;
                            self.compile_ast(
                                scope,
                                &mut temp_stack,
                                *case.body,
                                module_path.clone(),
                            )?;
                            if !self.current_block_terminated() {
                                self.builder.build_unconditional_branch(merge_block)?;
                                let bb = self
                                    .builder
                                    .get_insert_block()
                                    .ok_or(CompilerError::IfWithoutFunction)?;
                                values_and_blocks.push((temp_stack.pop_n(n_push_types), bb));
                            }
                        }
                        _ => return Err(CompilerError::UnsupportedPattern),
                    }
                }
                stack.pop_n(match_type.pop_types.len());
                self.builder.position_at_end(merge_block);
                // INVARIANT: every arm pushes the same number of values, each of
                // the same LLVM type, in the same order. This is guaranteed by the
                // type checker (TypeCheckerError::InvalidMatchBody rejects arms whose
                // stack effect differs), so building one phi per position is sound.
                // If that check is ever weakened, mismatched arms would silently
                // produce malformed IR here rather than a clean compiler error.
                let mut values_for_phi = Vec::new();
                for (values, block) in values_and_blocks.iter() {
                    for (index, value) in values.iter().enumerate() {
                        if values_for_phi.get(index).is_none() {
                            values_for_phi
                                .push(((value.0.clone(), value.1.get_type()), Vec::new()));
                        }
                        values_for_phi[index]
                            .1
                            .push((&value.1 as &dyn BasicValue, *block));
                    }
                }
                for (ty, values) in values_for_phi.into_iter() {
                    let phi = self.builder.build_phi(ty.1, "phi")?;
                    phi.add_incoming(values.as_slice());
                    stack.push((ty.0, phi.as_basic_value()));
                }
                Ok(())
            }
            UnitType::Custom { .. } => {
                let rows: Vec<MatchRow<'ctx>> = cases
                    .into_iter()
                    .map(|case| MatchRow {
                        patterns: vec![case.pattern],
                        bindings: Vec::new(),
                        body: *case.body,
                    })
                    .collect();

                // The match is exhaustive (type checker guarantees it), so the
                // final fall-through is unreachable.
                let default_block = self
                    .context
                    .append_basic_block(current_function, "match_unreachable");
                let mut values_and_blocks = Vec::new();
                // For tail-positioned arms, the back-edge bypasses the merge drop
                // below, so register the scrutinee as a deferred cleanup it replays.
                // (A non-tail match never back-edges, so skip the bookkeeping.)
                if outer_tail {
                    self.tail_cleanups
                        .push((match_value.0.clone(), match_value.1));
                }
                self.compile_rows(
                    &scope,
                    std::slice::from_ref(&match_value),
                    rows,
                    stack,
                    &module_path,
                    merge_block,
                    default_block,
                    &mut values_and_blocks,
                    outer_tail,
                )?;
                if outer_tail {
                    self.tail_cleanups.pop();
                }
                self.builder.position_at_end(default_block);
                self.builder.build_unreachable()?;

                stack.pop_n(match_type.pop_types.len() - 1);
                self.builder.position_at_end(merge_block);
                // INVARIANT: every arm pushes the same number of values, each of the
                // same LLVM type, in the same order (guaranteed by the type checker
                // via InvalidMatchBody), so one phi per position is sound.
                let mut values_for_phi = Vec::new();
                for (values, block) in values_and_blocks.iter() {
                    for (index, value) in values.iter().enumerate() {
                        if values_for_phi.get(index).is_none() {
                            values_for_phi
                                .push(((value.0.clone(), value.1.get_type()), Vec::new()));
                        }
                        values_for_phi[index]
                            .1
                            .push((&value.1 as &dyn BasicValue, *block));
                    }
                }
                for (ty, values) in values_for_phi.into_iter() {
                    let phi = self.builder.build_phi(ty.1, "phi")?;
                    phi.add_incoming(values.as_slice());
                    stack.push((ty.0, phi.as_basic_value()));
                }
                // Release the scrutinee NODE ONLY — never its payload fields. Arm
                // patterns bind fields as borrowed aliases into this payload (no
                // retain; see the field load in `compile_rows`), and an arm may let a
                // bound field escape into the match's result — e.g. `result::map`'s
                // `Err(error) -> { error ... Err }` re-wraps the inner error into a
                // fresh node. A deep `drop_value` here would free that still-referenced
                // field out from under the result, a use-after-free. Freeing just the
                // node is the same trade-off the self-tail-call back-edge already makes
                // (see `build_rc_release_node_only`): a bound field that is genuinely
                // dead leaks rather than risking a double-free.
                self.build_rc_release_node_only(match_value.0, match_value.1)?;
                Ok(())
            }
            other => Err(CompilerError::UnsupportedType(other)),
        }
    }

    pub fn get_type(&self, name: Vec<String>) -> Option<CustomType> {
        self.type_definitions.get(&name).cloned()
    }

    /// Layout of every heap-allocated custom-type value (packed):
    /// `{ i64 refcount, i8 variant_tag, payload }`. The variant tag is an `i8`
    /// (≤256 variants), saving 7 bytes per object versus an `i64`.
    pub fn base_custom_type(&self) -> StructType<'ctx> {
        let fields = vec![
            self.context.i64_type().into(),
            self.context.i8_type().into(),
            self.context.i8_type().array_type(0).into(),
        ];
        self.context.struct_type(&fields, true)
    }

    /// Builds a `List<Char>` (a `String`) value from a NUL-terminated ASCII C
    /// buffer at runtime, by walking it back-to-front and consing each byte.
    /// Used by the native `f64::to_string` (which formats via `sprintf`).
    pub fn emit_string_from_cstr(
        &self,
        buffer: PointerValue<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        let list = self
            .get_type(vec!["std".into(), "list".into(), "List".into()])
            .ok_or(CompilerError::TypeNotInScope)?;
        let mut generics_map = HashMap::new();
        if let Some((_, var)) = list.generics.first() {
            generics_map.insert(var.clone(), UnitType::Literal(LiteralType::Char));
        }
        let empty_index = list
            .variants
            .iter()
            .position(|v| v.0 == "Empty")
            .ok_or_else(|| CompilerError::VariantNotFound("Empty".into()))?;
        let list_index = list
            .variants
            .iter()
            .position(|v| v.0 == "List")
            .ok_or_else(|| CompilerError::VariantNotFound("List".into()))?;
        let empty_variant = list.variants[empty_index].clone();
        let list_variant = list.variants[list_index].clone();

        let base = self.base_custom_type();
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();
        let i8_type = self.context.i8_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());

        let empty_struct = custom_type_variant_struct(empty_variant, generics_map.clone(), self)?;
        let list_struct = custom_type_variant_struct(list_variant, generics_map.clone(), self)?;
        let base_size = base.size_of().expect("sized");

        let build_empty = || -> Result<PointerValue<'ctx>, CompilerError> {
            let total = self.builder.build_int_add(
                base_size,
                empty_struct.size_of().expect("sized"),
                "sz",
            )?;
            let p = self.build_pool_alloc(total)?;
            self.builder.build_store(
                self.builder.build_struct_gep(base, p, 0, "rc")?,
                i64_type.const_int(1, false),
            )?;
            self.builder.build_store(
                self.builder.build_struct_gep(base, p, 1, "variant")?,
                i8_type.const_int(empty_index as u64, false),
            )?;
            Ok(p)
        };
        let build_cons = |next: PointerValue<'ctx>,
                          element: inkwell::values::IntValue<'ctx>|
         -> Result<PointerValue<'ctx>, CompilerError> {
            let total = self.builder.build_int_add(
                base_size,
                list_struct.size_of().expect("sized"),
                "sz",
            )?;
            let p = self.build_pool_alloc(total)?;
            self.builder.build_store(
                self.builder.build_struct_gep(base, p, 0, "rc")?,
                i64_type.const_int(1, false),
            )?;
            self.builder.build_store(
                self.builder.build_struct_gep(base, p, 1, "variant")?,
                i8_type.const_int(list_index as u64, false),
            )?;
            let payload = self.builder.build_struct_gep(base, p, 2, "payload")?;
            // Field order matches the variant declaration `List(next, element)`.
            self.builder.build_store(
                self.builder
                    .build_struct_gep(list_struct, payload, 0, "next")?,
                next,
            )?;
            self.builder.build_store(
                self.builder
                    .build_struct_gep(list_struct, payload, 1, "element")?,
                element,
            )?;
            Ok(p)
        };

        let strlen = self
            .module
            .get_function("strlen")
            .ok_or(CompilerError::GetFunctionError("strlen".into()))?;
        let len = self
            .builder
            .build_call(strlen, &[buffer.into()], "len")?
            .try_as_basic_value()
            .left()
            .ok_or(CompilerError::FunctionCallError)?
            .into_int_value();
        let acc0 = build_empty()?;

        let function = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?
            .get_parent()
            .ok_or(CompilerError::IfWithoutFunction)?;
        let entry = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?;
        let cond = self.context.append_basic_block(function, "decode_cond");
        let body = self.context.append_basic_block(function, "decode_body");
        let done = self.context.append_basic_block(function, "decode_done");
        self.builder.build_unconditional_branch(cond)?;

        self.builder.position_at_end(cond);
        let i_phi = self.builder.build_phi(i64_type, "i")?;
        let acc_phi = self.builder.build_phi(ptr_type, "acc")?;
        i_phi.add_incoming(&[(&len as &dyn BasicValue, entry)]);
        acc_phi.add_incoming(&[(&acc0 as &dyn BasicValue, entry)]);
        let i_val = i_phi.as_basic_value().into_int_value();
        let acc_val = acc_phi.as_basic_value().into_pointer_value();
        let positive = self.builder.build_int_compare(
            inkwell::IntPredicate::UGT,
            i_val,
            i64_type.const_zero(),
            "pos",
        )?;
        self.builder
            .build_conditional_branch(positive, body, done)?;

        self.builder.position_at_end(body);
        let idx = self
            .builder
            .build_int_sub(i_val, i64_type.const_int(1, false), "idx")?;
        let char_ptr = unsafe {
            self.builder
                .build_gep(i8_type, buffer, &[idx], "char_ptr")?
        };
        let byte = self
            .builder
            .build_load(i8_type, char_ptr, "byte")?
            .into_int_value();
        let code_point = self
            .builder
            .build_int_z_extend(byte, i32_type, "code_point")?;
        let new_acc = build_cons(acc_val, code_point)?;
        let body_end = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?;
        i_phi.add_incoming(&[(&idx as &dyn BasicValue, body_end)]);
        acc_phi.add_incoming(&[(&new_acc as &dyn BasicValue, body_end)]);
        self.builder.build_unconditional_branch(cond)?;

        self.builder.position_at_end(done);
        Ok(acc_val.as_basic_value_enum())
    }
}

/// Deeply replaces every `Var` in `ty` using `generics_map`, recursing into the
/// generic arguments of `Custom` types and nested function `Type`s. Needed so a
/// nested field type like `List<a>` resolves to `List<I64>` (not `List<Var>`)
/// before codegen, which cannot lower a bare type variable.
/// Whether a stack-effect type still mentions a type variable — i.e. it was not
/// fully concretized by resolution/monomorphization. A function value with such
/// a type can't be lowered to a concrete LLVM function.
fn type_contains_var(ty: &Type) -> bool {
    fn unit_contains_var(unit: &UnitType) -> bool {
        match unit {
            UnitType::Var(_) => true,
            UnitType::Custom { generic_types, .. } => generic_types.iter().any(unit_contains_var),
            UnitType::Type(inner) => type_contains_var(inner),
            UnitType::Literal(_) => false,
        }
    }
    ty.pop_types.iter().any(unit_contains_var) || ty.push_types.iter().any(unit_contains_var)
}

fn substitute_unit(ty: &UnitType, generics_map: &HashMap<VarType, UnitType>) -> UnitType {
    match ty {
        UnitType::Var(var) => generics_map.get(var).cloned().unwrap_or_else(|| ty.clone()),
        UnitType::Custom {
            name,
            generic_types,
        } => UnitType::Custom {
            name: name.clone(),
            generic_types: generic_types
                .iter()
                .map(|t| substitute_unit(t, generics_map))
                .collect(),
        },
        UnitType::Type(inner) => UnitType::Type(Type::new(
            inner
                .pop_types
                .iter()
                .map(|t| substitute_unit(t, generics_map))
                .collect(),
            inner
                .push_types
                .iter()
                .map(|t| substitute_unit(t, generics_map))
                .collect(),
        )),
        UnitType::Literal(_) => ty.clone(),
    }
}

/// Builds the `type-var -> concrete` map by structurally matching a generic
/// `template` type against the `concrete` type requested for a monomorphic
/// instance. One-directional (every variable lives in `template`), recursing
/// through `Custom` generics and nested function types.
fn bind_generics(template: &UnitType, concrete: &UnitType, map: &mut HashMap<VarType, UnitType>) {
    match (template, concrete) {
        (UnitType::Var(var), concrete) => {
            map.insert(var.clone(), concrete.clone());
        }
        (
            UnitType::Custom {
                generic_types: t, ..
            },
            UnitType::Custom {
                generic_types: c, ..
            },
        ) => {
            for (t, c) in t.iter().zip(c.iter()) {
                bind_generics(t, c, map);
            }
        }
        (UnitType::Type(t), UnitType::Type(c)) => {
            for (t, c) in t.pop_types.iter().zip(c.pop_types.iter()) {
                bind_generics(t, c, map);
            }
            for (t, c) in t.push_types.iter().zip(c.push_types.iter()) {
                bind_generics(t, c, map);
            }
        }
        _ => {}
    }
}

/// Resolves a call's signature to the concrete monomorphic instance to invoke,
/// using the actual types of the arguments on the stack rather than the node's
/// annotated type. The type checker may leave free type variables in a call
/// node's type (each call site is instantiated with fresh variables), but at
/// codegen the operands on the stack are concrete — so binding the signature's
/// pop types against them yields the concrete instance. Without this, a generic
/// recursive call (e.g. `fold` calling itself) would dispatch to an
/// un-monomorphized generic instance.
fn concretize_call_type(node_ty: &Type, stack: &Stack) -> Type {
    let args = stack.top_n(node_ty.pop_types.len());
    let mut map = HashMap::new();
    for (template, (concrete, _)) in node_ty.pop_types.iter().zip(args) {
        bind_generics(template, concrete, &mut map);
    }
    if map.is_empty() {
        return node_ty.clone();
    }
    Type::with_effects(
        node_ty
            .pop_types
            .iter()
            .map(|t| substitute_unit(t, &map))
            .collect(),
        node_ty
            .push_types
            .iter()
            .map(|t| substitute_unit(t, &map))
            .collect(),
        node_ty.effects.clone(),
    )
}

/// Rewrites every `type_definition` in an AST subtree with `map`, used to
/// concretize a generic definition's body for a monomorphic instance. Reuses
/// [`substitute_unit`], which recurses through function and custom types.
fn substitute_ast_types(node: &mut AstNodeWithType, map: &HashMap<VarType, UnitType>) {
    node.type_definition = Type::new(
        node.type_definition
            .pop_types
            .iter()
            .map(|t| substitute_unit(t, map))
            .collect(),
        node.type_definition
            .push_types
            .iter()
            .map(|t| substitute_unit(t, map))
            .collect(),
    );
    match &mut node.node_type {
        AstNodeType::Block(nodes) | AstNodeType::Quotation(nodes) => {
            for n in nodes {
                substitute_ast_types(n, map);
            }
        }
        AstNodeType::Match(cases) => {
            for case in cases {
                substitute_ast_types(&mut case.body, map);
            }
        }
        AstNodeType::Definition { body, .. } => substitute_ast_types(body, map),
        _ => {}
    }
}

/// One arm in the match decision matrix: the remaining column patterns, the leaf
/// bindings gathered while descending the tree, and the body to compile on match.
#[derive(Clone)]
struct MatchRow<'ctx> {
    patterns: Vec<Pattern>,
    bindings: Vec<(String, (UnitType, BasicValueEnum<'ctx>))>,
    body: AstNodeWithType,
}

/// The integer value of a scalar literal pattern (`Char` code point or integer),
/// used to key the `switch` when discriminating a literal column. `None` for
/// non-literal patterns (and floats, which aren't matched).
fn literal_key(pattern: &Pattern) -> Option<u64> {
    match pattern {
        Pattern::Char(c) => Some(*c as u64),
        Pattern::Number(Number::Integer(n)) => Some(match n {
            IntegerNumber::U8(v) => *v as u64,
            IntegerNumber::U16(v) => *v as u64,
            IntegerNumber::U32(v) => *v as u64,
            IntegerNumber::U64(v) => *v,
            IntegerNumber::U128(v) => *v as u64,
            IntegerNumber::I8(v) => *v as u64,
            IntegerNumber::I16(v) => *v as u64,
            IntegerNumber::I32(v) => *v as u64,
            IntegerNumber::I64(v) => *v as u64,
            IntegerNumber::I128(v) => *v as u64,
        }),
        _ => None,
    }
}

/// The sub-patterns for a variant's fields, in declaration order (a field the
/// pattern omits becomes a wildcard).
fn variant_sub_patterns(
    variant: &(String, Vec<(String, UnitType)>),
    fields: &[FieldPattern],
) -> Vec<Pattern> {
    variant
        .1
        .iter()
        .map(|(field_name, _)| {
            fields
                .iter()
                .find(|f| &f.field == field_name)
                .map(|f| f.pattern.clone())
                .unwrap_or(Pattern::Wildcard(None))
        })
        .collect()
}

/// Specializes the matrix by `constructor`: keeps rows whose column `col` matches
/// it (expanding into the variant's field columns) or is a wildcard (expanding to
/// wildcard columns, and binding the whole value if the wildcard was named).
fn specialize_rows<'ctx>(
    rows: &[MatchRow<'ctx>],
    col: usize,
    constructor: &str,
    variant: &(String, Vec<(String, UnitType)>),
    col_ty: &UnitType,
    col_value: BasicValueEnum<'ctx>,
) -> Vec<MatchRow<'ctx>> {
    let mut out = Vec::new();
    for row in rows {
        let (sub, extra_binding) = match &row.patterns[col] {
            Pattern::Variant {
                variant_name,
                fields,
            } if variant_name.last().map(|s| s.as_str()) == Some(constructor) => {
                (variant_sub_patterns(variant, fields), None)
            }
            Pattern::Wildcard(name) => (
                vec![Pattern::Wildcard(None); variant.1.len()],
                name.as_ref()
                    .map(|name| (name.clone(), (col_ty.clone(), col_value))),
            ),
            _ => continue,
        };
        let mut patterns = row.patterns[..col].to_vec();
        patterns.extend(sub);
        patterns.extend_from_slice(&row.patterns[col + 1..]);
        let mut bindings = row.bindings.clone();
        bindings.extend(extra_binding);
        out.push(MatchRow {
            patterns,
            bindings,
            body: row.body.clone(),
        });
    }
    out
}

/// The default matrix: rows whose column `col` is a wildcard (it matches any
/// remaining constructor), with that column removed and a binding added if named.
fn default_rows<'ctx>(
    rows: &[MatchRow<'ctx>],
    col: usize,
    col_ty: &UnitType,
    col_value: BasicValueEnum<'ctx>,
) -> Vec<MatchRow<'ctx>> {
    let mut out = Vec::new();
    for row in rows {
        if let Pattern::Wildcard(name) = &row.patterns[col] {
            let mut patterns = row.patterns.clone();
            patterns.remove(col);
            let mut bindings = row.bindings.clone();
            if let Some(name) = name {
                bindings.push((name.clone(), (col_ty.clone(), col_value)));
            }
            out.push(MatchRow {
                patterns,
                bindings,
                body: row.body.clone(),
            });
        }
    }
    out
}

fn custom_type_variant_struct<'ctx>(
    variant: (String, Vec<(String, UnitType)>),
    generics_map: HashMap<VarType, UnitType>,
    compiler_context: &CompilerContext<'ctx>,
) -> Result<StructType<'ctx>, CompilerError> {
    Ok(compiler_context.context.struct_type(
        &variant
            .1
            .iter()
            .map(|field| -> Result<BasicTypeEnum<'ctx>, CompilerError> {
                compiler_context.unit_type_to_llvm_type(match &field.1 {
                    UnitType::Var(var) => generics_map
                        .get(var)
                        .ok_or(CompilerError::FunctionCallError)?,
                    other => other,
                })
            })
            .collect::<Result<Vec<_>, CompilerError>>()?,
        true,
    ))
}

#[derive(Debug, Clone)]
pub struct Stack<'ctx> {
    stack: Vec<(UnitType, BasicValueEnum<'ctx>)>,
}

impl<'ctx> Stack<'ctx> {
    fn new() -> Self {
        Self { stack: Vec::new() }
    }

    pub fn push(&mut self, value: (UnitType, BasicValueEnum<'ctx>)) {
        self.stack.push(value);
    }

    pub fn pop(&mut self) -> Option<(UnitType, BasicValueEnum<'ctx>)> {
        self.stack.pop()
    }

    fn pop_n(&mut self, n: usize) -> Vec<(UnitType, BasicValueEnum<'ctx>)> {
        self.stack.split_off(self.stack.len().saturating_sub(n))
    }

    /// The top `n` entries (the arguments a call about to run will consume),
    /// bottom-most first. Used to read the concrete argument types at a call site.
    fn top_n(&self, n: usize) -> &[(UnitType, BasicValueEnum<'ctx>)] {
        &self.stack[self.stack.len().saturating_sub(n)..]
    }

    fn remove_all(&mut self) -> Vec<(UnitType, BasicValueEnum<'ctx>)> {
        std::mem::take(&mut self.stack)
    }

    fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }
}

pub type BoxDefinitionType<'ctx> =
    Box<dyn Fn(&mut CompilerContext<'ctx>, &mut Stack<'ctx>) -> Result<(), CompilerError> + 'ctx>;
pub type DefinitionType<'ctx> = Rc<BoxDefinitionType<'ctx>>;

/// The monomorphised instances of a (possibly generic) definition: each is a
/// concrete `Type` paired with the code that compiles it.
// The third element is the materialized LLVM function for this instance, present
// only for real `def`s (used by `\name` references). Builtins and variant
// constructors emit inline IR and have no single function, so they store `None`.
type DefinitionInstances<'ctx> =
    Rc<RefCell<Vec<(Type, DefinitionType<'ctx>, Option<FunctionValue<'ctx>>)>>>;

/// Lazily specialises a definition for a requested `Type`, pushing the compiled
/// instance into the shared [`DefinitionInstances`] list.
type DefinitionCreator<'ctx> = Box<
    dyn Fn(Type, &mut CompilerContext<'ctx>, DefinitionInstances<'ctx>) -> Result<(), CompilerError>
        + 'ctx,
>;

#[derive(Clone)]
pub struct Scope<'ctx> {
    scope: Rc<RefCell<InternalScope<'ctx>>>,
}

struct InternalScope<'ctx> {
    definitions: HashMap<String, (Option<DefinitionCreator<'ctx>>, DefinitionInstances<'ctx>)>,
    external_definitions: HashMap<String, Type>,
    imported: HashMap<String, Scope<'ctx>>,
    imported_functions: HashMap<String, (String, String)>,
    values: HashMap<String, (UnitType, BasicValueEnum<'ctx>)>,
    /// Eager value definitions (`def x { ... }`) bound in this scope. Each name
    /// maps to the captured output value(s) (a def may produce several). Unlike
    /// `values` (match-arm bindings, which alias into a scrutinee), an owned
    /// binding holds its own reference: referencing it pushes a `clone_value`
    /// copy (rc++), and the binding's reference is released at scope exit.
    owned_values: HashMap<String, Vec<(UnitType, BasicValueEnum<'ctx>)>>,
    /// Insertion order of `owned_values`, so scope-exit release is deterministic.
    owned_value_order: Vec<String>,
    /// Member namespaces: the retained body scope of an eager namespace def
    /// (`def std { def string { ... } }`), keyed by the def's name. Navigated by
    /// `::` in `call_symbol`/`materialize_symbol`, alongside `imported`. Privacy is
    /// enforced by the type checker, so there is no privacy bit here.
    members: HashMap<String, Scope<'ctx>>,
    parent: Option<Scope<'ctx>>,
    id: u64,
}

static SCOPE_ID: AtomicU64 = AtomicU64::new(0);
// Unique suffix for the LLVM functions lifted out of `\{ ... }` quotations.
static QUOT_ID: AtomicU64 = AtomicU64::new(0);

impl<'ctx> Scope<'ctx> {
    fn with_parent(parent: Scope<'ctx>) -> Self {
        Self {
            scope: Rc::new(RefCell::new(InternalScope {
                external_definitions: HashMap::new(),
                definitions: HashMap::new(),
                imported: HashMap::new(),
                imported_functions: HashMap::new(),
                parent: Some(parent),
                values: HashMap::new(),
                owned_values: HashMap::new(),
                owned_value_order: Vec::new(),
                members: HashMap::new(),
                id: SCOPE_ID.fetch_add(1, Ordering::Relaxed),
            })),
        }
    }

    fn id(&self) -> u64 {
        self.scope.borrow().id
    }

    fn call_symbol(
        &self,
        mut symbol: Vec<String>,
        context: &mut CompilerContext<'ctx>,
        ty: Type,
        stack: &mut Stack<'ctx>,
    ) -> Result<(), CompilerError> {
        let inner = self.scope.borrow();

        match symbol.len() {
            1 => {
                let last = symbol
                    .last()
                    .expect("We checked for the symbol size")
                    .clone();

                // Match-bound field: push a clone (rc++) so each *use* owns its
                // own reference. A binding may be referenced more than once (e.g.
                // `pair first ... pair second`), and each consumer releases the
                // value it receives; without a per-use retain the second use would
                // over-release and free the value out from under the still-live
                // scrutinee tree. Mirrors the eager-binding (`owned_values`) path.
                if let Some((ty, value)) = inner.values.get(&last).cloned() {
                    let pushed = context.clone_value(ty.clone(), value)?;
                    stack.push((ty, pushed));
                    return Ok(());
                }

                // Eager value binding: push a clone of each captured value so the
                // binding keeps owning its own reference (released at scope exit).
                if let Some(owned) = inner.owned_values.get(&last).cloned() {
                    for (ty, value) in owned {
                        let pushed = context.clone_value(ty.clone(), value)?;
                        stack.push((ty, pushed));
                    }
                    return Ok(());
                }

                if let Some(from_definitions) =
                    inner
                        .definitions
                        .get(&last)
                        .and_then(|(creator, definitions)| {
                            if let Some(definition) =
                                definitions.borrow().iter().find(|def_ty| ty == def_ty.0)
                            {
                                return Some(definition.1(context, stack));
                            }
                            if let Some(creator) = creator {
                                let creator = creator(ty.clone(), context, definitions.clone());
                                match creator {
                                    Ok(()) => {
                                        let definitions = definitions.borrow();
                                        let Some(function) =
                                            definitions.iter().find(|def_ty| ty == def_ty.0)
                                        else {
                                            unreachable!("We just added this function to the list")
                                        };
                                        return Some(function.1(context, stack));
                                    }
                                    Err(err) => {
                                        return Some(Err(err));
                                    }
                                };
                            }

                            None
                        })
                {
                    return from_definitions;
                }
                if let Some(from_definitions) =
                    inner.external_definitions.get(&last).cloned().map(|_| {
                        call_function(context, stack, last.clone(), last.clone(), ty.clone())
                    })
                {
                    return from_definitions;
                }
                if let Some(imported_functions) = inner.imported_functions.get(&last) {
                    return self.call_symbol(
                        vec![imported_functions.1.clone(), imported_functions.0.clone()],
                        context,
                        ty,
                        stack,
                    );
                }
                if let Some(parent) = inner.parent.as_ref() {
                    return parent.call_symbol(symbol, context, ty, stack);
                }
                Err(CompilerError::UndefinedSymbol(symbol.join("::")))
            }
            0 => Err(CompilerError::UndefinedSymbol(symbol.join("::"))),
            _ => {
                let first = symbol.remove(0);
                if let Some(from_imports) = inner.imported.get(&first) {
                    return from_imports.call_symbol(symbol, context, ty, stack);
                }
                if let Some(member_scope) = inner.members.get(&first) {
                    return member_scope.call_symbol(symbol, context, ty, stack);
                }
                if let Some(parent) = inner.parent.as_ref() {
                    symbol.insert(0, first);
                    return parent.call_symbol(symbol, context, ty, stack);
                }

                Err(CompilerError::UndefinedSymbol(symbol.join("::")))
            }
        }
    }

    /// Resolves a symbol to its materialized LLVM function (instantiating the
    /// monomorphic instance for `ty` if needed) without calling it — used by
    /// `\name` to push a function pointer onto the stack. Mirrors the lookup
    /// chain of [`call_symbol`].
    fn materialize_symbol(
        &self,
        mut symbol: Vec<String>,
        context: &mut CompilerContext<'ctx>,
        ty: Type,
    ) -> Result<FunctionValue<'ctx>, CompilerError> {
        let inner = self.scope.borrow();
        match symbol.len() {
            1 => {
                let last = symbol
                    .last()
                    .expect("We checked for the symbol size")
                    .clone();

                if let Some((creator, definitions)) = inner.definitions.get(&last) {
                    // Already materialized (a real `def`, or a builtin we wrapped
                    // earlier at this type)?
                    if let Some(function) = definitions
                        .borrow()
                        .iter()
                        .find(|def_ty| ty == def_ty.0)
                        .and_then(|def_ty| def_ty.2)
                    {
                        return Ok(function);
                    }
                    // Make sure an instance for this concrete type exists.
                    if !definitions.borrow().iter().any(|def_ty| ty == def_ty.0) {
                        if let Some(creator) = creator {
                            creator(ty.clone(), context, definitions.clone())?;
                        } else {
                            return Err(CompilerError::CannotReferenceFunction(last));
                        }
                    }
                    // A `def` instance carries `Some(function)` and was returned
                    // above. Reaching here means a builtin (inline IR, no function):
                    // build a wrapper around its emitter closure and cache it.
                    let inline = {
                        let definitions = definitions.borrow();
                        let instance = definitions
                            .iter()
                            .find(|def_ty| ty == def_ty.0)
                            .ok_or_else(|| CompilerError::CannotReferenceFunction(last.clone()))?;
                        if let Some(function) = instance.2 {
                            return Ok(function);
                        }
                        instance.1.clone()
                    };
                    let wrapper =
                        context.materialize_builtin_wrapper(&last, ty.clone(), &inline)?;
                    if let Some(instance) = definitions
                        .borrow_mut()
                        .iter_mut()
                        .find(|def_ty| ty == def_ty.0)
                    {
                        instance.2 = Some(wrapper);
                    }
                    return Ok(wrapper);
                }
                if inner.external_definitions.contains_key(&last) {
                    return context
                        .module
                        .get_function(&last)
                        .ok_or(CompilerError::GetFunctionError(last));
                }
                if let Some(imported_functions) = inner.imported_functions.get(&last) {
                    return self.materialize_symbol(
                        vec![imported_functions.1.clone(), imported_functions.0.clone()],
                        context,
                        ty,
                    );
                }
                if let Some(parent) = inner.parent.as_ref() {
                    return parent.materialize_symbol(symbol, context, ty);
                }
                Err(CompilerError::UndefinedSymbol(symbol.join("::")))
            }
            0 => Err(CompilerError::UndefinedSymbol(symbol.join("::"))),
            _ => {
                let first = symbol.remove(0);
                if let Some(from_imports) = inner.imported.get(&first) {
                    return from_imports.materialize_symbol(symbol, context, ty);
                }
                if let Some(member_scope) = inner.members.get(&first) {
                    return member_scope.materialize_symbol(symbol, context, ty);
                }
                if let Some(parent) = inner.parent.as_ref() {
                    symbol.insert(0, first);
                    return parent.materialize_symbol(symbol, context, ty);
                }
                Err(CompilerError::UndefinedSymbol(symbol.join("::")))
            }
        }
    }

    fn add_value(&self, name: String, value: (UnitType, BasicValueEnum<'ctx>)) {
        let mut inner = self.scope.borrow_mut();
        inner.values.insert(name, value);
    }

    /// Binds an eager value definition's captured output(s) in this scope. The
    /// binding owns one reference to each custom-typed value; see `owned_values`.
    fn add_owned_values(&self, name: String, values: Vec<(UnitType, BasicValueEnum<'ctx>)>) {
        let mut inner = self.scope.borrow_mut();
        if inner.owned_values.insert(name.clone(), values).is_none() {
            inner.owned_value_order.push(name);
        }
    }

    /// Releases the reference each eager binding in this scope owns. Called when
    /// the scope (a block / function body) exits on a fall-through path. A
    /// reference to a binding pushes a clone (rc++), so dropping the binding's own
    /// reference here frees the value only once every referenced copy is also
    /// gone; top-level (entry/module) scopes never call this, so their bindings
    /// live for the whole program.
    fn release_owned_values(
        &self,
        context: &mut CompilerContext<'ctx>,
    ) -> Result<(), CompilerError> {
        let owned: Vec<(UnitType, BasicValueEnum<'ctx>)> = {
            let inner = self.scope.borrow();
            inner
                .owned_value_order
                .iter()
                .rev()
                .filter_map(|name| inner.owned_values.get(name))
                .flatten()
                .cloned()
                .collect()
        };
        for (ty, value) in owned {
            context.drop_value(ty, value)?;
        }
        Ok(())
    }

    fn add_import(&self, alias: String, scope: Scope<'ctx>) {
        let mut inner = self.scope.borrow_mut();
        inner.imported.insert(alias, scope);
    }

    /// Registers the retained body scope of an eager namespace def as a member,
    /// reachable via `name::member` in `call_symbol`/`materialize_symbol`.
    fn add_member(&self, name: String, scope: Scope<'ctx>) {
        let mut inner = self.scope.borrow_mut();
        inner.members.insert(name, scope);
    }

    fn add_function_import(&self, alias: String, real_name: String, module_alias: String) {
        let mut inner = self.scope.borrow_mut();
        inner
            .imported_functions
            .insert(alias, (real_name, module_alias));
    }

    fn add_function_definition(&self, symbol: &str, creator: DefinitionCreator<'ctx>) {
        let mut inner = self.scope.borrow_mut();
        inner.definitions.insert(
            symbol.to_string(),
            (Some(creator), Rc::new(RefCell::new(vec![]))),
        );
    }

    fn empty() -> Scope<'ctx> {
        Self {
            scope: Rc::new(RefCell::new(InternalScope {
                definitions: HashMap::new(),
                external_definitions: HashMap::new(),
                imported: HashMap::new(),
                imported_functions: HashMap::new(),

                parent: None,
                values: HashMap::new(),
                owned_values: HashMap::new(),
                owned_value_order: Vec::new(),
                members: HashMap::new(),
                id: SCOPE_ID.fetch_add(1, Ordering::Relaxed),
            })),
        }
    }

    fn add_external_definition(&self, symbol: String, ty: Type) {
        self.scope
            .borrow_mut()
            .external_definitions
            .insert(symbol, ty);
    }
}

fn call_function<'ctx>(
    compiler_context: &CompilerContext<'ctx>,
    stack: &mut Stack<'ctx>,
    symbol_name: String,
    function_name: String,
    ty: Type,
) -> Result<(), CompilerError> {
    let params = stack.pop_n(ty.pop_types.len());
    if params.len() != ty.pop_types.len() {
        return Err(CompilerError::StackUnderflow);
    }

    // Tail-call optimization: a self-call in tail position is rewritten into a
    // branch back to the function's loop header instead of a real call. We store
    // the freshly computed arguments into the parameter slots and jump; the slots
    // are reloaded at the header, so the frame is reused and the recursion runs
    // in constant stack. Only direct self-recursion (matching `function_name`)
    // qualifies — mutual/cross-function tail calls fall through to a normal call.
    if compiler_context.tail_position
        && let Some(tail_ctx) = compiler_context.tail_ctx.as_ref()
        && tail_ctx.function_name == function_name
    {
        for (slot, (_, value)) in tail_ctx.param_slots.iter().zip(params.iter()) {
            compiler_context.builder.build_store(*slot, *value)?;
        }
        // This path bypasses every enclosing `match` merge, so release their
        // deferred scrutinee references here (innermost first) before looping;
        // otherwise each iteration leaks its scrutinee. We release only the node
        // (not its fields) — see `build_rc_release_node_only` — because a field may
        // have been bound out and threaded into the next iteration.
        for (ty, value) in compiler_context.tail_cleanups.iter().rev() {
            compiler_context.build_rc_release_node_only(ty.clone(), *value)?;
        }
        compiler_context
            .builder
            .build_unconditional_branch(tail_ctx.loop_header)?;
        return Ok(());
    }

    let params = params
        .into_iter()
        .map(|param| param.1.into())
        .collect::<Vec<_>>();

    let function = compiler_context
        .module
        .get_function(&function_name)
        .ok_or(CompilerError::FunctionCallError)?;

    let call =
        compiler_context
            .builder
            .build_call(function, &params, &format!("{}_call", symbol_name))?;
    if ty.push_types.is_empty() {
        return Ok(());
    }

    let value = call.try_as_basic_value();
    if value.is_right() {
        return Err(CompilerError::FunctionCallError);
    }

    let return_value = value.left().ok_or(CompilerError::FunctionCallError)?;
    if ty.push_types.len() == 1 {
        stack.push((ty.push_types[0].clone(), return_value));
    } else {
        let struct_value = return_value.into_struct_value().as_aggregate_value_enum();

        for (index, field_type) in ty.push_types.iter().enumerate() {
            let field_value = compiler_context.builder.build_extract_value(
                struct_value,
                index as u32,
                &format!("field_{}", index),
            )?;

            stack.push((field_type.clone(), field_value));
        }
    }

    Ok(())
}

/// Lowers `apply`: pop the function value on top of the stack, pop the arguments
/// its signature requires, and call it through its pointer with an indirect call.
fn apply_function<'ctx>(
    compiler_context: &CompilerContext<'ctx>,
    stack: &mut Stack<'ctx>,
) -> Result<(), CompilerError> {
    let (func_unit, func_value) = stack.pop().ok_or(CompilerError::StackUnderflow)?;
    let UnitType::Type(sig) = func_unit else {
        return Err(CompilerError::UnexpectedType);
    };

    let params = stack.pop_n(sig.pop_types.len());
    if params.len() != sig.pop_types.len() {
        return Err(CompilerError::StackUnderflow);
    }
    let params = params
        .into_iter()
        .map(|param| param.1.into())
        .collect::<Vec<BasicMetadataValueEnum>>();

    let fn_type = compiler_context.get_llvm_function_type(&sig)?;
    let function_pointer = func_value.into_pointer_value();
    let call = compiler_context.builder.build_indirect_call(
        fn_type,
        function_pointer,
        &params,
        "apply_call",
    )?;
    if sig.push_types.is_empty() {
        return Ok(());
    }

    let value = call.try_as_basic_value();
    if value.is_right() {
        return Err(CompilerError::FunctionCallError);
    }
    let return_value = value.left().ok_or(CompilerError::FunctionCallError)?;
    if sig.push_types.len() == 1 {
        stack.push((sig.push_types[0].clone(), return_value));
    } else {
        let struct_value = return_value.into_struct_value().as_aggregate_value_enum();
        for (index, field_type) in sig.push_types.iter().enumerate() {
            let field_value = compiler_context.builder.build_extract_value(
                struct_value,
                index as u32,
                &format!("field_{}", index),
            )?;
            stack.push((field_type.clone(), field_value));
        }
    }

    Ok(())
}

fn match_types(left: &[UnitType], right: &[UnitType]) -> bool {
    if left.len() != right.len() {
        return false;
    }
    let mut var_type_map: HashMap<VarType, UnitType> = HashMap::new();
    for (left, right) in left.iter().zip(right.iter()) {
        let match_ty = match (left, right) {
            (UnitType::Literal(a), UnitType::Literal(b)) => a == b,
            (UnitType::Var(a), UnitType::Var(b)) => var_type_map
                .insert(a.clone(), UnitType::Var(b.clone()))
                .is_none_or(|previous| previous == UnitType::Var(b.clone())),
            (
                UnitType::Custom {
                    name: name1,
                    generic_types: generic_types1,
                },
                UnitType::Custom {
                    name: name2,
                    generic_types: generic_types2,
                },
            ) => name1 == name2 && match_types(generic_types1, generic_types2),
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
