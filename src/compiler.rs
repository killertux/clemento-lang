use std::{
    cell::RefCell,
    collections::HashMap,
    fs::read_to_string,
    path::{Path, PathBuf},
    rc::Rc,
    sync::atomic::{AtomicU64, Ordering},
};

use inkwell::{
    AddressSpace,
    builder::{Builder, BuilderError},
    context::Context,
    module::Module,
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, IntType, PointerType, StructType},
    values::{AggregateValue, BasicValue, BasicValueEnum, IntValue, PointerValue},
};
use thiserror::Error;

use crate::{
    internal_functions::{InternalFunction, builtins_functions},
    lexer::{IntegerNumber, Number, Position},
    parser::{
        AstNode, AstNodeType, LiteralType, NumberType, Parser, ParserError, Pattern, Type,
        UnitType, VarType,
    },
    type_checker::{AstNodeWithType, CustomType, TypeChecker, TypeCheckerError},
};

pub struct CompilerContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub internal_functions: Vec<InternalFunction<'ctx>>,
    pub imports: HashMap<String, Scope<'ctx>>,
    pub ref_count: RefCount<'ctx>,
    pub type_definitions: HashMap<Vec<String>, CustomType>,
}

pub fn compile(file: impl AsRef<Path>) -> Result<PathBuf, CompilerError> {
    let path_as_string = file.as_ref().display().to_string();
    let file_content = read_to_string(file.as_ref())?;

    let program = Parser::new_from_file(&file_content, path_as_string)
        .collect::<Result<Vec<AstNode>, ParserError>>()?;
    let program = TypeChecker::new().type_check(
        AstNode {
            node_type: AstNodeType::Block(program),
            position: Position::default(),
            type_definition: None,
        },
        true,
        vec![],
    )?;
    let context = Context::create();
    let mut stack = Stack::new();

    let scope = Scope::empty();
    let mut compiler_context = CompilerContext::new(&context);
    compiler_context.compile_ast(scope, &mut stack, program.0, vec![])?;

    let mut output_path = file.as_ref().to_path_buf();
    output_path.set_extension("ll");
    compiler_context
        .module
        .print_to_file(&output_path)
        .map_err(|err| CompilerError::WriteLLVMError(err.to_string()))?;
    Ok(output_path)
}

pub struct RefCount<'ctx> {
    type_marker: IntType<'ctx>,
    ptr_type: PointerType<'ctx>,
    len_type: IntType<'ctx>,
    ref_count_type: IntType<'ctx>,
    ref_count_struct: StructType<'ctx>,
}

impl<'ctx> RefCount<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        let type_marker = context.i8_type();
        let ptr_type = context.ptr_type(AddressSpace::default());
        let len_type = context.i64_type();
        let ref_count_type = context.i64_type();
        let ref_count_struct = context.struct_type(
            &[
                type_marker.into(),
                ptr_type.into(),
                len_type.into(),
                ref_count_type.into(),
            ],
            true,
        );
        Self {
            type_marker,
            ptr_type,
            len_type,
            ref_count_type,
            ref_count_struct,
        }
    }

    pub fn create_with_const_len(
        &self,
        builder: &Builder<'ctx>,
        ty: UnitType,
        ptr: PointerValue<'ctx>,
        len: u64,
    ) -> Result<PointerValue<'ctx>, CompilerError> {
        let type_marker = self.type_marker;
        let len_type = self.len_type;
        let ref_count_type = self.ref_count_type;
        let ref_count_struct = self.ref_count_struct;

        let ty = match ty {
            UnitType::Literal(LiteralType::String) => 0,
            UnitType::Custom { .. } => 1,
            _ => return Err(CompilerError::UnsupportedType(ty)),
        };

        let struct_val = builder.build_malloc(ref_count_struct, "struct_value")?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 0, "type")?;
        builder.build_store(field_ptr, type_marker.const_int(ty, false))?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 1, "ptr")?;
        builder.build_store(field_ptr, ptr)?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 2, "len")?;
        builder.build_store(field_ptr, len_type.const_int(len, false))?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 3, "rc")?;
        builder.build_store(field_ptr, ref_count_type.const_int(1, false))?;

        Ok(struct_val)
    }

    pub fn create(
        &self,
        builder: &Builder<'ctx>,
        ty: UnitType,
        ptr: PointerValue<'ctx>,
        len: IntValue<'ctx>,
    ) -> Result<PointerValue<'ctx>, CompilerError> {
        let type_marker = self.type_marker;
        let ref_count_type = self.ref_count_type;
        let ref_count_struct = self.ref_count_struct;

        let ty = match ty {
            UnitType::Literal(LiteralType::String) => 0,
            UnitType::Custom { .. } => 1,
            _ => return Err(CompilerError::UnsupportedType(ty)),
        };

        let struct_val = builder.build_malloc(ref_count_struct, "struct_value")?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 0, "type")?;
        builder.build_store(field_ptr, type_marker.const_int(ty, false))?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 1, "ptr")?;
        builder.build_store(field_ptr, ptr)?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 2, "len")?;
        builder.build_store(field_ptr, len)?;
        let field_ptr = builder.build_struct_gep(ref_count_struct, struct_val, 3, "rc")?;
        builder.build_store(field_ptr, ref_count_type.const_int(1, false))?;

        Ok(struct_val)
    }
}

impl<'ctx> CompilerContext<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        let module = context.create_module("std");
        let builder = context.create_builder();
        let internal_functions = builtins_functions(context, &module);

        Self {
            context,
            module,
            builder,
            internal_functions,
            imports: HashMap::new(),
            ref_count: RefCount::new(context),
            type_definitions: HashMap::new(),
        }
    }

    pub fn drop_value(&self, value: BasicValueEnum<'ctx>) -> Result<(), CompilerError> {
        match value {
            BasicValueEnum::PointerValue(ptr) => {
                let rc_field_ptr = self.builder.build_struct_gep(
                    self.ref_count.ref_count_struct,
                    ptr,
                    3,
                    "ref_count",
                )?;
                let rc = self
                    .builder
                    .build_load(self.ref_count.ref_count_type, rc_field_ptr, "get_ref_count")?
                    .into_int_value();
                let result = self.builder.build_int_add(
                    rc,
                    self.ref_count.ref_count_type.const_int(1, false),
                    "inc_ref_count",
                )?;
                let condition = self.builder.build_int_compare(
                    inkwell::IntPredicate::NE,
                    result,
                    self.ref_count.ref_count_type.const_int(0, false),
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

                self.builder.position_at_end(with_more_references);
                self.builder.build_store(rc_field_ptr, result)?;
                self.builder.build_unconditional_branch(merge_block)?;

                self.builder.position_at_end(free_rc);
                let ptr_field_ptr = self.builder.build_struct_gep(
                    self.ref_count.ref_count_struct,
                    ptr,
                    1,
                    "ref_count",
                )?;
                let ptr_field = self
                    .builder
                    .build_load(self.ref_count.ptr_type, ptr_field_ptr, "get_ptr")?
                    .into_pointer_value();
                self.builder.build_free(ptr_field)?;
                self.builder.build_free(ptr)?;
                self.builder.build_unconditional_branch(merge_block)?;
                self.builder.position_at_end(merge_block);
                Ok(())
            }
            _ => Ok(()),
        }
    }

    pub fn clone_value(
        &self,
        value: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match value {
            BasicValueEnum::PointerValue(ptr) => {
                let rc_field_ptr = self.builder.build_struct_gep(
                    self.ref_count.ref_count_struct,
                    ptr,
                    3,
                    "ref_count",
                )?;
                let rc = self
                    .builder
                    .build_load(self.ref_count.ref_count_type, rc_field_ptr, "get_ref_count")?
                    .into_int_value();
                let result = self.builder.build_int_sub(
                    rc,
                    self.ref_count.ref_count_type.const_int(1, false),
                    "inc_ref_count",
                )?;
                self.builder.build_store(rc_field_ptr, result)?;
                Ok(BasicValueEnum::PointerValue(ptr))
            }
            other => Ok(other),
        }
    }

    pub fn get_ptr_len(&self, ptr: PointerValue<'ctx>) -> Result<IntValue<'ctx>, CompilerError> {
        let len_field_ptr =
            self.builder
                .build_struct_gep(self.ref_count.ref_count_struct, ptr, 2, "ref_len")?;
        Ok(self
            .builder
            .build_load(
                self.ref_count.ref_count_type,
                len_field_ptr,
                "get_ref_count",
            )?
            .into_int_value())
    }

    pub fn get_ptr_ptr(
        &self,
        ptr: PointerValue<'ctx>,
    ) -> Result<PointerValue<'ctx>, CompilerError> {
        let ptr_field_ptr =
            self.builder
                .build_struct_gep(self.ref_count.ref_count_struct, ptr, 1, "ref_ptr")?;
        Ok(self
            .builder
            .build_load(self.ref_count.ptr_type, ptr_field_ptr, "get_ptr")?
            .into_pointer_value())
    }

    pub fn deref_rc_if_necessary(
        &self,
        value: BasicValueEnum<'ctx>,
    ) -> Result<BasicValueEnum<'ctx>, CompilerError> {
        match value {
            BasicValueEnum::PointerValue(ptr) => Ok(self.get_ptr_ptr(ptr)?.into()),
            _ => Ok(value),
        }
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
            AstNodeType::String(string) => self.compile_string(stack, string),
            AstNodeType::Boolean(boolean) => self.compile_boolean(stack, boolean),
            AstNodeType::Symbol(symbol) => {
                scope.call_symbol(vec![symbol], self, program.type_definition, stack)?;
                Ok(())
            }
            AstNodeType::SymbolWithPath(symbol) => {
                scope.call_symbol(symbol, self, program.type_definition, stack)?;
                Ok(())
            }
            AstNodeType::Block(nodes) => {
                let scope = Scope::with_parent(scope);
                for node in nodes {
                    self.compile_ast(scope.clone(), stack, node, module_path.clone())?;
                }

                Ok(())
            }
            AstNodeType::Definition {
                name: symbol, body, ..
            } => self.compile_definition(scope, &symbol, *body, module_path),
            AstNodeType::ExternalDefinition(symbol, ty) => {
                for function in &self.internal_functions {
                    if function.name == symbol && match_types(&ty.pop_types, &function.ty.pop_types)
                    {
                        let fun = function.function.clone();
                        scope.add_function_definition(
                            function.name.as_str(),
                            Box::new(
                                move |ty: Type,
                                      _: &mut CompilerContext<'ctx>,
                                      definitions: Rc<
                                    RefCell<Vec<(Type, DefinitionType<'ctx>)>>,
                                >|
                                      -> Result<(), CompilerError> {
                                    let mut definitions = definitions.borrow_mut();
                                    definitions.push((ty, fun.clone()));
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
            AstNodeType::If(true_body, false_body) => {
                self.compile_if(scope, *true_body, false_body, stack, module_path)
            }
            AstNodeType::Import(path, import_node) => {
                let import_scope = if let Some(nodes) = import_node.node {
                    let AstNodeType::Block(nodes) = nodes.node_type else {
                        return Err(CompilerError::InvalidImportType(program.position));
                    };
                    let import_scope = Scope::empty();
                    let mut module_path = module_path.clone();
                    module_path.extend(path);
                    for node in nodes {
                        self.compile_ast(import_scope.clone(), stack, node, module_path.clone())?;
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
                    let generics = generics.clone();
                    scope.add_function_definition(
                        variant.0.clone().as_str(),
                        Box::new(
                            move |ty: Type,
                                  _: &mut CompilerContext<'ctx>,
                                  definitions: Rc<RefCell<Vec<(Type, DefinitionType<'ctx>)>>>|
                                  -> Result<(), CompilerError> {
                                let mut definitions = definitions.borrow_mut();
                                let variant = variant.clone();
                                let UnitType::Custom {  name:_, generic_types } = &ty.clone().push_types[0] else {
                                    return Err(CompilerError::UnexpectedType);
                                };
                                let generics_map = generics.iter().map(|generic| generic.1.clone()).zip(generic_types.iter().cloned()).collect::<HashMap<_, _>>();
                                definitions.push((ty.clone(), Rc::new(Box::new(move |compiler_context: &CompilerContext<'ctx>,
                                      stack: &mut Stack<'ctx>|
                                      -> Result<(), CompilerError> {
                                         let variant_struct = custom_type_variant_struct(variant.clone(), generics_map.clone(), compiler_context)?;
                                        let values = stack.pop_n(ty.pop_types.len());

                                        let struct_val = compiler_context.builder.build_malloc(variant_struct, "struct_value")?;
                                        let field_ptr = compiler_context.builder.build_struct_gep(variant_struct, struct_val, 0, "variant")?;
                                        compiler_context.builder.build_store(field_ptr, compiler_context.context.i8_type().const_int(index as u64, false))?;
                                        (1..(variant_struct.count_fields() as usize)).try_for_each(|field_index| -> Result<(), CompilerError> {
                                            let field_ptr = compiler_context.builder.build_struct_gep(variant_struct, struct_val, field_index as u32, &format!("field_{}", field_index))?;
                                            compiler_context.builder.build_store(field_ptr, values[field_index - 1].1)?;
                                            Ok(())
                                        })?;
                                        let ref_count = compiler_context.ref_count.create_with_const_len(&compiler_context.builder, ty.push_types[0].clone(), struct_val, 0)?;
                                        stack.push((ty.push_types[0].clone(), ref_count.into()));
                                        Ok(())
                                }))));
                                Ok(())
                            },
                        ),
                    );
                }

                Ok(())
            }
            AstNodeType::Match(cases) => self.compile_match(scope, cases, stack, module_path),
        }
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

        if symbol_name == "main" {
            let function_name = "main";
            let function_type = self.context.i32_type().fn_type(&[], false);
            let function = self
                .module
                .add_function(&function_name, function_type, None);
            let new_scope = Scope::with_parent(cloned_scope);

            let entry = self.context.append_basic_block(function, "entry");
            self.builder.position_at_end(entry);

            let mut stack = Stack::new();

            for param in body
                .type_definition
                .pop_types
                .clone()
                .into_iter()
                .zip(function.get_param_iter())
            {
                stack.push(param);
            }

            self.compile_ast(new_scope, &mut stack, body, module_path)?;

            match stack.pop() {
                Some(value) => {
                    self.builder.build_return(Some(&value.1))?;
                }
                None => {
                    self.builder.build_return(Some(
                        &self.context.i32_type().const_zero().as_basic_value_enum(),
                    ))?;
                }
            }
            return Ok(());
        }
        let id = scope.id();

        scope.add_function_definition(
            symbol,
            Box::new(
                move |ty: Type,
                      context: &mut CompilerContext<'ctx>,
                      definitions: Rc<RefCell<Vec<(Type, DefinitionType<'ctx>)>>>| {
                    let cloned_scope = cloned_scope.clone();
                    let body = body.clone();
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
                    let function_type = function_type;

                    let function = context
                        .module
                        .add_function(&function_name, function_type, None);
                    let symbol_name_cloned = symbol_name.clone();
                    {
                        let mut definitions = definitions.borrow_mut();
                        definitions.push((
                            ty.clone(),
                            Rc::new(Box::new(
                                move |compiler_context: &CompilerContext<'ctx>,
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
                        ));
                    }
                    let new_scope = Scope::with_parent(cloned_scope);

                    let entry = context.context.append_basic_block(function, "entry");
                    context.builder.position_at_end(entry);

                    let mut stack = Stack::new();

                    for param in body
                        .type_definition
                        .pop_types
                        .clone()
                        .into_iter()
                        .zip(function.get_param_iter())
                    {
                        stack.push(param);
                    }

                    context.compile_ast(new_scope, &mut stack, body, module_path.clone())?;

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
                LiteralType::String => Ok(self.context.ptr_type(AddressSpace::default()).into()),
                LiteralType::Boolean => Ok(self.context.bool_type().into()),
            },
            UnitType::Var(_) => todo!("Handle variatic types"),
            UnitType::Type(_) => todo!("Handle function types"),
            UnitType::Custom { .. } => Ok(self.context.ptr_type(AddressSpace::default()).into()),
        }
    }

    fn compile_string(&self, stack: &mut Stack<'ctx>, string: String) -> Result<(), CompilerError> {
        let value = self.builder.build_global_string_ptr(&string, "str")?;
        stack.push((
            UnitType::Literal(LiteralType::String),
            self.ref_count
                .create_with_const_len(
                    &self.builder,
                    UnitType::Literal(LiteralType::String),
                    value.as_pointer_value(),
                    (string.len() + 1) as u64,
                )?
                .as_basic_value_enum(),
        ));
        Ok(())
    }

    fn compile_boolean(&self, stack: &mut Stack<'ctx>, boolean: bool) -> Result<(), CompilerError> {
        let value = self.context.bool_type().const_int(boolean as u64, false);
        stack.push((UnitType::Literal(LiteralType::Boolean), value.into()));
        Ok(())
    }

    fn compile_if(
        &mut self,
        scope: Scope<'ctx>,
        true_body: AstNodeWithType,
        false_body: Option<Box<AstNodeWithType>>,
        stack: &mut Stack<'ctx>,
        module_path: Vec<String>,
    ) -> Result<(), CompilerError> {
        let (condition_type, condition_value) = stack.pop().unwrap();
        let condition = match condition_type {
            UnitType::Literal(LiteralType::Boolean) => {
                let int_value = condition_value.into_int_value();
                self.builder.build_int_compare(
                    inkwell::IntPredicate::NE,
                    int_value,
                    int_value.get_type().const_zero(),
                    "if_cond",
                )?
            }
            _ => return Err(CompilerError::UnexpectedType),
        };

        let current_function = self
            .builder
            .get_insert_block()
            .ok_or(CompilerError::IfWithoutFunction)?
            .get_parent()
            .ok_or(CompilerError::IfWithoutFunction)?;

        let true_block = self.context.append_basic_block(current_function, "true");
        let merge_block = self.context.append_basic_block(current_function, "merge");
        match false_body {
            Some(false_body) => {
                let false_block = self.context.append_basic_block(current_function, "false");
                self.builder
                    .build_conditional_branch(condition, true_block, false_block)?;

                self.builder.position_at_end(true_block);
                let mut true_stack = stack.clone();
                let push_types_len = true_body.type_definition.push_types.len();
                self.compile_ast(
                    scope.clone(),
                    &mut true_stack,
                    true_body,
                    module_path.clone(),
                )?;
                let true_values = true_stack.pop_n(push_types_len);
                self.builder.build_unconditional_branch(merge_block)?;
                let true_end_bb = self
                    .builder
                    .get_insert_block()
                    .ok_or(CompilerError::IfWithoutFunction)?;

                self.builder.position_at_end(false_block);
                self.compile_ast(scope, stack, *false_body, module_path)?;
                let false_values = stack.pop_n(push_types_len);
                self.builder.build_unconditional_branch(merge_block)?;
                let false_end_bb = self
                    .builder
                    .get_insert_block()
                    .ok_or(CompilerError::IfWithoutFunction)?;

                self.builder.position_at_end(merge_block);
                for ((tr_ty, true_value), (fl_ty, false_value)) in
                    true_values.into_iter().zip(false_values.into_iter())
                {
                    let phi = self
                        .builder
                        .build_phi(true_value.get_type(), "phi")
                        .unwrap();
                    phi.add_incoming(&[(&true_value, true_end_bb), (&false_value, false_end_bb)]);
                    assert_eq!(tr_ty, fl_ty);
                    stack.push((tr_ty, phi.as_basic_value()));
                }
            }
            None => {
                self.builder
                    .build_conditional_branch(condition, true_block, merge_block)?;

                self.builder.position_at_end(true_block);
                self.compile_ast(scope, stack, true_body, module_path)?;
                self.builder.build_unconditional_branch(merge_block)?;

                self.builder.position_at_end(merge_block);
            }
        };
        Ok(())
    }

    fn compile_match(
        &mut self,
        scope: Scope<'ctx>,
        cases: Vec<crate::parser::Case<AstNodeWithType>>,
        stack: &mut Stack<'ctx>,
        module_path: Vec<String>,
    ) -> Result<(), CompilerError> {
        let Some(match_value) = stack.pop() else {
            return Err(CompilerError::StackUnderflow);
        };
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
                self.builder.build_switch(
                    match_value.1.into_int_value(),
                    case_blocks[case_blocks.len() - 1],
                    cases
                        .iter()
                        .map(|case| match &case.pattern {
                            Pattern::Number(n) => {
                                self.number_to_llvm_number(n.clone()).1.into_int_value()
                            }
                            _ => panic!("Unsupported pattern type"),
                        })
                        .zip(case_blocks[0..case_blocks.len() - 1].iter().cloned())
                        .collect::<Vec<_>>()
                        .as_slice(),
                )?;
                for (index, case) in cases.into_iter().enumerate() {
                    let mut temp_stack = stack.clone();
                    match case.pattern {
                        Pattern::Number(_) => {
                            self.builder.position_at_end(case_blocks[index]);
                            let n_push_types = case.body.type_definition.push_types.len();
                            self.compile_ast(
                                scope.clone(),
                                &mut temp_stack,
                                *case.body,
                                module_path.clone(),
                            )?;
                            self.builder.build_unconditional_branch(merge_block)?;
                            let bb = self
                                .builder
                                .get_insert_block()
                                .ok_or(CompilerError::IfWithoutFunction)?;
                            values_and_blocks.push((temp_stack.pop_n(n_push_types), bb));
                        }
                        Pattern::Wildcard(name) => {
                            self.builder.position_at_end(case_blocks[index]);
                            let n_push_types = case.body.type_definition.push_types.len();
                            let scope = scope.clone();
                            if let Some(name) = name {
                                scope.add_value(name, match_value.clone());
                            }
                            self.compile_ast(
                                scope,
                                &mut temp_stack,
                                *case.body,
                                module_path.clone(),
                            )?;
                            self.builder.build_unconditional_branch(merge_block)?;
                            let bb = self
                                .builder
                                .get_insert_block()
                                .ok_or(CompilerError::IfWithoutFunction)?;
                            values_and_blocks.push((temp_stack.pop_n(n_push_types), bb));
                        }
                        _ => panic!("This is not a valid pattern for this type"),
                    }
                }
                self.builder.position_at_end(merge_block);
                let mut values_for_phi = Vec::new();
                for (values, block) in values_and_blocks.iter() {
                    for (index, value) in values.iter().enumerate() {
                        if values_for_phi.get(index).is_none() {
                            values_for_phi
                                .push(((value.0.clone(), value.1.get_type()), Vec::new()));
                        }
                        values_for_phi[index]
                            .1
                            .push((&value.1 as &dyn BasicValue, block.clone()));
                    }
                }
                for (ty, values) in values_for_phi.into_iter() {
                    let phi = self.builder.build_phi(ty.1, "phi").unwrap();
                    phi.add_incoming(values.as_slice());
                    stack.push((ty.0, phi.as_basic_value()));
                }
                Ok(())
            }
            UnitType::Custom {
                name,
                generic_types,
                ..
            } => {
                let Some(custom_type) = self.get_type(name) else {
                    panic!("We should always find the custom type in the scope")
                };
                let mut case_blocks = Vec::new();
                let else_block = self.context.append_basic_block(current_function, "else");
                let mut values_and_blocks = Vec::new();
                let mut index_to_variant_index = HashMap::new();
                for (index, case) in cases.iter().enumerate() {
                    match &case.pattern {
                        Pattern::Wildcard(_) => {}
                        Pattern::Variant { variant_name, .. } => {
                            let variant_index = custom_type
                                .variants
                                .iter()
                                .position(|variant| Some(&variant.0) == variant_name.last())
                                .unwrap();
                            index_to_variant_index.insert(index, variant_index);
                            case_blocks.push(self.context.append_basic_block(
                                current_function,
                                &format!("case_{}", variant_index),
                            ));
                        }
                        _ => panic!("Unsupported pattern type"),
                    }
                }
                let match_ptr = self.get_ptr_ptr(match_value.clone().1.into_pointer_value())?;

                let struct_type = self
                    .context
                    .struct_type(&[self.context.i8_type().into()], true);
                let ptr_field_ptr =
                    self.builder
                        .build_struct_gep(struct_type, match_ptr, 0, "variant_value")?;
                let variant_value = self.builder.build_load(
                    self.context.i8_type(),
                    ptr_field_ptr,
                    "variant_value_load",
                )?;
                self.builder.build_switch(
                    variant_value.into_int_value(),
                    else_block,
                    cases
                        .iter()
                        .enumerate()
                        .filter_map(|(index, case)| match &case.pattern {
                            Pattern::Variant { .. } => Some(
                                self.context.i8_type().const_int(
                                    *index_to_variant_index
                                        .get(&index)
                                        .expect("We created the map before")
                                        as u64,
                                    false,
                                ),
                            ),
                            _ => None,
                        })
                        .zip(case_blocks[0..case_blocks.len()].iter().cloned())
                        .collect::<Vec<_>>()
                        .as_slice(),
                )?;

                let generics_map = custom_type
                    .generics
                    .iter()
                    .map(|generic| generic.1.clone())
                    .zip(generic_types.iter().cloned())
                    .collect::<HashMap<_, _>>();
                let mut has_wild_card = false;
                for (index, case) in cases.into_iter().enumerate() {
                    let mut temp_stack = stack.clone();
                    match case.pattern {
                        Pattern::Wildcard(name) => {
                            has_wild_card = true;
                            self.builder.position_at_end(else_block);
                            let n_push_types = case.body.type_definition.push_types.len();
                            let scope = scope.clone();
                            if let Some(name) = name {
                                scope.add_value(name, match_value.clone());
                            }
                            self.compile_ast(
                                scope,
                                &mut temp_stack,
                                *case.body,
                                module_path.clone(),
                            )?;
                            self.builder.build_unconditional_branch(merge_block)?;
                            let bb = self
                                .builder
                                .get_insert_block()
                                .ok_or(CompilerError::IfWithoutFunction)?;
                            values_and_blocks.push((temp_stack.pop_n(n_push_types), bb));
                        }
                        Pattern::Variant {
                            variant_name,
                            fields,
                        } => {
                            self.builder
                                .position_at_end(case_blocks[index_to_variant_index[&index]]);
                            let n_push_types = case.body.type_definition.push_types.len();
                            let variant = custom_type
                                .variants
                                .iter()
                                .find(|v| Some(&v.0) == variant_name.last())
                                .expect("The variant should always exist")
                                .clone();
                            let struct_type = custom_type_variant_struct(
                                variant.clone(),
                                generics_map.clone(),
                                &self,
                            )?;

                            let scope = scope.clone();
                            for field in fields {
                                let field_index = variant
                                    .1
                                    .iter()
                                    .position(|f| f.0 == field.name)
                                    .expect("We should always find the field");
                                let ptr_field_ptr = self.builder.build_struct_gep(
                                    struct_type,
                                    match_ptr,
                                    (field_index + 1) as u32,
                                    "field_ptr",
                                )?;
                                let field_value = self.builder.build_load(
                                    struct_type
                                        .get_field_type_at_index(field_index as u32)
                                        .expect("We know that this field exists"),
                                    ptr_field_ptr,
                                    "field_value",
                                )?;
                                let ty = &variant.1[field_index].1;
                                let ty = match ty {
                                    UnitType::Var(var) => generics_map.get(var).unwrap_or(ty),
                                    _ => ty,
                                };
                                scope.add_value(field.alias, (ty.clone(), field_value));
                            }
                            self.compile_ast(
                                scope,
                                &mut temp_stack,
                                *case.body,
                                module_path.clone(),
                            )?;
                            self.builder.build_unconditional_branch(merge_block)?;
                            let bb = self
                                .builder
                                .get_insert_block()
                                .ok_or(CompilerError::IfWithoutFunction)?;
                            values_and_blocks.push((temp_stack.pop_n(n_push_types), bb));
                        }
                        _ => panic!("Unsupported variant type"),
                    }
                }

                if !has_wild_card {
                    self.builder.position_at_end(else_block);
                    self.builder.build_unconditional_branch(merge_block)?;
                }

                self.builder.position_at_end(merge_block);
                let mut values_for_phi = Vec::new();
                for (values, block) in values_and_blocks.iter() {
                    for (index, value) in values.iter().enumerate() {
                        if values_for_phi.get(index).is_none() {
                            values_for_phi
                                .push(((value.0.clone(), value.1.get_type()), Vec::new()));
                        }
                        values_for_phi[index]
                            .1
                            .push((&value.1 as &dyn BasicValue, block.clone()));
                    }
                }
                for (ty, values) in values_for_phi.into_iter() {
                    let phi = self.builder.build_phi(ty.1, "phi").unwrap();
                    phi.add_incoming(values.as_slice());
                    stack.push((ty.0, phi.as_basic_value()));
                }
                Ok(())
            }
            other => return Err(CompilerError::UnsupportedType(other)),
        }
    }

    fn get_type(&self, name: Vec<String>) -> Option<CustomType> {
        self.type_definitions.get(&name).cloned()
    }
}

fn custom_type_variant_struct<'ctx>(
    variant: (String, Vec<(String, UnitType)>),
    generics_map: HashMap<VarType, UnitType>,
    compiler_context: &CompilerContext<'ctx>,
) -> Result<StructType<'ctx>, CompilerError> {
    let mut fields = vec![compiler_context.context.i8_type().into()];
    variant
        .1
        .iter()
        .try_for_each(|field| -> Result<(), CompilerError> {
            Ok(fields.push(
                compiler_context.unit_type_to_llvm_type(match &field.1 {
                    UnitType::Var(var) => generics_map
                        .get(var)
                        .ok_or(CompilerError::FunctionCallError)?,
                    other => other,
                })?,
            ))
        })?;
    Ok(compiler_context.context.struct_type(&fields, true))
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

    fn remove_all(&mut self) -> Vec<(UnitType, BasicValueEnum<'ctx>)> {
        std::mem::take(&mut self.stack)
    }

    fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }
}

pub type BoxDefinitionType<'ctx> =
    Box<dyn Fn(&CompilerContext<'ctx>, &mut Stack<'ctx>) -> Result<(), CompilerError> + 'ctx>;
pub type DefinitionType<'ctx> = Rc<BoxDefinitionType<'ctx>>;

#[derive(Clone)]
pub struct Scope<'ctx> {
    scope: Rc<RefCell<InternalScope<'ctx>>>,
}

struct InternalScope<'ctx> {
    definitions: HashMap<
        String,
        (
            Option<
                Box<
                    dyn (Fn(
                            Type,
                            &mut CompilerContext<'ctx>,
                            Rc<RefCell<Vec<(Type, DefinitionType<'ctx>)>>>,
                        ) -> Result<(), CompilerError>)
                        + 'ctx,
                >,
            >,
            Rc<RefCell<Vec<(Type, DefinitionType<'ctx>)>>>,
        ),
    >,
    external_definitions: HashMap<String, Type>,
    imported: HashMap<String, Scope<'ctx>>,
    imported_functions: HashMap<String, (String, String)>,
    values: HashMap<String, (UnitType, BasicValueEnum<'ctx>)>,
    parent: Option<Scope<'ctx>>,
    id: u64,
}

static SCOPE_ID: AtomicU64 = AtomicU64::new(0);

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

                if let Some(value) = inner.values.get(&last) {
                    stack.push(value.clone());
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
                if let Some(from_definitions) = inner
                    .external_definitions
                    .get(&last)
                    .cloned()
                    .and_then(|_| {
                        Some(call_function(
                            context,
                            stack,
                            last.clone(),
                            last.clone(),
                            ty.clone(),
                        ))
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
                if let Some(parent) = inner.parent.as_ref() {
                    symbol.insert(0, first);
                    return parent.call_symbol(symbol, context, ty, stack);
                }

                Err(CompilerError::UndefinedSymbol(symbol.join("::")))
            }
        }
    }

    fn add_value(&self, name: String, value: (UnitType, BasicValueEnum<'ctx>)) {
        let mut inner = self.scope.borrow_mut();
        inner.values.insert(name, value);
    }

    fn add_import(&self, alias: String, scope: Scope<'ctx>) {
        let mut inner = self.scope.borrow_mut();
        inner.imported.insert(alias, scope);
    }

    fn add_function_import(&self, alias: String, real_name: String, module_alias: String) {
        let mut inner = self.scope.borrow_mut();
        inner
            .imported_functions
            .insert(alias, (real_name, module_alias));
    }

    fn add_function_definition(
        &self,
        symbol: &str,
        creator: Box<
            dyn (Fn(
                    Type,
                    &mut CompilerContext<'ctx>,
                    Rc<RefCell<Vec<(Type, DefinitionType<'ctx>)>>>,
                ) -> Result<(), CompilerError>)
                + 'ctx,
        >,
    ) {
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
        return Ok(());
    }
    // params.into_iter().try_for_each(|param| {
    //     compiler_context.drop_value(
    //         param
    //             .try_into()
    //             .expect("Created from a basic value enum. Should never fail"),
    //     )
    // })?;

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

#[derive(Debug, Error)]
pub enum CompilerError {
    #[error(transparent)]
    Parser(#[from] ParserError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
    #[error(transparent)]
    TypeChecker(#[from] TypeCheckerError),
    #[error("Failed to write LLVM IR to file: {0}")]
    WriteLLVMError(String),
    #[error("Stack underflow")]
    StackUnderflow,
    #[error("Builder error: {0}")]
    BuilderError(#[from] BuilderError),
    #[error("Failed to get function: {0}")]
    GetFunctionError(String),
    #[error("Undefined symbol: {0}")]
    UndefinedSymbol(String),
    #[error("Invalid stack for function {0}")]
    InvalidStackForFunction(String),
    #[error("Function call error")]
    FunctionCallError,
    #[error("Unexpected type")]
    UnexpectedType,
    #[error("If statement without function")]
    IfWithoutFunction,
    #[error("Invalid import type at {0}")]
    InvalidImportType(Position),
    #[error("Import not found")]
    ImportNotFound,
    #[error("Unsupported type")]
    UnsupportedType(UnitType),
}
