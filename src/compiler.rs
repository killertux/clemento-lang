use std::{
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
    types::{BasicMetadataTypeEnum, BasicTypeEnum, StructType},
    values::{BasicValue, BasicValueEnum, FunctionValue},
};
use thiserror::Error;

use crate::{
    internal_functions::{InternalFunction, builtins_functions},
    lexer::{IntegerNumber, Number, Position},
    parser::{
        AstNode, AstNodeType, LiteralType, NumberType, Parser, ParserError, Type, UnitType, VarType,
    },
    type_checker::{AstNodeWithType, TypeCheckerError, type_check},
};

pub struct CompilerContext<'ctx> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub internal_functions: Vec<InternalFunction<'ctx>>,
}

pub fn compile(file: impl AsRef<Path>) -> Result<PathBuf, CompilerError> {
    let path_as_string = file.as_ref().display().to_string();
    let file_content = read_to_string(file.as_ref())?;

    let program = Parser::new_from_file(&file_content, path_as_string)
        .collect::<Result<Vec<AstNode>, ParserError>>()?;
    let program = type_check(
        AstNode {
            node_type: AstNodeType::Block(program),
            position: Position::default(),
            type_definition: None,
        },
        true,
    )?;
    let context = Context::create();
    let mut stack = Stack::new();

    let compiler_context = CompilerContext::new(&context);
    let mut scope = Scope::empty();
    compiler_context.compile_ast(&mut scope, &mut stack, program.0)?;

    let mut output_path = file.as_ref().to_path_buf();
    output_path.set_extension("ll");
    compiler_context
        .module
        .print_to_file(&output_path)
        .map_err(|err| CompilerError::WriteLLVMError(err.to_string()))?;
    Ok(output_path)
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
        }
    }

    fn compile_ast(
        &self,
        scope: &mut Scope<'_, 'ctx>,
        stack: &mut Stack<'ctx>,
        program: AstNodeWithType,
    ) -> Result<(), CompilerError> {
        match program.node_type {
            AstNodeType::Number(number) => self.compile_number(stack, number),
            AstNodeType::String(string) => self.compile_string(stack, string),
            AstNodeType::Boolean(boolean) => self.compile_boolean(stack, boolean),
            AstNodeType::Symbol(symbol) => {
                scope.call_symbol(&symbol, self, program.type_definition, stack)?;
                Ok(())
            }
            AstNodeType::SymbolWithPath(_symbol) => {
                todo!()
            }
            AstNodeType::Block(nodes) => {
                let mut scope = Scope::with_parent(scope);
                for node in nodes {
                    self.compile_ast(&mut scope, stack, node)?;
                }
                Ok(())
            }
            AstNodeType::Definition(symbol, body) => self.compile_definition(scope, &symbol, *body),
            AstNodeType::ExternalDefinition(symbol, ty) => {
                for function in &self.internal_functions {
                    if function.name == symbol && match_types(&ty.pop_types, &function.ty.pop_types)
                    {
                        scope
                            .definitions
                            .entry(function.name.clone())
                            .or_default()
                            .push((function.ty.clone(), function.function.clone()));
                        return Ok(());
                    }
                }
                Err(CompilerError::UndefinedSymbol(symbol))
            }
            AstNodeType::If(true_body, false_body) => {
                self.compile_if(scope, *true_body, false_body, stack)
            }
            AstNodeType::Import(_path, import_nodes) => {
                for import_node in import_nodes {
                    let AstNodeType::Block(nodes) = import_node.node_type else {
                        return Err(CompilerError::InvalidImportType(program.position));
                    };
                    let mut import_scope = Scope::empty();
                    for node in nodes {
                        self.compile_ast(&mut import_scope, stack, node)?;
                    }
                    scope.imported.push(import_scope);
                }
                Ok(())
            }
        }
    }

    fn compile_number(&self, stack: &mut Stack<'ctx>, number: Number) -> Result<(), CompilerError> {
        stack.push(match number {
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
        });
        Ok(())
    }

    fn compile_definition(
        &self,
        scope: &mut Scope<'_, 'ctx>,
        symbol: &str,
        body: AstNodeWithType,
    ) -> Result<(), CompilerError> {
        let function_type = self.get_llvm_function_type(&body.type_definition)?;
        let function_name = if symbol == "main" {
            "main".into()
        } else {
            format!("{}_{}_{}", body.type_definition, symbol, scope.id)
        };
        let function_type = if symbol == "main" {
            self.context.i32_type().fn_type(&[], false)
        } else {
            function_type
        };
        let function = self
            .module
            .add_function(&function_name, function_type, None); // TODO: Handle name clashes. Probably name the function based on the scope
        let ty = body.type_definition.clone();
        scope.add_definition(symbol, function, ty.clone());

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

        self.compile_ast(scope, &mut stack, body)?;

        match function_type.get_return_type() {
            Some(_) => {
                let return_type = self.get_return_type(&ty)?;
                if symbol == "main" {
                    if ty.push_types.is_empty() {
                        self.builder.build_return(Some(
                            &self.context.i32_type().const_zero().as_basic_value_enum(),
                        ))?;
                        return Ok(());
                    }
                    if ty.push_types.len() == 1 {
                        self.builder.build_return(Some(
                            &stack.pop().ok_or(CompilerError::StackUnderflow)?.1,
                        ))?;
                        return Ok(());
                    }
                }
                let return_val = stack.remove_all();
                let struct_ptr = self
                    .builder
                    .build_alloca(return_type, &format!("{}_return_type", symbol))?;
                for (index, field) in return_val.into_iter().enumerate() {
                    let field_ptr = self.builder.build_struct_gep(
                        return_type,
                        struct_ptr,
                        index as u32,
                        &format!("field_{}", index),
                    )?;
                    self.builder.build_store(field_ptr, field.1)?;
                }
                self.builder
                    .build_return(Some(&struct_ptr.as_basic_value_enum()))?;
            }
            None => {
                if !stack.is_empty() {
                    return Err(CompilerError::InvalidStackForFunction(symbol.into()));
                }
                self.builder.build_return(None)?;
            }
        }

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
        Ok(self
            .context
            .ptr_type(AddressSpace::default())
            .fn_type(&param_types, false))
    }

    fn get_return_type(&self, type_def: &Type) -> Result<StructType<'ctx>, CompilerError> {
        let mut return_types = Vec::new();
        for push_types in &type_def.push_types {
            return_types.push(self.unit_type_to_llvm_type(push_types)?);
        }
        Ok(self.context.struct_type(&return_types, true))
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
        }
    }

    fn compile_string(&self, stack: &mut Stack<'ctx>, string: String) -> Result<(), CompilerError> {
        let value = self.builder.build_global_string_ptr(&string, "str")?;
        stack.push((
            UnitType::Literal(LiteralType::String),
            value.as_pointer_value().into(),
        ));
        Ok(())
    }

    fn compile_boolean(&self, stack: &mut Stack<'ctx>, boolean: bool) -> Result<(), CompilerError> {
        let value = self.context.bool_type().const_int(boolean as u64, false);
        stack.push((UnitType::Literal(LiteralType::Boolean), value.into()));
        Ok(())
    }

    fn compile_if(
        &self,
        scope: &mut Scope<'_, 'ctx>,
        true_body: AstNodeWithType,
        false_body: Option<Box<AstNodeWithType>>,
        stack: &mut Stack<'ctx>,
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
                self.compile_ast(scope, &mut true_stack, true_body)?;
                let true_values = true_stack.pop_n(push_types_len);
                self.builder.build_unconditional_branch(merge_block)?;
                let true_end_bb = self
                    .builder
                    .get_insert_block()
                    .ok_or(CompilerError::IfWithoutFunction)?;

                self.builder.position_at_end(false_block);
                self.compile_ast(scope, stack, *false_body)?;
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
                self.compile_ast(scope, stack, true_body)?;
                self.builder.build_unconditional_branch(merge_block)?;

                self.builder.position_at_end(merge_block);
            }
        }
        Ok(())
    }
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

pub struct Scope<'a, 'ctx> {
    definitions: HashMap<String, Vec<(Type, DefinitionType<'ctx>)>>,
    imported: Vec<Scope<'a, 'ctx>>,
    parent: Option<&'a Scope<'a, 'ctx>>,
    id: u64,
}

static SCOPE_ID: AtomicU64 = AtomicU64::new(0);

impl<'a, 'ctx> Scope<'a, 'ctx> {
    fn with_parent(parent: &'a Scope<'a, 'ctx>) -> Self {
        Self {
            definitions: HashMap::new(),
            imported: Vec::new(),
            parent: Some(parent),
            id: SCOPE_ID.fetch_add(1, Ordering::Relaxed),
        }
    }

    fn call_symbol(
        &self,
        symbol: &str,
        context: &CompilerContext<'ctx>,
        ty: Type,
        stack: &mut Stack<'ctx>,
    ) -> Result<(), CompilerError> {
        self.definitions
            .get(symbol)
            .and_then(|closures| {
                for (ty_closure, closure) in closures {
                    if match_types(&ty.pop_types, &ty_closure.pop_types) {
                        return Some(closure(context, stack));
                    }
                }
                None
            })
            .or_else(|| {
                for imported in &self.imported {
                    let value = imported.call_symbol(symbol, context, ty.clone(), stack);
                    if let Err(CompilerError::UndefinedSymbol(_)) = value {
                        continue;
                    }
                    return Some(value);
                }
                None
            })
            .or_else(|| {
                self.parent
                    .map(|parent| parent.call_symbol(symbol, context, ty, stack))
            })
            .ok_or(CompilerError::UndefinedSymbol(symbol.into()))?
    }

    fn add_definition(&mut self, symbol: &str, function: FunctionValue<'ctx>, ty: Type) {
        let symbol_name = symbol.to_string();
        let function_name = function.get_name().to_string_lossy().to_string();
        let param_count = function.get_params().len();

        self.definitions
            .entry(symbol_name.clone())
            .or_default()
            .push((
                ty.clone(),
                Rc::new(Box::new(
                    move |compiler_context: &CompilerContext<'ctx>,
                          stack: &mut Stack<'ctx>|
                          -> Result<(), CompilerError> {
                        let params = stack.pop_n(param_count);
                        if params.len() != param_count {
                            return Err(CompilerError::StackUnderflow);
                        }

                        let function = compiler_context
                            .module
                            .get_function(&function_name)
                            .ok_or(CompilerError::FunctionCallError)?;

                        let call = compiler_context.builder.build_call(
                            function,
                            &params
                                .into_iter()
                                .map(|param| param.1.into())
                                .collect::<Vec<_>>(),
                            &format!("{}_call", symbol_name),
                        )?;

                        let value = call.try_as_basic_value();
                        if value.is_right() {
                            return Ok(());
                        }
                        let value = value.left().ok_or(CompilerError::FunctionCallError)?;
                        let struct_value = value.into_pointer_value();
                        let struct_type = compiler_context.get_return_type(&ty)?;

                        for (index, field_type) in ty.push_types.iter().enumerate() {
                            let field_ptr = compiler_context.builder.build_struct_gep(
                                struct_type,
                                struct_value,
                                index as u32,
                                &format!("field_{}", index),
                            )?;
                            let field_value = compiler_context.builder.build_load(
                                compiler_context.unit_type_to_llvm_type(field_type)?,
                                field_ptr,
                                &format!("field_{}_value", index),
                            )?;
                            stack.push((field_type.clone(), field_value));
                        }
                        Ok(())
                    },
                )),
            ));
    }

    fn empty() -> Scope<'a, 'ctx> {
        Scope {
            parent: None,
            imported: Vec::new(),
            definitions: HashMap::new(),
            id: SCOPE_ID.fetch_add(1, Ordering::Relaxed),
        }
    }
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
}
