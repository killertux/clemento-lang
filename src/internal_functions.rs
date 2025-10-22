use std::rc::Rc;

use inkwell::{
    AddressSpace, IntPredicate, context::Context, module::Module, values::BasicValueEnum,
};

use crate::{
    compiler::{BoxDefinitionType, CompilerContext, CompilerError, DefinitionType, Stack},
    parser::{LiteralType, NumberType, Type, UnitType, VarType},
};

#[derive(Clone)]
pub struct InternalFunction<'ctx> {
    pub name: String,
    pub ty: Type,
    pub function: DefinitionType<'ctx>,
}

pub fn builtins_functions<'ctx>(
    context: &'ctx Context,
    module: &Module<'ctx>,
) -> Vec<InternalFunction<'ctx>> {
    let ptr_type = context.ptr_type(AddressSpace::default());
    let printf_type = context.i32_type().fn_type(&[ptr_type.into()], true);
    module.add_function("printf", printf_type, None);
    let strcmp_type = context
        .i32_type()
        .fn_type(&[ptr_type.into(), ptr_type.into()], false);
    module.add_function("strcmp", strcmp_type, None);
    let sprintf_type = context
        .i32_type()
        .fn_type(&[ptr_type.into(), ptr_type.into()], true);
    module.add_function("sprintf", sprintf_type, None);
    let strlen_type = context.i64_type().fn_type(&[ptr_type.into()], false);
    module.add_function("strlen", strlen_type, None);

    let all_integer_types = vec![
        UnitType::Literal(LiteralType::Number(NumberType::U8)),
        UnitType::Literal(LiteralType::Number(NumberType::U16)),
        UnitType::Literal(LiteralType::Number(NumberType::U32)),
        UnitType::Literal(LiteralType::Number(NumberType::U64)),
        UnitType::Literal(LiteralType::Number(NumberType::U128)),
        UnitType::Literal(LiteralType::Number(NumberType::I8)),
        UnitType::Literal(LiteralType::Number(NumberType::I16)),
        UnitType::Literal(LiteralType::Number(NumberType::I32)),
        UnitType::Literal(LiteralType::Number(NumberType::I64)),
        UnitType::Literal(LiteralType::Number(NumberType::I128)),
    ];

    let mut all_number_types = all_integer_types.clone();
    all_number_types.push(UnitType::Literal(LiteralType::Number(NumberType::F64)));

    let mut all_literal_types = all_number_types.clone();
    all_literal_types.push(UnitType::Literal(LiteralType::String));
    all_literal_types.push(UnitType::Literal(LiteralType::Boolean));

    [
        vec![InternalFunction {
            name: "concat".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::String),
                    UnitType::Literal(LiteralType::String),
                ],
                vec![UnitType::Literal(LiteralType::String)],
            ),
            function: Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let value2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (value2, value1) {
                        (
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(p1),
                            ),
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(p2),
                            ),
                        ) => {
                            let output_buffer = compiler_context.builder.build_alloca(
                                compiler_context.context.i8_type().array_type(1024),
                                "output_buffer",
                            )?;
                            let format_str = compiler_context
                                .builder
                                .build_global_string_ptr("%s%s", "concat_fmt")?
                                .as_pointer_value();
                            let sprintf = compiler_context
                                .module
                                .get_function("sprintf")
                                .ok_or(CompilerError::GetFunctionError("sprintf".into()))?;
                            compiler_context.builder.build_call(
                                sprintf,
                                &[
                                    output_buffer.into(),
                                    format_str.into(),
                                    p1.into(),
                                    p2.into(),
                                ],
                                "call_sprintf",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::String),
                                output_buffer.into(),
                            ));
                        }
                        _other => return Err(CompilerError::FunctionCallError),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        pop1_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::String)),
            "String".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let format_str = get_format_str(value.0)?;
                    let output_buffer = compiler_context.builder.build_alloca(
                        compiler_context.context.i8_type().array_type(40),
                        "output_buffer",
                    )?;
                    let format_str = compiler_context
                        .builder
                        .build_global_string_ptr(format_str, "int_fmt")?
                        .as_pointer_value();
                    let sprintf = compiler_context
                        .module
                        .get_function("sprintf")
                        .ok_or(CompilerError::GetFunctionError("sprintf".into()))?;
                    compiler_context.builder.build_call(
                        sprintf,
                        &[output_buffer.into(), format_str.into(), value.1.into()],
                        "call_sprintf",
                    )?;
                    stack.push((UnitType::Literal(LiteralType::String), output_buffer.into()));
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop1_push0(
            &all_literal_types,
            "print".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let format_str = get_format_str(value.0)?;
                    let format_str = compiler_context
                        .builder
                        .build_global_string_ptr(format_str, "int_fmt")?
                        .as_pointer_value();
                    let printf = compiler_context
                        .module
                        .get_function("printf")
                        .ok_or(CompilerError::GetFunctionError("printf".into()))?;
                    compiler_context.builder.build_call(
                        printf,
                        &[format_str.into(), value.1.into()],
                        "printf_call",
                    )?;
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop1_push0(
            &all_literal_types,
            "println".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let format_str = format!("{}\n", get_format_str(value.0)?);
                    let format_str = compiler_context
                        .builder
                        .build_global_string_ptr(&format_str, "int_fmt")?
                        .as_pointer_value();
                    let printf = compiler_context
                        .module
                        .get_function("printf")
                        .ok_or(CompilerError::GetFunctionError("printf".into()))?;
                    compiler_context.builder.build_call(
                        printf,
                        &[format_str.into(), value.1.into()],
                        "printf_call",
                    )?;
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        vec![InternalFunction {
            name: "dup".into(),
            ty: {
                let var = VarType::new();
                Type::new(
                    vec![UnitType::Var(var.clone())],
                    vec![UnitType::Var(var.clone()), UnitType::Var(var.clone())],
                )
            },
            function: Rc::new(Box::new(
                |_compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    stack.push(value.clone());
                    stack.push(value.clone());
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        vec![InternalFunction {
            name: "touch".into(),
            ty: {
                let var = VarType::new();
                Type::new(
                    vec![UnitType::Var(var.clone())],
                    vec![UnitType::Var(var.clone())],
                )
            },
            function: Rc::new(Box::new(
                |_compiler_context: &CompilerContext<'ctx>,
                 _stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> { Ok(()) },
            ) as BoxDefinitionType<'ctx>),
        }],
        vec![InternalFunction {
            name: "dup2".into(),
            ty: {
                let var1 = VarType::new();
                let var2 = VarType::new();
                Type::new(
                    vec![UnitType::Var(var1.clone()), UnitType::Var(var2.clone())],
                    vec![
                        UnitType::Var(var1.clone()),
                        UnitType::Var(var2.clone()),
                        UnitType::Var(var1.clone()),
                        UnitType::Var(var2.clone()),
                    ],
                )
            },
            function: Rc::new(Box::new(
                |_compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let value2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;

                    stack.push(value2.clone());
                    stack.push(value1.clone());
                    stack.push(value2.clone());
                    stack.push(value1.clone());
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        vec![InternalFunction {
            name: "swap".into(),
            ty: {
                let var1 = VarType::new();
                let var2 = VarType::new();
                Type::new(
                    vec![UnitType::Var(var1.clone()), UnitType::Var(var2.clone())],
                    vec![UnitType::Var(var2.clone()), UnitType::Var(var1.clone())],
                )
            },
            function: Rc::new(Box::new(
                |_compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let value2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;

                    stack.push(value1.clone());
                    stack.push(value2.clone());
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        vec![InternalFunction {
            name: "rot".into(),
            ty: {
                let var1 = VarType::new();
                let var2 = VarType::new();
                let var3 = VarType::new();
                Type::new(
                    vec![
                        UnitType::Var(var1.clone()),
                        UnitType::Var(var2.clone()),
                        UnitType::Var(var3.clone()),
                    ],
                    vec![
                        UnitType::Var(var2.clone()),
                        UnitType::Var(var3.clone()),
                        UnitType::Var(var1.clone()),
                    ],
                )
            },
            function: Rc::new(Box::new(
                |_compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let value2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let value3 = stack.pop().ok_or(CompilerError::StackUnderflow)?;

                    stack.push(value2.clone());
                    stack.push(value1.clone());
                    stack.push(value3.clone());
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        vec![InternalFunction {
            name: "drop".into(),
            ty: Type::new(vec![UnitType::Var(VarType::new())], vec![]),
            function: Rc::new(Box::new(
                |_compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let _ = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        vec![InternalFunction {
            name: "drop2".into(),
            ty: Type::new(
                vec![UnitType::Var(VarType::new()), UnitType::Var(VarType::new())],
                vec![],
            ),
            function: Rc::new(Box::new(
                |_compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let _ = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let _ = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        vec![InternalFunction {
            name: "&&".into(),
            ty: {
                Type::new(
                    vec![
                        UnitType::Literal(LiteralType::Boolean),
                        UnitType::Literal(LiteralType::Boolean),
                    ],
                    vec![UnitType::Literal(LiteralType::Boolean)],
                )
            },
            function: Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg1, arg2) {
                        (
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n1)),
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n2)),
                        ) => {
                            let result =
                                compiler_context.builder.build_and(n1, n2, "and_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::FunctionCallError),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        pop2_push1(
            &all_number_types,
            None,
            "+".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg1, arg2) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_add(n1, n2, "add_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop2_push1(
            &all_number_types,
            None,
            "-".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg2, arg1) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_sub(n1, n2, "sub_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop2_push1(
            &all_number_types,
            None,
            "*".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg1, arg2) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_mul(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop2_push1(
            &all_number_types,
            None,
            "/".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg2, arg1) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_unsigned_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_unsigned_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_unsigned_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_unsigned_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_unsigned_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_signed_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_signed_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_signed_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_signed_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_signed_div(
                                n1,
                                n2,
                                "mul_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_div(n1, n2, "mul_result")?;
                            stack.push((
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        rem(),
        pop2_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            ">".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg2, arg1) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::UGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::UGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::UGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::UGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::UGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_float_compare(
                                inkwell::FloatPredicate::OGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n1)),
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n2)),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::UGT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n2),
                            ),
                        ) => {
                            let strcmp_fn = compiler_context
                                .module
                                .get_function("strcmp")
                                .ok_or(CompilerError::FunctionCallError)?;

                            let strcmp_result = compiler_context
                                .builder
                                .build_call(strcmp_fn, &[n1.into(), n2.into()], "strcmp_call")?
                                .try_as_basic_value()
                                .left()
                                .unwrap()
                                .into_int_value();

                            let zero = compiler_context.context.i32_type().const_zero();
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SGT,
                                strcmp_result,
                                zero,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop2_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            "<".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg2, arg1) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::ULT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::ULT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::ULT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::ULT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::ULT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SLT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SLT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SLT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SLT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SLT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_float_compare(
                                inkwell::FloatPredicate::OLT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n1)),
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n2)),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::ULT,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n2),
                            ),
                        ) => {
                            let strcmp_fn = compiler_context
                                .module
                                .get_function("strcmp")
                                .ok_or(CompilerError::FunctionCallError)?;

                            let strcmp_result = compiler_context
                                .builder
                                .build_call(strcmp_fn, &[n1.into(), n2.into()], "strcmp_call")?
                                .try_as_basic_value()
                                .left()
                                .unwrap()
                                .into_int_value();

                            let zero = compiler_context.context.i32_type().const_zero();
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::SLT,
                                strcmp_result,
                                zero,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop2_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            "=".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg2, arg1) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "eq_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_float_compare(
                                inkwell::FloatPredicate::OEQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n1)),
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n2)),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n2),
                            ),
                        ) => {
                            let strcmp_fn = compiler_context
                                .module
                                .get_function("strcmp")
                                .ok_or(CompilerError::FunctionCallError)?;

                            let strcmp_result = compiler_context
                                .builder
                                .build_call(strcmp_fn, &[n1.into(), n2.into()], "strcmp_call")?
                                .try_as_basic_value()
                                .left()
                                .unwrap()
                                .into_int_value();

                            let zero = compiler_context.context.i32_type().const_zero();
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::EQ,
                                strcmp_result,
                                zero,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        pop2_push1(
            &all_literal_types,
            Some(UnitType::Literal(LiteralType::Boolean)),
            "!=".into(),
            Rc::new(Box::new(
                |compiler_context: &CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    match (arg2, arg1) {
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::U128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I8)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I16)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I32)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I64)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::I128)),
                                BasicValueEnum::IntValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::Number(NumberType::F64)),
                                BasicValueEnum::FloatValue(n2),
                            ),
                        ) => {
                            let result = compiler_context.builder.build_float_compare(
                                inkwell::FloatPredicate::ONE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n1)),
                            (UnitType::Literal(LiteralType::Boolean), BasicValueEnum::IntValue(n2)),
                        ) => {
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                n1,
                                n2,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        (
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n1),
                            ),
                            (
                                UnitType::Literal(LiteralType::String),
                                BasicValueEnum::PointerValue(n2),
                            ),
                        ) => {
                            let strcmp_fn = compiler_context
                                .module
                                .get_function("strcmp")
                                .ok_or(CompilerError::FunctionCallError)?;

                            let strcmp_result = compiler_context
                                .builder
                                .build_call(strcmp_fn, &[n1.into(), n2.into()], "strcmp_call")?
                                .try_as_basic_value()
                                .left()
                                .unwrap()
                                .into_int_value();

                            let zero = compiler_context.context.i32_type().const_zero();
                            let result = compiler_context.builder.build_int_compare(
                                IntPredicate::NE,
                                strcmp_result,
                                zero,
                                "gt_result",
                            )?;
                            stack.push((
                                UnitType::Literal(LiteralType::Boolean),
                                BasicValueEnum::IntValue(result),
                            ));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
    ]
    .concat()
}

fn rem<'ctx>() -> Vec<InternalFunction<'ctx>> {
    let function = Rc::new(Box::new(
        |compiler_context: &CompilerContext<'ctx>,
         stack: &mut Stack<'ctx>|
         -> Result<(), CompilerError> {
            let i8_type = compiler_context.context.i8_type();
            let i16_type = compiler_context.context.i16_type();
            let i32_type = compiler_context.context.i32_type();
            let i64_type = compiler_context.context.i64_type();
            let i128_type = compiler_context.context.i128_type();
            let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
            let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
            match (arg2, arg1) {
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_z_extend(n2, i16_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_z_extend(n2, i32_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_z_extend(n2, i32_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_z_extend(n2, i64_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_z_extend(n2, i64_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_z_extend(n2, i64_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_z_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_z_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_z_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_z_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i64_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::U128)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_unsigned_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U128)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_s_extend(n2, i16_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_s_extend(n2, i32_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_s_extend(n2, i32_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_s_extend(n2, i64_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_s_extend(n2, i64_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 =
                        compiler_context
                            .builder
                            .build_int_s_extend(n2, i64_type, "upcast_type")?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_s_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_s_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_s_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let n2 = compiler_context.builder.build_int_s_extend(
                        n2,
                        i128_type,
                        "upcast_type",
                    )?;
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    compiler_context.builder.build_int_truncate(
                        result,
                        i64_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                (
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I128)),
                        BasicValueEnum::IntValue(n1),
                    ),
                    (
                        UnitType::Literal(LiteralType::Number(NumberType::I128)),
                        BasicValueEnum::IntValue(n2),
                    ),
                ) => {
                    let result =
                        compiler_context
                            .builder
                            .build_int_signed_rem(n1, n2, "rem_result")?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I128)),
                        BasicValueEnum::IntValue(result),
                    ));
                }
                _ => return Err(CompilerError::UnexpectedType),
            }
            Ok(())
        },
    ) as BoxDefinitionType<'ctx>);
    vec![
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U8)),
                    UnitType::Literal(LiteralType::Number(NumberType::U8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U16)),
                    UnitType::Literal(LiteralType::Number(NumberType::U8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U16)),
                    UnitType::Literal(LiteralType::Number(NumberType::U16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U32)),
                    UnitType::Literal(LiteralType::Number(NumberType::U8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U32)),
                    UnitType::Literal(LiteralType::Number(NumberType::U16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U32)),
                    UnitType::Literal(LiteralType::Number(NumberType::U32)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U32))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U64)),
                    UnitType::Literal(LiteralType::Number(NumberType::U8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U64)),
                    UnitType::Literal(LiteralType::Number(NumberType::U16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U64)),
                    UnitType::Literal(LiteralType::Number(NumberType::U32)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U32))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U64)),
                    UnitType::Literal(LiteralType::Number(NumberType::U64)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U64))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U128)),
                    UnitType::Literal(LiteralType::Number(NumberType::U8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U128)),
                    UnitType::Literal(LiteralType::Number(NumberType::U16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U128)),
                    UnitType::Literal(LiteralType::Number(NumberType::U32)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U32))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U128)),
                    UnitType::Literal(LiteralType::Number(NumberType::U64)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U64))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::U128)),
                    UnitType::Literal(LiteralType::Number(NumberType::U128)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::U128))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I8)),
                    UnitType::Literal(LiteralType::Number(NumberType::I8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I16)),
                    UnitType::Literal(LiteralType::Number(NumberType::I8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I16)),
                    UnitType::Literal(LiteralType::Number(NumberType::I16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I32)),
                    UnitType::Literal(LiteralType::Number(NumberType::I8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I32)),
                    UnitType::Literal(LiteralType::Number(NumberType::I16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I32)),
                    UnitType::Literal(LiteralType::Number(NumberType::I32)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I32))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I64)),
                    UnitType::Literal(LiteralType::Number(NumberType::I8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I64)),
                    UnitType::Literal(LiteralType::Number(NumberType::I16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I64)),
                    UnitType::Literal(LiteralType::Number(NumberType::I32)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I32))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I64)),
                    UnitType::Literal(LiteralType::Number(NumberType::I64)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I64))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I128)),
                    UnitType::Literal(LiteralType::Number(NumberType::I8)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I8))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I128)),
                    UnitType::Literal(LiteralType::Number(NumberType::I16)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I16))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I128)),
                    UnitType::Literal(LiteralType::Number(NumberType::I32)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I32))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I128)),
                    UnitType::Literal(LiteralType::Number(NumberType::I64)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I64))],
            ),
            function: function.clone(),
        },
        InternalFunction {
            name: "%".into(),
            ty: Type::new(
                vec![
                    UnitType::Literal(LiteralType::Number(NumberType::I128)),
                    UnitType::Literal(LiteralType::Number(NumberType::I128)),
                ],
                vec![UnitType::Literal(LiteralType::Number(NumberType::I128))],
            ),
            function: function.clone(),
        },
    ]
}

fn get_format_str(value: UnitType) -> Result<&'static str, CompilerError> {
    let format_str = match value {
        UnitType::Literal(LiteralType::Number(NumberType::U8)) => "%hhu",
        UnitType::Literal(LiteralType::Number(NumberType::I8)) => "%hhi",
        UnitType::Literal(LiteralType::Number(NumberType::U16)) => "%hu",
        UnitType::Literal(LiteralType::Number(NumberType::I16)) => "%hi",
        UnitType::Literal(LiteralType::Number(NumberType::U32)) => "%u",
        UnitType::Literal(LiteralType::Number(NumberType::I32)) => "%i",
        UnitType::Literal(LiteralType::Number(NumberType::U64)) => "%llu",
        UnitType::Literal(LiteralType::Number(NumberType::I64)) => "%lli",
        UnitType::Literal(LiteralType::Number(NumberType::U128)) => "%llu", //TODO We will need to implement a custom format specifier for u128
        UnitType::Literal(LiteralType::Number(NumberType::I128)) => "%lli",
        UnitType::Literal(LiteralType::Number(NumberType::F64)) => "%f",
        UnitType::Literal(LiteralType::String) => "%s",
        UnitType::Literal(LiteralType::Boolean) => "%d",
        _other => return Err(CompilerError::FunctionCallError),
    };
    Ok(format_str)
}

fn pop1_push0<'ctx>(
    types: &[UnitType],
    name: String,
    function: DefinitionType<'ctx>,
) -> Vec<InternalFunction<'ctx>> {
    let mut result = Vec::new();
    for ty in types {
        result.push(InternalFunction {
            name: name.clone(),
            ty: Type::new(vec![ty.clone()], vec![]),
            function: function.clone(),
        });
    }
    result
}

fn pop1_push1<'ctx>(
    types: &[UnitType],
    push_type: Option<UnitType>,
    name: String,
    function: DefinitionType<'ctx>,
) -> Vec<InternalFunction<'ctx>> {
    let mut result = Vec::new();
    for ty in types {
        result.push(InternalFunction {
            name: name.clone(),
            ty: Type::new(
                vec![ty.clone()],
                vec![push_type.clone().unwrap_or(ty.clone())],
            ),
            function: function.clone(),
        });
    }
    result
}

fn pop2_push1<'ctx>(
    pop_types: &[UnitType],
    push_type: Option<UnitType>,
    name: String,
    function: DefinitionType<'ctx>,
) -> Vec<InternalFunction<'ctx>> {
    let mut result = Vec::new();
    for ty in pop_types {
        result.push(InternalFunction {
            name: name.clone(),
            ty: Type::new(
                vec![ty.clone(), ty.clone()],
                vec![push_type.clone().unwrap_or(ty.clone())],
            ),
            function: function.clone(),
        });
    }
    result
}
