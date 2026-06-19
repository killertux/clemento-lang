use std::rc::Rc;

use inkwell::{
    AddressSpace, FloatPredicate, IntPredicate,
    values::{BasicValue, BasicValueEnum},
};

use crate::{
    compiler::{BoxDefinitionType, CompilerContext, CompilerError, DefinitionType, Stack},
    types::{LiteralType, NumberType, Type, UnitType, VarType},
};

#[derive(Clone)]
pub struct InternalFunction<'ctx> {
    pub name: String,
    pub ty: Type,
    pub function: DefinitionType<'ctx>,
}

pub fn builtins_functions<'ctx>(
    context: &mut CompilerContext<'ctx>,
) -> Vec<InternalFunction<'ctx>> {
    if context.module.get_function("printf").is_none() {
        let ptr_type = context.context.ptr_type(AddressSpace::default());
        let printf_type = context.context.i32_type().fn_type(&[ptr_type.into()], true);
        context.module.add_function("printf", printf_type, None);
        let strcmp_type = context
            .context
            .i32_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], false);
        context.module.add_function("strcmp", strcmp_type, None);
        let sprintf_type = context
            .context
            .i32_type()
            .fn_type(&[ptr_type.into(), ptr_type.into()], true);
        context.module.add_function("sprintf", sprintf_type, None);
        let strlen_type = context
            .context
            .i64_type()
            .fn_type(&[ptr_type.into()], false);
        context.module.add_function("strlen", strlen_type, None);
        let putchar_type = context
            .context
            .i32_type()
            .fn_type(&[context.context.i32_type().into()], false);
        context.module.add_function("putchar", putchar_type, None);
        // `putchar`'s stderr counterpart (linked from clem_runtime.c); same signature.
        context
            .module
            .add_function("clem_putchar_err", putchar_type, None);
        // Slab-pool allocator runtime (linked from clem_runtime.c).
        let clem_alloc_type = ptr_type.fn_type(&[context.context.i64_type().into()], false);
        context
            .module
            .add_function("clem_alloc", clem_alloc_type, None);
        let clem_free_type = context
            .context
            .void_type()
            .fn_type(&[ptr_type.into()], false);
        context
            .module
            .add_function("clem_free", clem_free_type, None);
        // FFI string marshalling (clem_runtime.c): String (List<Char>) <-> char*.
        let from_cstr_type = ptr_type.fn_type(&[ptr_type.into()], false);
        context
            .module
            .add_function("clem_string_from_cstr", from_cstr_type, None);
        let to_cstr_type = ptr_type.fn_type(&[ptr_type.into()], false);
        context
            .module
            .add_function("clem_string_to_cstr", to_cstr_type, None);
        // libc free, for releasing buffers produced by `ffi::to_cstr`.
        let free_type = context
            .context
            .void_type()
            .fn_type(&[ptr_type.into()], false);
        context.module.add_function("free", free_type, None);
    }

    let boolean_type = context
        .get_type(vec!["std".into(), "boolean".into(), "Boolean".into()])
        .map(|t| UnitType::Custom {
            name: t.name,
            generic_types: vec![],
        })
        .unwrap_or(UnitType::Var(VarType::new()));

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

    // Comparisons are defined for numbers only; strings (now `List<Char>`) are
    // compared in the standard library.
    let all_literal_types = all_number_types.clone();

    [
        vec![
            // `from_code_point (U32 -> Char)` and `to_code_point (Char -> U32)` are
            // no-op reinterpretations: a Char is just its i32 code point.
            InternalFunction {
                name: "from_code_point".into(),
                ty: Type::new(
                    vec![UnitType::Literal(LiteralType::Number(NumberType::U32))],
                    vec![UnitType::Literal(LiteralType::Char)],
                ),
                function: Rc::new(Box::new(
                    |_compiler_context: &mut CompilerContext<'ctx>,
                     stack: &mut Stack<'ctx>|
                     -> Result<(), CompilerError> {
                        let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                        stack.push((UnitType::Literal(LiteralType::Char), value.1));
                        Ok(())
                    },
                ) as BoxDefinitionType<'ctx>),
            },
            InternalFunction {
                name: "to_code_point".into(),
                ty: Type::new(
                    vec![UnitType::Literal(LiteralType::Char)],
                    vec![UnitType::Literal(LiteralType::Number(NumberType::U32))],
                ),
                function: Rc::new(Box::new(
                    |_compiler_context: &mut CompilerContext<'ctx>,
                     stack: &mut Stack<'ctx>|
                     -> Result<(), CompilerError> {
                        let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                        stack.push((
                            UnitType::Literal(LiteralType::Number(NumberType::U32)),
                            value.1,
                        ));
                        Ok(())
                    },
                ) as BoxDefinitionType<'ctx>),
            },
            InternalFunction {
                name: "print".into(),
                ty: Type::new(vec![UnitType::Literal(LiteralType::Char)], vec![]),
                function: Rc::new(Box::new(
                    |compiler_context: &mut CompilerContext<'ctx>,
                     stack: &mut Stack<'ctx>|
                     -> Result<(), CompilerError> {
                        let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                        compiler_context.emit_print_char(value.1.into_int_value())?;
                        Ok(())
                    },
                ) as BoxDefinitionType<'ctx>),
            },
            InternalFunction {
                name: "print_err".into(),
                ty: Type::new(vec![UnitType::Literal(LiteralType::Char)], vec![]),
                function: Rc::new(Box::new(
                    |compiler_context: &mut CompilerContext<'ctx>,
                     stack: &mut Stack<'ctx>|
                     -> Result<(), CompilerError> {
                        let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                        compiler_context
                            .emit_print_char_with(value.1.into_int_value(), "clem_putchar_err")?;
                        Ok(())
                    },
                ) as BoxDefinitionType<'ctx>),
            },
        ],
        vec![
            widen_cast(NumberType::U8, NumberType::U64, "to_u64", false),
            widen_cast(NumberType::U16, NumberType::U64, "to_u64", false),
            widen_cast(NumberType::U32, NumberType::U64, "to_u64", false),
            widen_cast(NumberType::I8, NumberType::I64, "to_i64", true),
            widen_cast(NumberType::I16, NumberType::I64, "to_i64", true),
            widen_cast(NumberType::I32, NumberType::I64, "to_i64", true),
        ],
        vec![InternalFunction {
            // Float formatting can't be expressed in clem; format via sprintf then
            // decode the ASCII buffer into a List<Char>.
            name: "to_string".into(),
            ty: Type::new(
                vec![UnitType::Literal(LiteralType::Number(NumberType::F64))],
                vec![string_type()],
            ),
            function: Rc::new(Box::new(
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let buffer = compiler_context.builder.build_array_malloc(
                        compiler_context.context.i8_type(),
                        compiler_context.context.i64_type().const_int(64, false),
                        "f64_buffer",
                    )?;
                    let format_str = compiler_context.build_global_string("%f".into())?;
                    let sprintf = compiler_context
                        .module
                        .get_function("sprintf")
                        .ok_or(CompilerError::GetFunctionError("sprintf".into()))?;
                    compiler_context.builder.build_call(
                        sprintf,
                        &[buffer.into(), format_str.into(), value.1.into()],
                        "sprintf",
                    )?;
                    let list = compiler_context.emit_string_from_cstr(buffer)?;
                    stack.push((string_type(), list));
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
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
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    stack.push(value.clone());
                    stack.push((
                        value.0.clone(),
                        compiler_context.clone_value(value.0, value.1)?,
                    ));
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
                |_compiler_context: &mut CompilerContext<'ctx>,
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
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let value2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;

                    stack.push(value2.clone());
                    stack.push(value1.clone());
                    stack.push((
                        value2.0.clone(),
                        compiler_context.clone_value(value2.0, value2.1)?,
                    ));
                    stack.push((
                        value1.0.clone(),
                        compiler_context.clone_value(value1.0, value1.1)?,
                    ));
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
                |_compiler_context: &mut CompilerContext<'ctx>,
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
                |_compiler_context: &mut CompilerContext<'ctx>,
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
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    compiler_context.drop_value(value.0, value.1)?;
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
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    compiler_context.drop_value(value1.0, value1.1)?;
                    let value2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    compiler_context.drop_value(value2.0, value2.1)?;
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        }],
        pop2_push1(
            &all_number_types,
            None,
            "+".into(),
            Rc::new(Box::new(
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let result_ty = arg1.0.clone();
                    match (arg1.1, arg2.1) {
                        (BasicValueEnum::IntValue(n1), BasicValueEnum::IntValue(n2)) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_add(n1, n2, "add_result")?;
                            stack.push((result_ty, BasicValueEnum::IntValue(result)));
                        }
                        (BasicValueEnum::FloatValue(n1), BasicValueEnum::FloatValue(n2)) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_add(n1, n2, "add_result")?;
                            stack.push((result_ty, BasicValueEnum::FloatValue(result)));
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
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let result_ty = arg1.0.clone();
                    // `a b -` computes `a - b`; `a` was pushed first (arg2), `b` last (arg1).
                    match (arg2.1, arg1.1) {
                        (BasicValueEnum::IntValue(n1), BasicValueEnum::IntValue(n2)) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_sub(n1, n2, "sub_result")?;
                            stack.push((result_ty, BasicValueEnum::IntValue(result)));
                        }
                        (BasicValueEnum::FloatValue(n1), BasicValueEnum::FloatValue(n2)) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_sub(n1, n2, "sub_result")?;
                            stack.push((result_ty, BasicValueEnum::FloatValue(result)));
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
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let result_ty = arg1.0.clone();
                    match (arg1.1, arg2.1) {
                        (BasicValueEnum::IntValue(n1), BasicValueEnum::IntValue(n2)) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_int_mul(n1, n2, "mul_result")?;
                            stack.push((result_ty, BasicValueEnum::IntValue(result)));
                        }
                        (BasicValueEnum::FloatValue(n1), BasicValueEnum::FloatValue(n2)) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_mul(n1, n2, "mul_result")?;
                            stack.push((result_ty, BasicValueEnum::FloatValue(result)));
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
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let result_ty = arg1.0.clone();
                    let signed = is_signed_number(&result_ty);
                    // `a b /` computes `a / b`; `a` was pushed first (arg2), `b` last (arg1).
                    match (arg2.1, arg1.1) {
                        (BasicValueEnum::IntValue(n1), BasicValueEnum::IntValue(n2)) => {
                            let result = if signed {
                                compiler_context.builder.build_int_signed_div(
                                    n1,
                                    n2,
                                    "div_result",
                                )?
                            } else {
                                compiler_context.builder.build_int_unsigned_div(
                                    n1,
                                    n2,
                                    "div_result",
                                )?
                            };
                            stack.push((result_ty, BasicValueEnum::IntValue(result)));
                        }
                        (BasicValueEnum::FloatValue(n1), BasicValueEnum::FloatValue(n2)) => {
                            let result =
                                compiler_context
                                    .builder
                                    .build_float_div(n1, n2, "div_result")?;
                            stack.push((result_ty, BasicValueEnum::FloatValue(result)));
                        }
                        _ => return Err(CompilerError::UnexpectedType),
                    }
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        ),
        rem(),
        comparison_op(
            &all_literal_types,
            boolean_type.clone(),
            "gt",
            IntPredicate::UGT,
            IntPredicate::SGT,
            FloatPredicate::OGT,
        ),
        comparison_op(
            &all_literal_types,
            boolean_type.clone(),
            "lt",
            IntPredicate::ULT,
            IntPredicate::SLT,
            FloatPredicate::OLT,
        ),
        comparison_op(
            &all_literal_types,
            boolean_type.clone(),
            "=",
            IntPredicate::EQ,
            IntPredicate::EQ,
            FloatPredicate::OEQ,
        ),
        comparison_op(
            &all_literal_types,
            boolean_type.clone(),
            "!=",
            IntPredicate::NE,
            IntPredicate::NE,
            FloatPredicate::ONE,
        ),
        ffi_builtins(),
    ]
    .concat::<_>()
}

/// FFI marshalling builtins, exposed through `std/ffi.clem`:
///   - `to_cstr (String -> CStr)`   — render a `List<Char>` to a malloc'd C string,
///     consuming (dropping) the input string.
///   - `from_cstr (CStr -> String)` — build an owned `List<Char>` from a C string;
///     the input pointer is left untouched.
///   - `free_cstr (CStr ->)`        — `free()` a buffer produced by `to_cstr`.
///
/// These call the helpers in `clem_runtime.c`, which own the heap layout.
fn ffi_builtins<'ctx>() -> Vec<InternalFunction<'ctx>> {
    let cstr = UnitType::Literal(LiteralType::CStr);
    vec![
        InternalFunction {
            name: "to_cstr".into(),
            ty: Type::new(vec![string_type()], vec![cstr.clone()]),
            function: Rc::new(Box::new(
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let to_cstr = compiler_context
                        .module
                        .get_function("clem_string_to_cstr")
                        .ok_or(CompilerError::GetFunctionError(
                            "clem_string_to_cstr".into(),
                        ))?;
                    let buffer = compiler_context
                        .builder
                        .build_call(to_cstr, &[value.1.into()], "to_cstr")?
                        .try_as_basic_value()
                        .left()
                        .ok_or(CompilerError::FunctionCallError)?;
                    // The C string is an independent copy, so release the input String.
                    compiler_context.drop_value(value.0, value.1)?;
                    stack.push((UnitType::Literal(LiteralType::CStr), buffer));
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        },
        InternalFunction {
            name: "from_cstr".into(),
            ty: Type::new(vec![cstr.clone()], vec![string_type()]),
            function: Rc::new(Box::new(
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let from_cstr = compiler_context
                        .module
                        .get_function("clem_string_from_cstr")
                        .ok_or(CompilerError::GetFunctionError(
                            "clem_string_from_cstr".into(),
                        ))?;
                    let list = compiler_context
                        .builder
                        .build_call(from_cstr, &[value.1.into()], "from_cstr")?
                        .try_as_basic_value()
                        .left()
                        .ok_or(CompilerError::FunctionCallError)?;
                    stack.push((string_type(), list));
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        },
        InternalFunction {
            name: "free_cstr".into(),
            ty: Type::new(vec![cstr.clone()], vec![]),
            function: Rc::new(Box::new(
                |compiler_context: &mut CompilerContext<'ctx>,
                 stack: &mut Stack<'ctx>|
                 -> Result<(), CompilerError> {
                    let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                    let free = compiler_context
                        .module
                        .get_function("free")
                        .ok_or(CompilerError::GetFunctionError("free".into()))?;
                    compiler_context
                        .builder
                        .build_call(free, &[value.1.into()], "free_cstr")?;
                    Ok(())
                },
            ) as BoxDefinitionType<'ctx>),
        },
    ]
}

fn rem<'ctx>() -> Vec<InternalFunction<'ctx>> {
    let function = Rc::new(Box::new(
        |compiler_context: &mut CompilerContext<'ctx>,
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U16)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U32)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i64_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::U64)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i8_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I8)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i16_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I16)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i32_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I32)),
                        BasicValueEnum::IntValue(truncated_result),
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
                    let truncated_result = compiler_context.builder.build_int_truncate(
                        result,
                        i64_type,
                        "truncate_result",
                    )?;
                    stack.push((
                        UnitType::Literal(LiteralType::Number(NumberType::I64)),
                        BasicValueEnum::IntValue(truncated_result),
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
            name: "%u8".into(),
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
            name: "%u8".into(),
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
            name: "%u16".into(),
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
            name: "%u8".into(),
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
            name: "%u16".into(),
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
            name: "%u32".into(),
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
            name: "%u8".into(),
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
            name: "%u16".into(),
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
            name: "%u32".into(),
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
            name: "%u64".into(),
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
            name: "%i8".into(),
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
            name: "%i8".into(),
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
            name: "%i16".into(),
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
            name: "%i8".into(),
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
            name: "%i16".into(),
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
            name: "%i32".into(),
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
            name: "%i8".into(),
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
            name: "%i16".into(),
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
            name: "%i32".into(),
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
            name: "%i64".into(),
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

/// Builds the overloads for a comparison operator (`gt`, `lt`, `=`, `!=`) over
/// numeric types. Integers pick `signed_pred`/`unsigned_pred` based on the
/// operand's signedness; floats use `float_pred`. The result is wrapped into a
/// `Boolean`. (Strings are `List<Char>` now and compared in the stdlib.)
fn comparison_op<'ctx>(
    types: &[UnitType],
    boolean_type: UnitType,
    name: &str,
    unsigned_pred: IntPredicate,
    signed_pred: IntPredicate,
    float_pred: FloatPredicate,
) -> Vec<InternalFunction<'ctx>> {
    pop2_push1(
        types,
        Some(boolean_type),
        name.into(),
        Rc::new(Box::new(
            move |compiler_context: &mut CompilerContext<'ctx>,
                  stack: &mut Stack<'ctx>|
                  -> Result<(), CompilerError> {
                let arg1 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                let arg2 = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                let signed = is_signed_number(&arg2.0);
                // `a b <cmp>` compares `a` (arg2, pushed first) against `b` (arg1).
                let result = match (arg2.1, arg1.1) {
                    (BasicValueEnum::IntValue(n1), BasicValueEnum::IntValue(n2)) => {
                        let pred = if signed { signed_pred } else { unsigned_pred };
                        compiler_context
                            .builder
                            .build_int_compare(pred, n1, n2, "cmp_result")?
                    }
                    (BasicValueEnum::FloatValue(n1), BasicValueEnum::FloatValue(n2)) => {
                        compiler_context.builder.build_float_compare(
                            float_pred,
                            n1,
                            n2,
                            "cmp_result",
                        )?
                    }
                    _ => return Err(CompilerError::UnexpectedType),
                };
                stack.push(create_boolean_result(
                    compiler_context,
                    result.as_basic_value_enum(),
                )?);
                Ok(())
            },
        ) as BoxDefinitionType<'ctx>),
    )
}

/// A widening integer cast (`to_u64`/`to_i64`) used by the stdlib so the smaller
/// integer types can delegate `to_string` to the 64-bit implementations.
fn widen_cast<'ctx>(
    from: NumberType,
    to: NumberType,
    name: &str,
    signed: bool,
) -> InternalFunction<'ctx> {
    let pushed = to.clone();
    InternalFunction {
        name: name.into(),
        ty: Type::new(
            vec![UnitType::Literal(LiteralType::Number(from))],
            vec![UnitType::Literal(LiteralType::Number(to))],
        ),
        function: Rc::new(Box::new(
            move |compiler_context: &mut CompilerContext<'ctx>,
                  stack: &mut Stack<'ctx>|
                  -> Result<(), CompilerError> {
                let value = stack.pop().ok_or(CompilerError::StackUnderflow)?;
                let i64_type = compiler_context.context.i64_type();
                let v = value.1.into_int_value();
                let extended = if signed {
                    compiler_context
                        .builder
                        .build_int_s_extend(v, i64_type, "sext")?
                } else {
                    compiler_context
                        .builder
                        .build_int_z_extend(v, i64_type, "zext")?
                };
                stack.push((
                    UnitType::Literal(LiteralType::Number(pushed.clone())),
                    extended.as_basic_value_enum(),
                ));
                Ok(())
            },
        ) as BoxDefinitionType<'ctx>),
    }
}

/// The `String` type = `List<Char>`. Uses the fully-qualified `std::list::List`
/// name the type checker canonicalises to, so that builtin signatures (e.g.
/// `to_cstr (String -> CStr)`) match `defx` declarations and drops resolve the
/// type definition.
fn string_type() -> UnitType {
    UnitType::Custom {
        name: vec!["std".into(), "list".into(), "List".into()],
        generic_types: vec![UnitType::Literal(LiteralType::Char)],
    }
}

/// Whether a numeric type is signed (used to pick signed vs unsigned LLVM ops).
fn is_signed_number(ty: &UnitType) -> bool {
    matches!(
        ty,
        UnitType::Literal(LiteralType::Number(
            NumberType::I8 | NumberType::I16 | NumberType::I32 | NumberType::I64 | NumberType::I128
        ))
    )
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

fn create_boolean_result<'ctx>(
    compiler_context: &mut CompilerContext<'ctx>,
    value: BasicValueEnum<'ctx>,
) -> Result<(UnitType, BasicValueEnum<'ctx>), CompilerError> {
    let boolean_struct_type = compiler_context.base_custom_type();
    let struct_val = compiler_context.build_pool_alloc(
        boolean_struct_type
            .size_of()
            .expect("Should have a known size"),
    )?;
    let field_ptr =
        compiler_context
            .builder
            .build_struct_gep(boolean_struct_type, struct_val, 0, "rc")?;
    compiler_context.builder.build_store(
        field_ptr,
        compiler_context.context.i64_type().const_int(1, true),
    )?;
    let field_ptr =
        compiler_context
            .builder
            .build_struct_gep(boolean_struct_type, struct_val, 1, "variant")?;
    // The boolean (i1) is stored directly as the variant tag (True=1/False=0),
    // which is now an i8.
    let bool_i8 = compiler_context.builder.build_int_z_extend(
        value.into_int_value(),
        compiler_context.context.i8_type(),
        "bool_i8",
    )?;
    compiler_context
        .builder
        .build_store(field_ptr, bool_i8.as_basic_value_enum())?;

    let ty = compiler_context
        .get_type(vec!["std".into(), "boolean".into(), "Boolean".into()])
        .ok_or(CompilerError::UnexpectedType)?;
    let ty = UnitType::Custom {
        name: ty.name.clone(),
        generic_types: vec![],
    };

    Ok((ty, struct_val.as_basic_value_enum()))
}
