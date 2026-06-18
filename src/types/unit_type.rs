use super::signature::{Type, VarType};

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum UnitType {
    Literal(LiteralType),
    Var(VarType),
    Custom {
        name: Vec<String>,
        generic_types: Vec<UnitType>,
    },
    Type(Type),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LiteralType {
    Number(NumberType),
    /// A single Unicode scalar (code point), stored as an i32 at runtime.
    /// (Strings are `List<Char>`, not a primitive.)
    Char,
    /// A raw, NUL-terminated C string (`char*`). An FFI type: it crosses the C
    /// boundary verbatim as an `i8*` pointer and is *not* reference counted or
    /// pool-managed. Convert to/from a Clemento `String` with `ffi::from_cstr` /
    /// `ffi::to_cstr`.
    CStr,
    /// An opaque raw pointer (`void*`), for C handles (e.g. `FILE*`). Like
    /// `CStr`, it is an `i8*` passed verbatim across FFI and is not managed by
    /// the runtime.
    Ptr,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum NumberType {
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    F64,
}
