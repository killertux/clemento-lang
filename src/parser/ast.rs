use std::fmt::Display;

use crate::lexer::{Number, Position};
use crate::types::{Type, UnitType, VarType};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum AstNodeType<T> {
    Number(Number),
    Char(char),
    Symbol(String),
    SymbolWithPath(Vec<String>),
    Import(Vec<String>, Box<Import<T>>),
    Definition {
        name: String,
        is_private: bool,
        /// `true` for a lazy function def (`def f \{ ... }` / `def f \g`):
        /// referencing the name runs the body. `false` for an eager value def
        /// (`def x { ... }`): the body runs once and its result is captured into
        /// the name. The parser unwraps the `\` of a lazy body into the `body`
        /// (a `Block`), recording the distinction here.
        is_lazy: bool,
        body: Box<T>,
    },
    ExternalDefinition(String, Type),
    Block(Vec<T>),
    /// `\name` / `\mod::name`: pushes a reference to a named definition as a
    /// function value (instead of invoking it).
    FunctionRef(Vec<String>),
    /// `\{ ... }`: an anonymous quotation. Structurally a block, but pushed onto
    /// the stack as a function value rather than executed inline.
    Quotation(Vec<T>),
    CustomType {
        name: String,
        generics: Vec<(String, VarType)>,
        variants: Vec<(String, Vec<(String, UnitType)>)>,
    },
    /// `effect IO`: declares a side effect. Treated like a type with no value;
    /// it never reaches codegen. Defining it changes nothing on the stack.
    EffectDefinition(String),
    Match(Vec<Case<T>>),
}

impl<T> AstNodeType<T> {
    /// Whether a definition body of this shape is a *lazy function* rather than
    /// an *eager value binding*. A body that is a bare function value — `\name`
    /// (`FunctionRef`) or `\{ ... }` (`Quotation`) — defines a callable function
    /// (referencing the name runs it). Any other body is evaluated eagerly and
    /// its result captured into the name. See the eager/lazy `def` split in the
    /// type checker and compiler.
    pub fn is_lazy_body(&self) -> bool {
        matches!(
            self,
            AstNodeType::FunctionRef(_) | AstNodeType::Quotation(_)
        )
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Case<T> {
    pub pattern: Pattern,
    pub body: Box<T>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Pattern {
    Wildcard(Option<String>),
    Number(Number),
    Char(char),
    Variant {
        variant_name: Vec<String>,
        fields: Vec<FieldPattern>,
    },
}

/// A field of a variant pattern: which `field` of the variant, and the
/// sub-`pattern` to match it against. A leaf `Wildcard(Some(name))` binds the
/// field to `name`; a nested `Variant` recurses (enabling e.g. list patterns).
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct FieldPattern {
    pub field: String,
    pub pattern: Pattern,
}

impl Display for FieldPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match &self.pattern {
            Pattern::Wildcard(Some(alias)) if alias == &self.field => write!(f, "{}", self.field),
            Pattern::Wildcard(Some(alias)) => write!(f, "{} as {}", self.field, alias),
            other => write!(f, "{} {}", self.field, other),
        }
    }
}

impl Display for Pattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pattern::Wildcard(Some(name)) => write!(f, "* as {}", name),
            Pattern::Wildcard(None) => write!(f, "*"),
            Pattern::Number(number) => write!(f, "{}", number),
            Pattern::Char(c) => write!(f, "{:?}", c),
            Pattern::Variant {
                variant_name,
                fields,
            } => {
                if fields.is_empty() {
                    write!(f, "{}", variant_name.join("::"))
                } else {
                    write!(
                        f,
                        "{}({})",
                        variant_name.join("::"),
                        fields
                            .iter()
                            .map(|field| field.to_string())
                            .collect::<Vec<String>>()
                            .join(" ")
                    )
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Import<T> {
    pub name: NameWithAlias,
    pub functions: Vec<NameWithAlias>,
    pub node: Option<T>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct NameWithAlias {
    pub name: String,
    pub alias: String,
}

impl<T> Display for AstNodeType<T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AstNodeType::Number(number) => write!(f, "{}", number),
            AstNodeType::Char(c) => write!(f, "{:?}", c),
            AstNodeType::Symbol(symbol) => write!(f, "{}", symbol),
            AstNodeType::SymbolWithPath(symbol) => write!(f, "{}", symbol.join("::")),
            AstNodeType::Definition {
                name: symbol,
                is_private,
                is_lazy,
                body,
            } => {
                let keyword = if *is_private { "defp" } else { "def" };
                if *is_lazy {
                    writeln!(f, "{} {} \\{{ {} }}", keyword, symbol, body)
                } else {
                    writeln!(f, "{} {} {}", keyword, symbol, body)
                }
            }
            AstNodeType::ExternalDefinition(symbol, ty) => writeln!(f, "defx {} {}", symbol, ty),
            AstNodeType::Import(symbol, import) => {
                write!(f, "import {}", symbol.join("::"))?;
                if !import.functions.is_empty() {
                    write!(
                        f,
                        "({})",
                        import
                            .functions
                            .iter()
                            .map(|func| {
                                if func.name != func.alias {
                                    format!("{} as {}", func.name, func.alias)
                                } else {
                                    func.name.to_string()
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(" ")
                    )?;
                }
                if import.name.alias != symbol[symbol.len() - 1] {
                    write!(f, " as {}", import.name.alias)?;
                }
                Ok(())
            }
            AstNodeType::Block(nodes) => write!(
                f,
                "{{{}}}",
                nodes
                    .iter()
                    .map(|node| node.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            AstNodeType::FunctionRef(symbol) => write!(f, "\\{}", symbol.join("::")),
            AstNodeType::Quotation(nodes) => write!(
                f,
                "\\{{{}}}",
                nodes
                    .iter()
                    .map(|node| node.to_string())
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            AstNodeType::CustomType {
                name,
                generics,
                variants,
            } => {
                write!(f, "type {}", name)?;
                if !generics.is_empty() {
                    write!(f, "<")?;

                    write!(
                        f,
                        "{}",
                        generics
                            .iter()
                            .map(|(name, _)| name.clone())
                            .collect::<Vec<_>>()
                            .join(" ")
                    )?;
                    write!(f, ">")?;
                }
                write!(f, " {{")?;

                let mut variants_str = Vec::new();
                for (variant, fields) in variants {
                    let mut variant_str = variant.clone();
                    if !fields.is_empty() {
                        variant_str += "(";

                        for (field, ty) in fields {
                            variant_str += &format!("{} {}", field, ty);
                        }
                        variant_str += ")";
                    }
                    variants_str.push(variant_str);
                }
                write!(f, "{}", variants_str.join(" "))?;
                write!(f, "}}")
            }
            AstNodeType::EffectDefinition(name) => write!(f, "effect {}", name),
            AstNodeType::Match(cases) => {
                write!(f, "match {{")?;

                let mut case_str = Vec::new();
                for case in cases {
                    case_str.push(format!("{} => {}", case.pattern, case.body));
                }
                write!(f, "{}", case_str.join(" "))?;
                write!(f, "}}")
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct AstNode {
    pub node_type: AstNodeType<AstNode>,
    pub position: Position,
    pub type_definition: Option<Type>,
}
