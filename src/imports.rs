use std::{
    cell::RefCell,
    collections::HashSet,
    fs::read_to_string,
    path::{Path, PathBuf},
    rc::Rc,
};

use crate::lexer::Position;
use crate::parser::{AstNode, AstNodeType, Import, NameWithAlias, Parser, ParserError};

/// Resolves a module's relative path (e.g. `std/io.clem`) to a concrete file on
/// disk. The current directory is tried first (preserving the historical
/// behavior), then each search directory in order; the first hit wins.
pub fn resolve_module_file(relative: &Path, search_paths: &[PathBuf]) -> Option<PathBuf> {
    if relative.exists() {
        return Some(relative.to_path_buf());
    }
    search_paths
        .iter()
        .map(|dir| dir.join(relative))
        .find(|candidate| candidate.exists())
}

/// Resolves a single `import` directive: locates the imported file (current
/// directory first, then `search_paths` in order), reads it, recursively parses
/// it, and embeds the resulting block into an [`Import`] node.
///
/// `seen` tracks already-resolved module paths so a module is read and parsed
/// at most once; subsequent imports of the same path yield an [`Import`] with
/// `node: None`.
///
/// As a side effect, a sibling C glue file co-located with the resolved module
/// (`<dir>/foo.clem` -> `<dir>/foo.c`) is appended to `c_sources` so the driver
/// links it — the same convention as the top-level file, applied per module.
pub fn resolve_import(
    seen: &mut HashSet<String>,
    name: NameWithAlias,
    functions: Vec<NameWithAlias>,
    path: &Path,
    search_paths: &Rc<[PathBuf]>,
    c_sources: &Rc<RefCell<Vec<PathBuf>>>,
) -> Result<Import<AstNode>, ParserError> {
    if seen.contains(&name.name) {
        return Ok(Import {
            name,
            functions,
            node: None,
        });
    }

    let resolved = resolve_module_file(path, search_paths).ok_or_else(|| {
        ParserError::ImportError(
            name.name.clone(),
            format!("module not found: {}", path.display()),
        )
    })?;

    let file_content = read_to_string(&resolved)
        .map_err(|err| ParserError::ImportError(name.name.clone(), err.to_string()))?;

    // Auto-link a sibling C glue file next to the resolved module, if present.
    let sibling_c = resolved.with_extension("c");
    if sibling_c.exists() {
        let mut sources = c_sources.borrow_mut();
        if !sources.contains(&sibling_c) {
            sources.push(sibling_c);
        }
    }

    let program = Parser::new_from_file_with(
        &file_content,
        name.name.clone(),
        search_paths.clone(),
        c_sources.clone(),
    )
    .collect::<Result<Vec<AstNode>, ParserError>>()?;

    seen.insert(name.name.clone());
    Ok(Import {
        name,
        functions,
        node: Some(AstNode {
            node_type: AstNodeType::Block(program),
            position: Position::default(),
            type_definition: None,
        }),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolve_module_file_prefers_current_directory() {
        // A path that exists relative to CWD resolves there, ignoring search paths.
        let cargo_toml = Path::new("Cargo.toml");
        let resolved = resolve_module_file(cargo_toml, &[PathBuf::from("/nonexistent")]);
        assert_eq!(resolved, Some(PathBuf::from("Cargo.toml")));
    }

    #[test]
    fn resolve_module_file_falls_through_search_paths_in_order() {
        // `src/main.rs` does not exist relative to CWD as `main.rs`, but does
        // under `src`; the first matching search dir wins.
        let relative = Path::new("main.rs");
        let resolved = resolve_module_file(
            relative,
            &[PathBuf::from("nonexistent"), PathBuf::from("src")],
        );
        assert_eq!(resolved, Some(PathBuf::from("src/main.rs")));
    }

    #[test]
    fn resolve_module_file_returns_none_when_absent() {
        let relative = Path::new("definitely/not/here.clem");
        assert_eq!(resolve_module_file(relative, &[]), None);
    }
}
