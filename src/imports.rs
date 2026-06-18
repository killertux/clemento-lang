use std::{collections::HashSet, fs::read_to_string, path::Path};

use crate::lexer::Position;
use crate::parser::{AstNode, AstNodeType, Import, NameWithAlias, Parser, ParserError};

/// Resolves a single `import` directive: reads the imported file, recursively
/// parses it, and embeds the resulting block into an [`Import`] node.
///
/// `seen` tracks already-resolved module paths so a module is read and parsed
/// at most once; subsequent imports of the same path yield an [`Import`] with
/// `node: None`.
pub fn resolve_import(
    seen: &mut HashSet<String>,
    name: NameWithAlias,
    functions: Vec<NameWithAlias>,
    path: &Path,
) -> Result<Import<AstNode>, ParserError> {
    if seen.contains(&name.name) {
        return Ok(Import {
            name,
            functions,
            node: None,
        });
    }

    let file_content = read_to_string(path)
        .map_err(|err| ParserError::ImportError(name.name.clone(), err.to_string()))?;

    let program = Parser::new_from_file(&file_content, name.name.clone())
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
