use thiserror::Error;

use crate::{
    lexer::Position,
    parser::{AstNode, AstNodeType, Parser, ParserError},
    type_checker::{TypeChecker, TypeCheckerError},
};
use std::{
    cell::RefCell,
    fs::read_to_string,
    path::{Path, PathBuf},
    rc::Rc,
};

pub fn print_type(
    file: impl AsRef<Path>,
    search_paths: &[PathBuf],
) -> Result<(), TypePrinterError> {
    let path_as_string = file.as_ref().display().to_string();
    let file_content = read_to_string(file.as_ref())?;

    let program = Parser::new_from_file_with(
        &file_content,
        path_as_string,
        Rc::from(search_paths.to_vec()),
        Rc::new(RefCell::new(Vec::new())),
    )
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
    println!("{}", program.0);
    Ok(())
}

#[derive(Debug, Error)]
pub enum TypePrinterError {
    #[error(transparent)]
    TypeChecker(#[from] TypeCheckerError),
    #[error(transparent)]
    Parser(#[from] ParserError),
    #[error(transparent)]
    IO(#[from] std::io::Error),
}
