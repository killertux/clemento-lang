use thiserror::Error;

use crate::{
    lexer::Position,
    parser::{AstNode, AstNodeType, Parser, ParserError},
    type_checker::{TypeCheckerError, type_check},
};
use std::{fs::read_to_string, path::Path};

pub fn print_type(file: impl AsRef<Path>) -> Result<(), TypePrinterError> {
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
    println!("{}", program);
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
