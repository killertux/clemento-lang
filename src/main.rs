use clap::{Parser, Subcommand};
use std::process::Command as StdCommand;
use std::{path::PathBuf, process::ExitCode};

use crate::compiler::compile;

mod compiler;
mod internal_functions;
mod lexer;
mod parser;
mod type_checker;
mod type_printer;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    Run {
        /// Path to the file to run
        #[arg(short, long)]
        path: PathBuf,
    },
    TypePrinter {
        /// Path to the file to print types for
        #[arg(short, long)]
        path: PathBuf,
    },
    Compile {
        /// Path to the file to compile
        #[arg(short, long)]
        path: PathBuf,
    },
}

fn main() -> Result<ExitCode, Box<dyn std::error::Error>> {
    let args = Args::parse();
    match args.command {
        Commands::Run { path } => {
            let output_path = compile(path).map_err(|err| err.to_string())?;
            let mut execute_file = output_path.clone();
            execute_file.set_extension("");
            StdCommand::new("clang")
                .arg(output_path)
                .arg("-o")
                .arg(execute_file.clone())
                .output()?;
            let result: u8 = StdCommand::new(&format!("./{}", execute_file.display()))
                .status()?
                .code()
                .unwrap_or(0)
                .try_into()?;
            Ok(result.into())
        }
        Commands::TypePrinter { path } => {
            type_printer::print_type(path).map_err(|err| err.to_string())?;
            Ok(0.into())
        }
        Commands::Compile { path } => {
            compile(path).map_err(|err| err.to_string())?;
            Ok(0.into())
        }
    }
}
