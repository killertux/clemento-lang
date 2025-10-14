use std::{path::PathBuf, process::ExitCode};

use clap::{Parser, Subcommand};

mod internal_functions;
mod interpreter;
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
}

fn main() -> Result<ExitCode, Box<dyn std::error::Error>> {
    let args = Args::parse();
    match args.command {
        Commands::Run { path } => Ok(interpreter::interpret(path)
            .map_err(|err| err.to_string())?
            .into()),
        Commands::TypePrinter { path } => {
            type_printer::print_type(path).map_err(|err| err.to_string())?;
            Ok(0.into())
        }
    }
}
