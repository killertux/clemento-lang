use std::process::ExitCode;

use clap::Parser;

use crate::cli::{Args, Commands};

mod cli;
mod compiler;
mod driver;
mod imports;
mod internal_functions;
mod lexer;
mod parser;
mod type_checker;
mod type_printer;
mod types;

fn main() -> Result<ExitCode, Box<dyn std::error::Error>> {
    match Args::parse().command {
        Commands::Run { path, c_sources } => driver::run(path, &c_sources),
        Commands::Compile { path, c_sources } => driver::compile_only(path, &c_sources),
        Commands::TypePrinter { path } => driver::print_types(path),
    }
}
