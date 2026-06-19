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
        Commands::Run {
            path,
            c_sources,
            search_paths,
            clang_args,
        } => driver::run(path, &c_sources, &search_paths, &clang_args),
        Commands::Compile {
            path,
            c_sources,
            search_paths,
            clang_args,
        } => driver::compile_only(path, &c_sources, &search_paths, &clang_args),
        Commands::TypePrinter { path, search_paths } => driver::print_types(path, &search_paths),
    }
}
