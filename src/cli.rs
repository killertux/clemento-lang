use std::path::PathBuf;

use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(version, about, long_about = None)]
pub struct Args {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand)]
pub enum Commands {
    Run {
        /// Path to the file to run
        #[arg(short, long)]
        path: PathBuf,
        /// Extra C source files to compile and link (FFI glue). A sibling
        /// `<name>.c` next to the `.clem` file is linked automatically.
        #[arg(short = 'c', long = "c-source")]
        c_sources: Vec<PathBuf>,
        /// Additional directories to search for imported modules, tried in
        /// order after the current directory.
        #[arg(short = 'L', long = "search-path")]
        search_paths: Vec<PathBuf>,
        /// Extra arguments forwarded verbatim to `clang` (repeatable).
        /// Hyphen-leading values are allowed, e.g. `--clang-arg -lm`.
        #[arg(long = "clang-arg", allow_hyphen_values = true)]
        clang_args: Vec<String>,
    },
    TypePrinter {
        /// Path to the file to print types for
        #[arg(short, long)]
        path: PathBuf,
        /// Additional directories to search for imported modules, tried in
        /// order after the current directory.
        #[arg(short = 'L', long = "search-path")]
        search_paths: Vec<PathBuf>,
    },
    Compile {
        /// Path to the file to compile
        #[arg(short, long)]
        path: PathBuf,
        /// Extra C source files to compile and link (FFI glue). A sibling
        /// `<name>.c` next to the `.clem` file is linked automatically.
        #[arg(short = 'c', long = "c-source")]
        c_sources: Vec<PathBuf>,
        /// Additional directories to search for imported modules, tried in
        /// order after the current directory.
        #[arg(short = 'L', long = "search-path")]
        search_paths: Vec<PathBuf>,
        /// Extra arguments forwarded verbatim to `clang` (repeatable).
        /// Hyphen-leading values are allowed, e.g. `--clang-arg -lm`.
        #[arg(long = "clang-arg", allow_hyphen_values = true)]
        clang_args: Vec<String>,
    },
}
