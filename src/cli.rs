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
        /// Extra C source files to compile and link (FFI glue). A sibling
        /// `<name>.c` next to the `.clem` file is linked automatically.
        #[arg(short = 'c', long = "c-source")]
        c_sources: Vec<PathBuf>,
    },
}
