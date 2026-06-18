use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use crate::compiler::compile;
use crate::type_printer;

type DriverError = Box<dyn std::error::Error>;

/// The slab-pool allocator runtime, linked into every compiled program.
/// Generated code calls `clem_alloc`/`clem_free` (declared in `internal_functions`)
/// instead of `malloc`/`free`. It also provides the FFI string-marshalling
/// helpers (`clem_string_to_cstr`/`from_cstr`).
const CLEM_RUNTIME: &str = include_str!("clem_runtime.c");

/// The FFI header for C glue code (`#include "clem.h"`). Written next to the IR
/// so a sibling C source can include it.
const CLEM_HEADER: &str = include_str!("clem.h");

/// Compiles a `.clem` source file to LLVM IR and links it into a native
/// executable with `clang`, returning the path to the produced binary.
///
/// In addition to the always-linked runtime, this links in any FFI glue:
///   - a sibling C file (`foo.clem` -> `foo.c`), if present, and
///   - any extra C sources passed on the command line (`-c`/`--c-source`).
fn compile_and_link(path: impl AsRef<Path>, c_sources: &[PathBuf]) -> Result<PathBuf, DriverError> {
    // Resolve the sibling C glue file (`foo.clem` -> `foo.c`) before compiling,
    // since `compile` rewrites the path's extension.
    let sibling_c = path.as_ref().with_extension("c");

    let output_path = compile(path).map_err(|err| err.to_string())?;
    let mut execute_file = output_path.clone();
    execute_file.set_extension("");

    // Write the allocator runtime and the FFI header next to the IR; the header
    // lets a sibling C source `#include "clem.h"`.
    let mut runtime_path = output_path.clone();
    runtime_path.set_file_name("clem_runtime.c");
    std::fs::write(&runtime_path, CLEM_RUNTIME)?;
    let mut header_path = output_path.clone();
    header_path.set_file_name("clem.h");
    std::fs::write(&header_path, CLEM_HEADER)?;

    let mut command = Command::new("clang");
    command.arg(&output_path).arg(&runtime_path);
    if sibling_c.exists() {
        command.arg(&sibling_c);
    }
    for c_source in c_sources {
        command.arg(c_source);
    }
    // Let glue files find the header regardless of where they live.
    if let Some(dir) = header_path.parent() {
        command.arg("-I").arg(dir);
    }
    // Optimize the generated IR. Besides the usual wins, this lets LLVM's
    // TailCallElimination turn straightforward self-tail-calls into loops.
    // It is only opportunistic, though — recursion split across `match` arms
    // keeps a phi between the call and the `ret`, defeating it; the guaranteed
    // tail-call handling lives in the compiler's own self-tail-call lowering.
    command.arg("-O2");
    command.arg("-o").arg(&execute_file);

    let output = command.output()?;
    if !output.status.success() {
        return Err(format!(
            "Compilation failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )
        .into());
    }
    Ok(execute_file)
}

/// Compiles, links and runs the program, forwarding its exit code.
pub fn run(path: impl AsRef<Path>, c_sources: &[PathBuf]) -> Result<ExitCode, DriverError> {
    let execute_file = compile_and_link(path, c_sources)?;
    let result: u8 = Command::new(format!("./{}", execute_file.display()))
        .status()?
        .code()
        .unwrap_or(0)
        .try_into()?;
    Ok(result.into())
}

/// Compiles and links the program without running it.
pub fn compile_only(
    path: impl AsRef<Path>,
    c_sources: &[PathBuf],
) -> Result<ExitCode, DriverError> {
    compile_and_link(path, c_sources)?;
    Ok(ExitCode::SUCCESS)
}

/// Type-checks the program and prints the inferred types.
pub fn print_types(path: impl AsRef<Path>) -> Result<ExitCode, DriverError> {
    type_printer::print_type(path).map_err(|err| err.to_string())?;
    Ok(ExitCode::SUCCESS)
}
