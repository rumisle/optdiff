use clap::Parser;
use color_eyre::{
    eyre::{eyre, WrapErr},
    Result,
};
use color_print::cformat;
use is_terminal::IsTerminal;
use itertools::Itertools;
use memchr::memmem;
use optpipeline::Pass;
use regex::Regex;
use similar::TextDiff;
use std::path::PathBuf;
use std::{
    collections::HashSet,
    io::{self, Read, Write},
};

#[cfg(unix)]
use pager::Pager;

mod cli_write;
mod demangle;
mod optpipeline;

#[derive(Parser)]
#[command(
    author,
    version,
    about = "Display diffs of LLVM IR changes between optimization passes"
)]
#[command(after_help = cformat!("<s><u>Note:</u></s>
   For syntax highlighting of diffs, install delta: https://github.com/dandavison/delta

<s><u>Examples:</u></s>
   <i># View optimization changes:</i>
   clang input.c -O2 -mllvm -print-before-all -mllvm -print-after-all -c -o /dev/null 2>&1 | optdiff

   <i># To limit output to a specific function:</i>
   clang input.c -O2 -mllvm -print-before-all -mllvm -print-after-all -mllvm -filter-print-funcs=foo -c -o /dev/null 2>&1 | optdiff

   <i># From a saved dump file:</i>
   clang input.c -O2 -mllvm -print-before-all -mllvm -print-after-all -c -o /dev/null &> dump.txt
   optdiff dump.txt

   <i># To filter functions/passes (and optionally with regex `-E`):</i>
   optdiff dump.txt -E -f 'foo.*'              # match functions starting with 'foo'
   optdiff dump.txt -E -P 'Combine|Simplify'   # match passes containing 'Combine' or 'Simplify'
   optdiff dump.txt -E -f '^main$' -P '.*Opt$' # match exactly 'main' function and passes ending in 'Opt'"))]
struct Args {
    /// Path to LLVM pass dump file. If not provided, reads from stdin
    #[arg(value_name = "FILE")]
    input: Option<PathBuf>,

    /// Hide optimization passes that don't modify the IR
    #[arg(short = 's', long = "skip-unchanged")]
    skip_unchanged: bool,

    /// Only show passes for specified function
    #[arg(short = 'f', long = "function")]
    function: Option<String>,

    /// Only show passes with names containing this string
    #[arg(short = 'P', long = "pass")]
    pass: Option<String>,

    /// Enable extended regex patterns for -f and -P
    #[arg(short = 'E', long = "extended-regex")]
    extended_regex: bool,

    /// List available functions
    #[arg(short = 'l', long = "list")]
    list: bool,

    /// Demangle C++ symbols
    #[arg(short = 'd', long = "demangle")]
    demangle: bool,

    /// Which pager to use
    #[arg(short = 'p', long = "pager", env = "OPTDIFF_PAGER")]
    pager: Option<String>,

    /// Pass through prefix
    #[arg(long = "passthrough")]
    passthrough: bool,

    /// Don't break down into individual functions, diff the whole module
    #[arg(short = 'w', long = "whole-module")]
    whole_module: bool,
}

fn read_input(args: &Args) -> Result<String, io::Error> {
    match &args.input {
        Some(path) => std::fs::read_to_string(path),
        None => {
            let mut buffer = String::new();
            io::stdin().read_to_string(&mut buffer)?;
            Ok(buffer)
        }
    }
}

fn matches_pattern(text: &str, pattern: &str, use_regex: bool) -> Result<bool> {
    if use_regex {
        let regex =
            Regex::new(pattern).wrap_err_with(|| format!("Invalid regex pattern: {}", pattern))?;
        Ok(regex.is_match(text))
    } else {
        Ok(text.to_lowercase().contains(&pattern.to_lowercase()))
    }
}

fn demangle_text(text: &str, should_demangle: bool) -> String {
    if !should_demangle {
        return text.to_string();
    }

    let mut output = Vec::new();
    let options = demangle::DemangleBuilder::new().build();
    if demangle::demangle_line(&mut output, text.as_bytes(), options).is_ok() {
        String::from_utf8_lossy(&output).to_string()
    } else {
        text.to_string()
    }
}

fn print_func(
    func_name: &str,
    pipeline: &[Pass],
    skip_unchanged: bool,
    pass_filter: Option<&str>,
    use_regex: bool,
    should_demangle: bool,
) -> Result<()> {
    for (i, pass) in pipeline.iter().enumerate() {
        let demangled_name = demangle_text(&pass.name, should_demangle);

        if let Some(filter) = pass_filter {
            if !matches_pattern(&demangled_name, filter, use_regex)? {
                continue;
            }
        }

        if skip_unchanged && pass.before == pass.after {
            continue;
        }

        let demangled_before = demangle_text(&pass.before, should_demangle) + "\n";
        let demangled_after = demangle_text(&pass.after, should_demangle) + "\n";

        let diff = TextDiff::from_lines(&demangled_before, &demangled_after);

        let title = format!("({}·{}) {}", i + 1, func_name, &pass.name);
        let mut stdout = io::stdout();
        cli_writeln!(stdout, "diff --git a/{} b/{}", title, title)?;
        cli_writeln!(stdout, "--- a/{}", title)?;
        cli_writeln!(stdout, "+++ b/{}", title)?;
        cli_writeln!(stdout, "{}", diff.unified_diff().context_radius(10))?;
    }

    Ok(())
}

fn auto_select_pager() -> Option<&'static str> {
    if which::which("delta").is_ok() {
        Some("delta")
    } else if which::which("riff").is_ok() {
        Some("riff")
    } else if which::which("less").is_ok() {
        Some("less -R")
    } else {
        None
    }
}

#[cfg(unix)]
fn enter_pager(pager: Option<&str>) {
    if io::stdout().is_terminal() {
        let pager = match pager {
            None => auto_select_pager(),
            Some(pager) if pager.trim().is_empty() => None,
            Some(pager) => Some(pager),
        };
        if let Some(pager) = pager {
            Pager::with_default_pager(pager).setup();
        }
    }
}

#[cfg(not(unix))]
fn enter_pager(_pager: Option<&str>) {}

fn list_functions(dump: &str, should_demangle: bool) -> HashSet<String> {
    let mut functions = HashSet::new();
    let haystack = dump.as_bytes();
    {
        let it = memmem::find_iter(haystack, b"define ");
        for start in it {
            let start = start + memchr::memchr(b'@', &haystack[start..]).unwrap() + 1;
            let end = memchr::memchr(b'(', &haystack[start..]).unwrap();
            let name = &dump[start..start + end];
            let demangled = if should_demangle {
                demangle_text(name, true)
            } else {
                name.to_string()
            };
            functions.insert(demangled);
        }
    }
    {
        let it = memmem::find_iter(haystack, b"# Machine code for function ");
        for start in it {
            let start = start + b"# Machine code for function ".len();
            let end = memchr::memchr(b':', &haystack[start..]).unwrap();
            let name = &dump[start..start + end];
            let demangled = if should_demangle {
                demangle_text(name, true)
            } else {
                name.to_string()
            };
            functions.insert(demangled);
        }
    }
    functions
}

fn main() -> Result<()> {
    color_eyre::install()?;

    let args = Args::parse();
    let dump = read_input(&args).wrap_err_with(|| match &args.input {
        None => "Failed to read from stdin".to_string(),
        Some(path) => format!("Failed to read from file: {}", path.display()),
    })?;

    if !dump.contains("IR Dump Before") {
        return Err(eyre!("Did you forget to add `-mllvm -print-before-all`?"));
    }

    if !dump.contains("IR Dump After") {
        return Err(eyre!("Did you forget to add `-mllvm -print-after-all`?"));
    }

    if args.list {
        for func in list_functions(&dump, args.demangle).into_iter().sorted() {
            cli_writeln!(io::stdout(), "{func}")?;
        }
        return Ok(());
    }

    let (prefix, result) =
        optpipeline::process(&dump, true, args.whole_module).wrap_err("Parsing error")?;
    cli_write!(io::stderr(), "{}", prefix)?;

    if let Some(expected) = args.function {
        let (func_name, pipeline) = if args.extended_regex {
            let regex = Regex::new(&expected)
                .wrap_err_with(|| format!("Invalid regex pattern: {}", expected))?;
            result
                .iter()
                .map(|(func_name, pipeline)| (demangle_text(func_name, args.demangle), pipeline))
                .find(|(func_name,_)| regex.is_match(func_name))
                .ok_or_else(|| {
                    eyre!(
                        "No function matching regex '{}' was found in the input, use option `--list/-l` to find out all available functions",
                        expected
                    )
                })?
        } else {
            result
                .iter()
                .map(|(func_name, pipeline)| (demangle_text(func_name, args.demangle), pipeline))
                .find(|(func_name,_)| func_name == &expected)
                .ok_or_else(|| eyre!("Function '{}' was not found in the input, use option `--list/-l` to find out all available functions", expected))?
        };

        enter_pager(args.pager.as_deref());
        print_func(
            &func_name,
            pipeline,
            args.skip_unchanged,
            args.pass.as_deref(),
            args.extended_regex,
            args.demangle,
        )?;
    } else {
        enter_pager(args.pager.as_deref());
        for (func, pipeline) in result.iter().sorted_by_key(|(func, _)| *func) {
            print_func(
                func,
                pipeline,
                args.skip_unchanged,
                args.pass.as_deref(),
                args.extended_regex,
                args.demangle,
            )?;
        }
    }

    Ok(())
}
