use itertools::Itertools;
use memchr::memchr_iter;
use regex::Regex;
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug)]
pub struct Pass {
    pub name: String,
    pub machine: bool,
    pub after: String,
    pub before: String,
    pub ir_changed: bool,
}

type OptPipelineResults = HashMap<String, Vec<Pass>>;

#[allow(dead_code)]
#[derive(Debug)]
struct OptPipelineBackendOptions {
    filter_debug_info: bool,
    filter_ir_metadata: bool,
    full_module: bool,
    no_discard_value_names: bool,
    demangle: bool,
    library_functions: bool,
    apply_filters: bool,
}

#[derive(Debug)]
struct PassDump {
    header: String,
    affected_function: Option<String>,
    machine: bool,
    lines: String,
}

#[derive(Debug)]
struct SplitPassDump {
    header: String,
    machine: bool,
    functions: HashMap<String, Vec<String>>,
}

pub struct LlvmPassDumpParser {
    ir_dump_header: Regex,
    machine_code_dump_header: Regex,
    // function_define: Regex,
    // machine_function_begin: Regex,
    function_end: Regex,
    machine_function_end: Regex,
}

#[derive(Debug, Error)]
pub enum PassDumpError {
    #[error(
        "Consecutive pass headers in dump file do not match:\n\
        First:  '{before_header}'\n\
        Second: '{after_header}'\n\n\
        'optdiff' compares each pass dump with its immediate next dump in the file.\n\
        This error typically occurs when multiple compiler instances write to the same dump file.\n\
        Please run a single compiler instance at a time."
    )]
    PassMismatch {
        before_header: String,
        after_header: String,
    },
}
impl LlvmPassDumpParser {
    fn new() -> Self {
        LlvmPassDumpParser {
            ir_dump_header: Regex::new(
                r"^;?\s?(?:\*{3} (.+) \*{3}|// -----// (.+) //----- //)(?:\s+\((?:function: |loop: )(%?[\w$.]+)\))?(?:;.+)?$",
            )
            .unwrap(),
            machine_code_dump_header: Regex::new(r"^# \*{3} (.+) \*{3}:$").unwrap(),
            // function_define: Regex::new(r"^define .+ @([\w.]+|'[^']+')\(.+$").unwrap(),
            // machine_function_begin: Regex::new(r"^# Machine code for function ([\w$.]+):.*$")
            //     .unwrap(),
            function_end: Regex::new(r"^}$").unwrap(),
            machine_function_end: Regex::new(r"^# End machine code for function ([\w$.]+).$")
                .unwrap(),
        }
    }

    fn breakdown_output_into_pass_dumps(&self, ir: &str) -> Vec<PassDump> {
        let mut raw_passes = Vec::new();
        let mut pass: Option<PassDump> = None;
        let mut last_was_blank = false;

        for line in ir.lines() {
            let is_header = line.starts_with("; *** ")
                || line.starts_with("*** ")
                || line.starts_with("// -----// ")
                || line.starts_with("# *** ");

            if is_header {
                if let Some(current_pass) = pass.take() {
                    raw_passes.push(current_pass);
                }
                let header_prefix = if line.starts_with(';') || line.starts_with("#") {
                    "; *** "
                } else if line.starts_with("//") {
                    "// -----// "
                } else {
                    "*** "
                };
                let header_suffix = if line.starts_with("//") {
                    " //----- //"
                } else {
                    " ***"
                };
                let header = &line[header_prefix.len()..];
                let header = &header[..header.find(header_suffix).unwrap()];

                let affected_function =
                    if let Some(idx) = line.find("(function: ").or(line.find("(loop: ")) {
                        let content = &line[idx + 1..];
                        Some(
                            content[content.find(' ').unwrap() + 1..content.find(')').unwrap()]
                                .to_string(),
                        )
                    } else {
                        None
                    };

                pass = Some(PassDump {
                    header: header.to_string(),
                    affected_function,
                    machine: line.starts_with("#"),
                    lines: String::new(),
                });

                last_was_blank = true;
            } else if let Some(ref mut current_pass) = pass {
                if line.trim().is_empty() {
                    if !last_was_blank {
                        current_pass.lines += line;
                        current_pass.lines += "\n";
                    }
                    last_was_blank = true;
                } else {
                    current_pass.lines += line;
                    current_pass.lines += "\n";
                    last_was_blank = false;
                }
            }
        }
        if let Some(current_pass) = pass {
            raw_passes.push(current_pass);
        }
        raw_passes
    }

    fn breakdown_pass_dumps_into_functions(&self, dump: PassDump) -> SplitPassDump {
        let mut pass = SplitPassDump {
            header: dump.header,
            machine: dump.machine,
            functions: HashMap::new(),
        };
        let mut func: Option<(String, Vec<String>)> = None;
        let mut is_machine_function_open = false;

        for line in dump.lines.lines() {
            let line = line.to_string();
            let is_ir_fn = line.starts_with("define ")
                || line.trim().starts_with("func.func ")
                || line.trim().starts_with("tt.func");
            let is_machine_fn = line.starts_with("# Machine code for function ");

            if is_ir_fn {
                if func.is_some() {
                    let (name, lines) = func.take().unwrap();
                    pass.functions.insert(name, lines);
                }
                let name = &line[line.find('@').unwrap() + 1..];
                let name = &name[..name.find('(').unwrap()];
                func = Some((name.to_string(), vec![line]));

                is_machine_function_open = false;
            } else if is_machine_fn {
                if func.is_some() {
                    let (name, lines) = func.take().unwrap();
                    pass.functions.insert(name, lines);
                }
                let name = &line["# Machine code for function ".len()..line.find(':').unwrap()];
                func = Some((name.to_string(), vec![line]));
                is_machine_function_open = true;
            } else if line.starts_with("; Preheader:") {
                if func.is_none() {
                    func = Some(("<loop>".to_string(), vec![line]));
                }
            } else if let Some((ref mut name, ref mut lines)) = func {
                if (!is_machine_function_open && self.function_end.is_match(line.trim()))
                    || (is_machine_function_open && self.machine_function_end.is_match(line.trim()))
                {
                    lines.push(line);
                    pass.functions.insert(name.clone(), lines.clone());
                    func = None;
                } else {
                    lines.push(line);
                }
            }
        }

        if let Some((name, lines)) = func {
            pass.functions.insert(name, lines);
        }

        pass
    }

    fn breakdown_into_pass_dumps_by_function(
        &self,
        pass_dumps: Vec<SplitPassDump>,
    ) -> HashMap<String, Vec<PassDump>> {
        let mut pass_dumps_by_function = HashMap::new();
        let mut previous_function: Option<String> = None;

        for pass in pass_dumps {
            for (function_name, lines) in pass.functions {
                let name = if function_name == "<loop>" {
                    previous_function.clone().unwrap()
                } else {
                    function_name.clone()
                };
                if !pass_dumps_by_function.contains_key(&name) {
                    pass_dumps_by_function.insert(name.clone(), Vec::new());
                }
                pass_dumps_by_function
                    .get_mut(&name)
                    .unwrap()
                    .push(PassDump {
                        header: pass.header.clone(),
                        affected_function: None,
                        machine: pass.machine,
                        lines: lines.join("\n"),
                    });
                if function_name != "<loop>" {
                    previous_function = Some(name);
                }
            }
        }
        pass_dumps_by_function
    }

    fn associate_full_dumps_with_functions(
        &self,
        pass_dumps: Vec<PassDump>,
    ) -> HashMap<String, Vec<PassDump>> {
        let mut pass_dumps_by_function = HashMap::new();

        for pass in &pass_dumps {
            if let Some(ref func) = pass.affected_function {
                if !pass_dumps_by_function.contains_key(func) {
                    pass_dumps_by_function.insert(func.clone(), Vec::new());
                }
            }
        }

        pass_dumps_by_function.insert("<Full Module>".to_string(), Vec::new());
        let mut previous_function: Option<String> = None;

        for pass in pass_dumps {
            if let Some(ref func) = pass.affected_function {
                let func_name = if func.starts_with('%') {
                    previous_function.clone().unwrap()
                } else {
                    func.clone()
                };
                pass_dumps_by_function
                    .get_mut(&func_name)
                    .unwrap()
                    .push(PassDump {
                        header: format!("{} ({})", pass.header, func_name),
                        affected_function: Some(func_name.clone()),
                        machine: pass.machine,
                        lines: pass.lines.clone(),
                    });
                previous_function = Some(func_name);
            } else {
                for (_, entry) in pass_dumps_by_function.iter_mut() {
                    entry.push(PassDump {
                        header: pass.header.clone(),
                        affected_function: None,
                        machine: pass.machine,
                        lines: pass.lines.clone(),
                    });
                }
                previous_function = None;
            }
        }
        pass_dumps_by_function
    }

    fn match_pass_dumps(
        &self,
        pass_dumps_by_function: HashMap<String, Vec<PassDump>>,
    ) -> Result<OptPipelineResults, PassDumpError> {
        let mut final_output = HashMap::new();

        for (function_name, pass_dumps) in pass_dumps_by_function {
            let mut passes: Vec<Pass> = Vec::new();
            let mut i = 0;

            while i < pass_dumps.len() {
                let mut pass = Pass {
                    name: "".to_string(),
                    machine: false,
                    after: String::new(),
                    before: String::new(),
                    ir_changed: true,
                };
                let current_dump = &pass_dumps[i];
                let next_dump = if i < pass_dumps.len() - 1 {
                    Some(&pass_dumps[i + 1])
                } else {
                    None
                };

                if current_dump.header.starts_with("IR Dump After ") {
                    pass.name = current_dump.header["IR Dump After ".len()..].to_string();
                    pass.after = current_dump.lines.clone();
                    i += 1;
                } else if current_dump.header.starts_with("IR Dump Before ") {
                    if let Some(next_dump) = next_dump {
                        if next_dump.header.starts_with("IR Dump After ") {
                            passes_match(&current_dump.header, &next_dump.header)?;
                            assert!(current_dump.machine == next_dump.machine);
                            pass.name = current_dump.header["IR Dump Before ".len()..].to_string();
                            pass.before = current_dump.lines.clone();
                            pass.after = next_dump.lines.clone();
                            i += 2;
                        } else {
                            pass.name = current_dump.header["IR Dump Before ".len()..].to_string();
                            pass.before = current_dump.lines.clone();
                            i += 1;
                        }
                    } else {
                        pass.name = current_dump.header["IR Dump Before ".len()..].to_string();
                        pass.before = current_dump.lines.clone();
                        i += 1;
                    }
                } else {
                    panic!("Unexpected pass header {}", current_dump.header);
                }
                pass.machine = current_dump.machine;

                // handle isel diff, and NOT handle machine-outliner (before != after)
                if let Some(previous_pass) = passes.last() {
                    if !previous_pass.machine && pass.machine && pass.before != pass.after {
                        pass.before = previous_pass.after.clone();
                    }
                }

                pass.ir_changed = pass.before != pass.after;
                passes.push(pass);
            }

            for i in 0..passes.len() {
                // If 'before' is empty and there’s a previous pass, use its 'after'
                if passes[i].before.is_empty() && i > 0 {
                    passes[i].before = passes[i - 1].after.clone();
                }

                // If 'after' is empty and there’s a next pass, use its 'before'
                if passes[i].after.is_empty() && i < passes.len() - 1 {
                    passes[i].after = passes[i + 1].before.clone();
                }

                // Recalculate ir_changed after filling
                passes[i].ir_changed = passes[i].before != passes[i].after;
            }

            final_output.insert(function_name, passes);
        }
        Ok(final_output)
    }

    fn breakdown_output(
        &self,
        ir: &str,
        opt_pipeline_options: &OptPipelineBackendOptions,
    ) -> Result<OptPipelineResults, PassDumpError> {
        let raw_passes = self.breakdown_output_into_pass_dumps(ir);

        if opt_pipeline_options.full_module {
            let pass_dumps_by_function = self.associate_full_dumps_with_functions(raw_passes);
            Ok(self.match_pass_dumps(pass_dumps_by_function)?)
        } else {
            let pass_dumps = raw_passes
                .into_iter()
                .map(|dump| self.breakdown_pass_dumps_into_functions(dump))
                .collect();
            let pass_dumps_by_function = self.breakdown_into_pass_dumps_by_function(pass_dumps);
            Ok(self.match_pass_dumps(pass_dumps_by_function)?)
        }
    }

    fn apply_ir_filters(
        &self,
        ir: &str,
        opt_pipeline_options: &OptPipelineBackendOptions,
    ) -> String {
        let mut inline_filters = vec![r"(?m),? #\d+( \{)?$"];
        let mut line_filters = vec![
            r"; ModuleID = '.+'",
            r"(source_filename|target datalayout|target triple) = '.+'",
            r"; Function Attrs: .+",
            r"declare .+",
            r"attributes #\d+ = \{ .+ \}",
        ];

        let debug_inline_filters = [r",? !dbg !\d+", r",? debug-location !\d+"];
        let metadata_inline_filters = [r",?(?: ![\d.A-Za-z]+){2}"];

        let debug_line_filters = [
            r"\s+(tail\s)?call void @llvm\.dbg.+",
            r"[ \t]+DBG_.+",
            r"(!\d+) = (?:distinct )?!DI([A-Za-z]+)\(([^)]+?)\).*", // appended .*
            r"(!\d+) = (?:distinct )?!\{.*\}.*",                    // appended .*
            r"(![.A-Z_a-z-]+) = (?:distinct )?!\{.*\}.*",           // appended .*
        ];

        if opt_pipeline_options.filter_debug_info {
            line_filters.extend(debug_line_filters);
            inline_filters.extend(debug_inline_filters);
        }

        if opt_pipeline_options.filter_ir_metadata {
            inline_filters.extend(metadata_inline_filters);
        }

        let line_re = line_filters
            .into_iter()
            .map(|re| format!(r"(?:{})", re))
            .join("|")
            .to_string();
        let line_re = format!(r"(?m)^(:?{})(?:\r\n|\n|\r)", line_re);

        let inline_re = inline_filters
            .into_iter()
            .map(|re| format!(r"(?:{})", re))
            .join("|")
            .to_string();

        let combined = format!("(:?{})|(:?{})", line_re, inline_re);
        let re = Regex::new(&combined).unwrap();

        re.replace_all(ir, "").to_string()
    }

    fn process<'a>(
        &self,
        output: &'a str,
        opt_pipeline_options: &OptPipelineBackendOptions,
    ) -> Result<(&'a str, OptPipelineResults), PassDumpError> {
        let offset = {
            let mut pos = 0;
            let newlines = memchr_iter(b'\n', output.as_bytes());

            for newline_pos in newlines {
                let line = &output[pos..newline_pos];
                if self.ir_dump_header.is_match(line)
                    || self.machine_code_dump_header.is_match(line)
                {
                    break;
                }
                pos = newline_pos + 1;
            }
            pos
        };
        let ir = &output[offset..];
        let ir = match opt_pipeline_options.apply_filters {
            true => &self.apply_ir_filters(ir, opt_pipeline_options),
            false => ir,
        };
        Ok((
            &output[..offset],
            self.breakdown_output(ir, opt_pipeline_options)?,
        ))
    }
}

fn passes_match(before: &str, after: &str) -> Result<(), PassDumpError> {
    assert!(before.starts_with("IR Dump Before "));
    assert!(after.starts_with("IR Dump After "));
    let before = &before["IR Dump Before ".len()..];
    let mut after = &after["IR Dump After ".len()..];
    if after.ends_with(" (invalidated)") {
        after = &after[..after.len() - " (invalidated)".len()];
    }

    if before == after {
        Ok(())
    } else {
        Err(PassDumpError::PassMismatch {
            before_header: before.to_string(),
            after_header: after.to_string(),
        })
    }
}

pub fn process(
    dump: &str,
    apply_filters: bool,
    full_module: bool,
) -> Result<(&str, OptPipelineResults), PassDumpError> {
    let llvm_pass_dump_parser = LlvmPassDumpParser::new();
    llvm_pass_dump_parser.process(
        dump,
        &OptPipelineBackendOptions {
            filter_debug_info: true,
            filter_ir_metadata: true,
            full_module,
            no_discard_value_names: false,
            demangle: false,
            library_functions: false,
            apply_filters,
        },
    )
}
