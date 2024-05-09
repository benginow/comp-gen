mod cost;
mod desugar;
mod error;
mod fuzz;
mod handwritten;
mod lang;
mod rewriteconcats;
mod smt;
mod stringconversion;
mod synthesis;
mod desugared_lang;
mod desugared_synthesis;
mod desugared_workloads;
mod util;

use crate::desugar::Desugar;
use anyhow::Context;
use argh::FromArgs;
use comp_gen::config::{self, default_compiler_config};
use egg::*;
pub use error::Res;
use log::info;
use std::{fs, io::Write, path::PathBuf, process};

// use std::sync::{Once};
// pub static mut CANON_FORCE: Option<bool> = None;
// pub static INIT: Once = Once::new();

/// Generate and run an automatically generated compiler
/// for the Diospyros vector language.
#[derive(FromArgs)]
struct Cmdline {
    #[argh(subcommand)]
    nested: Commands,
}

#[derive(FromArgs)]
#[argh(subcommand)]
enum Commands {
    /// synthesize a new ruleset
    Synth(SynthOpts),
    /// compile an input program using a ruleset
    Compile(CompileOpts),
}

#[derive(Clone, FromArgs)]
#[argh(subcommand, name = "synth")]
/// Synth options.
pub struct SynthOpts {
    #[argh(positional)]
    output: String,

    /// path to a dios configuration file
    #[argh(option, from_str_fn(read_dios_config))]
    config: Option<synthesis::DiosConfig>,

    /// path to a synthesis config file
    #[argh(option, from_str_fn(read_synth_config))]
    synth: Option<synthesis::SynthesisConfig>,

    /// path to a chkpt file
    #[argh(option, from_str_fn(read_path))]
    checkpoint: Option<PathBuf>,
}


/// Read a `synthesis::DiosConfig` from a path (represented as a `&str`).
fn read_synth_config(path: &str) -> Result<synthesis::SynthesisConfig, String> {
    let config_file = fs::File::open(path)
        .context("open synth path")
        .map_err(|e| e.to_string())?;
    let parsed: synthesis::SynthesisConfig = serde_json::from_reader(config_file)
        .context(format!("parse {path:?} as dios_config"))
        .map_err(|e| e.to_string())?;
    Ok(parsed)
}

/// Read a `synthesis::DiosConfig` from a path (represented as a `&str`).
fn read_dios_config(path: &str) -> Result<synthesis::DiosConfig, String> {
    let config_file = fs::File::open(path)
        .context("open config path")
        .map_err(|e| e.to_string())?;
    let parsed: synthesis::DiosConfig = serde_json::from_reader(config_file)
        .context(format!("parse {path:?} as dios_config"))
        .map_err(|e| e.to_string())?;
    Ok(parsed)
}

#[derive(Debug, FromArgs)]
#[argh(subcommand, name = "compile")]
/// Compile options.
struct CompileOpts {
    /// input file
    #[argh(positional)]
    input: String,

    /// dios-example-gen binary
    #[argh(option, from_str_fn(read_path))]
    dios_example_bin: PathBuf,

    /// diosbinary
    #[argh(option, from_str_fn(read_path))]
    dios_bin: PathBuf,

    /// dios example params
    #[argh(option, from_str_fn(read_path))]
    dios_params: PathBuf,

    /// vector width
    #[argh(option)]
    vector_width: usize,

    /// ruleset
    #[argh(option, from_str_fn(read_path))]
    rules: PathBuf,

    /// pre-desugared
    #[argh(switch)]
    pre_desugared: bool,

    /// config
    #[argh(option, from_str_fn(read_compiler_config))]
    config: Option<comp_gen::config::CompilerConfiguration>,

    /// output dir
    #[argh(option, from_str_fn(read_path))]
    output_dir: Option<PathBuf>,

    /// cost fun
    #[argh(option)]
    costfn: String,
}

fn read_path(path: &str) -> Result<PathBuf, String> {
    Ok(PathBuf::from(path))
}

fn read_compiler_config(
    path: &str,
) -> Result<comp_gen::config::CompilerConfiguration, String> {
    let file = fs::File::open(path).map_err(|e| format!("{e}"))?;
    let compile_config =
        serde_json::from_reader(file).map_err(|e| format!("{e}"))?;
    Ok(compile_config)
}

/// Synthesize a new ruleset using `Ruler`.
fn synth(synth_opts: SynthOpts) -> Res<()> {
    let synth_config = synth_opts.synth.unwrap_or_default();
    // INIT.call_once(|| {
    //     // Since this access is inside a call_once, before any other accesses, it is safe
    //     unsafe {
    //         CANON_FORCE = Some(synth_config.canon_force);
    //     }
    // });
    let report = synthesis::run(
        synth_opts.config.unwrap_or_default(),
        synth_config,
        synth_opts.checkpoint,
    )?;

   

    let file = std::fs::File::create(&synth_opts.output)
        .unwrap_or_else(|_| panic!("Failed to open '{}'", &synth_opts.output));
    // report.to_file(&synth_opts.output);
    serde_json::to_writer_pretty(file, &report).expect("failed to write json");
    Ok(())
}

fn compile_shfl(prog: egg::RecExpr<desugared_lang::VecLangDesugared>) -> (f64, RecExpr<desugared_lang::VecLangDesugared>) {
    let mut compiler: comp_gen::Compiler<desugared_lang::VecLangDesugared, (), _> = comp_gen::Compiler::with_cost_fn(cost::VecCostFnDesugared::dios());

    // compiler.add_external_rules(&PathBuf::from("../sum_and_shufl_rules.json"));

    compiler.with_init_node(desugared_lang::VecLangDesugared::Const(desugared_lang::Value::Int(0)));

        // add predesugared rules
    compiler.add_external_rules(&PathBuf::from("../sum_and_shufl_rules.json"));
    // add litvec rules
    compiler
        .add_rules(
            handwritten::build_litvec_rule_desugared(4).into_iter(),
        )
        .output_rule_distribution("rule_distribution.csv", |x| x);


    let config = default_compiler_config();
    compiler.with_config(&config);

    // compiler.with_explanations();
    let (cost, prog, mut _eg) = compiler.compile(prog);
    (cost, prog)
        
}

/// Run the entire phased eqsat compilation process on a Dios program.
///  - this first calls the existing Dios code to generate an input program
///  - once we have an input program, we construct and call a `comp-gen` compiler.
fn compile(opts: CompileOpts) -> Res<()> {
    log::debug!("{opts:#?}");

    let output_dir = if let Some(path) = opts.output_dir {
        path
    } else {
        PathBuf::from(format!("{}-out", opts.input.as_str()))
    };

    // generate the example with dios_example_gen
    process::Command::new(opts.dios_example_bin)
        .arg("-w")
        .arg(opts.vector_width.to_string())
        .arg("-b")
        .arg(&opts.input)
        .arg("-o")
        .arg(&output_dir)
        .arg("-p")
        .arg(opts.dios_params)
        .stdout(process::Stdio::inherit())
        .stderr(process::Stdio::inherit())
        .output()?;

    // read in program
    let prog_str = fs::read_to_string(output_dir.join("spec.rkt"))?;
    let converted: String = stringconversion::convert_string(&prog_str)?;

    // rewrite into concats of vecs
    let concats =
        rewriteconcats::list_to_concats(opts.vector_width, &converted);
    // finally parse into a rec expr
    let prog: egg::RecExpr<lang::VecLang> = concats?.parse()?;
    // log::debug!("input: {}", prog.pretty(80));

    let mut compiler: comp_gen::Compiler<lang::VecLang, (), _> =
        comp_gen::Compiler::with_cost_fn(match opts.costfn.as_str() {
            "alternative" => cost::VecCostFn::alternative(),
            "dios" => cost::VecCostFn::dios(),
            "accurate" => cost::VecCostFn::accurate(),
            _ => panic!("Not a valid cost function."),
        });

    // add rules to compiler
    compiler.with_init_node(lang::VecLang::Const(lang::Value::Int(0)));

    // add predesugared rules
    if opts.pre_desugared {
        compiler.add_external_rules(&opts.rules);
    } else {
        compiler.add_processed_external_rules(&opts.rules, |p| {
            p.desugar(opts.vector_width)
        });
    }

    // add litvec rules
    compiler
        .add_rules(
            handwritten::build_litvec_rule(opts.vector_width).into_iter(),
        )
        .output_rule_distribution("rule_distribution.csv", |x| x);

    // load configuration
    if let Some(config) = &opts.config {
        compiler.with_config(config);
    }

    // compiler.with_explanations();
    let (cost, prog, mut _eg) = compiler.compile(prog);
    info!("cost: {cost}");

    //vec sum and shufl stuff
    let string_prog = prog.to_string();
    let prog: egg::RecExpr<desugared_lang::VecLangDesugared> = string_prog.parse()?;

    let (cost, prog) = compile_shfl(prog);

    // write to spec.rkt
    let path = output_dir.join("res.rkt");
    let mut spec_file = fs::File::create(&path)?;
    log::debug!("writing to {path:?}");
    writeln!(spec_file, "{}", prog)?;

    // call ./dios -w <vec_width> --egg --suppress-git -o <dir>/kernel.c <dir>
    // this generates the kernel.c file
    process::Command::new(opts.dios_bin)
        .arg("-w")
        .arg(opts.vector_width.to_string())
        .arg("--egg")
        .arg("--suppress-git")
        .arg("-o")
        .arg(output_dir.join("kernel.c"))
        .arg(output_dir)
        .stdout(process::Stdio::inherit())
        .stderr(process::Stdio::inherit())
        .output()?;

    Ok(())
}

fn main() -> Res<()> {
    let _ = env_logger::builder().try_init();

    let args: Cmdline = argh::from_env();

    match args.nested {
        Commands::Synth(opts) => synth(opts),
        Commands::Compile(opts) => compile(opts),
    }

    
    // println!("{:#?}", desugared_synthesis::run());
    // Ok(())
}


// shuffle vectors: 
// swaps: Vec (1 0 2 3), Vec (0 1 3 2), Vec (3 1 2 0), Vec (0 3 2 1), Vec(0 2 1 3), Vec(2 1 0 3)
// rotations: Vec (3 0 1 2), Vec (1 2 3 0)
#[cfg(test)]
mod shuffle_tests {
    use super::*;
    use egg::*;
    use log::debug;

    #[test]
    fn shuffling() {
        let program = "(List (VecAdd (VecAdd (VecAdd 
            (Vec (Get I 0) 0 0 0)
            (Vec (Get I 1) 0 0 0))
            (Vec (Get I 2) 0 0 0))
            (Vec (Get I 3) 0 0 0))
        )";
        let concats = rewriteconcats::list_to_concats(4, &program).unwrap();
        println!("list to concats returned this: {}",concats);
        let prog: egg::RecExpr<desugared_lang::VecLangDesugared> = concats.parse().unwrap();
        println!("parsing concats returns this: {}", prog);

        let mut compiler: comp_gen::Compiler<desugared_lang::VecLangDesugared, (), _> = comp_gen::Compiler::with_cost_fn(cost::VecCostFnDesugared::dios());

        // add rules to compiler
        compiler.with_init_node(desugared_lang::VecLangDesugared::Const(desugared_lang::Value::Int(0)));

        // add predesugared rules
        compiler.add_external_rules(&PathBuf::from("testing_rulesets/sum_and_shufl_rules.json"));

        // add litvec rules
        compiler
            .add_rules(
                handwritten::build_litvec_rule_desugared(4).into_iter(),
            )
            .output_rule_distribution("rule_distribution.csv", |x| x);


        let config = default_compiler_config();
        compiler.with_config(&config);

        // compiler.with_explanations();
        let (cost, prog, mut _eg) = compiler.compile(prog);
        println!("this is the outputted program: {}", prog);
        println!("cost: {cost}");
    }
}

#[cfg(test)]
mod sum_tests {
    use super::*;
    use egg::*;
    use log::debug;

    #[test]
    fn generate_vecsum_rules() {
        let ruleset = desugared_synthesis::run().unwrap();
        println!("{:#?}", ruleset);
    }

    #[test]
    fn futzing_about() {
        let spec: String = "(list
            (box (* I$0 F$0))
            (box (+ (* I$0 F$1) (* I$1 F$0)))
            (box (* I$1 F$1))
            (box (+ (* I$0 F$2) (* I$2 F$0)))
            (box (+ (* I$0 F$3) (* I$1 F$2) (* I$2 F$1) (* I$3 F$0)))
            (box (+ (* I$1 F$3) (* I$3 F$1)))
            (box (* I$2 F$2))
            (box (+ (* I$2 F$3) (* I$3 F$2)))
            (box (* I$3 F$3)))".to_string();
        let program: String = stringconversion::convert_string(&spec).unwrap();
        println!("convert string returned this: {}",program);
        let concats = rewriteconcats::list_to_concats(4, &program).unwrap();
        println!("list to concats returned this: {}",concats);
        let prog: egg::RecExpr<lang::VecLang> = concats.parse().unwrap();
        println!("parsing concats returns this: {}", prog);
    }

    #[test]
    fn vecsum_fun() {
        // this doesn't seem 100% right, but it is what it is.
        let program = "(List (+ (Get I 0) (+ (Get I 1) (+ (Get I 2) (Get I 3)))))";
        let concats = rewriteconcats::list_to_concats(4, &program).unwrap();
        println!("list to concats returned this: {}",concats);
        let prog = concats.parse().unwrap();
        println!("parsing concats returns this: {}", prog);

        let mut compiler: comp_gen::Compiler<desugared_lang::VecLangDesugared, (), _> = comp_gen::Compiler::with_cost_fn(cost::VecCostFnDesugared::dios());

        // add rules to compiler
        compiler.with_init_node(desugared_lang::VecLangDesugared::Const(desugared_lang::Value::Int(0)));

        // add predesugared rules
        compiler.add_external_rules(&PathBuf::from("sum_rules.json"));

        // add litvec rules
        compiler
            .add_rules(
                handwritten::build_litvec_rule_desugared(4).into_iter(),
            )
            .output_rule_distribution("rule_distribution.csv", |x| x);


        let config = default_compiler_config();
        compiler.with_config(&config);

        // compiler.with_explanations();
        let (cost, prog, mut _eg) = compiler.compile(prog);
        println!("this is the outputted program: {}", prog);


        println!("cost: {cost}");
    }

}