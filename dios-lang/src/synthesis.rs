use comp_gen::ruler::{
    self, enumo::*, recipe_utils,
};
use log::debug;
use num::{integer::Roots, ToPrimitive};
// ruler no longer has Equality and Synthesizer
use ruler::{
    CVec
};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::thread::JoinHandle;

use crate::{lang, synth, Res};
use crate::util::{generate_rules, handpicked, handpicked_thinner, iter_dios_lt, vals, vars};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DiosConstant {
    pub kind: String,
    pub value: i64,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DiosSeedRules {
    pub lhs: String,
    pub rhs: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
enum Operations {
    Algorithm,
    HandPicked,
    HandPickedThinner,
    AllAtOnce
}
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SynthesisConfig {
    pub name: String,
    pub operation_matching: Operations,
    pub canon_force: bool,
    pub arity_shorting: bool,
}

impl Default for SynthesisConfig {
    fn default() -> Self {
        Self {
            name: "default".to_string(),
            operation_matching: Operations::AllAtOnce,
            canon_force: false,
            arity_shorting: false
        }
    }
}

/// Dios configuration struct
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DiosConfig {
    pub constants: Vec<DiosConstant>,
    pub seed_rules: Vec<String>,
    pub unops: Vec<String>,
    pub binops: Vec<String>,
    pub triops: Vec<String>,
    pub use_scalar: bool,
    pub use_vector: bool,
    pub variable_duplication: bool,
    pub vector_size: usize,
    pub always_smt: bool,
    pub smt_fallback: bool,
}

impl Default for DiosConfig {
    fn default() -> Self {
        Self {
            constants: vec![],
            seed_rules: vec![],
            unops: vec![],
            binops: vec![],
            triops: vec![],
            use_scalar: false,
            use_vector: false,
            variable_duplication: false,
            vector_size: 1,
            always_smt: false,
            smt_fallback: true,
        }
    }
}


pub fn vecs_eq(lvec: &CVec<lang::VecLang>, rvec: &CVec<lang::VecLang>) -> bool {
    if lvec.iter().all(|x| x.is_none()) && rvec.iter().all(|x| x.is_none()) {
        false
    } else {
        lvec.iter().zip(rvec.iter()).all(|tup| match tup {
            (Some(l), Some(r)) => l == r,
            (None, None) => true,
            _ => false,
        })
    }
}

fn arity_shorting(depth: usize, values: Workload, variable_names: Workload, operations: Vec<Vec<String>>) -> Workload {
    // there will ops up to triops here -> if this changes, this code needs to change
    let iter_depth = {
    if depth <= 2{
         depth
    }
    else {
        depth - 1
    }};
    let one_less_workload = iter_dios_lt(iter_depth, values.clone(), variable_names.clone(), &mut vec![], operations[0..operations.len() - 1].to_vec());

    // for example, 
    // let mut triop_workload = Workload::new(["EXPR", "(OP1 EXPR)", "(OP2 EXPR)", "(OP3 EXPR EXPR EXPR)"]);
    let mut truncated_workload = recipe_utils::base_lang(operations.len()).plug("VAL", &values.clone()).plug("VAR", &variable_names.clone());
    for (i, operation_layer) in itertools::enumerate(operations) {
        truncated_workload = truncated_workload.plug(format!("OP{}", i+1), &Workload::new(operation_layer.clone()));
    }
    // not sure what happens with val here -> tbd
    let final_workload = truncated_workload
                            .plug("EXPR",&one_less_workload);

    final_workload
}

fn seed() -> ruler::enumo::Ruleset<lang::VecLang> {
    Ruleset::new([
        "(+ ?a ?b) ==> (+ ?b ?a)",
        "(* ?a ?b) ==> (* ?b ?a)",
        "(VecAdd ?a ?b) ==> (VecAdd ?b ?a)",
        "(VecMul ?a ?b) ==> (VecMul ?b ?a)",
        "(VecAdd (Vec ?b) (Vec ?a)) ==> (Vec (+ ?b ?a))", 
        "(VecDiv (Vec ?b) (Vec ?a)) ==> (Vec (/ ?b ?a))"]
    )
}


fn generate_workload(depth: usize, vals: Workload, vars: Workload,  filters: Vec<Filter>, ops: Vec<Vec<String>>, arity_truncation: bool, is_canon: bool) -> Workload {
    let workload = if arity_truncation && ops.len() >= 3 {
        println!("calling arity truncation for {ops:?}");
        arity_shorting(depth, vals, vars, ops)
    }
    else {
        println!("calling iter dios for {ops:?}");
        iter_dios_lt(depth, vals, vars, &mut filters.clone(), ops)
    };
    if !is_canon {
        workload.is_not_canon();
    }
    // debug!("Workload is: {:#?}", workload.clone().force().collect::<Vec<_>>());
    workload
}

// fn build_graph(sets: Vec<Vec<String>>) {
    
// }

fn randomly_generate_operation_sets(set_size: usize, ops: Vec<Vec<String>>) -> Vec<(Vec<Vec<String>>, usize)> {
    use std::collections::{HashMap, HashSet};
    use rand::prelude::SliceRandom;

    // change usize 
    let mut graph: HashMap<String, HashSet<String>> = HashMap::new();

    let mut flattened: Vec<&String> = ops.iter().flat_map(|v| v.iter()).collect();
    // we may want some randomness here -> could be interesting. then again, may add some variability to the rulesets generated.
    flattened.shuffle(&mut rand::thread_rng());
    let sets: Vec<Vec<&String>> = flattened.chunks(set_size).map(|chunk| chunk.to_vec()).collect();
    if sets.len() > 0 && sets[sets.len()-1].len() == 1 {
        
    }

    vec![]
}



fn ruleset_gen(rules: &mut Ruleset<lang::VecLang>, 
                        ops: Vec<Vec<String>>, 
                        vals: Workload, 
                        vars: Workload, 
                        arity_truncation: bool,
                        operations: Operations,
                        canon_force: bool
                        ) 
{
    use recipe_utils::run_workload;


    let operation_iterations: Vec<(Vec<Vec<String>>, usize)> = match operations {
        Operations::Algorithm => {
            // TODO
            vec![(ops,3)]
        }
        Operations::HandPicked => {
            handpicked()
        }
        Operations::HandPickedThinner => {
            handpicked_thinner()
        }
        Operations::AllAtOnce => vec![(ops, 3)],
    };

    for (operation_set, depth) in operation_iterations {
        let contains_vector_ops = operation_set.iter().flatten().any(|x| x.contains("Vec"));
        let filters = { 
            if contains_vector_ops {
                vec![Filter::Contains("Vec".parse().unwrap())]
            }
            else { 
                // theoretically, this is just the scalar operation pass
                vec![]
            }
        };
        let workload: ruler::enumo::Workload = generate_workload(depth, vals.clone(), vars.clone(), filters, operation_set, arity_truncation, canon_force);
        println!("depth is {depth}");

        let generated_rules = run_workload(workload, (*rules).clone(), ruler::Limits::synthesis(), ruler::Limits::synthesis(), true);
        rules.extend(generated_rules)
    }
}


pub fn run(
    dios_config: DiosConfig,
    synth_config: SynthesisConfig,
    _chkpt_path: Option<PathBuf>,
) -> Res<ruler::enumo::Ruleset<lang::VecLang>>
{
    use core::time::Duration;
    use std::time::Instant;

    let run_name = synth_config.name.clone();
    log::info!("running with config: {dios_config:#?}");
    log::info!("running with synth config: {:#?}", synth_config.clone());

    let beginning = Instant::now();

    // add all seed rules
    let mut seed_rules : ruler::enumo::Ruleset<lang::VecLang> = ruler::enumo::Ruleset::default();

    for rule in dios_config.seed_rules.into_iter() {
        match ruler::enumo::Rule::from_string(&rule) {
            Ok(r) => {
                seed_rules.add(r.0);
                match r.1 {
                    Some(bidirectional) => seed_rules.add(bidirectional),
                    None => ()
                }
            },
            Err(msg) => panic!("provided a malformed seed rule, {:?}\n{:?}", rule, msg)
        } 
    }

    seed_rules.extend(seed());

    let vals = vals();
    let vars = vars();

    let mut rules = seed_rules.clone();
    let operations = vec![dios_config.unops.clone(), dios_config.binops.clone(), dios_config.triops.clone()];

    // let (vec_ops, scalar_ops) = crate::util::extract_vector_operations(operations);
    
    // let rules_scalar = Ruleset::from_file("rational_rules.txt");
    // rules.extend(rules_scalar);
    // let rules = 
    ruleset_gen(&mut rules, operations, vals, vars, synth_config.arity_shorting, synth_config.operation_matching, synth_config.canon_force);


    let time_taken = Instant::now() - beginning;
    ruler::logger::log_rules(&rules, Some("rulesets/ruleset.json"), run_name, time_taken);

    Ok(rules)
}