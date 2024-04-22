use comp_gen::ruler::{
    self, enumo::*,
};
use egg::{EGraph, Id};
use log::debug;
use rand::Rng;
use rand_pcg::Pcg32;
use ruler::{
    map, self_product, CVec, SynthAnalysis, SynthLanguage
};

use crate::{desugared_lang, desugared_workloads::*, smt::SmtEquals, Res, util::*};

fn sum_rules(
    ops: Vec<Vec<String>>, 
    run_name: &str
) -> Ruleset<desugared_lang::VecLangDesugared> 
{
    let workload = workload_sum(ops);
    let mut rules = Ruleset::default();
    generate_rules(&workload, &mut rules, run_name, true, sum_workload_depth());

    rules.clone()
}

fn shfl_rules(
    ops: Vec<Vec<String>>, 
    run_name: &str
) -> Ruleset<desugared_lang::VecLangDesugared> 
{
    let workload = workload_shfl(ops);
    println!("h");
    println!("shuffle workload looks like this: {:?}", workload.clone().force().collect::<Vec<_>>());
    let mut rules = Ruleset::default();
    generate_rules(&workload, &mut rules, run_name, true, sum_workload_depth());

    rules.clone()
}

// what is the metric for success here?
pub fn run(
) -> Res<ruler::enumo::Ruleset<desugared_lang::VecLangDesugared>>
{
    use std::time::Instant;
    // let run_name = "learning desugared rules, sum";
    // let mut seed_rules : ruler::enumo::Ruleset<desugared_lang::VecLangDesugared> = ruler::enumo::Ruleset::default();
    let run_name = "desugared rules";
    println!("running {run_name}");

    let beginning = Instant::now();

    // // hard coded for now
    // let unops = vec!["VecSum"].iter().map(|x| x.to_string()).collect();
    // let unops = vec!["Shfl"].iter().map(|x| x.to_string()).collect();
    // let binops: Vec<String> = vec!["+", "-", "*", "/", "VecAdd", "VecMinus", "VecMul", "VecDiv"].iter().map(|x| x.to_string()).collect();

    // let ops = vec![unops, binops.clone()];
    // let mut rules = sum_rules(ops, run_name);

    // let ops = vec![unops, binops];
    let ops = vec![vec![],vec![]];
    let rules = shfl_rules(ops, run_name);

    // rules.extend(shfl_rules);
    let duration = Instant::now() - beginning;
    ruler::logger::log_rules(&rules, Some("rulesets/ruleset_desugared.json"), run_name.to_string(), duration);

    Ok(rules)
}

mod test {
    use comp_gen::ruler::{
        self, enumo::*, ValidationResult,
    };
    use egg::{EGraph, Id};
    use log::debug;
    use rand::Rng;
    use rand_pcg::Pcg32;
    use ruler::{
        map, self_product, CVec, SynthAnalysis, SynthLanguage
    };
    use crate::{desugared_lang, desugared_workloads::*, smt::SmtEquals, Res};

    fn debugging_workload() -> Workload {
        Workload::new(["(VecSum (Vec ?a ?b ?c ?d))", "(VecSum (Vec (+ ?a ?b) 0 ?c ?d))"])
    }
     #[test]
    fn test_run(){
        let _ = crate::desugared_synthesis::run();
    }
}