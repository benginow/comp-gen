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

pub fn run(
) -> Res<ruler::enumo::Ruleset<desugared_lang::VecLangDesugared>>
{
    // let run_name = "learning desugared rules, sum";
    let mut seed_rules : ruler::enumo::Ruleset<desugared_lang::VecLangDesugared> = ruler::enumo::Ruleset::default();
    let run_name = "desugared rules";

    // // hard coded for now
    let unops = vec!["VecSum"].iter().map(|x| x.to_string()).collect();
    let binops = vec!["+", "-", "*", "/", "VecAdd", "VecMinus", "VecMul", "VecDiv"].iter().map(|x| x.to_string()).collect();

    let ops = vec![unops, binops];
    let rules = sum_rules(ops, run_name);

    ruler::logger::log_rules(&rules, Some("rulesets/ruleset.json"), run_name.to_string());

    Ok(rules)

    // Ok(seed_rules)
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
}