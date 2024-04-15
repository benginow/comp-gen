use std::{time::Instant, io::Write};

use crate::{
    enumo::{Filter, Metric, Ruleset, Scheduler, Workload},
    Limits, SynthLanguage,
};

pub fn iter_metric(wkld: Workload, atom: &str, met: Metric, n: usize) -> Workload {
    let mut pegs = wkld.clone();
    for i in 1..(n + 1) {
        pegs = wkld
            .clone()
            .plug(atom, &pegs)
            .filter(Filter::MetricLt(met, i + 1));
    }
    pegs
}

pub fn substitute(workload: Workload, sub: Workload, atom: &str) -> Workload {
    let mut pegs = Workload::Set(vec![]);
    let substitutions = sub.force();
    for sub in substitutions {
        pegs = pegs.append(workload.clone().plug(atom, &Workload::Set(vec![sub])));
    }
    pegs
}

fn run_workload_internal<L: SynthLanguage>(
    workload: Workload,
    prior: Ruleset<L>,
    prior_limits: Limits,
    minimize_limits: Limits,
    fast_match: bool,
    allow_empty: bool,
) -> Ruleset<L> {
    use std::time::Instant;
    use std::fs::*;
    use std::fs::File;

    // let file_path = "timings.txt";

    // Create OpenOptions with the append flag
    let mut options = OpenOptions::new();
    options.append(true);

    // Open the file with write access and append flag
    // let mut file = match options.open(file_path) {
    //     Ok(file) => file,
    //     Err(e) => {
    //         // Handle the error
    //         panic!("Error opening file: {}", e);
    //     }
    // };
    // let mut file = File::open("timings.txt").unwrap();

    let t = Instant::now();
    println!("workload is {:#?}", workload);
    let egraph = workload.to_egraph::<L>();
    // let elapsed = t.elapsed();
    // let info = format!("time taken to convert workload to egraph {elapsed:?}");
    // write!(file, "1 time taken to convert workload to egraph {elapsed:?}\n").unwrap();

    
    // let now = Instant::now();
    let compressed = Scheduler::Compress(prior_limits).run(&egraph, &prior);
    // let elapsed = now.elapsed();
    // write elapsed time to a file
    // write!(file, "2 time taken to compress egraph {elapsed:?}\n").unwrap();

    // println!("Compression time: {:.2?}", elapsed);

    // let now = Instant::now();
    let mut candidates = if fast_match {
        Ruleset::fast_cvec_match(&compressed)
    } else {
        Ruleset::cvec_match(&compressed)
    };
    // let elapsed = now.elapsed();
    // write!(&file, "3 time taken to cvec match {elapsed:?}\n").unwrap();

    let num_prior = prior.len();
    let now = Instant::now();
    println!("minimizing candidates");
    let (chosen, _) = candidates.minimize(prior, Scheduler::Compress(minimize_limits));
    let elapsed = now.elapsed();
    println!("minimizing candidates took {elapsed:?}");
    // let elapsed = now.elapsed();
    // write!(file, "4 time taken to minimize chandidates {elapsed:?}\n").unwrap();

    let time = t.elapsed().as_secs_f64();

    if chosen.is_empty() && !allow_empty {
        // log::debug!("Didn't learn any rules");
        panic!("Didn't learn any rules!");
    }

    println!(
        "Learned {} bidirectional rewrites ({} total rewrites) in {} using {} prior rewrites",
        chosen.bidir_len(),
        chosen.len(),
        time,
        num_prior
    );

    chosen.pretty_print();

    chosen
}

pub fn run_workload<L: SynthLanguage>(
    workload: Workload,
    prior: Ruleset<L>,
    prior_limits: Limits,
    minimize_limits: Limits,
    fast_match: bool,
) -> Ruleset<L> {
    run_workload_internal(
        workload,
        prior,
        prior_limits,
        minimize_limits,
        fast_match,
        false,
    )
}

pub fn run_rule_lifting<L: SynthLanguage>(
    workload: Workload,
    prior: Ruleset<L>,
    prior_limits: Limits,
    minimize_limits: Limits,
) -> Ruleset<L> {
    let t = Instant::now();

    let egraph = workload.to_egraph::<L>();
    let num_prior = prior.len();
    let mut candidates = Ruleset::allow_forbid_actual(egraph, prior.clone(), prior_limits);

    let chosen = candidates
        .minimize(prior, Scheduler::Compress(minimize_limits))
        .0;
    let time = t.elapsed().as_secs_f64();

    println!(
        "Learned {} bidirectional rewrites ({} total rewrites) in {} using {} prior rewrites",
        chosen.bidir_len(),
        chosen.len(),
        time,
        num_prior
    );

    chosen.pretty_print();

    chosen
}

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Lang {
    pub vals: Vec<String>,
    pub vars: Vec<String>,
    pub ops: Vec<Vec<String>>,
}

impl Lang {
    pub fn new(vals: &[&str], vars: &[&str], ops: &[&[&str]]) -> Self {
        Self {
            vals: vals.iter().map(|x| x.to_string()).collect(),
            vars: vars.iter().map(|x| x.to_string()).collect(),
            ops: ops
                .iter()
                .map(|o| o.iter().map(|x| x.to_string()).collect())
                .collect(),
        }
    }
}

pub fn recursive_rules<L: SynthLanguage>(
    metric: Metric,
    n: usize,
    lang: Lang,
    prior: Ruleset<L>,
) -> Ruleset<L> {
    if n < 1 {
        Ruleset::default()
    } else {
        let mut rec = recursive_rules(metric, n - 1, lang.clone(), prior.clone());
        let base_lang = if lang.ops.len() == 2 {
            base_lang(2)
        } else {
            base_lang(3)
        };
        let mut wkld = iter_metric(base_lang, "EXPR", metric, n)
            .filter(Filter::Contains("VAR".parse().unwrap()))
            .plug("VAR", &Workload::new(lang.vars))
            .plug("VAL", &Workload::new(lang.vals));
        // let ops = vec![lang.uops, lang.bops, lang.tops];
        for (i, ops) in lang.ops.iter().enumerate() {
            wkld = wkld.plug(format!("OP{}", i + 1), &Workload::new(ops));
        }
        rec.extend(prior);
        let allow_empty = n < 3;
        let new = run_workload_internal(
            wkld,
            rec.clone(),
            Limits::synthesis(),
            Limits::minimize(),
            true,
            allow_empty,
        );
        let mut all = new;
        all.extend(rec);
        all
    }
}

// pub fn base_lang(n: usize) -> Workload {
//     let mut vals = vec!["VAR".to_string(), "VAL".to_string()];
//     for i in 1..(n + 1) {
//         let mut str = "".to_string();
//         for j in 0..i {
//             let e = (format!(" EXPR{}", j));
//             str = format!("{}{}", str, e);
//         }
//         let s = format!("(OP{}{})", i, str);
//         vals.push(s);
//     }
//     Workload::new(vals)
// }
pub fn base_lang(n: usize) -> Workload {
    let mut vals = vec!["VAR".to_string(), "VAL".to_string()];
    for i in 1..(n + 1) {
        let s = format!("(OP{}{})", i, " EXPR".repeat(i));
        vals.push(s);
    }
    Workload::new(vals)
}

#[cfg(test)]
mod test {
    use crate::{
        enumo::{Metric, Workload},
        recipe_utils::{base_lang, iter_metric},
    };

    #[test]
    fn iter_metric_test() {
        let lang = base_lang(2);
        let atoms1 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 1).force();
        assert_eq!(atoms1.collect::<Vec<_>>().len(), 2);

        let atoms2 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 2).force();
        assert_eq!(atoms2.collect::<Vec<_>>().len(), 4);

        let atoms3 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 3).force();
        assert_eq!(atoms3.collect::<Vec<_>>().len(), 10);

        let atoms4 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 4).force();
        assert_eq!(atoms4.collect::<Vec<_>>().len(), 24);

        let atoms5 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 5).force();
        assert_eq!(atoms5.collect::<Vec<_>>().len(), 66);

        let atoms6 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 6).force();
        assert_eq!(atoms6.collect::<Vec<_>>().len(), 188);

        let atoms6 = iter_metric(lang.clone(), "EXPR", Metric::Atoms, 7).force();
        assert_eq!(atoms6.collect::<Vec<_>>().len(), 570);

        let depth1 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 1).force();
        assert_eq!(depth1.collect::<Vec<_>>().len(), 2);

        let depth2 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 2).force();
        assert_eq!(depth2.collect::<Vec<_>>().len(), 8);

        let depth3 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 3).force();
        assert_eq!(depth3.collect::<Vec<_>>().len(), 74);

        let depth4 = iter_metric(lang.clone(), "EXPR", Metric::Depth, 4).force();
        assert_eq!(depth4.collect::<Vec<_>>().len(), 5552);

        let lists1 = iter_metric(lang.clone(), "EXPR", Metric::Lists, 1).force();
        assert_eq!(lists1.collect::<Vec<_>>().len(), 8);

        let lists2 = iter_metric(lang.clone(), "EXPR", Metric::Lists, 2).force();
        assert_eq!(lists2.collect::<Vec<_>>().len(), 38);

        let lists3 = iter_metric(lang.clone(), "EXPR", Metric::Lists, 3).force();
        assert_eq!(lists3.collect::<Vec<_>>().len(), 224);
    }

    #[test]
    fn iter_metric_fast() {
        // This test will not finish if the pushing monotonic filters through plugs optimization is not working.
        let three = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 3);
        assert_eq!(three.force().collect::<Vec<_>>().len(), 10);

        let four = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 4);
        assert_eq!(four.force().collect::<Vec<_>>().len(), 32);

        let five = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 5);
        assert_eq!(five.force().collect::<Vec<_>>().len(), 106);

        let six = iter_metric(base_lang(3), "EXPR", Metric::Atoms, 6);
        assert_eq!(six.force().collect::<Vec<_>>().len(), 388);
    }

    #[test]
    fn base_lang_test() {
        assert_eq!(base_lang(0).force().collect::<Vec<_>>().len(), 2);
        assert_eq!(base_lang(1).force().collect::<Vec<_>>().len(), 3);
        assert_eq!(base_lang(2).force().collect::<Vec<_>>().len(), 4);
        assert_eq!(base_lang(3).force().collect::<Vec<_>>().len(), 5);
    }

    #[test]
    fn empty_plug() {
        let wkld =
            iter_metric(base_lang(3), "EXPR", Metric::Atoms, 6).plug("OP3", &Workload::empty());
        assert_eq!(wkld.force().collect::<Vec<_>>().len(), 188);
    }
}
