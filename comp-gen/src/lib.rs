pub mod config;
mod stats;

use log::{debug, info};
pub use ruler;
use ruler::egg;
use ruler::egg::rewrite as rw;
use std::io::Write;
use std::marker::PhantomData;
use std::{
    fs::File,
    path::{Path, PathBuf},
};

use crate::stats::EggStats;

pub trait Interpreter {
    type Env: Default;
    type Res;

    fn eval_with_env(&self, env: &mut Self::Env) -> Self::Res;
    fn eval(&self) -> Self::Res {
        self.eval_with_env(&mut Self::Env::default())
    }
}

/// Recursively translate some type `T` into a `egg::RecExpr`.
pub trait ToRecExpr<T> {
    fn to_recexpr(&self, expr: &mut egg::RecExpr<T>) -> egg::Id;
}

/// A trait that specifies how an `egg::PatternAst` can be converted
/// into an `egg::RecExpr`.
pub trait FromPattern: Sized {
    fn from_pattern(pat: &egg::PatternAst<Self>) -> egg::RecExpr<Self>;
}

/// Metrics defined on an `egg::CostFunction` that are useful for categorizing rules.
pub trait CostMetrics<L, N>: egg::CostFunction<L>
where
    L: egg::Language + FromPattern,
    N: egg::Analysis<L>,
{
    fn cost_differential(&mut self, r: &egg::Rewrite<L, N>) -> Self::Cost;
    fn cost_average(&mut self, r: &egg::Rewrite<L, N>) -> Self::Cost;
    fn all(&mut self, r: &egg::Rewrite<L, N>) -> CostMetric<L, N, Self>
    where
        Self: Sized,
    {
        CostMetric {
            cd: self.cost_differential(r),
            ca: self.cost_average(r),
            phantom: PhantomData,
        }
    }
}

/// Find the depth of a `RecExpr` starting at a particular `root` node.
fn depth<L: egg::Language, I: Into<egg::Id>>(
    term: &egg::RecExpr<L>,
    root: I,
) -> usize {
    if term.is_dag() {
        1 + term[root.into()]
            .fold(0, |acc, id| std::cmp::max(acc, depth(term, id)))
    } else {
        usize::max_value()
    }
}

pub struct CostMetric<
    L: egg::Language + FromPattern,
    N: egg::Analysis<L>,
    C: egg::CostFunction<L>,
> {
    pub cd: C::Cost,
    pub ca: C::Cost,
    phantom: PhantomData<N>,
}

#[derive(Debug, Clone)]
pub struct Stats<L: egg::Language, C: egg::CostFunction<L>> {
    phase_name: String,
    rules: usize,
    stop_reason: Option<egg::StopReason>,
    iterations: usize,
    egraph_total_nodes: usize,
    egraph_total_classes: usize,
    egraph_total_size: usize,
    old_cost: Option<C::Cost>,
    cost: Option<C::Cost>,
}

impl<L, C> Stats<L, C>
where
    L: egg::Language + egg::FromOp + Send + Sync + FromPattern + 'static,
    C: egg::CostFunction<L> + Clone,
{
    fn from_runner<N: egg::Analysis<L> + Default + Clone>(
        phase: &SinglePhase<L, N, C>,
        n_rules: usize,
        runner: &egg::Runner<L, N, ()>,
    ) -> Self {
        Self {
            phase_name: phase.name.to_string(),
            rules: n_rules,
            stop_reason: runner.stop_reason.clone(),
            iterations: runner.iterations.len(),
            egraph_total_nodes: runner.egraph.total_number_of_nodes(),
            egraph_total_classes: runner.egraph.number_of_classes(),
            egraph_total_size: runner.egraph.total_size(),
            old_cost: None,
            cost: None,
        }
    }

    fn report(&self) {
        // let search_time: f64 =
        //     runner.iterations.iter().map(|i| i.search_time).sum();
        // let apply_time: f64 =
        //     runner.iterations.iter().map(|i| i.apply_time).sum();
        // let rebuild_time: f64 =
        //     runner.iterations.iter().map(|i| i.rebuild_time).sum();
        // let total_time: f64 =
        //     runner.iterations.iter().map(|i| i.total_time).sum();

        // let rebuilds: usize =
        //     runner.iterations.iter().map(|i| i.n_rebuilds).sum();

        // let eg = &runner.egraph;
        info!("  Runner report");
        info!("  =============");
        info!("    Phase: {} with {} rules", self.phase_name, self.rules);
        info!("    Stop reason: {:?}", self.stop_reason.as_ref().unwrap());
        info!("    Iterations: {}", self.iterations);
        info!(
            "    Cost: {:?} (old: {:?})",
            self.cost.as_ref().unwrap(),
            self.old_cost.as_ref()
        );
        info!(
            "    Egraph size: {} nodes, {} classes, {} memo",
            self.egraph_total_nodes,
            self.egraph_total_classes,
            self.egraph_total_size
        );
        // eprintln!(
        //     "    Rebuilds: {}, {:.2} per iter",
        //     rebuilds,
        //     (rebuilds as f64) / (iters as f64)
        // );
        // eprintln!("    Total time: {}", total_time);
        // eprintln!(
        //     "      Search:  ({:.2}) {}",
        //     search_time / total_time,
        //     search_time
        // );
        // eprintln!(
        //     "      Apply:   ({:.2}) {}",
        //     apply_time / total_time,
        //     apply_time
        // );
        // eprintln!(
        //     "      Rebuild: ({:.2}) {}",
        //     rebuild_time / total_time,
        //     rebuild_time
        // );
    }
}

pub struct EqSatResult<
    L: egg::Language + FromPattern,
    // N: egg::Analysis<L>,
    C: egg::CostFunction<L>,
> {
    cost: C::Cost,
    prog: egg::RecExpr<L>,
    // egraph: egg::EGraph<L, N>,
    stats: Stats<L, C>,
}

pub struct SinglePhase<
    L: egg::Language + egg::FromOp + Send + Sync + FromPattern + 'static,
    N: egg::Analysis<L> + Default + Clone,
    C: egg::CostFunction<L> + Clone,
> {
    name: String,
    // rules: Vec<egg::Rewrite<L, N>>,
    select: Box<dyn Fn(CostMetric<L, N, C>) -> bool>,
    fresh_egraph: bool,
    node_limit: usize,
    iter_limit: usize,
}

pub enum Phase<
    L: egg::Language + egg::FromOp + Send + Sync + FromPattern + 'static,
    N: egg::Analysis<L> + Default + Clone,
    C: egg::CostFunction<L> + Clone,
> {
    Single(SinglePhase<L, N, C>),
    Loop {
        // TODO: maybe generalize this to allow arbitrary nesting?
        phases: Vec<SinglePhase<L, N, C>>,
        loops: u64,
    },
}

// /// Structure that defines a rule phase.
// pub struct Phase<
//     L: egg::Language + egg::FromOp + Send + Sync + FromPattern + 'static,
//     N: egg::Analysis<L> + Default + Clone,
// > {
//     name: String,
//     rules: Vec<egg::Rewrite<L, N>>,
//     fresh_egraph: bool,
//     node_limit: usize,
//     iter_limit: usize,
// }

/// An equality saturation based compiler.
pub struct Compiler<
    L: egg::Language + egg::FromOp + Send + Sync + FromPattern + 'static,
    N: egg::Analysis<L> + Default + Clone,
    C: egg::CostFunction<L> + Clone,
> {
    /// All of the rewrite rules for this compiler.
    rules: Vec<egg::Rewrite<L, N>>,

    /// Optional function that filters valid rewrite rules.
    filter: Option<Box<dyn Fn(CostMetric<L, N, C>) -> bool>>,

    /// Phases.
    phases: Vec<Phase<L, N, C>>,
    cost_fn: C,
    init_node: Option<L>,
    total_node_limit: usize,
    total_iter_limit: usize,
    timeout: u64,
    dry_run: bool,
    dump_rules: bool,
    reuse_egraphs: bool,
    rule_distribution: Vec<(PathBuf, Box<dyn Fn(C::Cost) -> f64>)>,
    explanations: bool,
    scheduler: config::RuleSchedulerOpt,
    stats: Option<PathBuf>,
}

impl<L, N, C> Compiler<L, N, C>
where
    L: egg::Language
        + egg::FromOp
        + Send
        + Sync
        + FromPattern
        + std::fmt::Display
        + 'static,
    N: egg::Analysis<L> + Default + Clone,
    C: CostMetrics<L, N> + egg::CostFunction<L> + Clone,
    <C as egg::CostFunction<L>>::Cost: PartialOrd<f64>,
{
    /// Construct a compiler using `cost_fn` to distinguish
    /// between the `source` and `target` languages.
    /// Defaults to using a `node_limit=1_000_000` and
    /// a `timeout=120 seconds`.
    pub fn with_cost_fn(cost_fn: C) -> Self {
        Self {
            rules: vec![],
            phases: vec![],
            filter: None,
            cost_fn,
            init_node: None,
            total_node_limit: 1_000_000,
            total_iter_limit: 30,
            timeout: 120,
            dry_run: false,
            dump_rules: false,
            reuse_egraphs: false,
            rule_distribution: vec![],
            explanations: false,
            scheduler: config::RuleSchedulerOpt::default(),
            stats: None,
        }
    }

    /// Return rules read in from a json file.
    pub fn add_external_rules(&mut self, filename: &Path) -> &mut Self {
        self.add_processed_external_rules(filename, |x| x)
    }

    pub fn add_processed_external_rules<F>(
        &mut self,
        filename: &Path,
        proc: F,
    ) -> &mut Self
    where
        F: Fn(egg::Pattern<L>) -> egg::Pattern<L>,
    {
        let contents = std::fs::read_to_string(filename).unwrap();
        let data = json::parse(&contents).unwrap();

        let mut rules = vec![];
        for (idx, eq) in data["eqs"].members().enumerate() {
            let lpat_raw: egg::Pattern<L> =
                eq["lhs"].as_str().unwrap().parse().unwrap();
            let rpat_raw: egg::Pattern<L> =
                eq["rhs"].as_str().unwrap().parse().unwrap();

            let lpat = proc(lpat_raw);
            let rpat = proc(rpat_raw);

            if eq["bidirectional"].as_bool().unwrap() {
                // we have to clone bc it is a bidirectional rule
                rules
                    .extend(rw!(format!("ruler_{}_lr", idx); { lpat.clone() } <=> { rpat.clone() }))
            } else {
                rules
                    .push(rw!(format!("ruler_{}_r", idx); { lpat } => { rpat }))
            }
        }

        self.rules.extend(rules);
        self
    }

    pub fn add_rules(
        &mut self,
        rules: impl Iterator<Item = egg::Rewrite<L, N>>,
    ) -> &mut Self {
        self.rules.extend(rules);
        self
    }

    pub fn with_init_node(&mut self, node: L) -> &mut Self {
        self.init_node = Some(node);
        self
    }

    pub fn with_total_node_limit(&mut self, node_limit: usize) -> &mut Self {
        self.total_node_limit = node_limit;
        self
    }

    pub fn with_total_iter_limit(&mut self, iter_limit: usize) -> &mut Self {
        self.total_iter_limit = iter_limit;
        self
    }

    pub fn with_timeout(&mut self, timeout: u64) -> &mut Self {
        self.timeout = timeout;
        self
    }

    pub fn with_filter<F: 'static>(&mut self, filter: F) -> &mut Self
    where
        F: Fn(CostMetric<L, N, C>) -> bool,
    {
        self.filter = Some(Box::new(filter));
        self
    }

    #[allow(unused)]
    /// Define a new phase named `name` using `filter`.
    /// Be careful to call this function after you have added all the rules
    /// to the compiler.
    fn new_single_phase<F, S>(
        &self,
        name: S,
        filter: F,
        fresh_egraph: bool,
        node_limit: Option<usize>,
        iter_limit: Option<usize>,
    ) -> Phase<L, N, C>
    where
        F: Fn(CostMetric<L, N, C>) -> bool + 'static,
        S: ToString,
    {
        // gather rules that pass the filter
        // let phase_rules = self
        //     .rules
        //     .iter()
        //     .filter(|r| filter(self.cost_fn.all(r)))
        //     .cloned()
        //     .collect::<Vec<_>>();

        // construct phase
        Phase::Single(SinglePhase {
            name: name.to_string(),
            // rules: phase_rules,
            select: Box::new(filter),
            fresh_egraph,
            node_limit: node_limit.unwrap_or(self.total_node_limit),
            iter_limit: iter_limit.unwrap_or(self.total_iter_limit),
        })
    }

    pub fn add_single_phase<F, S>(
        &mut self,
        name: S,
        filter: F,
        fresh_egraph: bool,
        node_limit: Option<usize>,
        iter_limit: Option<usize>,
    ) -> &mut Self
    where
        F: Fn(CostMetric<L, N, C>) -> bool + 'static,
        S: ToString,
    {
        // construct phase
        let phase = Phase::Single(SinglePhase {
            name: name.to_string(),
            // rules: phase_rules,
            select: Box::new(filter),
            fresh_egraph,
            node_limit: node_limit.unwrap_or(self.total_node_limit),
            iter_limit: iter_limit.unwrap_or(self.total_iter_limit),
        });
        self.phases.push(phase);
        self
    }

    /// Define a new phase named `name` using `filter`.
    /// Be careful to call this function after you have added all the rules
    /// to the compiler.
    fn new_single_phase_range<S>(
        &self,
        name: S,
        cd: [Option<f64>; 2],
        ca: [Option<f64>; 2],
        fresh_egraph: bool,
        node_limit: Option<usize>,
        iter_limit: Option<usize>,
    ) -> SinglePhase<L, N, C>
    where
        S: ToString,
    {
        let filter = move |cm: CostMetric<L, N, C>| {
            let [cd_low, cd_high] = cd;
            let [ca_low, ca_high] = ca;

            // check conditions. if condition doesn't exist,
            // then default to true
            //   cd conditions
            cd_low.map(|l| cm.cd > l).unwrap_or(true)
                && cd_high.map(|h| cm.cd <= h).unwrap_or(true)
	    // check ca conditions
                && ca_low.map(|l| cm.ca > l).unwrap_or(true)
                && ca_high.map(|h| cm.ca <= h).unwrap_or(true)
            // && config.cd_filter.map(|c| cm.cd > c).unwrap_or(true)
        };

        // construct phase
        SinglePhase {
            name: name.to_string(),
            // rules: phase_rules,
            select: Box::new(filter),
            fresh_egraph,
            node_limit: node_limit.unwrap_or(self.total_node_limit),
            iter_limit: iter_limit.unwrap_or(self.total_iter_limit),
        }
    }

    pub fn dry_run(&mut self) -> &mut Self {
        self.dry_run = true;
        self
    }

    pub fn dump_rules(&mut self) -> &mut Self {
        self.dump_rules = true;
        self
    }

    pub fn output_rule_distribution<P, F>(
        &mut self,
        output_file: P,
        f: F,
    ) -> &mut Self
    where
        P: Into<PathBuf>,
        F: Fn(C::Cost) -> f64 + 'static,
    {
        self.rule_distribution
            .push((output_file.into(), Box::new(f)));
        self
    }

    pub fn reuse_egraphs(&mut self) -> &mut Self {
        self.reuse_egraphs = true;
        self
    }

    /// Load config from a file. This overries anything previously set.
    pub fn with_config(
        &mut self,
        config: &config::CompilerConfiguration,
    ) -> &mut Self {
        self.total_node_limit = config.total_node_limit;
        self.total_iter_limit = config.total_iter_limit;
        self.timeout = config.timeout;
        self.dry_run = config.dry_run;
        self.dump_rules = config.dump_rules;
        self.reuse_egraphs = config.reuse_egraphs;
        for phase_config in config.phases.clone() {
            match phase_config {
                config::PhaseConfiguration::Single {
                    name,
                    cd,
                    ca,
                    fresh_egraph,
                    node_limit,
                    iter_limit,
                    disabled,
                } => {
                    // if disabled, skip this phase
                    if let Some(true) = disabled {
                        continue;
                    }

                    // let [cd_low, cd_high] = cd;
                    // let [ca_low, ca_high] = ca;
                    let phase = self.new_single_phase_range(
                        name,
                        cd,
                        ca,
                        fresh_egraph.unwrap_or(false),
                        node_limit,
                        iter_limit,
                    );

                    self.phases.push(Phase::Single(phase));
                }
                config::PhaseConfiguration::Phases { phases, loops } => {
                    let single_phases = phases
                        .into_iter()
                        .filter_map(|p| match p {
                            config::PhaseConfiguration::Single {
                                name,
                                cd,
                                ca,
                                fresh_egraph,
                                node_limit,
                                iter_limit,
                                disabled,
                            } => {
                                if disabled.unwrap_or(false) {
                                    None
                                } else {
                                    Some(self.new_single_phase_range(
                                        name,
                                        cd,
                                        ca,
                                        fresh_egraph.unwrap_or(false),
                                        node_limit,
                                        iter_limit,
                                    ))
                                }
                            }
                            config::PhaseConfiguration::Phases {
                                phases: _,
                                loops: _,
                            } => todo!(),
                        })
                        .collect::<Vec<_>>();
                    self.phases.push(Phase::Loop {
                        phases: single_phases,
                        loops,
                    })
                }
            }
        }
        self.scheduler = config
            .scheduler
            .clone()
            .unwrap_or(config::RuleSchedulerOpt::default());
        self.stats = config.stats.clone();
        self
    }

    pub fn with_explanations(&mut self) -> &mut Self {
        self.explanations = true;
        self
    }

    pub fn with_scheduler(
        &mut self,
        scheduler: config::RuleSchedulerOpt,
    ) -> &mut Self {
        self.scheduler = scheduler;
        self
    }

    pub fn with_stats_path(&mut self, path: PathBuf) -> &mut Self {
        self.stats = Some(path);
        self
    }

    fn equality_saturate(
        &self,
        phase: &SinglePhase<L, N, C>,
        egraph: egg::EGraph<L, N>,
        prog: &egg::RecExpr<L>,
    ) -> (egg::EGraph<L, N>, EqSatResult<L, C>) {
        debug!("Making runner");
        debug!(
            "Initial Program Depth: {}",
            depth(&prog, prog.as_ref().len() - 1)
        );

        let mut runner: egg::Runner<L, N, ()> =
            egg::Runner::new(Default::default())
                .with_egraph(egraph)
                .with_expr(prog)
                .with_node_limit(phase.node_limit)
                .with_iter_limit(phase.iter_limit)
                .with_time_limit(std::time::Duration::from_secs(self.timeout));

        // set the scheduler according to the options
        runner = match self.scheduler {
            config::RuleSchedulerOpt::Backoff => {
                runner.with_scheduler(egg::BackoffScheduler::default())
            }
            config::RuleSchedulerOpt::Simple => {
                runner.with_scheduler(egg::SimpleScheduler)
            }
        };

        // Add EggStats hook if we have a stats path
        runner = if let Some(_) = self.stats {
            runner.with_hook(EggStats::density())
        } else {
            runner
        };

        let rules = self
            .rules
            .iter()
            .filter(|r| (phase.select)(self.cost_fn.clone().all(r)))
            .cloned()
            .collect::<Vec<_>>();

        debug!("Starting equality saturation");
        runner = runner.run(&rules);

        // extract the best program
        let extractor =
            egg::Extractor::new(&runner.egraph, self.cost_fn.clone());
        let (cost, prog) = extractor.find_best(runner.roots[0]);

        debug!("Egraph size: {}", runner.egraph.total_size());
        debug!(
            "Final Program Depth: {}",
            depth(&prog, prog.as_ref().len() - 1)
        );
        let mut stats = Stats::from_runner(&phase, rules.len(), &runner);
        stats.cost = Some(cost.clone());
        stats.report();

        let res = EqSatResult {
            cost,
            prog,
            // egraph: runner.egraph,
            stats,
        };
        (runner.egraph, res)
    }

    fn run_single(
        &self,
        phase: &SinglePhase<L, N, C>,
        mut egraph: egg::EGraph<L, N>,
        prog: &egg::RecExpr<L>,
    ) -> (egg::EGraph<L, N>, Option<EqSatResult<L, C>>) {
        let msg = format!("Starting Phase {}", phase.name);
        info!("{}", "=".repeat(msg.len()));
        info!("{msg}");
        // gather rules that pass the filter
        let mut cost_fn = self.cost_fn.clone();
        let rules = self
            .rules
            .iter()
            .filter(|r| (phase.select)(cost_fn.all(r)))
            .cloned()
            .collect::<Vec<_>>();
        info!("Using {} rules", rules.len());
        info!("{}", "=".repeat(msg.len()));

        if self.dump_rules {
            for r in &rules {
                debug!(
                    "[cd:{:.2?} ca:{:.2?}] {} => {} ({})",
                    cost_fn.cost_differential(r),
                    cost_fn.cost_average(r),
                    r.searcher.get_pattern_ast().unwrap(),
                    r.applier.get_pattern_ast().unwrap(),
                    r.name
                );
            }
        }

        if self.dry_run {
            return (egraph, None);
        }

        // update egraph
        if phase.fresh_egraph || !self.reuse_egraphs {
            debug!("Using a fresh egraph for this phase");
            egraph = self.new_egraph();
        }
        // let (new_cost, new_prog, new_egraph) =
        //     self.equality_saturate(&phase, egraph, &prog);
        let (egraph, eq_sat) = self.equality_saturate(&phase, egraph, &prog);

        (egraph, Some(eq_sat))
    }

    fn run_loop(
        &self,
        phases: &[SinglePhase<L, N, C>],
        loops: u64,
        mut egraph: egg::EGraph<L, N>,
        prog: &egg::RecExpr<L>,
    ) -> (egg::EGraph<L, N>, Option<EqSatResult<L, C>>) {
        info!("Starting a loop! Running for {loops} iterations");

        let mut res = None;

        for _ in 0..loops {
            for phase in phases {
                let (egraph_new, eq_sat_opt) =
                    self.run_single(phase, egraph, prog);
                egraph = egraph_new;
                res = eq_sat_opt;
                // handle stats if we have them
                // if let Some(eq_sat) = eq_sat_opt {
                //     let mut stat = eq_sat.stats.clone();
                //     stat.old_cost = Some(cost.clone());
                //     stats.push(stat);

                //     info!("Cost: {:?} (old: {:?})", eq_sat.cost.clone(), cost);
                //     // update state for next iteration
                //     // (cost, prog) = (eq_sat.cost, eq_sat.prog);
                // }
            }
        }
        (egraph, res)
    }

    pub fn compile(
        &mut self,
        prog: &egg::RecExpr<L>,
    ) -> (C::Cost, egg::RecExpr<L>, egg::EGraph<L, N>) {
        self.rule_distribution.iter().for_each(|(path, conv)| {
            self.generate_rule_histogram(path, conv);
        });

        let mut egraph = self.new_egraph();
        // let mut cost_fn = self.cost_fn.clone();
        let mut prog = prog.clone();
        let mut cost = self.cost_fn.cost_rec(&prog);

        let mut stats: Vec<Stats<L, C>> = vec![];
        for phase in &self.phases {
            let (egraph_new, eq_sat_opt) = match phase {
                Phase::Single(phase) => self.run_single(phase, egraph, &prog),
                Phase::Loop { phases, loops } => {
                    self.run_loop(phases, *loops, egraph, &prog)
                }
            };
            // update the egraph with the one returned from run_single
            egraph = egraph_new;
            // handle stats if we have them
            if let Some(eq_sat) = eq_sat_opt {
                let mut stat = eq_sat.stats.clone();
                stat.old_cost = Some(cost.clone());
                stats.push(stat);

                info!("Cost: {:?} (old: {:?})", eq_sat.cost.clone(), cost);
                // update state for next iteration
                (cost, prog) = (eq_sat.cost, eq_sat.prog);
            }
        }

        // report the total stats
        for s in stats {
            s.report()
        }

        (cost, prog, egraph)
    }

    fn new_egraph(&self) -> egg::EGraph<L, N> {
        let mut egraph = if self.explanations {
            egg::EGraph::new(N::default()).with_explanations_enabled()
        } else {
            egg::EGraph::new(N::default()).with_explanations_disabled()
        };
        if let Some(node) = &self.init_node {
            egraph.add(node.clone());
        }
        egraph
    }

    fn generate_rule_histogram<F>(&self, path: &PathBuf, f: F)
    where
        F: Fn(C::Cost) -> f64,
    {
        let mut cost_fn = self.cost_fn.clone();
        let avg_data: Vec<(String, f64)> = self
            .rules
            .iter()
            .map(|r| (r.name.to_string(), f(cost_fn.cost_average(r))))
            .collect();
        let diff_data: Vec<(String, f64)> = self
            .rules
            .iter()
            .map(|r| (r.name.to_string(), f(cost_fn.cost_differential(r))))
            .collect();

        let mut file = File::create(path).unwrap();

        writeln!(file, "rule,name,value").unwrap();

        for (r, d) in avg_data {
            writeln!(file, "{r},average,{d}").unwrap();
        }

        for (r, d) in diff_data {
            writeln!(file, "{r},differential,{d}").unwrap();
        }
    }
}
