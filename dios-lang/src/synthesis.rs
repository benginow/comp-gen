use comp_gen::ruler::{
    self, enumo::*, recipe_utils, ValidationResult,
};
use egg::{self, EGraph, Id};
use log::debug;
use num::{integer::Roots, ToPrimitive};
use rand::Rng;
use rand_pcg::Pcg32;
// ruler no longer has Equality and Synthesizer
use ruler::{
    map, self_product, CVec, SynthAnalysis, SynthLanguage
};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;

use crate::{lang, smt::SmtEquals, Res};

pub fn split_into_halves(n: usize) -> (usize, usize) {
    if n % 2 == 0 {
        (n / 2, n / 2)
    } else {
        (n / 2, n / 2 + 1)
    }
}

/// Perform the integer divison `a / b`.
/// This is defined to be the `n`
/// such that `b * n = a`.
/// If no such `n` exists, then return None.
/// This is defined when b != 0 and there
/// exists some n such that b * n = a.
fn integer_division(a: i64, b: i64) -> Option<i64> {
    if b == 0 {
        None
    } else if a == 0 {
        Some(0)
    } else {
        Some(a / b)
    }
    // if a / b != 0
}

impl lang::Value {
    fn int1<F>(arg: &Self, f: F) -> Option<lang::Value>
    where
        F: Fn(i64) -> lang::Value,
    {
        if let lang::Value::Int(val) = arg {
            Some(f(*val))
        } else {
            None
        }
    }

    fn int2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<lang::Value>
    where
        F: Fn(i64, i64) -> lang::Value,
    {
        if let (lang::Value::Int(lv), lang::Value::Int(rv)) = (lhs, rhs) {
            Some(f(*lv, *rv))
        } else {
            None
        }
    }

    fn bool2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<lang::Value>
    where
        F: Fn(bool, bool) -> lang::Value,
    {
        if let (lang::Value::Bool(lv), lang::Value::Bool(rv)) = (lhs, rhs) {
            Some(f(*lv, *rv))
        } else {
            None
        }
    }

    fn vec1<F>(val: &Self, f: F) -> Option<lang::Value>
    where
        F: Fn(&[lang::Value]) -> Option<lang::Value>,
    {
        if let lang::Value::Vec(v) = val {
            f(v)
        } else {
            None
        }
    }

    fn vec2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<lang::Value>
    where
        F: Fn(&[lang::Value], &[lang::Value]) -> Option<lang::Value>,
    {
        if let (lang::Value::Vec(v1), lang::Value::Vec(v2)) = (lhs, rhs) {
            if v1.len() == v2.len() {
                f(v1, v2)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn vec3<F>(v1: &Self, v2: &Self, v3: &Self, f: F) -> Option<lang::Value>
    where
        F: Fn(
            &[lang::Value],
            &[lang::Value],
            &[lang::Value],
        ) -> Option<lang::Value>,
    {
        if let (
            lang::Value::Vec(v1),
            lang::Value::Vec(v2),
            lang::Value::Vec(v3),
        ) = (v1, v2, v3)
        {
            if v1.len() == v2.len() && v2.len() == v3.len() {
                f(v1, v2, v3)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn vec2_op<F>(lhs: &Self, rhs: &Self, f: F) -> Option<lang::Value>
    where
        F: Fn(&lang::Value, &lang::Value) -> Option<lang::Value>,
    {
        Self::vec2(lhs, rhs, |lhs, rhs| {
            lhs.iter()
                .zip(rhs)
                .map(|(l, r)| f(l, r))
                .collect::<Option<Vec<lang::Value>>>()
                .map(lang::Value::Vec)
        })
    }

    #[allow(unused)]
    fn int_range(min: i64, max: i64, num_samples: usize) -> Vec<lang::Value> {
        (min..=max)
            .step_by(((max - min) as usize) / num_samples)
            .map(lang::Value::Int)
            .collect::<Vec<_>>()
    }

    fn sample_int(
        rng: &mut Pcg32,
        min: i64,
        max: i64,
        num_samples: usize,
    ) -> Vec<lang::Value> {
        (0..num_samples)
            .map(|_| lang::Value::Int(rng.gen_range(min, max)))
            .collect::<Vec<_>>()
    }

    pub fn sample_vec(
        rng: &mut Pcg32,
        min: i64,
        max: i64,
        list_size: usize,
        num_samples: usize,
    ) -> Vec<lang::Value> {
        (0..num_samples)
            .map(|_| {
                lang::Value::Vec(lang::Value::sample_int(
                    rng, min, max, list_size,
                ))
            })
            .collect::<Vec<_>>()
    }
}

fn sgn(x: i64) -> i64 {
    match x.cmp(&0) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

fn sqrt_sgn(x: i64, y: i64) -> Option<i64> {
    if x >= 0 {
        Some(x.sqrt() * -sgn(y))
    } else {
        None
    }
}

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
    // pub ruler_config: ruler::SynthParams,
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
            // ruler_config: ruler::SynthParams::default(),
        }
    }
}

// Better post-processing support
// TODO JB: I'm sure there's a better way to do this. This is a little bit jank.

/// Reports for each run of Ruler.
// #[derive(Debug, Serialize, Deserialize)]
// #[serde(from = "SerializedRuleset")]
// #[serde(into = "SerializedRuleset")]
// #[serde(bound = "L: SynthLanguage")]



// impl lang::VecLang {
    
//     fn post_process(
//         ruleset: &RuleSet<lang::VecLang>,
//     ) -> Report<Self> {
//         let mut new_eqs: Vec<Equality<_>> = vec![];
//         for eq in &report.eqs {
//             let lhs_pre: Lang = eq.lhs.unpattern().into();
//             let lhs: egg::RecExpr<lang::VecLang> =
//                 lhs_pre.desugar(params.vector_size).into();
//             let rhs_pre: Lang = eq.rhs.unpattern().into();
//             let rhs: egg::RecExpr<lang::VecLang> =
//                 rhs_pre.desugar(params.vector_size).into();
//             if let Some(new_eq) = Equality::new(&lhs, &rhs) {
//                 new_eqs.push(new_eq);
//             } else {
//                 eprintln!("Could not make equation for {} <=> {}", lhs, rhs);
//             }
//         }
//         report.eqs = new_eqs;
//         report
//     }
// }

impl SynthLanguage for lang::VecLang {
    type Constant = lang::Value;
    // type Config = DiosConfig;

    fn is_rule_lifting() -> bool {
        true
    }

    fn get_lifting_rules() -> Ruleset<Self> {
        Ruleset::new([
            "(VecAdd (Vec ?b) (Vec ?a)) ==> (Vec (+ ?b ?a))", 
            "(VecDiv (Vec ?b) (Vec ?a)) ==> (Vec (/ ?b ?a))"]
        )
    }

    fn to_var(&self) -> Option<egg::Symbol> {
        if let lang::VecLang::Symbol(sym) = self {
            Some(*sym)
        } else {
            None
        }
    }

    fn mk_var(sym: egg::Symbol) -> Self {
        lang::VecLang::Symbol(sym)
    }

    fn is_constant(&self) -> bool {
        matches!(&self, lang::VecLang::Const(_))
    }

    fn mk_constant(c: <Self as SynthLanguage>::Constant, _e: &mut EGraph<Self, SynthAnalysis>) -> Self {
        lang::VecLang::Const(c)
    }

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        match self {
            lang::VecLang::Const(i) => vec![Some(i.clone()); cvec_len],
            lang::VecLang::Add([l, r]) => map!(get, l, r => {
                lang::Value::int2(l, r, |l, r| lang::Value::Int(l + r))
            }),
            lang::VecLang::Mul([l, r]) => map!(get, l, r => {
                lang::Value::int2(l, r, |l, r| lang::Value::Int(l * r))
            }),
            lang::VecLang::Minus([l, r]) => map!(get, l, r => {
                lang::Value::int2(l, r, |l, r| lang::Value::Int(l - r))
            }),
            lang::VecLang::Div([l, r]) => get(l)
                .iter()
                .zip(get(r).iter())
                .map(|tup| match tup {
                    (Some(lang::Value::Int(a)), Some(lang::Value::Int(b))) => {
                        integer_division(*a, *b).map(lang::Value::Int)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
            lang::VecLang::Or([l, r]) => {
                map!(get, l, r => lang::Value::bool2(l, r, |l, r| lang::Value::Bool(l || r)))
            }
            lang::VecLang::And([l, r]) => {
                map!(get, l, r => lang::Value::bool2(l, r, |l, r| lang::Value::Bool(l && r)))
            }
            lang::VecLang::Ite([_b, _t, _f]) => todo!(),
            lang::VecLang::Lt([l, r]) => {
                map!(get, l, r => lang::Value::int2(l, r, |l, r| lang::Value::Bool(l < r)))
            }
            lang::VecLang::SqrtSgn([l, r]) => map!(
                get,
                l, r => if let (lang::Value::Int(lv), lang::Value::Int(rv)) = (l, r) {
                    sqrt_sgn(*lv, *rv).map(lang::Value::Int)
                } else {
                    None
                }
            ),
            lang::VecLang::Sgn([x]) => {
                map!(get, x => lang::Value::int1(x, |x| lang::Value::Int(sgn(x))))
            }
            lang::VecLang::Sqrt([x]) => get(x)
                .iter()
                .map(|a| match a {
                    Some(lang::Value::Int(a)) => {
                        if *a >= 0 {
                            Some(lang::Value::Int(a.sqrt()))
                        } else {
                            None
                        }
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
            lang::VecLang::Neg([x]) => {
                map!(get, x => lang::Value::int1(x, |x| lang::Value::Int(-x)))
            }
            lang::VecLang::List(l) => l
                .iter()
                .fold(vec![Some(vec![]); cvec_len], |mut acc, item| {
                    acc.iter_mut().zip(get(item)).for_each(|(mut v, i)| {
                        if let (Some(v), Some(i)) = (&mut v, i) {
                            v.push(i.clone());
                        } else {
                            *v = None;
                        }
                    });
                    acc
                })
                .into_iter()
                .map(|acc| acc.map(lang::Value::List))
                .collect::<Vec<_>>(),
            lang::VecLang::Vec(l) => l
                .iter()
                .fold(vec![Some(vec![]); cvec_len], |mut acc, item| {
                    acc.iter_mut().zip(get(item)).for_each(|(mut v, i)| {
                        if let (Some(v), Some(i)) = (&mut v, i) {
                            v.push(i.clone());
                        } else {
                            *v = None;
                        }
                    });
                    acc
                })
                .into_iter()
                .map(|acc| acc.map(lang::Value::Vec))
                .collect::<Vec<_>>(),
            lang::VecLang::LitVec(l) => l
                .iter()
                .fold(vec![Some(vec![]); cvec_len], |mut acc, item| {
                    acc.iter_mut().zip(get(item)).for_each(|(mut v, i)| {
                        if let (Some(v), Some(i)) = (&mut v, i) {
                            v.push(i.clone());
                        } else {
                            *v = None;
                        }
                    });
                    acc
                })
                .into_iter()
                .map(|acc| acc.map(lang::Value::Vec))
                .collect::<Vec<_>>(),
            #[rustfmt::skip]
            lang::VecLang::Get([l, i]) => map!(get, l, i => {
                if let (lang::Value::Vec(v), lang::Value::Int(idx)) = (l, i) {
                    // get index and clone the inner lang::Value if there is one
                    v.get(*idx as usize).cloned()
                } else {
                    None
                }
            }),
            #[rustfmt::skip]
            lang::VecLang::Concat([l, r]) => map!(get, l, r => {
                lang::Value::vec2(l, r, |l, r| {
                    Some(lang::Value::List(
                        l.iter().chain(r).cloned().collect::<Vec<_>>(),
                    ))
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecAdd([l, r]) => map!(get, l, r => {
                lang::Value::vec2_op(l, r, |l, r| {
                    lang::Value::int2(l, r, |l, r| lang::Value::Int(l + r))
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecMinus([l, r]) => map!(get, l, r => {
                lang::Value::vec2_op(l, r, |l, r| {
                    lang::Value::int2(l, r, |l, r| lang::Value::Int(l - r))
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecMul([l, r]) => map!(get, l, r => {
                lang::Value::vec2_op(l, r, |l, r| {
                    lang::Value::int2(l, r, |l, r| lang::Value::Int(l * r))
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecDiv([l, r]) => map!(get, l, r => {
                lang::Value::vec2_op(l, r, |l, r| match (l, r) {
                    (lang::Value::Int(a), lang::Value::Int(b)) => {
                        integer_division(*a, *b).map(lang::Value::Int)
                    }
                    _ => None,
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecMulSgn([l, r]) => map!(get, l, r => {
                lang::Value::vec2_op(l, r, |l, r| {
                    lang::Value::int2(l, r, |l, r| lang::Value::Int(sgn(l) * r))
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecSqrtSgn([l, r]) => map!(get, l, r => {
                lang::Value::vec2_op(l, r, |l, r| {
                    if let (lang::Value::Int(lv), lang::Value::Int(rv)) = (l, r) {
                        sqrt_sgn(*lv, *rv).map(lang::Value::Int)
                    } else {
                        None
                    }
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecNeg([l]) => map!(get, l => {
                lang::Value::vec1(l, |l| {
                    if l.iter().all(|x| matches!(x, lang::Value::Int(_))) {
                        Some(lang::Value::Vec(
                            l.iter()
                                .map(|tup| match tup {
                                    lang::Value::Int(a) => lang::Value::Int(-a),
                                    x => panic!("NEG: Ill-formed: {}", x),
                                })
                                .collect::<Vec<_>>(),
                        ))
                    } else {
                        None
                    }
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecSqrt([l]) => map!(get, l => {
                lang::Value::vec1(l, |l| {
                    if l.iter().all(|x| {
                        if let lang::Value::Int(i) = x {
                            *i >= 0
                        } else {
                            false
                        }
                    }) {
                        Some(lang::Value::Vec(
                            l.iter()
                                .map(|tup| match tup {
                                    lang::Value::Int(a) => lang::Value::Int(a.sqrt()),
                                    x => panic!("SQRT: Ill-formed: {}", x),
                                })
                                .collect::<Vec<_>>(),
                        ))
                    } else {
                        None
                    }
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecSgn([l]) => map!(get, l => {
                lang::Value::vec1(l, |l| {
                    if l.iter().all(|x| matches!(x, lang::Value::Int(_))) {
                        Some(lang::Value::Vec(
                            l.iter()
                                .map(|tup| match tup {
                                    lang::Value::Int(a) => lang::Value::Int(sgn(*a)),
                                    x => panic!("SGN: Ill-formed: {}", x),
                                })
                                .collect::<Vec<_>>(),
                        ))
                    } else {
                        None
                    }
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecMAC([acc, v1, v2]) => map!(get, v1, v2, acc => {
                lang::Value::vec3(v1, v2, acc, |v1, v2, acc| {
                    v1.iter()
                        .zip(v2.iter())
                        .zip(acc.iter())
                        .map(|tup| match tup {
                            ((lang::Value::Int(v1), lang::Value::Int(v2)), lang::Value::Int(acc))
                => Some(lang::Value::Int((v1 * v2) + acc)),
                            _ => None,
                        })
                        .collect::<Option<Vec<lang::Value>>>()
                        .map(lang::Value::Vec)
                })
            }),
            #[rustfmt::skip]
            lang::VecLang::VecMULS([acc, v1, v2]) => map!(get, v1, v2, acc => {
                lang::Value::vec3(v1, v2, acc, |v1, v2, acc| {
                    v1.iter()
                        .zip(v2.iter())
                        .zip(acc.iter())
                        .map(|tup| match tup {
                            ((lang::Value::Int(v1), lang::Value::Int(v2)), lang::Value::Int(acc))
                => Some(lang::Value::Int(acc - (v1 * v2))),
                            _ => None,
                        })
                        .collect::<Option<Vec<lang::Value>>>()
                        .map(lang::Value::Vec)
                })
            }),
            lang::VecLang::Symbol(_) => vec![],
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        *egraph = egraph.clone().with_explanations_enabled();
        debug!("initializing variables");

        // TODO: consts are set upon creating DiosLang config, for now I've hard coded the constants but can clean it up later
        let consts = vec![0,1];
        // let consts = synth
        //     .lang_config
        //     .constants
        //     .iter()
        //     .map(|c| match c.kind.as_str() {
        //         "int" => lang::Value::Int(c.value),
        //         t => todo!("haven't implemented {t} yet."),
        //     })
        //     .collect_vec();

        // when we don't have any constants, just use the number of variables
        // as the cvec size.
        let cvec_size = if consts.is_empty() {
            vars.len()
        } else {
            self_product(
                &consts.iter().map(|x| Some(x.clone())).collect::<Vec<_>>(),
                vars.len(),
            )
            .len()
        } * 5;

        egraph.analysis.cvec_len = cvec_size;

        egraph.analysis.cvec_len = cvec_size;


        // read and add seed rules from config
        // JB: seed rules can be added by means of enumo's extend operator, so there is no longer any reason to add it here :)

        // add constants to egraph
        for v in consts {
            // int part is also hard-coded, fix this!
            egraph.add(lang::VecLang::Const(lang::Value::Int(v)));
        }

        use rand_pcg::Lcg64Xsh32;
        let mut rng = Lcg64Xsh32::new(0,0);

        // add variables
        // set the initial cvecs of variables. this represents all the possible
        // values that this variable can have
        for i in vars {
            let var = egg::Symbol::from(i);
            let id = egraph.add(lang::VecLang::Symbol(var));

            // make the cvec use real data
            let mut cvec = vec![];

            let (n_ints, n_vecs) = split_into_halves(cvec_size);

            cvec.extend(
                lang::Value::sample_int(&mut rng, -100, 100, n_ints)
                    .into_iter()
                    .map(Some),
            );

            cvec.extend(
                lang::Value::sample_vec(
                    &mut rng,
                    -100,
                    100,
                    1, // synth.params.vector_size
                    n_vecs,
                )
                .into_iter()
                .map(Some),
            );

            log::debug!("cvec for `{var}`: {cvec:?}");

            egraph[id].data.cvec = cvec;
        }
    }

    fn validate(
        lhs: &egg::Pattern<Self>,
        rhs: &egg::Pattern<Self>,
    ) -> ValidationResult {
        // JB TODO: allow for fuzz mode as well
        // let x = if synth.lang_config.always_smt {
            if Self::smt_equals(lhs, rhs) {
                ValidationResult::Valid
            } else {
                ValidationResult::Invalid
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

fn number_of_terms(operations: Vec<Vec<String>>, depth: usize, vars: usize) -> u64 {
    let mut number_of_op_combinations: u64 = 0;
    for (i, operation_layer) in itertools::enumerate(operations) {
        number_of_op_combinations += (operation_layer.len() * num::pow(vars, i)).to_u64().unwrap();
    }
    num::pow(number_of_op_combinations, depth)
} 

// now, instead of always passing in all operations, only some operations will be passed in 
fn iter_dios(depth: usize, values: Vec<String>, variable_names: Vec<String>, operations: Vec<Vec<String>>) -> Workload {

    println!("operations length {:?}", operations.len());
    let mut workload = recipe_utils::base_lang(operations.len());
    println!("beginning workload {:?}", workload.clone());
    
    workload = recipe_utils::iter_metric(workload, "EXPR", Metric::Depth, depth)
    // JB: was this just to ensure that variables included in rules/ don't learn val only rules? unsure, explore
    // .filter(Filter::Contains("VAR".parse().unwrap()))
    .plug("VAL", &Workload::new(values.clone()))
    .plug("VAR", &Workload::new(variable_names.clone()))
    // JB: toggle between eq and lt
    .filter(Filter::MetricLt(Metric::Depth, depth+1))
    // JB: I don't think this does much -- look into this
    .filter(Filter::Canon(variable_names.clone().into_iter().map(|x| x.to_string()).collect()));

    for (i, operation_layer) in operations.iter().enumerate() {
        // println!("plugging layer {i} {operation_layer:?}");
        workload = workload.plug(format!("OP{}", i+1), &Workload::new(operation_layer.clone()));
    }

    // println!("created workload is {:#?}", workload.clone().force().collect::<Vec<_>>());


    workload
}

fn iter_dios_limited(depth: usize, values: Vec<String>, variable_names: Vec<String>, operations: Vec<Vec<String>>) -> Workload {
    // there will ops up to triops here -> if this changes, this code needs to change
    let leq_binop_workload = iter_dios(depth-1, values, variable_names, operations[0..operations.len() - 1].to_vec());
    // println!("leq binop workload is {:?}", leq_binop_workload.clone().force().collect::<Vec<_>>());
    let triop_workload = Workload::new(["(OP3 EXPR EXPR EXPR)", "EXPR"]);
    let final_workload = triop_workload
                            .plug("OP3", &Workload::new(operations[operations.len()-1].clone()))
                            .plug("EXPR",&leq_binop_workload);
                        // println!("final workload is {:#?}", final_workload.clone().force().collect::<Vec<_>>().len());
                        // println!("final workload is {:#?}", final_workload.clone().force().collect::<Vec<_>>());

    final_workload

}

fn extend_rules() -> ruler::enumo::Ruleset<lang::VecLang>{
    Ruleset::new([
        "(VecAdd (Vec ?b) (Vec ?a)) ==> (Vec (+ ?b ?a))", 
        "(VecDiv (Vec ?b) (Vec ?a)) ==> (Vec (/ ?b ?a))"]
    )
}

fn explore_ops_at_depth(rules: &mut Ruleset<lang::VecLang>, 
                        ops: Vec<Vec<String>>, 
                        vals: Vec<String>, 
                        vars: Vec<String>, 
                        depth: usize, 
                        // change are_vec_ops to arbitrary filters
                        are_vec_ops: bool, 
                        run_name: String,
                        rule_lifting: bool) 
                        // -> &mut Ruleset<lang::VecLang> 
{
    use ruler::recipe_utils::*;
    use std::io;

    // JB todo: make it optional to do this
    let num_vars = number_of_terms(ops.clone(), depth, vars.len() + vals.len());
    println!("Number of nodes in egraph will be: {num_vars}. Are you sure you want to proceed? n for no");
    // let mut answer = String::new();
    // io::stdin().read_line(&mut answer)
    //     .expect("Failed to read line");
    // if answer.contains("n") {
    //     return ();
    // }
    let mut vars = vars.clone();

    // main goal is to cut down on size of variables, even before using the canonical filter
    // if depth == 2 && vars.len() > ops.len() {
    //     vars = vars[0..ops.len()].to_vec();
    // }
    // else if depth == 3 && vars.len() > ops.len() * 2 {
    //     vars = vars[0..ops.len()*2].to_vec();
    // }

    
    let workload: ruler::enumo::Workload = { 
        if (ops.len() >= 3) {
            debug!("running limited workload");
            iter_dios_limited(depth, vals.clone(), vars.clone(), ops.clone())
        } 
        else {
            iter_dios(depth, vals.clone(), vars.clone(), ops.clone())
        }
    };
    let workload = { 
        if are_vec_ops {
            workload.filter(Filter::Contains("Vec".parse().unwrap()))
        }
        else { 
            workload
        }
    };
    // println!("workload is {:?}", workload.clone().force().collect::<Vec<_>>());
    // std::process::exit(0);
    let new_ruleset = {
        if rule_lifting {
            run_rule_lifting(workload, (*rules).clone(), ruler::Limits::synthesis(), ruler::Limits::synthesis())
        }
        else {
            // println!("prior rules are {rules:?}");
            run_workload(workload, (*rules).clone(), ruler::Limits::synthesis(), ruler::Limits::synthesis(), true)
        }
    };
    let file_str = match are_vec_ops { true=>"vec", false=>"non-vec" };
    ruler::logger::log_rules(&new_ruleset, Some((format!("candidates/depth_{}_ruleset_{}.json", depth, file_str)).as_str()), &run_name);

    rules.extend(new_ruleset);
    // rules
}



fn extract_vector_operations(unops: Vec<String>, binops: Vec<String>, triops: Vec<String>) -> (Vec<Vec<String>>, Vec<Vec<String>>) {
    let (vector_rules_unops, scalar_rules_unops): (Vec<String>, Vec<String>) =
        unops.into_iter().partition(|element| element.to_lowercase().contains("vec"));
    let (vector_rules_binops, scalar_rules_binops): (Vec<_>, Vec<_>) =
        binops.into_iter().partition(|element| element.to_lowercase().contains("vec"));
    let (vector_rules_triops, scalar_rules_triops): (Vec<_>, Vec<_>) =
        triops.into_iter().partition(|element| element.to_lowercase().contains("vec"));

    //clunky, fix later
    // vector_rules_unops.append(&mut scalar_rules_unops.clone());
    // vector_rules_binops.append(&mut scalar_rules_binops.clone());
    // vector_rules_triops.append(&mut scalar_rules_triops.clone());

    let vector_ops = [vector_rules_unops, vector_rules_binops, vector_rules_triops].to_vec();
    let scalar_ops = [scalar_rules_unops, scalar_rules_binops, scalar_rules_triops].to_vec();

    return (vector_ops, scalar_ops)
}


fn a_la_carte(rules: &mut Ruleset<lang::VecLang>, 
                scalar_ops: Vec<Vec<String>>, 
                vector_ops: Vec<Vec<String>>, 
                vals: Vec<String>, 
                vars: Vec<String>,
                run_name: String) -> Ruleset<lang::VecLang> 
{
    // learn rules for scalar ops up to depth 2, no need to go much deeper i don't think
    debug!("Learning scalar rules");
    for i in 2..3 {
        debug!("Exploring scalar ops at depth {i}");
        explore_ops_at_depth(rules, scalar_ops.clone(), vals.clone(), vars.clone(), i, false, run_name.clone(), false);
    }

    // now, for each related vector rules and scalar rule (ie vecadd/add, pairwise learn rules about the two)

    
    // now, using rule lifting, learn rules for vector ops up to depth 3 -- might need to tweak to depth 2?

    // 
    assert!(vector_ops.len() >= 3);
    // let vector_unary_binary = vector_ops[0..2].to_vec();
    // let vector_ternary = vec![vector_ops[2].clone()];

    let related_unary: Vec<Vec<String>> = vec![vec!["Vec", "VecSgn", "sgn", "VecSqrt", "sqrt", "VecNeg", "neg"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let binary_ops = vec![vec!["Vec"], vec!["VecAdd", "+", "VecMinus", "-", "VecMul", "*", "VecDiv", "/"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    // let related_binary_mul = vec![vec!["Vec"], vec!["VecMul", "*", "VecDiv", "/"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    // JB: do the math for this 
    // let related_mac_muls = vec![vec!["Vec"], vec!["VecAdd", "+", "VecMul", "*"], vec!["VecMAC", "VecMULS"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let related_muls: Vec<Vec<String>> = vec![vec!["Vec"], vec!["VecMul", "VecMinus", "VecAdd"], vec!["VecMULS"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let related_mac = vec![vec!["Vec"], vec!["VecMul", "VecAdd", "VecMinus"], vec!["VecMAC"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let related_mac = vec![vec!["Vec"], vec!["VecMul", "VecAdd", "VecMinus"], vec!["VecMAC"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();

    // let related_mac_add = vec![vec!["Vec"], vec!["VecAdd"], vec!["VecMAC"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();


    // let related_mac_muls2 = vec![vec!["Vec"], vec!["VecMul", "*"], vec!["VecMAC", "VecMULS"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let rules_to_learn = vec![related_unary, binary_ops, related_mac, related_muls];
    // let rules_to_learn = vec![related_mac, related_muls, related_mac_add];
    
    // let rules_to_learn_d2 = vec![related_mac, related_muls, related_mac_add];

    for (i, opset) in itertools::enumerate(rules_to_learn) {
        // JB: todo make this a loop if needed
        debug!("Learning {opset:?} at depth 3");
        // maybe add additional filters?
        explore_ops_at_depth(rules, opset.clone(), vals.clone(), vars.clone(), 3, true, format!("opset{}_{}", i, run_name), false);
        // std::process::exit(0);

        // debug!("Learning {opset:?} at depth 3");
        // explore_ops_at_depth(rules, opset, vals.clone(), vars.clone(), 4, true, format!("opset{}_{}", i, run_name), false)
        
    }
    // for (i, opset) in itertools::enumerate(rules_to_learn_d2) {
    //     // JB: todo make this a loop if needed
    //     debug!("Learning {opset:?} at depth 2");
    //     // maybe add additional filters?
    //     explore_ops_at_depth(rules, opset.clone(), vals.clone(), vars.clone(), 2, true, format!("opset{}_{}", i, run_name), false);
    //     // std::process::exit(0);
    // }

    // explore all vector ops now
    // debug!("Exploring all vector ops at depth 3");
    // explore_ops_at_depth(rules, vector_ops.clone(), vals.clone(), vars.clone(), 3, true, run_name.clone(), false);


    // JB: why does it have to be depth 3. so weird.
    // for i in 3 {
    //     debug!("ITERATION {i}, unary+binary");
    //     debug!("exploring vector ops at depth {i}");
    // }
    // no need to learn super deep rules for vecMAC and vecMULS
    // for i in 2..2 {
        // debug!("ITERATION {}, ternary", 1);

        // explore_ops_at_depth(rules, vector_ternary.clone(), vals.clone(), vars.clone(), 3, true, format!("{} {}", run_name.clone(), "_ternary"), true);
    // }
    // explore_ops_at_depth(rules, vector_unary_binary.clone(), vals.clone(), vars.clone(), 2, true, run_name.clone(), false);
    
    (*rules).clone()
}

pub fn run(
    dios_config: DiosConfig,
    _chkpt_path: Option<PathBuf>,
) -> Res<ruler::enumo::Ruleset<lang::VecLang>>
{
    let run_name = "slow cvec match, up to depth 5, using depth instead of atoms";
    log::info!("running with config: {dios_config:#?}");

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

    seed_rules.extend(extend_rules());

    let vals = ["0", "1"].iter().map(|x| x.to_string()).collect();
    // if you pass in all vars and then use canon filter, it will still reify all 
    // and THEN filter them -> don't bother, send in exact number of vars needed
    let vars = ["a", "b", "c", "d", "e", "f"].iter().map(|x| x.to_string()).collect();

    let mut rules = seed_rules.clone();
    let (vec_ops, scalar_ops) = extract_vector_operations(dios_config.unops.clone(), dios_config.binops.clone(), dios_config.triops.clone());
    let mut scalar_ops = scalar_ops.clone();
    while scalar_ops[scalar_ops.len() - 1].len() == 0 {
        scalar_ops.pop();
    }
    // do the thing!
    // let rules_scalar = Ruleset::from_file("rational_rules.txt");
    // rules.extend(rules_scalar);
    println!("scalar ops {scalar_ops:?}\nvector ops {vec_ops:?}");
    // std::process::exit(0);
    let rules = a_la_carte(&mut rules, scalar_ops, vec_ops, vals, vars, "categorizing_vector_rules".to_string());

    ruler::logger::log_rules(&rules, Some("rulesets/ruleset.json"), run_name);

    Ok(rules)
}


