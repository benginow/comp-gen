use egg::{self, define_language, Id, Language, FromOp};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};
use std::str::FromStr;
use comp_gen::ruler::{
    self, enumo::*, ValidationResult,
};
use log::debug;
use rand::Rng;
use rand_pcg::Pcg32;
use ruler::{
    map, self_product, CVec, SynthAnalysis, SynthLanguage
};
use crate::{desugared_lang, desugared_workloads::*, smt::SmtEquals, Res, util};
use egg::EGraph;

#[derive(
    Debug, PartialOrd, Ord, PartialEq, Eq, Hash, Clone, Serialize, Deserialize,
)]
pub enum Value {
    // starts with i
    Int(i64),
    // starts with [
    List(Vec<Value>),
    // starts with <
    Vec(Vec<Value>),
    // starts with b
    Bool(bool),
}

impl FromStr for Value {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, <Self as FromStr>::Err> {
        let int = str::parse::<i64>(s).map_err(|e| e.to_string())?;
        Ok(Value::Int(int))
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            Value::Int(i) => write!(f, "{}", i),
            Value::Bool(b) => write!(f, "{}", b),
            Value::List(l) => write!(f, "{:?}", l),
            Value::Vec(v) => {
                write!(
                    f,
                    "(Vec {})",
                    v.iter().map(|x| format!("{}", x)).collect_vec().join(" ")
                )
            }
        }
    }
}

egg::define_language! {
    #[derive(Serialize, Deserialize)]
    pub enum VecLangDesugared {
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "-" = Minus([Id; 2]),
        "/" = Div([Id; 2]),

        // wec width is 4
        "VecAdd" = VecAdd([Id; 2]),
        "VecMinus" = VecMinus([Id; 2]),
        "VecMul" = VecMul([Id; 2]),
        "VecDiv" = VecDiv([Id; 2]),

        
        "VecSum" = VecSum([Id; 1]),

        // Vectors have width elements
        "Vec" = Vec(Box<[Id]>),

        // Lists have a variable number of elements
        "List" = List(Box<[Id]>),

        // Vector with all literals
        "LitVec" = LitVec(Box<[Id]>),
        "Get" = Get([Id; 2]),

        // Used for partitioning and recombining lists
        "Concat" = Concat([Id; 2]),

        // takes two vectors -> the given vector to shuffle, and then the shuffling indices
        "Shfl" = Shfl([Id; 2]),

        Const(Value),
        Symbol(egg::Symbol),
    }
}

impl comp_gen::FromPattern for VecLangDesugared {
    fn from_pattern(pat: &egg::PatternAst<Self>) -> egg::RecExpr<Self> {
        pat.as_ref()
            .iter()
            .map(|node| match node {
                egg::ENodeOrVar::Var(v) => {
                    VecLangDesugared::Symbol(v.to_string().into())
                }
                egg::ENodeOrVar::ENode(node) => node.clone(),
            })
            .collect::<Vec<_>>()
            .into()
    }
}


// copied over from synthesis.rs
pub fn split_into_halves(n: usize) -> (usize, usize) {
    if n % 2 == 0 {
        (n / 2, n / 2)
    } else {
        (n / 2, n / 2 + 1)
    }
}

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

impl desugared_lang::Value {
    fn int1<F>(arg: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(i64) -> desugared_lang::Value,
    {
        if let desugared_lang::Value::Int(val) = arg {
            Some(f(*val))
        } else {
            println!("arg is not an int {:?}", arg);
            None
        }
    }

    fn int2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(i64, i64) -> desugared_lang::Value,
    {
        if let (desugared_lang::Value::Int(lv), desugared_lang::Value::Int(rv)) = (lhs, rhs) {
            Some(f(*lv, *rv))
        } else {
            None
        }
    }

    fn bool2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(bool, bool) -> desugared_lang::Value,
    {
        if let (desugared_lang::Value::Bool(lv), desugared_lang::Value::Bool(rv)) = (lhs, rhs) {
            Some(f(*lv, *rv))
        } else {
            None
        }
    }

    fn vec1<F>(val: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(&[desugared_lang::Value]) -> Option<desugared_lang::Value>,
    {
        if let desugared_lang::Value::Vec(v) = val {
            f(v)
        } else {
            None
        }
    }

    fn vec2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(&[desugared_lang::Value], &[desugared_lang::Value]) -> Option<desugared_lang::Value>,
    {
        if let (desugared_lang::Value::Vec(v1), desugared_lang::Value::Vec(v2)) = (lhs, rhs) {
            if v1.len() == v2.len() {
                f(v1, v2)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn vec3<F>(v1: &Self, v2: &Self, v3: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(
            &[desugared_lang::Value],
            &[desugared_lang::Value],
            &[desugared_lang::Value],
        ) -> Option<desugared_lang::Value>,
    {
        if let (
            desugared_lang::Value::Vec(v1),
            desugared_lang::Value::Vec(v2),
            desugared_lang::Value::Vec(v3),
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

    fn vec1_op<F>(vec: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(&desugared_lang::Value) -> Option<desugared_lang::Value>,
    {
        Self::vec1(vec, |vec| {
            vec.iter()
                .map(|v| {println!("Value is {:?}", v);f(v)})
                .collect::<Option<Vec<desugared_lang::Value>>>()
                .map(desugared_lang::Value::Vec)
        })
    }


    fn vec2_op<F>(lhs: &Self, rhs: &Self, f: F) -> Option<desugared_lang::Value>
    where
        F: Fn(&desugared_lang::Value, &desugared_lang::Value) -> Option<desugared_lang::Value>,
    {
        Self::vec2(lhs, rhs, |lhs, rhs| {
            lhs.iter()
                .zip(rhs)
                .map(|(l, r)| f(l, r))
                .collect::<Option<Vec<desugared_lang::Value>>>()
                .map(desugared_lang::Value::Vec)
        })
    }

    #[allow(unused)]
    fn int_range(min: i64, max: i64, num_samples: usize) -> Vec<desugared_lang::Value> {
        (min..=max)
            .step_by(((max - min) as usize) / num_samples)
            .map(desugared_lang::Value::Int)
            .collect::<Vec<_>>()
    }

    fn sample_int(
        rng: &mut Pcg32,
        min: i64,
        max: i64,
        num_samples: usize,
    ) -> Vec<desugared_lang::Value> {
        (0..num_samples)
            .map(|_| desugared_lang::Value::Int(rng.gen_range(min, max)))
            .collect::<Vec<_>>()
    }

    pub fn sample_vec(
        rng: &mut Pcg32,
        min: i64,
        max: i64,
        list_size: usize,
        num_samples: usize,
    ) -> Vec<desugared_lang::Value> {
        (0..num_samples)
            .map(|_| {
                desugared_lang::Value::Vec(desugared_lang::Value::sample_int(
                    rng, min, max, list_size,
                ))
            })
            .collect::<Vec<_>>()
    }
}

impl SynthLanguage for desugared_lang::VecLangDesugared {
    type Constant = desugared_lang::Value;

    fn to_var(&self) -> Option<egg::Symbol> {
        if let desugared_lang::VecLangDesugared::Symbol(sym) = self {
            Some(*sym)
        } else {
            None
        }
    }

    fn mk_var(sym: egg::Symbol) -> Self {
        desugared_lang::VecLangDesugared::Symbol(sym)
    }

    fn is_constant(&self) -> bool {
        matches!(&self, desugared_lang::VecLangDesugared::Const(_))
    }

    fn mk_constant(c: <Self as SynthLanguage>::Constant, _e: &mut EGraph<Self, SynthAnalysis>) -> Self {
        desugared_lang::VecLangDesugared::Const(c)
    }

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        match self {
            desugared_lang::VecLangDesugared::Const(i) => vec![Some(i.clone()); cvec_len],
            desugared_lang::VecLangDesugared::Add([l, r]) => map!(get, l, r => {
                desugared_lang::Value::int2(l, r, |l, r| desugared_lang::Value::Int(l + r))
            }),
            desugared_lang::VecLangDesugared::Mul([l, r]) => map!(get, l, r => {
                desugared_lang::Value::int2(l, r, |l, r| desugared_lang::Value::Int(l * r))
            }),
            desugared_lang::VecLangDesugared::Minus([l, r]) => map!(get, l, r => {
                desugared_lang::Value::int2(l, r, |l, r| desugared_lang::Value::Int(l - r))
            }),
            desugared_lang::VecLangDesugared::Div([l, r]) => get(l)
                .iter()
                .zip(get(r).iter())
                .map(|tup| match tup {
                    (Some(desugared_lang::Value::Int(a)), Some(desugared_lang::Value::Int(b))) => {
                        integer_division(*a, *b).map(desugared_lang::Value::Int)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
            desugared_lang::VecLangDesugared::List(l) => l
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
                .map(|acc| acc.map(desugared_lang::Value::List))
                .collect::<Vec<_>>(),
            desugared_lang::VecLangDesugared::Vec(l) => l
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
                .map(|acc| acc.map(desugared_lang::Value::Vec))
                .collect::<Vec<_>>(),
            desugared_lang::VecLangDesugared::LitVec(l) => l
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
                .map(|acc| acc.map(desugared_lang::Value::Vec))
                .collect::<Vec<_>>(),
            #[rustfmt::skip]
            desugared_lang::VecLangDesugared::Get([l, i]) => map!(get, l, i => {
                if let (desugared_lang::Value::Vec(v), desugared_lang::Value::Int(idx)) = (l, i) {
                    // get index and clone the inner desugared_lang::Value if there is one
                    v.get(*idx as usize).cloned()
                } else {
                    None
                }
            }),
            #[rustfmt::skip]
            desugared_lang::VecLangDesugared::Concat([l, r]) => map!(get, l, r => {
                desugared_lang::Value::vec2(l, r, |l, r| {
                    Some(desugared_lang::Value::List(
                        l.iter().chain(r).cloned().collect::<Vec<_>>(),
                    ))
                })
            }),
            #[rustfmt::skip]
            desugared_lang::VecLangDesugared::VecAdd([l, r]) => map!(get, l, r => {
                desugared_lang::Value::vec2_op(l, r, |l, r| {
                    desugared_lang::Value::int2(l, r, |l, r| desugared_lang::Value::Int(l + r))
                })
            }),
            #[rustfmt::skip]
            desugared_lang::VecLangDesugared::VecMinus([l, r]) => map!(get, l, r => {
                desugared_lang::Value::vec2_op(l, r, |l, r| {
                    desugared_lang::Value::int2(l, r, |l, r| desugared_lang::Value::Int(l - r))
                })
            }),
            #[rustfmt::skip]
            desugared_lang::VecLangDesugared::VecMul([l, r]) => map!(get, l, r => {
                desugared_lang::Value::vec2_op(l, r, |l, r| {
                    desugared_lang::Value::int2(l, r, |l, r| desugared_lang::Value::Int(l * r))
                })
            }),
            #[rustfmt::skip]
            desugared_lang::VecLangDesugared::VecDiv([l, r]) => {
                let val = map!(get, l, r => {
                desugared_lang::Value::vec2_op(l, r, |l, r| match (l, r) {
                    (desugared_lang::Value::Int(a), desugared_lang::Value::Int(b)) => {
                        integer_division(*a, *b).map(desugared_lang::Value::Int)
                    }
                    _ => None,
                    })
                }); 
                val
            },
            desugared_lang::VecLangDesugared::VecSum([v]) => {
                use itertools::enumerate;
                let val = map!(get, v => {
                    println!("val is: {v:?}");
                    match v {
                        desugared_lang::Value::Vec(vec) => {
                            let mut worked = true;
                            let mut summed_list = vec![Some(desugared_lang::Value::Int(0))];
                            for (_idx, element) in enumerate(vec) {
                                match element {
                                    desugared_lang::Value::Int(i) => {
                                        summed_list[0] = match summed_list[0] {
                                            Some(desugared_lang::Value::Int(prev)) => {
                                                summed_list.push(Some(desugared_lang::Value::Int(0)));
                                                Some(desugared_lang::Value::Int(prev + i))},
                                            _ => {
                                                summed_list.push(None);
                                                worked = false;
                                                None}
                                        }
                                    }
                                    _ => {
                                        summed_list.push(None);
                                        worked = false;
                                        summed_list[0] = None
                                    }
                                }
                                
                            }
                            if worked {
                                Some(desugared_lang::Value::Vec(summed_list.into_iter().map(|x| x.unwrap()).collect()))
                            }
                            else {
                                None
                            }
                            
                        }
                        _ => None
                    }
                });
                println!{"val is {val:?}"};
                val
        },
            desugared_lang::VecLangDesugared::Shfl([l, r]) => {
                let shuffle_vec = map!(get, l => {
                    desugared_lang::Value::int1(l, |l| desugared_lang::Value::Int(l))
                });
                let indices = map!(get, r => {
                    desugared_lang::Value::int1(r, |r| desugared_lang::Value::Int(r))
                });
                let mut shuffled = vec![];
                for index in indices {
                    if let Some(desugared_lang::Value::Int(idx)) = index {
                        let idx = idx as usize;
                        shuffled.push(shuffle_vec[idx].clone());
                    }

                }
                shuffled
            }
            desugared_lang::VecLangDesugared::Symbol(_) => vec![],
        }
    }

    fn initialize_vars(egraph: &mut EGraph<Self, SynthAnalysis>, vars: &[String]) {
        *egraph = egraph.clone().with_explanations_enabled();
        debug!("initializing variables");

        // TODO: consts are set upon creating DiosLang config, for now I've hard coded the constants but can clean it up later
        let consts = vec![0,1];

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

        // add constants to egraph
        for v in consts {
            // int part is also hard-coded, fix this!
            egraph.add(desugared_lang::VecLangDesugared::Const(desugared_lang::Value::Int(v)));
        }

        use rand_pcg::Lcg64Xsh32;
        let mut rng = Lcg64Xsh32::new(0,0);

        // add variables
        // set the initial cvecs of variables. this represents all the possible
        // values that this variable can have
        for i in vars {
            let var = egg::Symbol::from(i);
            let id = egraph.add(desugared_lang::VecLangDesugared::Symbol(var));

            // make the cvec use real data
            let mut cvec = vec![];

            let (n_ints, n_vecs) = split_into_halves(cvec_size);

            cvec.extend(
                desugared_lang::Value::sample_int(&mut rng, -100, 100, n_ints)
                    .into_iter()
                    .map(Some),
            );

            cvec.extend(
                desugared_lang::Value::sample_vec(
                    &mut rng,
                    -100,
                    100,
                    4, // synth.params.vector_size
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
        // There is no fuzz validation for desugared synthesis right now -> tbd
            if Self::smt_equals(lhs, rhs) {
                ValidationResult::Valid
            } else {
                ValidationResult::Invalid
            }
    }
}