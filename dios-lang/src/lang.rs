use egg::{define_language, Id, Language, FromOp, EGraph};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};
use std::str::FromStr;
use comp_gen::ruler::{self, SynthLanguage, enumo::*, map, self_product, SynthAnalysis, CVec, ValidationResult};
use rand::Rng;
use rand_pcg::Pcg32;
use crate::util;
use num::{integer::Roots, ToPrimitive};
use log::debug;


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
    pub enum VecLang {
        // Id is a key to identify EClasses within an EGraph, represents
        // children nodes
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "-" = Minus([Id; 2]),
        "/" = Div([Id; 2]),

        "or" = Or([Id; 2]),
        "&&" = And([Id; 2]),
        "ite" = Ite([Id; 3]),
        "<" = Lt([Id; 2]),
        "sqrtsgn" = SqrtSgn([Id; 2]),

        "sgn" = Sgn([Id; 1]),
        "sqrt" = Sqrt([Id; 1]),
        "neg" = Neg([Id; 1]),

        // Lists have a variable number of elements
        "List" = List(Box<[Id]>),

        // Vectors have width elements
        "Vec" = Vec(Box<[Id]>),

        // Vector with all literals
        "LitVec" = LitVec(Box<[Id]>),

        "Get" = Get([Id; 2]),

        // Used for partitioning and recombining lists
        "Concat" = Concat([Id; 2]),

        // Vector operations that take 2 vectors of inputs
        "VecAdd" = VecAdd([Id; 2]),
        "VecMinus" = VecMinus([Id; 2]),
        "VecMul" = VecMul([Id; 2]),
        "VecDiv" = VecDiv([Id; 2]),
        "VecMulSgn" = VecMulSgn([Id; 2]),
        "VecSqrtSgn" = VecSqrtSgn([Id; 2]),

        // Vector operations that take 1 vector of inputs
        "VecNeg" = VecNeg([Id; 1]),
        "VecSqrt" = VecSqrt([Id; 1]),
        "VecSgn" = VecSgn([Id; 1]),
        // "VecRAdd" = VecRAdd([Id; 1]),

        // MAC takes 3 lists: acc, v1, v2
        "VecMAC" = VecMAC([Id; 3]),
        "VecMULS" = VecMULS([Id; 3]),

        Const(Value),

        // language items are parsed in order, and we want symbol to
        // be a fallback, so we put it last.
        // `Symbol` is an egg-provided interned string type
        Symbol(egg::Symbol),
    }
}

#[derive(Debug, Clone)]
pub enum VecAst {
    Add(Box<VecAst>, Box<VecAst>),
    Mul(Box<VecAst>, Box<VecAst>),
    Minus(Box<VecAst>, Box<VecAst>),
    Div(Box<VecAst>, Box<VecAst>),

    Or(Box<VecAst>, Box<VecAst>),
    And(Box<VecAst>, Box<VecAst>),
    #[allow(unused)]
    Ite(Box<VecAst>, Box<VecAst>, Box<VecAst>),
    Lt(Box<VecAst>, Box<VecAst>),
    SqrtSgn(Box<VecAst>, Box<VecAst>),
    Get(Box<VecAst>, Box<VecAst>),

    Sqrt(Box<VecAst>),
    Sgn(Box<VecAst>),
    Neg(Box<VecAst>),

    Vec(Vec<VecAst>),
    LitVec(Vec<VecAst>),

    VecAdd(Box<VecAst>, Box<VecAst>),
    VecMul(Box<VecAst>, Box<VecAst>),
    VecMinus(Box<VecAst>, Box<VecAst>),
    VecDiv(Box<VecAst>, Box<VecAst>),
    VecMulSgn(Box<VecAst>, Box<VecAst>),
    VecSqrtSgn(Box<VecAst>, Box<VecAst>),

    VecNeg(Box<VecAst>),
    VecSqrt(Box<VecAst>),
    VecSgn(Box<VecAst>),

    VecMAC(Box<VecAst>, Box<VecAst>, Box<VecAst>),
    VecMULS(Box<VecAst>, Box<VecAst>, Box<VecAst>),

    Const(Value),
    Symbol(String),
}

impl VecAst {
    fn to_recexpr(&self, expr: &mut egg::RecExpr<VecLang>) -> Id {
        match self {
            VecAst::Add(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::Add([left_id, right_id]))
            }
            VecAst::Mul(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::Mul([left_id, right_id]))
            }
            VecAst::Minus(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::Minus([left_id, right_id]))
            }
            VecAst::Div(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::Div([left_id, right_id]))
            }
            VecAst::Or(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::Or([left_id, right_id]))
            }
            VecAst::And(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::And([left_id, right_id]))
            }
            VecAst::Lt(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::Lt([left_id, right_id]))
            }
            VecAst::SqrtSgn(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::SqrtSgn([left_id, right_id]))
            }
            VecAst::VecAdd(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::VecAdd([left_id, right_id]))
            }
            VecAst::VecMul(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::VecMul([left_id, right_id]))
            }
            VecAst::VecMinus(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::VecMinus([left_id, right_id]))
            }
            VecAst::VecDiv(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::VecDiv([left_id, right_id]))
            }
            VecAst::VecMulSgn(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::VecMulSgn([left_id, right_id]))
            }
            VecAst::VecSqrtSgn(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::VecSqrtSgn([left_id, right_id]))
            }
            VecAst::Ite(_, _, _) => todo!(),
            VecAst::Sqrt(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::Sqrt([id]))
            }
            VecAst::Sgn(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::Sgn([id]))
            }
            VecAst::Neg(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::Neg([id]))
            }
            VecAst::VecNeg(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::VecNeg([id]))
            }
            VecAst::VecSqrt(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::VecSqrt([id]))
            }
            VecAst::VecSgn(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::VecSgn([id]))
            }
            VecAst::VecMAC(a, b, c) => {
                let a_id = a.to_recexpr(expr);
                let b_id = b.to_recexpr(expr);
                let c_id = c.to_recexpr(expr);
                expr.add(VecLang::VecMAC([a_id, b_id, c_id]))
            }
            VecAst::VecMULS(a, b, c) => {
                let a_id = a.to_recexpr(expr);
                let b_id = b.to_recexpr(expr);
                let c_id = c.to_recexpr(expr);
                expr.add(VecLang::VecMULS([a_id, b_id, c_id]))
            }
            VecAst::Vec(items) => {
                let ids =
                    items.iter().map(|it| it.to_recexpr(expr)).collect_vec();
                expr.add(VecLang::Vec(ids.into_boxed_slice()))
            }
            VecAst::LitVec(items) => {
                let ids =
                    items.iter().map(|it| it.to_recexpr(expr)).collect_vec();
                expr.add(VecLang::LitVec(ids.into_boxed_slice()))
            }
            VecAst::Get(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::Get([left_id, right_id]))
            }
            VecAst::Const(v) => expr.add(VecLang::Const(v.clone())),
            VecAst::Symbol(s) => expr.add(VecLang::Symbol(s.into())),
        }
    }
}

fn subtree(
    expr: &egg::RecExpr<VecLang>,
    new_root: Id,
) -> egg::RecExpr<VecLang> {
    expr[new_root].build_recexpr(|id| expr[id].clone())
}

impl From<egg::RecExpr<VecLang>> for VecAst {
    fn from(expr: egg::RecExpr<VecLang>) -> Self {
        let root: Id = Id::from(expr.as_ref().len() - 1);
        match &expr[root] {
            VecLang::Add([left, right]) => VecAst::Add(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::Mul([left, right]) => VecAst::Mul(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::Minus([left, right]) => VecAst::Minus(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::Div([left, right]) => VecAst::Div(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::Or([left, right]) => VecAst::Or(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::And([left, right]) => VecAst::And(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::Ite(_) => todo!(),
            VecLang::Lt([left, right]) => VecAst::Lt(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::SqrtSgn([left, right]) => VecAst::SqrtSgn(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::Sgn([inner]) => {
                VecAst::Sgn(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::Sqrt([inner]) => {
                VecAst::Sqrt(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::Neg([inner]) => {
                VecAst::Neg(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::List(_) => todo!(),
            VecLang::Vec(items) => VecAst::Vec(
                items
                    .iter()
                    .map(|id| subtree(&expr, *id).into())
                    .collect_vec(),
            ),
            VecLang::LitVec(items) => VecAst::LitVec(
                items
                    .iter()
                    .map(|id| subtree(&expr, *id).into())
                    .collect_vec(),
            ),
            VecLang::Get([left, right]) => VecAst::Get(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::Concat(_) => todo!(),
            VecLang::VecAdd([left, right]) => VecAst::VecAdd(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::VecMinus([left, right]) => VecAst::VecMinus(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::VecMul([left, right]) => VecAst::VecMul(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::VecDiv([left, right]) => VecAst::VecDiv(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::VecMulSgn([left, right]) => VecAst::VecMulSgn(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::VecSqrtSgn([left, right]) => VecAst::VecSqrtSgn(
                Box::new(subtree(&expr, *left).into()),
                Box::new(subtree(&expr, *right).into()),
            ),
            VecLang::VecNeg([inner]) => {
                VecAst::VecNeg(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::VecSqrt([inner]) => {
                VecAst::VecSqrt(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::VecSgn([inner]) => {
                VecAst::VecSgn(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::VecMAC([a, b, c]) => VecAst::VecMAC(
                Box::new(subtree(&expr, *a).into()),
                Box::new(subtree(&expr, *b).into()),
                Box::new(subtree(&expr, *c).into()),
            ),
            VecLang::VecMULS([a, b, c]) => VecAst::VecMULS(
                Box::new(subtree(&expr, *a).into()),
                Box::new(subtree(&expr, *b).into()),
                Box::new(subtree(&expr, *c).into()),
            ),
            VecLang::Const(v) => VecAst::Const(v.clone()),
            VecLang::Symbol(sym) => VecAst::Symbol(sym.to_string()),
        }
    }
}

impl From<VecAst> for egg::RecExpr<VecLang> {
    fn from(ast: VecAst) -> Self {
        let mut expr = egg::RecExpr::default();
        ast.to_recexpr(&mut expr);
        expr
    }
}

impl comp_gen::FromPattern for VecLang {
    fn from_pattern(pat: &egg::PatternAst<Self>) -> egg::RecExpr<Self> {
        pat.as_ref()
            .iter()
            .map(|node| match node {
                egg::ENodeOrVar::Var(v) => {
                    VecLang::Symbol(v.to_string().into())
                }
                egg::ENodeOrVar::ENode(node) => node.clone(),
            })
            .collect::<Vec<_>>()
            .into()
    }
}


impl Value {
    fn int1<F>(arg: &Self, f: F) -> Option<Value>
    where
        F: Fn(i64) -> Value,
    {
        if let Value::Int(val) = arg {
            Some(f(*val))
        } else {
            None
        }
    }

    fn int2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<Value>
    where
        F: Fn(i64, i64) -> Value,
    {
        if let (Value::Int(lv), Value::Int(rv)) = (lhs, rhs) {
            Some(f(*lv, *rv))
        } else {
            None
        }
    }

    fn bool2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<Value>
    where
        F: Fn(bool, bool) -> Value,
    {
        if let (Value::Bool(lv), Value::Bool(rv)) = (lhs, rhs) {
            Some(f(*lv, *rv))
        } else {
            None
        }
    }

    fn vec1<F>(val: &Self, f: F) -> Option<Value>
    where
        F: Fn(&[Value]) -> Option<Value>,
    {
        if let Value::Vec(v) = val {
            f(v)
        } else {
            None
        }
    }

    fn vec2<F>(lhs: &Self, rhs: &Self, f: F) -> Option<Value>
    where
        F: Fn(&[Value], &[Value]) -> Option<Value>,
    {
        if let (Value::Vec(v1), Value::Vec(v2)) = (lhs, rhs) {
            if v1.len() == v2.len() {
                f(v1, v2)
            } else {
                None
            }
        } else {
            None
        }
    }

    fn vec3<F>(v1: &Self, v2: &Self, v3: &Self, f: F) -> Option<Value>
    where
        F: Fn(
            &[Value],
            &[Value],
            &[Value],
        ) -> Option<Value>,
    {
        if let (
            Value::Vec(v1),
            Value::Vec(v2),
            Value::Vec(v3),
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

    fn vec2_op<F>(lhs: &Self, rhs: &Self, f: F) -> Option<Value>
    where
        F: Fn(&Value, &Value) -> Option<Value>,
    {
        Self::vec2(lhs, rhs, |lhs, rhs| {
            lhs.iter()
                .zip(rhs)
                .map(|(l, r)| f(l, r))
                .collect::<Option<Vec<Value>>>()
                .map(Value::Vec)
        })
    }

    #[allow(unused)]
    fn int_range(min: i64, max: i64, num_samples: usize) -> Vec<Value> {
        (min..=max)
            .step_by(((max - min) as usize) / num_samples)
            .map(Value::Int)
            .collect::<Vec<_>>()
    }

    fn sample_int(
        rng: &mut Pcg32,
        min: i64,
        max: i64,
        num_samples: usize,
    ) -> Vec<Value> {
        (0..num_samples)
            .map(|_| Value::Int(rng.gen_range(min, max)))
            .collect::<Vec<_>>()
    }

    pub fn sample_vec(
        rng: &mut Pcg32,
        min: i64,
        max: i64,
        list_size: usize,
        num_samples: usize,
    ) -> Vec<Value> {
        (0..num_samples)
            .map(|_| {
                Value::Vec(Value::sample_int(
                    rng, min, max, list_size,
                ))
            })
            .collect::<Vec<_>>()
    }
}

impl SynthLanguage for VecLang {
    type Constant = Value;

    fn get_lifting_rules() -> Ruleset<Self> {
        Ruleset::new([
            "(VecAdd (Vec ?b) (Vec ?a)) ==> (Vec (+ ?b ?a))", 
            "(Vec (+ ?b ?a)) ==> (VecAdd (Vec ?b) (Vec ?a))", 
            "(VecDiv (Vec ?b) (Vec ?a)) ==> (Vec (/ ?b ?a))",
            "(Vec (/ ?b ?a)) ==> (VecDiv (Vec ?b) (Vec ?a))"]
        )
    }

    fn to_var(&self) -> Option<egg::Symbol> {
        if let VecLang::Symbol(sym) = self {
            Some(*sym)
        } else {
            None
        }
    }

    fn mk_var(sym: egg::Symbol) -> Self {
        VecLang::Symbol(sym)
    }

    fn is_constant(&self) -> bool {
        matches!(&self, VecLang::Const(_))
    }

    fn mk_constant(c: <Self as SynthLanguage>::Constant, _e: &mut EGraph<Self, SynthAnalysis>) -> Self {
        VecLang::Const(c)
    }

    fn eval<'a, F>(&'a self, cvec_len: usize, mut get: F) -> CVec<Self>
    where
        F: FnMut(&'a Id) -> &'a CVec<Self>,
    {
        match self {
            VecLang::Const(i) => vec![Some(i.clone()); cvec_len],
            VecLang::Add([l, r]) => map!(get, l, r => {
                Value::int2(l, r, |l, r| Value::Int(l + r))
            }),
            VecLang::Mul([l, r]) => map!(get, l, r => {
                Value::int2(l, r, |l, r| Value::Int(l * r))
            }),
            VecLang::Minus([l, r]) => map!(get, l, r => {
                Value::int2(l, r, |l, r| Value::Int(l - r))
            }),
            VecLang::Div([l, r]) => get(l)
                .iter()
                .zip(get(r).iter())
                .map(|tup| match tup {
                    (Some(Value::Int(a)), Some(Value::Int(b))) => {
                        util::integer_division(*a, *b).map(Value::Int)
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
            VecLang::Or([l, r]) => {
                map!(get, l, r => Value::bool2(l, r, |l, r| Value::Bool(l || r)))
            }
            VecLang::And([l, r]) => {
                map!(get, l, r => Value::bool2(l, r, |l, r| Value::Bool(l && r)))
            }
            VecLang::Ite([_b, _t, _f]) => todo!(),
            VecLang::Lt([l, r]) => {
                map!(get, l, r => Value::int2(l, r, |l, r| Value::Bool(l < r)))
            }
            VecLang::SqrtSgn([l, r]) => map!(
                get,
                l, r => if let (Value::Int(lv), Value::Int(rv)) = (l, r) {
                    util::sqrt_sgn(*lv, *rv).map(Value::Int)
                } else {
                    None
                }
            ),
            VecLang::Sgn([x]) => {
                map!(get, x => Value::int1(x, |x| Value::Int(util::sgn(x))))
            }
            VecLang::Sqrt([x]) => get(x)
                .iter()
                .map(|a| match a {
                    Some(Value::Int(a)) => {
                        if *a >= 0 {
                            Some(Value::Int(a.sqrt()))
                        } else {
                            None
                        }
                    }
                    _ => None,
                })
                .collect::<Vec<_>>(),
            VecLang::Neg([x]) => {
                map!(get, x => Value::int1(x, |x| Value::Int(-x)))
            }
            VecLang::List(l) => l
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
                .map(|acc| acc.map(Value::List))
                .collect::<Vec<_>>(),
            VecLang::Vec(l) => l
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
                .map(|acc| acc.map(Value::Vec))
                .collect::<Vec<_>>(),
            VecLang::LitVec(l) => l
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
                .map(|acc| acc.map(Value::Vec))
                .collect::<Vec<_>>(),
            #[rustfmt::skip]
            VecLang::Get([l, i]) => map!(get, l, i => {
                if let (Value::Vec(v), Value::Int(idx)) = (l, i) {
                    // get index and clone the inner Value if there is one
                    v.get(*idx as usize).cloned()
                } else {
                    None
                }
            }),
            #[rustfmt::skip]
            VecLang::Concat([l, r]) => map!(get, l, r => {
                Value::vec2(l, r, |l, r| {
                    Some(Value::List(
                        l.iter().chain(r).cloned().collect::<Vec<_>>(),
                    ))
                })
            }),
            #[rustfmt::skip]
            VecLang::VecAdd([l, r]) => map!(get, l, r => {
                Value::vec2_op(l, r, |l, r| {
                    Value::int2(l, r, |l, r| Value::Int(l + r))
                })
            }),
            #[rustfmt::skip]
            VecLang::VecMinus([l, r]) => map!(get, l, r => {
                Value::vec2_op(l, r, |l, r| {
                    Value::int2(l, r, |l, r| Value::Int(l - r))
                })
            }),
            #[rustfmt::skip]
            VecLang::VecMul([l, r]) => map!(get, l, r => {
                Value::vec2_op(l, r, |l, r| {
                    Value::int2(l, r, |l, r| Value::Int(l * r))
                })
            }),
            #[rustfmt::skip]
            VecLang::VecDiv([l, r]) => map!(get, l, r => {
                Value::vec2_op(l, r, |l, r| match (l, r) {
                    (Value::Int(a), Value::Int(b)) => {
                        util::integer_division(*a, *b).map(Value::Int)
                    }
                    _ => None,
                })
            }),
            #[rustfmt::skip]
            VecLang::VecMulSgn([l, r]) => map!(get, l, r => {
                Value::vec2_op(l, r, |l, r| {
                    Value::int2(l, r, |l, r| Value::Int(util::sgn(l) * r))
                })
            }),
            #[rustfmt::skip]
            VecLang::VecSqrtSgn([l, r]) => map!(get, l, r => {
                Value::vec2_op(l, r, |l, r| {
                    if let (Value::Int(lv), Value::Int(rv)) = (l, r) {
                        util::sqrt_sgn(*lv, *rv).map(Value::Int)
                    } else {
                        None
                    }
                })
            }),
            #[rustfmt::skip]
            VecLang::VecNeg([l]) => map!(get, l => {
                Value::vec1(l, |l| {
                    if l.iter().all(|x| matches!(x, Value::Int(_))) {
                        Some(Value::Vec(
                            l.iter()
                                .map(|tup| match tup {
                                    Value::Int(a) => Value::Int(-a),
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
            VecLang::VecSqrt([l]) => map!(get, l => {
                Value::vec1(l, |l| {
                    if l.iter().all(|x| {
                        if let Value::Int(i) = x {
                            *i >= 0
                        } else {
                            false
                        }
                    }) {
                        Some(Value::Vec(
                            l.iter()
                                .map(|tup| match tup {
                                    Value::Int(a) => Value::Int(a.sqrt()),
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
            VecLang::VecSgn([l]) => map!(get, l => {
                Value::vec1(l, |l| {
                    if l.iter().all(|x| matches!(x, Value::Int(_))) {
                        Some(Value::Vec(
                            l.iter()
                                .map(|tup| match tup {
                                    Value::Int(a) => Value::Int(util::sgn(*a)),
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
            VecLang::VecMAC([acc, v1, v2]) => map!(get, v1, v2, acc => {
                Value::vec3(v1, v2, acc, |v1, v2, acc| {
                    v1.iter()
                        .zip(v2.iter())
                        .zip(acc.iter())
                        .map(|tup| match tup {
                            ((Value::Int(v1), Value::Int(v2)), Value::Int(acc))
                => Some(Value::Int((v1 * v2) + acc)),
                            _ => None,
                        })
                        .collect::<Option<Vec<Value>>>()
                        .map(Value::Vec)
                })
            }),
            #[rustfmt::skip]
            VecLang::VecMULS([acc, v1, v2]) => map!(get, v1, v2, acc => {
                Value::vec3(v1, v2, acc, |v1, v2, acc| {
                    v1.iter()
                        .zip(v2.iter())
                        .zip(acc.iter())
                        .map(|tup| match tup {
                            ((Value::Int(v1), Value::Int(v2)), Value::Int(acc))
                => Some(Value::Int(acc - (v1 * v2))),
                            _ => None,
                        })
                        .collect::<Option<Vec<Value>>>()
                        .map(Value::Vec)
                })
            }),
            VecLang::Symbol(_) => vec![],
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
        //         "int" => Value::Int(c.value),
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
            egraph.add(VecLang::Const(Value::Int(v)));
        }

        use rand_pcg::Lcg64Xsh32;
        let mut rng = Lcg64Xsh32::new(0,0);

        // add variables
        // set the initial cvecs of variables. this represents all the possible
        // values that this variable can have
        for i in vars {
            let var = egg::Symbol::from(i);
            let id = egraph.add(VecLang::Symbol(var));

            // make the cvec use real data
            let mut cvec = vec![];

            let (n_ints, n_vecs) = util::split_into_halves(cvec_size);

            cvec.extend(
                Value::sample_int(&mut rng, -100, 100, n_ints)
                    .into_iter()
                    .map(Some),
            );

            cvec.extend(
                Value::sample_vec(
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
        use crate::smt::SmtEquals;
        // JB TODO: allow for fuzz mode as well
        // let x = if synth.lang_config.always_smt {
            if Self::smt_equals(lhs, rhs) {
                ValidationResult::Valid
            } else {
                ValidationResult::Invalid
            }
    }
}