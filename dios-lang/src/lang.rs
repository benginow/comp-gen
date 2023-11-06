use egg::{self, define_language, Id, Language, FromOp};
use itertools::Itertools;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};
use std::str::FromStr;

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
    // vec of integers in order to simulate 3 vector lanes
    Vec3(i64, i64, i64)
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
            Value::Vec3(x,y,z) => write!(f, "{:?} {:?} {:?}", x, y, z)
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
        // vector is now represented by 3 exprs
        "VecAdd" = VecAdd([Id; 6]),
        "VecMinus" = VecMinus([Id; 6]),
        "VecMul" = VecMul([Id; 2]),
        "VecDiv" = VecDiv([Id; 2]),
        "VecMulSgn" = VecMulSgn([Id; 2]),
        "VecSqrtSgn" = VecSqrtSgn([Id; 2]),

        // Vector operations that take 1 vector of inputs
        "VecNeg" = VecNeg([Id; 3]),
        "VecSqrt" = VecSqrt([Id; 1]),
        "VecSgn" = VecSgn([Id; 1]),

        // JB: instead (was [Id;1]), now vecsum will have THREE children that are exprs.
        // all elements of a vecsum must be a mix of either vars or lits, but NOT vectors. 
        // add this to the type check.
        "VecSum" = VecSum([Id;3]),

        // "VecRAdd" = VecRAdd([Id; 1]),

        // MAC takes 3 lists: acc, v1, v2
        "VecMAC" = VecMAC([Id; 3]),
        "VecMULS" = VecMULS([Id; 3]),

        // Comment
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

    VecAdd(Box<VecAst>, Box<VecAst>, Box<VecAst>, Box<VecAst>, Box<VecAst>, Box<VecAst>),
    VecMul(Box<VecAst>, Box<VecAst>),
    VecMinus(Box<VecAst>, Box<VecAst>, Box<VecAst>, Box<VecAst>, Box<VecAst>, Box<VecAst>),
    VecDiv(Box<VecAst>, Box<VecAst>),
    VecMulSgn(Box<VecAst>, Box<VecAst>),
    VecSqrtSgn(Box<VecAst>, Box<VecAst>),

    VecNeg(Box<VecAst>, Box<VecAst>, Box<VecAst>),
    VecSqrt(Box<VecAst>),
    VecSgn(Box<VecAst>),

    VecSum(Box<VecAst>, Box<VecAst>, Box<VecAst>),

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
            VecAst::VecAdd(a, b, c, x, y, z) => {
                let a_id: Id = a.to_recexpr(expr);
                let b_id = b.to_recexpr(expr);
                let c_id = c.to_recexpr(expr);
                let x_id = x.to_recexpr(expr);
                let y_id = y.to_recexpr(expr);
                let z_id = z.to_recexpr(expr);
                expr.add(VecLang::VecAdd([a_id, b_id, c_id, x_id, y_id, z_id]))
            }
            VecAst::VecMul(left, right) => {
                let left_id = left.to_recexpr(expr);
                let right_id = right.to_recexpr(expr);
                expr.add(VecLang::VecMul([left_id, right_id]))
            }
            VecAst::VecMinus(a, b, c, x, y, z) => {
                let a_id: Id = a.to_recexpr(expr);
                let b_id = b.to_recexpr(expr);
                let c_id = c.to_recexpr(expr);
                let x_id = x.to_recexpr(expr);
                let y_id = y.to_recexpr(expr);
                let z_id = z.to_recexpr(expr);
                expr.add(VecLang::VecMinus([a_id, b_id, c_id, x_id, y_id, z_id]))
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
            VecAst::VecNeg(a,b,c) => {
                let a_id = a.to_recexpr(expr);
                let b_id = b.to_recexpr(expr);
                let c_id = c.to_recexpr(expr);
                expr.add(VecLang::VecNeg([a_id, b_id, c_id]))
            }
            VecAst::VecSqrt(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::VecSqrt([id]))
            }
            VecAst::VecSgn(inner) => {
                let id = inner.to_recexpr(expr);
                expr.add(VecLang::VecSgn([id]))
            }
            VecAst::VecSum(a,b,c) => {
                let a_id = a.to_recexpr(expr);
                let b_id = b.to_recexpr(expr);
                let c_id = c.to_recexpr(expr);
                expr.add(VecLang::VecSum([a_id, b_id, c_id]))
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
            VecLang::VecAdd([a,b,c,x,y,z]) => VecAst::VecAdd(
                Box::new(subtree(&expr, *a).into()),
                Box::new(subtree(&expr, *b).into()),
                Box::new(subtree(&expr, *c).into()),
                Box::new(subtree(&expr, *x).into()),
                Box::new(subtree(&expr, *y).into()),
                Box::new(subtree(&expr, *z).into()),
            ),
            VecLang::VecMinus([a,b,c,x,y,z]) => VecAst::VecMinus(
                Box::new(subtree(&expr, *a).into()),
                Box::new(subtree(&expr, *b).into()),
                Box::new(subtree(&expr, *c).into()),
                Box::new(subtree(&expr, *x).into()),
                Box::new(subtree(&expr, *y).into()),
                Box::new(subtree(&expr, *z).into()),
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
            VecLang::VecNeg([a,b,c]) => {
                VecAst::VecNeg(Box::new(subtree(&expr, *a).into()),
                Box::new(subtree(&expr, *b).into()),
                Box::new(subtree(&expr, *c).into()))
            }
            VecLang::VecSqrt([inner]) => {
                VecAst::VecSqrt(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::VecSgn([inner]) => {
                VecAst::VecSgn(Box::new(subtree(&expr, *inner).into()))
            }
            VecLang::VecSum([a,b,c]) => VecAst::VecSum(
                Box::new(subtree(&expr, *a).into()),
                Box::new(subtree(&expr, *b).into()),
                Box::new(subtree(&expr, *c).into()),
            ),
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
