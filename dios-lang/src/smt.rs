use comp_gen::{
    ruler,
    ruler::SynthLanguage,
};
use egg::*;
use log::{debug, warn};
use z3::ast::Ast;

use crate::{fuzz::FuzzEquals, lang};

pub trait TypeEquals: ruler::SynthLanguage {
    type T: Eq;
    /// Return the type of `expr` in the domain `Self::T`.
    /// Returns None if the expr is ill-formed.
    fn get_type(expr: &egg::Pattern<Self>) -> Option<Self::T>;

    /// Check if `lhs` and `rhs` have the same type. Requires that both
    /// sides by well-formed.
    fn type_equals(lhs: &egg::Pattern<Self>, rhs: &egg::Pattern<Self>) -> bool {
        if let (Some(lhs_type), Some(rhs_type)) =
            (Self::get_type(lhs), Self::get_type(rhs))
        {
            lhs_type == rhs_type
        } else {
            false
        }
    }
}

#[derive(Eq, Clone, Copy, Debug)]
pub enum VecLangType {
    Vector,
    Scalar,
    Variable,
}

impl PartialEq for VecLangType {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            // if either side is a variable, then true
            // JB: this is not true. this implies that "(VecNeg (VecNeg ?a))" = "?a" = "(neg (neg ?a))"
            // however, it would be nice to have rules in the form of "?a" = "(neg (neg ?a))"
            (VecLangType::Variable, VecLangType::Variable) => true,
            (VecLangType::Variable, VecLangType::Scalar) | (VecLangType::Scalar, VecLangType::Variable) => true,

            // if they are the same, true
            (VecLangType::Vector, VecLangType::Vector)
            | (VecLangType::Scalar, VecLangType::Scalar) => true,

            // otherwise false
            _ => false,
        }
    }
}

impl VecLangType {
    fn join(
        &self,
        b: &VecLangType,
        default: VecLangType,
    ) -> Option<VecLangType> {
        match (self, b) {
            // same type goes to same type -- could be cute and do op overloading but didn't
            // == didn't work for some reason originally
            (VecLangType::Variable, VecLangType::Variable) => Some(default),
            (VecLangType::Scalar, VecLangType::Scalar) => Some(VecLangType::Scalar),
            (VecLangType::Vector, VecLangType::Vector) => Some(VecLangType::Vector),

            // if one side is a variable, copy the type from the defined value
            (VecLangType::Vector, _) | (_, VecLangType::Vector) => {
                Some(VecLangType::Vector)
            }
            (VecLangType::Scalar, _) | (_, VecLangType::Scalar) => {
                Some(VecLangType::Scalar)
            }
        }
    }
}

impl TypeEquals for lang::VecLang {
    type T = VecLangType;

    fn get_type(expr: &egg::Pattern<Self>) -> Option<Self::T> {
        // This is tracking the type of the expression so far
        let mut types: Vec<Option<VecLangType>> = vec![];

        for node in Self::instantiate(expr).as_ref().iter() {
            match node {
                // unops
                lang::VecLang::Sgn([x])
                | lang::VecLang::Sqrt([x])
                | lang::VecLang::Neg([x]) => {
                    types.push(types[usize::from(*x)].and_then(|t| match t {
                        VecLangType::Vector => None,
                        VecLangType::Scalar => Some(t),
                        VecLangType::Variable => Some(VecLangType::Scalar),
                    }))
                }
                
                lang::VecLang::VecSqrt([x])
                | lang::VecLang::VecSgn([x]) => {
                    types.push(types[usize::from(*x)].and_then(|t| match t {
                        VecLangType::Vector => Some(t),
                        VecLangType::Scalar => None,
                        VecLangType::Variable => Some(VecLangType::Vector),
                    }))
                }

                // binops
                lang::VecLang::Add([x, y])
                | lang::VecLang::Mul([x, y])
                | lang::VecLang::Minus([x, y])
                | lang::VecLang::Div([x, y])
                | lang::VecLang::Or([x, y])
                | lang::VecLang::And([x, y])
                | lang::VecLang::SqrtSgn([x, y])
                | lang::VecLang::Lt([x, y]) => {
                    let type_x = &types[usize::from(*x)];
                    let type_y = &types[usize::from(*y)];
                    let t = type_x.and_then(|xt| {
                        type_y.and_then(|yt| xt.join(&yt, VecLangType::Scalar))
                    });
                    types.push(t);
                }

                lang::VecLang::Concat([x, y])
                | lang::VecLang::VecMul([x, y])
                | lang::VecLang::VecDiv([x, y])
                | lang::VecLang::VecSqrtSgn([x, y])
                | lang::VecLang::VecMulSgn([x, y]) => {
                    let type_x = &types[usize::from(*x)];
                    let type_y = &types[usize::from(*y)];
                    let t = type_x.and_then(|xt| {
                        type_y.and_then(|yt| xt.join(&yt, VecLangType::Vector))
                    });
                    types.push(t);
                }

                lang::VecLang::Get([_x, _y]) => todo!(),
                lang::VecLang::Ite([_x, _y, _z]) => todo!(),

                // triops
                lang::VecLang::VecMAC([x, y, z])
                | lang::VecLang::VecMULS([x,y,z]) => {
                    let type_x = &types[usize::from(*x)];
                    let type_y = &types[usize::from(*y)];
                    let type_z = &types[usize::from(*z)];
                    let t = type_x.and_then(|xt| {
                        type_y.and_then(|yt| {
                            xt.join(&yt, VecLangType::Vector).and_then(|xyt| {
                                type_z.and_then(|zt| {
                                    xyt.join(&zt, VecLangType::Vector)
                                })
                            })
                        })
                    });

                    types.push(t)
                }

                // converts types to scalar, triop
                lang::VecLang::VecNeg([x,y,z]) | lang::VecLang::VecSum([x,y,z]) => {
                    let type_x = &types[usize::from(*x)];
                    let type_y = &types[usize::from(*y)];
                    let type_z = &types[usize::from(*z)];
                    let t = type_x.and_then(|xt| {
                        type_y.and_then(|yt| {
                            type_z.and_then(|zt| {
                                match (xt, yt, zt) {
                                    (VecLangType::Vector, _, _) | (_, VecLangType::Vector, _) | (_, _, VecLangType::Vector) => None,
                                    (VecLangType::Scalar, VecLangType::Scalar, VecLangType::Scalar) => Some(VecLangType::Vector),
                                    _ => Some(VecLangType::Variable),
                                }
                            })
                        })
                    });
                    types.push(t)
                    // JB: this is what it was before adding width
                    //     VecLangType::Vector => Some(VecLangType::Scalar),
                    //     VecLangType::Scalar => None,
                    //     VecLangType::Variable => Some(VecLangType::Scalar),
                }

                lang::VecLang::VecAdd([x, y, z,a,b,c])
                | lang::VecLang::VecMinus([x, y,z,a,b,c]) => {
                    let type_x = &types[usize::from(*x)];
                    let type_y = &types[usize::from(*y)];
                    let type_z = &types[usize::from(*z)];
                    let vec1 = type_x.and_then(|xt| {
                        type_y.and_then(|yt| {
                            type_z.and_then(|zt| {
                                match (xt, yt, zt) {
                                    (VecLangType::Vector, _, _) | (_, VecLangType::Vector, _) | (_, _, VecLangType::Vector) => None,
                                    (VecLangType::Scalar, VecLangType::Scalar, VecLangType::Scalar) => Some(VecLangType::Vector),
                                    _ => Some(VecLangType::Vector),
                                }
                            })
                        })
                    });

                    let type_a = &types[usize::from(*a)];
                    let type_b = &types[usize::from(*b)];
                    let type_c= &types[usize::from(*c)];
                    let vec2 = type_a.and_then(|at| {
                        type_b.and_then(|bt| {
                            type_c.and_then(|ct| {
                                match (at, bt, ct) {
                                    (VecLangType::Vector, _, _) | (_, VecLangType::Vector, _) | (_, _, VecLangType::Vector) => None,
                                    (VecLangType::Scalar, VecLangType::Scalar, VecLangType::Scalar) => Some(VecLangType::Vector),
                                    _ => Some(VecLangType::Vector),
                                }
                            })
                        })
                    });
                }



                // constants
                lang::VecLang::List(_) | lang::VecLang::Vec(_) | lang::VecLang::LitVec(_) => {
                    types.push(Some(VecLangType::Vector))
                }
                lang::VecLang::Const(_) => {
                    types.push(Some(VecLangType::Scalar))
                }
                lang::VecLang::Symbol(_) => {
                    types.push(Some(VecLangType::Variable))
                }
            };
        }
        if let Some(x) = types.pop() {
            x
        } else {
            None
        }
    }
}

pub trait SmtEquals: ruler::SynthLanguage {
    fn smt_equals(
        // synth: &mut ruler::Synthesizer<Self, ruler::Init>,
        lhs: &egg::Pattern<Self>,
        rhs: &egg::Pattern<Self>,
    ) -> bool;
}

impl SmtEquals for lang::VecLang {
    fn smt_equals(
        // synth: &mut ruler::Synthesizer<Self, ruler::Init>,
        lhs: &egg::Pattern<Self>,
        rhs: &egg::Pattern<Self>,
    ) -> bool {
        // if the expressions dont have the same type, they can't be equal
        // abort now
        let type_check = Self::type_equals(lhs, rhs);
        // debug!("type check: {lhs} = {rhs}: {type_check}");
        if !type_check {
            return false;
        }

        let mut cfg = z3::Config::new();
        cfg.set_timeout_msec(10000);
        let ctx = z3::Context::new(&cfg);
        let mut solver = z3::Solver::new(&ctx);

        let sqrt_fun: z3::FuncDecl = z3::FuncDecl::new(
            &ctx,
            "sqrt",
            &[&z3::Sort::int(&ctx)],
            &z3::Sort::int(&ctx),
        );

        let lhs_type = Self::get_type(lhs);
        let rhs_type = Self::get_type(rhs);
        let left =
            egg_to_z3(&ctx, &mut solver, &Self::instantiate(lhs), lhs_type.unwrap(), &sqrt_fun);
        let right =
            egg_to_z3(&ctx, &mut solver, &Self::instantiate(rhs), rhs_type.unwrap(), &sqrt_fun);

        // if we can translate egg to z3 for both lhs, and rhs, then
        // run the z3 solver. otherwise fallback to fuzz_equals

        // JB: rewrite this to be cleaner later
        match (left, right) {
            (Z3CheckType::VecEq(x), Z3CheckType::VecEq(y)) => {
                let mut final_smt = true;
                for i in 0..3 {
                    if let (Some(lexpr), Some(rexpr)) = (&(x[i]), &(y[i])) {
                        // check to see if lexpr is NOT equal to rexpr.
                        // if we can't find a counter example to this
                        // then we know that they are equal.
                        solver.assert(&lexpr._eq(rexpr).not());
            
                        let smt = match solver.check() {
                            z3::SatResult::Unsat => {debug!("z3 check {} != {}", lexpr, rexpr);
                            debug!("z3 result: {}", true);true},
                            z3::SatResult::Unknown | z3::SatResult::Sat => false,
                        };
                        final_smt &= smt;
                    } else {
                        warn!("Couldn't translate {lhs} or {rhs} to smt");
                        final_smt &= Self::fuzz_equals(lhs, rhs, true);
                    }
                }
                final_smt
            }
            (Z3CheckType::ScalarEq(left), Z3CheckType::ScalarEq(right))  => {
                if let (Some(lexpr), Some(rexpr)) = (&left, &right) {
                    // check to see if lexpr is NOT equal to rexpr.
                    // if we can't find a counter example to this
                    // then we know that they are equal.
                    solver.assert(&lexpr._eq(rexpr).not());
        
                    let smt = match solver.check() {
                        z3::SatResult::Unsat => {debug!("z3 check {} != {}", lexpr, rexpr);
                        debug!("z3 result: {}", true);true},
                        z3::SatResult::Unknown | z3::SatResult::Sat => false,
                    };
                    
                    smt
                } else {
                    warn!("Couldn't translate {lhs} or {rhs} to smt");
                    Self::fuzz_equals(lhs, rhs, true)
                }
            }
            (_, _) => {debug!("type check failed"); return false;}
        }
    }
}

pub enum Z3CheckType<'a> {
    ScalarEq(Option<z3::ast::Int<'a>>),
    VecEq([Option<z3::ast::Int<'a>>; 3])   
}

/// Translate an egg::RecExpr into an equivalent z3 expression.
/// This only works for operations on integers for now.
pub fn egg_to_z3<'a>(
    ctx: &'a z3::Context,
    _solver: &mut z3::Solver,
    expr: &egg::RecExpr<lang::VecLang>,
    expr_type: VecLangType,
    sqrt_fun: &'a z3::FuncDecl,
) -> Z3CheckType<'a> {
    // This translate works by walking through the RecExpr vector
    // in order, and translating just that node. We push this
    // translation into a buffer as we go. Any time we need to
    // reference a child, we can look up the corresponding index
    // in the buffer. This works because we have the guarantee that
    // some element i in RecExpr only ever refers to elements j < i.
    // By the time we need them, we will have already translated them.

    let mut buf: Vec<z3::ast::Int> = vec![];

    for node in expr.as_ref().iter() {
        match node {
            lang::VecLang::Const(lang::Value::Int(i)) => {
                buf.push(z3::ast::Int::from_i64(ctx, *i as i64))
            }
            lang::VecLang::Symbol(v) => {
                buf.push(z3::ast::Int::new_const(ctx, v.to_string()))
            }
            lang::VecLang::Add([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int + y_int);
            }
            lang::VecLang::Mul([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int * y_int);
            }
            lang::VecLang::Minus([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int - y_int);
            }
            lang::VecLang::Div([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                // let zero = z3::ast::Int::from_i64(ctx, 0);
                // solver.assert(&y_int._eq(&zero).not());
                buf.push(x_int / y_int);
            }
            lang::VecLang::SqrtSgn([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];

                let sqrt_int = sqrt_fun
                    .apply(&[x_int])
                    .as_int()
                    .expect("z3 Sqrt didn't return an int.");

                let zero = z3::ast::Int::from_i64(ctx, 0);
                let one = z3::ast::Int::from_i64(ctx, 1);
                let m_one = z3::ast::Int::from_i64(ctx, -1);

                let inner: z3::ast::Int = (y_int.gt(&zero)).ite(&m_one, &one);
                let neg_sgn = (x_int._eq(&zero)).ite(&zero, &inner);

                buf.push(sqrt_int * neg_sgn)
            }
            lang::VecLang::Neg([x]) => {
                let x_int = &buf[usize::from(*x)];
                buf.push(-x_int);
            }
            lang::VecLang::Sgn([x]) => {
                let x_int = &buf[usize::from(*x)];
                let zero = z3::ast::Int::from_i64(ctx, 0);
                let one = z3::ast::Int::from_i64(ctx, 1);
                let m_one = z3::ast::Int::from_i64(ctx, -1);

                let inner: z3::ast::Int = (x_int.gt(&zero)).ite(&one, &m_one);
                let sgn = (x_int._eq(&zero)).ite(&zero, &inner);

                buf.push(sgn);
            }
            lang::VecLang::Sqrt([x]) => {
                let x_int = &buf[usize::from(*x)];
                buf.push(
                    sqrt_fun
                        .apply(&[x_int])
                        .as_int()
                        .expect("z3 Sqrt didn't return an int."),
                );
            }

            // an attempt to support vector operators.
            // I think I should just be able to map them
            // on to their scalar counter parts.
            // lang::VecLang::Add([x, y]) => {
            //     let x_int = &buf[usize::from(*x)];
            //     let y_int = &buf[usize::from(*y)];
            //     buf.push(x_int + y_int);
            // }
            lang::VecLang::VecAdd([x, y,z,a,b,c]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                let z_int = &buf[usize::from(*z)];
                let a_int = &buf[usize::from(*a)];
                let b_int = &buf[usize::from(*b)];
                let c_int = &buf[usize::from(*c)];
                buf.push(x_int+a_int);
                buf.push(y_int+b_int);
                buf.push(z_int+c_int);
            }
            lang::VecLang::VecMinus([x,y,z,a,b,c]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                let z_int = &buf[usize::from(*z)];
                let a_int = &buf[usize::from(*a)];
                let b_int = &buf[usize::from(*b)];
                let c_int = &buf[usize::from(*c)];
                buf.push(x_int-a_int);
                buf.push(y_int-b_int);
                buf.push(z_int-c_int);
            }
            lang::VecLang::VecMul([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int * y_int);
            }
            lang::VecLang::VecDiv([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int / y_int);
            }
            lang::VecLang::VecMulSgn([x, y]) => {
                // grab smt versions of inputs
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];

                // make a zero constant
                let zero = z3::ast::Int::from_i64(ctx, 0);

                // if x > 0 { y } else { -y }
                let inner: z3::ast::Int = (x_int.gt(&zero)).ite(y_int, &-y_int);
                // if x == 0 { 0 } else { inner }
                let sgn = (x_int._eq(&zero)).ite(&zero, &inner);

                buf.push(sgn);
            }
            lang::VecLang::VecNeg([x,y,z]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                let z_int = &buf[usize::from(*z)];
                buf.push(-x_int);
                buf.push(-y_int);
                buf.push(-z_int);
            }
            lang::VecLang::VecSum([x, y, z]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                let z_int = &buf[usize::from(*z)];
                buf.push(x_int + y_int + z_int);
            }
            lang::VecLang::VecMAC([acc, x, y]) => {
                let acc_int = &buf[usize::from(*acc)];
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push((x_int * y_int) + acc_int);
            }
            lang::VecLang::VecMULS([acc, x, y]) => {
                let acc_int = &buf[usize::from(*acc)];
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(acc_int - (x_int * y_int));
            }
            lang::VecLang::VecSgn([x]) => {
                let x_int = &buf[usize::from(*x)];
                let zero = z3::ast::Int::from_i64(ctx, 0);
                let one = z3::ast::Int::from_i64(ctx, 1);
                let m_one = z3::ast::Int::from_i64(ctx, -1);

                let inner: z3::ast::Int = (x_int.gt(&zero)).ite(&m_one, &one);
                let sgn = (x_int._eq(&zero)).ite(&zero, &inner);

                buf.push(sgn);
            }
            lang::VecLang::VecSqrt([x]) => {
                let x_int = &buf[usize::from(*x)];
                buf.push(
                    sqrt_fun
                        .apply(&[x_int])
                        .as_int()
                        .expect("z3 Sqrt didn't return an int."),
                );
            }
            lang::VecLang::VecSqrtSgn([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];

                let sqrt_int = sqrt_fun
                    .apply(&[x_int])
                    .as_int()
                    .expect("z3 Sqrt didn't return an int.");

                let zero = z3::ast::Int::from_i64(ctx, 0);
                let one = z3::ast::Int::from_i64(ctx, 1);
                let m_one = z3::ast::Int::from_i64(ctx, -1);

                let inner: z3::ast::Int = (y_int.gt(&zero)).ite(&m_one, &one);
                let neg_sgn = (x_int._eq(&zero)).ite(&zero, &inner);

                buf.push(sqrt_int * neg_sgn)
            }
            // JB
            lang::VecLang::Vec(inner) if inner.len() == 1 => {
                let x = inner[0];
                let x_int = &buf[usize::from(x)];
                buf.push(x_int.clone());
            }
            lang::VecLang::LitVec(inner) if inner.len() == 1 => {
                let x = inner[0];
                let x_int = &buf[usize::from(x)];
                buf.push(x_int.clone());
            }
            // unsupported operations
            // return early
            lang::VecLang::Const(_)
            | lang::VecLang::Or(_)
            | lang::VecLang::And(_)
            | lang::VecLang::Ite(_)
            | lang::VecLang::Lt(_)
            | lang::VecLang::List(_)
            | lang::VecLang::Get(_)
            | lang::VecLang::Vec(_)
            | lang::VecLang::LitVec(_)
            | lang::VecLang::Concat(_) => return Z3CheckType::ScalarEq(None),
        }
    }
    // return the last element
    if expr_type == VecLangType::Vector {
        return Z3CheckType::VecEq([buf.pop(), buf.pop(), buf.pop()])
    } else {
        return Z3CheckType::ScalarEq(buf.pop())
    }
}

mod test 
{
    use std::str::FromStr;
    use crate::lang;

    #[test]
    fn type_equals_works(){
        use crate::smt::TypeEquals;
        use crate::lang::VecLang;
        use egg::Pattern;
        
        let lhs = &Pattern::from_str("(/ ?b (sqrt ?a))").unwrap();
        let rhs = &Pattern::from_str("(VecDiv ?b (VecSqrt ?a))").unwrap();
        let lhs_type = lang::VecLang::get_type(lhs);
        let rhs_type = lang::VecLang::get_type(rhs);
        assert!(lhs_type != rhs_type);

        // variable
        let lhs = &Pattern::from_str("?a").unwrap();
        //vector
        let rhs = &Pattern::from_str("(VecNeg (VecNeg ?a))").unwrap();
        let lhs_type = lang::VecLang::get_type(lhs).unwrap();
        let rhs_type = lang::VecLang::get_type(rhs).unwrap();
        assert!(lhs_type != rhs_type);
    }
}
