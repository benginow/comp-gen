use comp_gen::{
    ruler,
    ruler::SynthLanguage,
};
use egg::*;
use log::{debug, warn};
use z3::ast::Ast;

use crate::{fuzz::FuzzEquals, lang, desugared_lang};

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

        let left =
            egg_to_z3(&ctx, &mut solver, &Self::instantiate(lhs), &sqrt_fun);
        let right =
            egg_to_z3(&ctx, &mut solver, &Self::instantiate(rhs), &sqrt_fun);

        // if we can translate egg to z3 for both lhs, and rhs, then
        // run the z3 solver. otherwise fallback to fuzz_equals
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
}


impl SmtEquals for desugared_lang::VecLangDesugared {
    fn smt_equals(
        // synth: &mut ruler::Synthesizer<Self, ruler::Init>,
        lhs: &egg::Pattern<Self>,
        rhs: &egg::Pattern<Self>,
    ) -> bool {
        // if the expressions dont have the same type, they can't be equal
        // abort now

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

        let left =
            egg_to_z3_desugared(&ctx, &mut solver, &Self::instantiate(lhs), &sqrt_fun);
        let right =
            egg_to_z3_desugared(&ctx, &mut solver, &Self::instantiate(rhs), &sqrt_fun);

        // if we can translate egg to z3 for both lhs, and rhs, then
        // run the z3 solver. otherwise fallback to fuzz_equals
        use std::iter::zip;
        let mut smt = true;
        for (l, r) in zip(left, right) {
            if let (Some(lexpr), Some(rexpr)) = (&l, &r) {

                // check to see if lexpr is NOT equal to rexpr.
                // if we can't find a counter example to this
                // then we know that they are equal.
                solver.assert(&lexpr._eq(rexpr).not());
    
                smt &= match solver.check() {
                    z3::SatResult::Unsat => {debug!("z3 check {} != {}", lexpr, rexpr);
                    debug!("z3 result: {}", true);
                    true
                },
                    z3::SatResult::Unknown | z3::SatResult::Sat => false,
                };

                if !smt {
                    println!("no");
                    return smt;
                }
                
                // smt = smt
            } else {
                println!("no");
                warn!("Couldn't translate {lhs} or {rhs} to smt");
                warn!("Quitting for now, returning false");
                return false;
                // Self::fuzz_equals(lhs, rhs, true)
            }
        }
        smt
    }
}

/// Translate an egg::RecExpr into an equivalent z3 expression.
/// This only works for operations on integers for now.
pub fn egg_to_z3<'a>(
    ctx: &'a z3::Context,
    _solver: &mut z3::Solver,
    expr: &egg::RecExpr<lang::VecLang>,
    sqrt_fun: &'a z3::FuncDecl,
) -> Option<z3::ast::Int<'a>> {
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
            lang::VecLang::VecAdd([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int + y_int);
            }
            lang::VecLang::VecMinus([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int - y_int);
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
            lang::VecLang::VecNeg([x]) => {
                let x_int = &buf[usize::from(*x)];
                buf.push(-x_int);
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
            | lang::VecLang::Concat(_) => return None,
        }
    }
    // return the last element
    buf.pop()
}

/// Translate an egg::RecExpr into an equivalent z3 expression.
/// This only works for operations on integers for now.
pub fn egg_to_z3_desugared<'a>(
    ctx: &'a z3::Context,
    _solver: &mut z3::Solver,
    expr: &egg::RecExpr<desugared_lang::VecLangDesugared>,
    _sqrt_fun: &'a z3::FuncDecl,
) -> Vec<Option<z3::ast::Int<'a>>> {
    use num::ToPrimitive;

    println!("solving: {:?}", expr.clone().pretty(4));
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
            desugared_lang::VecLangDesugared::Const(desugared_lang::Value::Int(i)) => {
                buf.push(z3::ast::Int::from_i64(ctx, *i as i64))
            }
            desugared_lang::VecLangDesugared::Symbol(v) => {
                buf.push(z3::ast::Int::new_const(ctx, v.to_string()))
            }
            desugared_lang::VecLangDesugared::Add([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int + y_int);
            }
            desugared_lang::VecLangDesugared::Mul([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int * y_int);
            }
            desugared_lang::VecLangDesugared::Minus([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                buf.push(x_int - y_int);
            }
            desugared_lang::VecLangDesugared::Div([x, y]) => {
                let x_int = &buf[usize::from(*x)];
                let y_int = &buf[usize::from(*y)];
                // let zero = z3::ast::Int::from_i64(ctx, 0);
                // solver.assert(&y_int._eq(&zero).not());
                buf.push(x_int / y_int);
            }
            // an attempt to support vector operators.
            // I think I should just be able to map them
            // on to their scalar counter parts.
            // lang::VecLang::Add([x, y]) => {
            //     let x_int = &buf[usize::from(*x)];
            //     let y_int = &buf[usize::from(*y)];
            //     buf.push(x_int + y_int);
            // }
            &desugared_lang::VecLangDesugared::Shfl([x, y]) => {
                if buf.len() <= usize::from(x) + 4 {
                    return vec![None];
                }
                if buf.len() <= usize::from(y) + 4 {
                    return vec![None];
                }
                let shuffle = vec![buf[usize::from(x)].clone(),
                                            buf[usize::from(x)+1].clone(),
                                            buf[usize::from(x)+2].clone(),
                                            buf[usize::from(x)+3].clone()];
                let indices = vec![buf[usize::from(y)].clone(),
                                            buf[usize::from(y)+1].clone(),
                                            buf[usize::from(y)+2].clone(),
                                            buf[usize::from(y)+3].clone()];
                for idx in indices.clone() {
                    if let Some(x) = idx.as_u64() {
                        if x >= 4 {
                            println!("indexing outside of buffer in shfl");
                            return vec![None];
                        }
                    }
                    else {
                        println!("uh oh");
                        return vec![None];
                    }
                }
                buf.push(shuffle[indices[0].as_u64().unwrap().to_usize().unwrap()].clone());
                buf.push(shuffle[indices[1].as_u64().unwrap().to_usize().unwrap()].clone());
                buf.push(shuffle[indices[2].as_u64().unwrap().to_usize().unwrap()].clone());
                buf.push(shuffle[indices[3].as_u64().unwrap().to_usize().unwrap()].clone());
            }
            desugared_lang::VecLangDesugared::VecAdd([x, y]) => {
                // println!("length of buf is: {}", buf.len());
                // println!("usize is: {}", usize::from(*x));
                // println!("usize is: {}", usize::from(*y));
                // println!("at the beginning of adding vector: {buf:?}");

                if buf.len() <= usize::from(*x) + 4 {
                    return vec![None];
                }
                if buf.len() <= usize::from(*y) + 4 {
                    return vec![None];
                }

                // a part of me believes that this may not work given that 
                // idk how id is set? may not be the starting point necessarily.. hm
                let x_int0 = buf[usize::from(*x)].clone();
                let x_int1 = buf[usize::from(*x)+1].clone();
                let x_int2 = buf[usize::from(*x)+2].clone();
                let x_int3 = buf[usize::from(*x)+3].clone();
                let y_int0 = buf[usize::from(*y)].clone();
                let y_int1 = buf[usize::from(*y)+1].clone();
                let y_int2 = buf[usize::from(*y)+2].clone();
                let y_int3 = buf[usize::from(*y)+3].clone();
                buf.push(x_int0 + y_int0);
                buf.push(x_int1 + y_int1);
                buf.push(x_int2 + y_int2);
                buf.push(x_int3 + y_int3);
                println!("at the end of adding vector: {buf:?}");

            }
            desugared_lang::VecLangDesugared::VecMinus([x, y]) => {
                // println!("length of buf is: {}", buf.len());
                // println!("usize is: {}", usize::from(*x));
                // println!("usize is: {}", usize::from(*y));
                // println!("at the beginning of adding vector: {buf:?}");

                if buf.len() <= usize::from(*x) + 4 {
                    return vec![None];
                }
                if buf.len() <= usize::from(*y) + 4 {
                    return vec![None];
                }

                let x_int0 = buf[usize::from(*x)].clone();
                let x_int1 = buf[usize::from(*x)+1].clone();
                let x_int2 = buf[usize::from(*x)+2].clone();
                let x_int3 = buf[usize::from(*x)+3].clone();
                let y_int0 = buf[usize::from(*y)].clone();
                let y_int1 = buf[usize::from(*y)+1].clone();
                let y_int2 = buf[usize::from(*y)+2].clone();
                let y_int3 = buf[usize::from(*y)+3].clone();
                buf.push(x_int0 - y_int0);
                buf.push(x_int1 - y_int1);
                buf.push(x_int2 - y_int2);
                buf.push(x_int3 - y_int3);
                println!("at the end of adding vector: {buf:?}");

            }
            desugared_lang::VecLangDesugared::VecMul([x, y]) => {
                // println!("length of buf is: {}", buf.len());
                // println!("usize is: {}", usize::from(*x));
                // println!("usize is: {}", usize::from(*y));
                // println!("at the beginning of adding vector: {buf:?}");

                if buf.len() <= usize::from(*x) + 4 {
                    return vec![None];
                }
                if buf.len() <= usize::from(*y) + 4 {
                    return vec![None];
                }

                let x_int0 = buf[usize::from(*x)].clone();
                let x_int1 = buf[usize::from(*x)+1].clone();
                let x_int2 = buf[usize::from(*x)+2].clone();
                let x_int3 = buf[usize::from(*x)+3].clone();
                let y_int0 = buf[usize::from(*y)].clone();
                let y_int1 = buf[usize::from(*y)+1].clone();
                let y_int2 = buf[usize::from(*y)+2].clone();
                let y_int3 = buf[usize::from(*y)+3].clone();
                buf.push(x_int0 * y_int0);
                buf.push(x_int1 * y_int1);
                buf.push(x_int2 * y_int2);
                buf.push(x_int3 * y_int3);
                println!("at the end of adding vector: {buf:?}");

            }
            desugared_lang::VecLangDesugared::VecDiv([x, y]) => {
                // println!("length of buf is: {}", buf.len());
                // println!("usize is: {}", usize::from(*x));
                // println!("usize is: {}", usize::from(*y));
                // println!("at the beginning of adding vector: {buf:?}");

                if buf.len() < usize::from(*x) + 4 {
                    return vec![None];
                }
                if buf.len() < usize::from(*y) + 4 {
                    return vec![None];
                }

                let x_int0 = buf[usize::from(*x)].clone();
                let x_int1 = buf[usize::from(*x)+1].clone();
                let x_int2 = buf[usize::from(*x)+2].clone();
                let x_int3 = buf[usize::from(*x)+3].clone();
                let y_int0 = buf[usize::from(*y)].clone();
                let y_int1 = buf[usize::from(*y)+1].clone();
                let y_int2 = buf[usize::from(*y)+2].clone();
                let y_int3 = buf[usize::from(*y)+3].clone();
                buf.push(x_int0 / y_int0);
                buf.push(x_int1 / y_int1);
                buf.push(x_int2 / y_int2);
                buf.push(x_int3 / y_int3);
                println!("at the end of adding vector: {buf:?}");

            }
            // JB: changed vecwidth here
            desugared_lang::VecLangDesugared::Vec(inner) if inner.len() == 4 => {
                // println!("adding vector, inner is {inner:?}");
                println!("at the beginning of adding vector: {buf:?}");
                let x = inner[0];
                let y = inner[1];
                let z = inner[2];
                let w = inner[3];
                let x_int = buf[usize::from(x)].clone();
                let y_int = buf[usize::from(y)].clone();
                let z_int = buf[usize::from(z)].clone();
                let w_int = buf[usize::from(w)].clone();
                buf.push(x_int);
                buf.push(y_int);
                buf.push(z_int);
                buf.push(w_int);
                println!("at the end of adding vector: {buf:?}");

            }
            desugared_lang::VecLangDesugared::LitVec(inner) if inner.len() == 4 => {
                let x = inner[0];
                let y = inner[1];
                let z = inner[2];
                let w = inner[3];
                let x_int = buf[usize::from(x)].clone();
                let y_int = buf[usize::from(y)].clone();
                let z_int = buf[usize::from(z)].clone();
                let w_int = buf[usize::from(w)].clone();
                buf.push(x_int);
                buf.push(y_int);
                buf.push(z_int);
                buf.push(w_int);
            }
            &desugared_lang::VecLangDesugared::VecSum([x]) => {
                if usize::from(x) + 4 > buf.len() {
                    println!("quitting sum");
                    return vec![None];
                }
                let x_int0 = buf[usize::from(x)].clone();
                let x_int1 = buf[usize::from(x)+1].clone();
                let x_int2 = buf[usize::from(x)+2].clone();
                let x_int3 = buf[usize::from(x)+3].clone();
                buf.push(x_int0 + x_int1 + x_int2 + x_int3);
                buf.push(z3::ast::Int::from_i64(ctx, 0));
                buf.push(z3::ast::Int::from_i64(ctx, 0));
                buf.push(z3::ast::Int::from_i64(ctx, 0));
            }
            // unsupported operations
            // return early
            desugared_lang::VecLangDesugared::Const(_)
            | desugared_lang::VecLangDesugared::List(_)
            | desugared_lang::VecLangDesugared::Get(_)
            | desugared_lang::VecLangDesugared::Vec(_)
            | desugared_lang::VecLangDesugared::LitVec(_)
            | desugared_lang::VecLangDesugared::Concat(_) => return vec![None],
        }
    }
    // return the last element
    buf.into_iter().map(|x| Some(x)).collect()
}