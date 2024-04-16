use comp_gen::ruler::{
    enumo::*, recipe_utils::*, Limits, logger::*
};
use log::*;
use crate::desugared_lang;
use num::{integer::Roots, ToPrimitive};


pub(crate) fn sgn(x: i64) -> i64 {
    match x.cmp(&0) {
        std::cmp::Ordering::Less => -1,
        std::cmp::Ordering::Equal => 0,
        std::cmp::Ordering::Greater => 1,
    }
}

pub(crate) fn sqrt_sgn(x: i64, y: i64) -> Option<i64> {
    if x >= 0 {
        Some(x.sqrt() * -sgn(y))
    } else {
        None
    }
}

pub(crate) fn split_into_halves(n: usize) -> (usize, usize) {
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
pub(crate) fn integer_division(a: i64, b: i64) -> Option<i64> {
    if b == 0 {
        None
    } else if a == 0 {
        Some(0)
    } else {
        Some(a / b)
    }
}

fn number_of_terms(operations: Vec<Vec<String>>, depth: usize, vars: usize) -> u64 {
    let mut number_of_op_combinations: u64 = 0;
    for (i, operation_layer) in itertools::enumerate(operations) {
        number_of_op_combinations += (operation_layer.len() * num::pow(vars, i)).to_u64().unwrap();
    }
    num::pow(number_of_op_combinations, depth)
} 

pub(crate) fn sum_workload_depth() -> usize {
    3
}

pub(crate) fn generate_rules(workload: &Workload, prior_rules: &mut Ruleset<desugared_lang::VecLangDesugared>, run_name: &str, vec_ops: bool, depth: usize) {
    use std::time::Instant;
    let beginning = Instant::now();
    let rules = {
            run_workload(workload.clone(), (*prior_rules).clone(), Limits::synthesis(), Limits::synthesis(), true)
    };
    let file_str = match vec_ops { true=>"vec", false=>"non-vec" };
    let duration = Instant::now() -  beginning;
    log_rules(&rules, Some((format!("candidates/depth_{}_ruleset_{}.json", depth, file_str)).as_str()), run_name.to_string(), duration);
    
    (*prior_rules).extend(rules)
}

pub(crate) fn permutation_vectors() -> Vec<String> {
    // types of permutations -> should be able to compose these to make any kind of permutation?
    let swaps = vec!["(Vec 1 0 2 3)", "(Vec 0 1 3 2)", "(Vec 3 1 2 0)", "(Vec 0 3 2 1)", "(Vec 0 2 1 3)", "(Vec 2 1 0 3)"];
    let mut rotations = vec!["(Vec 3 0 1 2)", "(Vec 1 2 3 0)"];

    let mut shuffles = swaps.clone();
    shuffles.append(&mut rotations);

    shuffles.iter().map(|x| x.to_string()).collect()
}

// if you dont want the exprs, don't pass anything in for scalar ops
pub(crate) fn interesting_vectors(scalar_ops: Vec<Vec<String>>) -> Workload {
    let scalar_wkld = scalar_exprs(scalar_ops);
    let vectors: Vec<String> = vec!["(Vec a b c d)", "(Vec a b c 0)", "(Vec a b 0 c)", "(Vec a 0 b c)", "(Vec 0 a b c)", "(Vec 0 0 a b)", "(Vec a b 0 0)", "(Vec a 0 0 0)", "(Vec EXPR VAR VAR VAR)"].into_iter().map(|x| x.to_string()).collect();
    // let vectors: Vec<String> = vec!["(Vec a b c d)", "(Vec a b c 0)", "(Vec a b 0 c)", "(Vec a 0 b c)", "(Vec 0 a b c)", "(Vec 0 0 a b)", "(Vec a b 0 0)", "(Vec a 0 0 0)"].into_iter().map(|x| x.to_string()).collect();
    let vector_filler: Workload = Workload::new(vectors.clone()).plug("EXPR", &scalar_wkld).plug("VAR", &vars());
    // let vector_filler: Workload = Workload::new(vectors);
    vector_filler
}

// various constants
pub(crate) fn vals() -> Workload {
    let vals: Vec<String> = ["0", "1"].iter().map(|x| x.to_string()).collect();
    Workload::new(vals)
}

pub(crate) fn vars() -> Workload {
    let vars: Vec<String> = ["a", "b", "c", "d"].iter().map(|x| x.to_string()).collect();
    Workload::new(vars)
}

pub(crate) fn scalar_exprs(scalar_ops: Vec<Vec<String>>) -> Workload {
    let vals = vals();
    let vars = vars();
    let mut filters: Vec<Filter> = vec![];
    println!("scalar ops are {scalar_ops:?}");
    let scalar_wkld = iter_dios_lt(3,vals,vars, &mut filters, scalar_ops);
    scalar_wkld
}

pub(crate) fn extract_vector_operations(operations: Vec<Vec<String>>) -> (Vec<Vec<String>>, Vec<Vec<String>>) {
    let mut vector_ops = vec![];
    let mut scalar_ops = vec![];
    for layer in operations {
        let (vec_layer, scalar_layer): (Vec<String>, Vec<String>) = layer.into_iter().partition(|element| element.to_lowercase().contains("vec"));
        vector_ops.push(vec_layer);
        scalar_ops.push(scalar_layer);
    }
    return (vector_ops, scalar_ops)
}

pub(crate) fn iter_dios(depth: usize, values: Workload, variable_names: Workload, filters: Vec<Filter>, operations: Vec<Vec<String>>) -> Workload {
    println!("depth is {depth}");
    let mut workload = iter_metric(base_lang(operations.len()), "EXPR", Metric::Depth, depth);
    
    // JB: put this back when doing vecsum only!
    // append(Workload::new(["(VecSum (Vec EXPR VAL VAL VAL))"]));;

    workload = workload
    .plug("VAL", &values)
    .plug("VAR", &variable_names);

    for (i, operation_layer) in operations.iter().enumerate() {
        workload = workload.plug(format!("OP{}", i+1), &Workload::new(operation_layer.clone()));
    }

    for filter in filters {
        workload = workload.filter(filter);
    }
    info!("Workload is {:?}", workload.clone());

    workload
}

// will generate less than depth
pub(crate) fn iter_dios_lt(depth: usize, values: Workload, variable_names: Workload, filters: &mut Vec<Filter>, operations: Vec<Vec<String>>) -> Workload {
    let lt = Filter::MetricLt(Metric::Depth, depth+1);
    filters.push(lt);
    iter_dios(depth, values, variable_names, filters.clone(), operations)
}

// will generate only equal to depth
pub(crate) fn iter_dios_eq(depth: usize, values: Workload, variable_names: Workload, filters: &mut Vec<Filter>, operations: Vec<Vec<String>>) -> Workload {
    let eq = Filter::MetricEq(Metric::Depth, depth);
    filters.push(eq);
    iter_dios(depth, values, variable_names, filters.clone(), operations)
}

// sets of hand-picked rules
pub(crate) fn handpicked_thinner() -> Vec<(Vec<Vec<String>>, usize)> {
    // start with scalar
    // let scalar = vec![vec!["sqrt", "sgn", "neg"], vec!["*", "/", "-", "+"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();

    // depth 4
    // let unary_ops: Vec<Vec<String>>  = vec![vec!["Vec", "VecSgn", "sgn", "VecNeg", "neg"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    // let related_binary_mul = vec![vec!["Vec"], vec!["VecMul", "*", "VecDiv", "/"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    // let related_binary_add = vec![vec!["Vec"], vec!["VecAdd", "+", "VecMinus", "-"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    // let related_binary_add_mul = vec![vec!["Vec"], vec!["VecAdd", "+", "VecMul", "*"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    
    // depth 3
    let unary_binary1: Vec<Vec<String>> = vec![vec!["Vec", "VecSgn", "sgn"], vec!["VecAdd", "+"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let unary_binary2: Vec<Vec<String>> = vec![vec!["Vec", "VecNeg", "neg"], vec!["VecAdd", "+"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();    
    let related_muls: Vec<Vec<String>> = vec![vec!["Vec"], vec!["VecMul", "VecMinus"], vec!["VecMULS"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let related_mac = vec![vec!["Vec"], vec!["VecMul", "VecAdd", "+"], vec!["VecMAC"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    // vec![(scalar, 3), (unary_ops, 3), (related_binary_add, 3), (related_binary_mul, 3), (related_binary_add_mul, 3), (unary_binary1, 3), (unary_binary2, 3), (related_muls, 2), (related_mac, 2)]
    vec![(unary_binary1, 3), (unary_binary2, 3), (related_muls, 2), (related_mac, 2)]

}

pub(crate) fn handpicked() -> Vec<(Vec<Vec<String>>, usize)> {
    // start with scalar
    let scalar = vec![vec!["sqrt", "sgn", "neg"], vec!["*", "/", "-", "+"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();

    // depth 4
    let unary_ops: Vec<Vec<String>>  = vec![vec!["Vec", "VecSgn", "sgn",  "VecNeg", "neg"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let binary_ops = vec![vec!["Vec"], vec!["VecAdd", "+", "VecMinus", "-", "VecMul", "*", "VecDiv", "/"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    // // depth 3

    // let unary_binary: Vec<Vec<String>> = vec![vec!["Vec", "VecSgn", "sgn", "VecNeg", "neg"], vec!["VecAdd", "+", "VecMul", "*"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let related_muls: Vec<Vec<String>> = vec![vec!["Vec"], vec!["VecMul", "VecMinus"], vec!["VecMULS"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();
    let related_mac = vec![vec!["Vec"], vec!["VecMul", "VecAdd", "+"], vec!["VecMAC"]].iter().map(|x| x.iter().map(|&x| String::from(x)).collect()).collect();

    // vec![(scalar, 3), (unary_ops, 3), (binary_ops, 3), (unary_binary, 3), (related_muls, 2), (related_mac, 2)]
    vec![(scalar, 3), (unary_ops, 3), (binary_ops, 3), (related_muls, 2), (related_mac, 2)]

}