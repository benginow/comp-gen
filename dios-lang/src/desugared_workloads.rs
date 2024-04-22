use comp_gen::ruler::{
    enumo::*
};
use crate::util::*;

pub fn workload_sum(ops: Vec<Vec<String>>) -> Workload {
    let (scalar_ops, vector_ops) = extract_vector_operations(ops.clone());
    
    // various vectors that may be interesting for sum operations
    let vectors = interesting_vectors_sum(scalar_ops);
    let vars = vars().append(vectors);

    let mut filters = vec![Filter::Contains("Vec".parse().unwrap())];
    // feel free to change depth as needed
    let wkld = iter_dios_lt(sum_workload_depth(),vals(), vars, &mut filters, vector_ops);
    println!("Sum workload is: {:#?}", wkld.clone().force().collect::<Vec<_>>());
    wkld
}

pub fn workload_shfl(ops: Vec<Vec<String>>) -> Workload
{
    // not sure if vector ops are necessary for shfl yet -> may just append shfl workload to sum workload and see what happens
    let (scalar_ops, _) = extract_vector_operations(ops.clone());
    let shuffles = permutation_vectors();
    let vector_exprs = interesting_vectors_shfl(scalar_ops);

    println!("shfl workload");
    println!("shuffles: {shuffles:?}");
    println!("vector exprs: {:?}", vector_exprs.clone().force().collect::<Vec<_>>());

    let wkld = Workload::new(["(Shfl (Vec a b c d) SHUFFLES)", "EXPR"]).plug("SHUFFLES", &Workload::new(shuffles)).plug("EXPR", &vector_exprs);

    println!("Shuffle workload is: {:#?}", wkld.clone().force().collect::<Vec<_>>());
    wkld
}