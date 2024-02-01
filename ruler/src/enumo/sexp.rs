use std::{str::FromStr, iter::FromIterator};
use std::{collections::VecDeque, fmt::Display};
use super::*;

// =========================== CANON ONLY ITERATOR ===========================

#[derive(Clone, Debug)]
pub struct SexpSubstIterCanon<I, F>
where
    I: Iterator<Item = Sexp>,
    F: Fn() -> I, 
{
    needle: String,
    // spawns a new iterator for the pegs -> this function needs to be modified s.t. it takes the current element and truncates
    spawn_iterator: F,
    // stack contains a sexp and an interator
    stack: VecDeque<(Sexp, I, usize)>,
}

impl<I, F> SexpSubstIterCanon<I, F>
where
    I: Iterator<Item = Sexp>,
    F: Fn() -> I,
{
    pub(crate) fn new<S: ToString>(inital_sexp: Sexp, needle: S, spawn_iterator: F) -> Self {
        let initial_iter = spawn_iterator();
        SexpSubstIterCanon {
            needle: needle.to_string(),
            spawn_iterator,
            stack: VecDeque::from([(inital_sexp, initial_iter, 0)]),
        }
    }
}

impl<I, F> Iterator for SexpSubstIterCanon<I, F>
where
    I: Iterator<Item = Sexp>,
    F: Fn() -> I,
{
    type Item = Sexp;

    fn next(&mut self) -> Option<Self::Item> {
        use itertools::Itertools;

        if let Some((parent_sexp, mut parent_iter, idx)) = self.stack.pop_front() {
            // if there is juice left in the iterator
            if let Some(next_item) = parent_iter.next() {

                // try to go deeper one layer by replacing the first instance of the
                // needle with the item we got from the iterator
                if let Some(child_sexp) = parent_sexp.replace_first(&self.needle, &next_item) {
                    // there might be more juice in the parent_iter,
                    // so push it back on the stack so that we try
                    // to process it again
                    self.stack.push_front((parent_sexp, parent_iter, idx+1));

                    // next we want to spawn a new iterator representing one layer
                    // deeper in the search. we want to make sure that this item
                    // is the next item processed on the stack so that we perform
                    // a depth-first traversal of the tree.
                    // how can we truncate spawn_iterator s.t. it starts at a certain index?
                    let child_iter = (self.spawn_iterator)().dropping(idx);
                    self.stack.push_front((child_sexp, child_iter, idx));

                    self.next()
                } else {
                    // otherwise (no needle), we are at a leaf and all instances
                    // of the needle are fully instantiated. we can yield this
                    // item from the iterator
                    Some(parent_sexp)
                }
            } else {
                // we are done with this layer of the tree. continue processing
                // the next item on the stack
                self.next()
            }
        } else {
            None
        }
    }
}

// =========================== NON-CANON ITERATOR ===========================


// #[derive(Clone, Debug)]
// pub struct SexpSubstIter<I, F>
// where
//     I: Iterator<Item = Sexp>,
//     F: Fn() -> I,
// {
//     needle: String,
//     spawn_iterator: F,
//     stack: VecDeque<(Sexp, I)>,
// }

// impl<I, F> SexpSubstIter<I, F>
// where
//     I: Iterator<Item = Sexp>,
//     F: Fn() -> I,
// {
//     pub(crate) fn new<S: ToString>(inital_sexp: Sexp, needle: S, spawn_iterator: F) -> Self {
//         let initial_iter = spawn_iterator();
//         SexpSubstIter {
//             needle: needle.to_string(),
//             spawn_iterator,
//             stack: VecDeque::from([(inital_sexp, initial_iter)]),
//         }
//     }
// }

// impl<I, F> Iterator for SexpSubstIter<I, F>
// where
//     I: Iterator<Item = Sexp>,
//     F: Fn() -> I,
// {
//     type Item = Sexp;

//     fn next(&mut self) -> Option<Self::Item> {
//         if let Some((parent_sexp, mut parent_iter)) = self.stack.pop_front() {
//             // if there is juice left in the iterator
//             if let Some(next_item) = parent_iter.next() {
//                 // try to go deeper one layer by replacing the first instance of the
//                 // needle with the item we got from the iterator
//                 if let Some(child_sexp) = parent_sexp.replace_first(&self.needle, &next_item) {
//                     // there might be more juice in the parent_iter,
//                     // so push it back on the stack so that we try
//                     // to process it again
//                     self.stack.push_front((parent_sexp, parent_iter));

//                     // next we want to spawn a new iterator representing one layer
//                     // deeper in the search. we want to make sure that this item
//                     // is the next item processed on the stack so that we perform
//                     // a depth-first traversal of the tree.
//                     let child_iter = (self.spawn_iterator)();
//                     self.stack.push_front((child_sexp, child_iter));

//                     self.next()
//                 } else {
//                     // otherwise (no needle), we are at a leaf and all instances
//                     // of the needle are fully instantiated. we can yield this
//                     // item from the iterator
//                     Some(parent_sexp)
//                 }
//             } else {
//                 // we are done with this layer of the tree. continue processing
//                 // the next item on the stack
//                 self.next()
//             }
//         } else {
//             None
//         }
//     }
// }

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Sexp {
    Atom(String),
    List(Vec<Self>),
}

trait ClonableIterator: Iterator + Clone {}
impl<I> ClonableIterator for I where I: Iterator + Clone {}

impl FromStr for Sexp {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        use symbolic_expressions::parser::parse_str;
        let sexp = parse_str(s).unwrap();
        Ok(Self::from_symbolic_expr(sexp))
    }
}

impl std::fmt::Display for Sexp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sexp::Atom(x) => write!(f, "{}", x),
            Sexp::List(l) => {
                write!(f, "(").expect("not written");
                for x in l {
                    write!(f, "{} ", x).expect("not written");
                }
                write!(f, ")").expect("not written");
                Ok(())
            }
        }
    }
}

impl Sexp {
    fn first(&mut self, needle: &str) -> Option<&mut Self> {
        match self {
            Sexp::Atom(a) if a == needle => Some(self),
            Sexp::Atom(_) => None,
            Sexp::List(list) => list.into_iter().find_map(|s| s.first(needle)),
        }
    }

    pub(crate) fn replace_first(&self, needle: &str, new: &Sexp) -> Option<Self> {
        let mut copy = self.clone();
        if let Some(ptr) = copy.first(needle) {
            *ptr = new.clone();
            Some(copy)
        } else {
            None
        }
    }

    fn from_symbolic_expr(sexp: symbolic_expressions::Sexp) -> Self {
        match sexp {
            symbolic_expressions::Sexp::String(s) => Self::Atom(s),
            symbolic_expressions::Sexp::List(ss) => Self::List(
                ss.iter()
                    .map(|s| Sexp::from_symbolic_expr(s.clone()))
                    .collect(),
            ),
            symbolic_expressions::Sexp::Empty => Self::List(vec![]),
        }
    }

    fn mk_canon(
        &self,
        symbols: &[String],
        mut idx: usize,
        mut subst: HashMap<String, String>,
    ) -> (HashMap<String, String>, usize) {
        match self {
            Sexp::Atom(x) => {
                if symbols.contains(x) && !subst.contains_key(x) {
                    subst.insert(x.into(), symbols[idx].clone());
                    idx += 1;
                }
                (subst, idx)
            }
            Sexp::List(exps) => exps.iter().fold((subst, idx), |(acc, idx), item| {
                item.mk_canon(symbols, idx, acc)
            }),
        }
    }

    fn apply_subst(&self, subst: &HashMap<String, String>) -> Self {
        match self {
            Sexp::Atom(s) => {
                if let Some(v) = subst.get(s) {
                    Sexp::Atom(v.into())
                } else {
                    Sexp::Atom(s.into())
                }
            }
            Sexp::List(exps) => Sexp::List(exps.iter().map(|s| s.apply_subst(subst)).collect()),
        }
    }

    pub(crate) fn canon(&self, symbols: &[String]) -> Self {
        let (subst, _) = self.mk_canon(symbols, 0, Default::default());
        self.apply_subst(&subst)
    }

    pub(crate) fn plug(&self, name: &str, pegs: &[Self]) -> Vec<Sexp> {
        use itertools::Itertools;
        match self {
            Sexp::Atom(s) if s == name => pegs.to_vec(),
            Sexp::Atom(_) => vec![self.clone()],
            Sexp::List(sexps) => sexps
                .iter()
                .map(|x| x.plug(name, pegs))
                .multi_cartesian_product()
                .map(Sexp::List)
                .collect(),
        } 
    }

    // change this to the substitute function 
    // pub(crate) fn plug(&self, name: &str, pegs: Box<Workload>) -> Box<dyn Iterator<Item = Sexp>> {

    //     match self {
    //         Sexp::Atom(s) if s == name => {
    //             return Box::new(pegs.into_iter());
    //         },
    //         Sexp::Atom(_) => { 
    //             return Box::new(vec![self.clone()].into_iter()); 
    //         },
    //         Sexp::List(sexps) => {

    //             let v = sexps.clone()
    //             .into_iter()
    //             .map(move |sexp| (sexp, name.clone(), pegs))
    //                 .map(|(sexp, name, pegs)| {
    //                     SexpSubstIter::new(sexp, name, move || pegs.into_iter())
    //                 })
    //             .flatten();
    //             return Box::new(v);
    //         }
    //     }
    // }

    pub(crate) fn measure(&self, metric: Metric) -> usize {
        match self {
            Sexp::Atom(_) => match metric {
                Metric::Lists => 0,
                Metric::Atoms | Metric::Depth => 1,
            },
            Sexp::List(s) => match metric {
                Metric::Atoms => s.iter().map(|x| x.measure(metric)).sum::<usize>(),
                Metric::Lists => s.iter().map(|x| x.measure(metric)).sum::<usize>() + 1,
                Metric::Depth => s.iter().map(|x| x.measure(metric)).max().unwrap() + 1,
            },
        }
    }
}



#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn from_str() {
        assert_eq!("a".parse::<Sexp>().unwrap(), Sexp::Atom("a".into()));
        assert_eq!(
            "(+ (- 1 2) 0)".parse::<Sexp>().unwrap(),
            Sexp::List(vec![
                Sexp::Atom("+".into()),
                Sexp::List(vec![
                    Sexp::Atom("-".into()),
                    Sexp::Atom("1".into()),
                    Sexp::Atom("2".into()),
                ]),
                Sexp::Atom("0".into()),
            ])
        )
    }

    #[test]
    fn measure_atoms() {
        let exprs = vec![
            ("a", 1),
            ("(a b)", 2),
            ("(a b c)", 3),
            ("(a (b c))", 3),
            ("(a b (c d))", 4),
            ("(a (b (c d)))", 4),
            ("(a (b c) (d e))", 5),
        ];
        for (expr, size) in exprs {
            assert_eq!(expr.parse::<Sexp>().unwrap().measure(Metric::Atoms), size);
        }
    }

    #[test]
    fn measure_lists() {
        let exprs = vec![
            ("a", 0),
            ("(a b)", 1),
            ("(a b c)", 1),
            ("(a (b c))", 2),
            ("(a b (c d))", 2),
            ("(a (b (c d)))", 3),
            ("(a (b c) (d e))", 3),
        ];
        for (expr, size) in exprs {
            assert_eq!(expr.parse::<Sexp>().unwrap().measure(Metric::Lists), size);
        }
    }

    #[test]
    fn measure_depth() {
        let exprs = vec![
            ("a", 1),
            ("(a b)", 2),
            ("(a b c)", 2),
            ("(a (b c))", 3),
            ("(a b (c d))", 3),
            ("(a (b (c d)))", 4),
            ("(a (b c) (d e))", 3),
        ];
        for (expr, size) in exprs {
            assert_eq!(expr.parse::<Sexp>().unwrap().measure(Metric::Depth), size);
        }
    }

    #[test]
    fn plug() {
        let x = "x".parse::<Sexp>().unwrap();
        let pegs = Workload::new(["1", "2", "3"]).force().collect::<Vec<_>>();
        let expected = vec![x.clone()];
        let actual = x.plug("a", &pegs);
        assert_eq!(actual, expected);

        let expected = pegs.clone();
        let actual = x.plug("x", &pegs);
        assert_eq!(actual, expected);
    }

    #[test]
    fn play_with_iterators() {
        let x = "(x x)".parse::<Sexp>().unwrap();
        let pegs = Workload::new(["1", "2", "3"]).force().collect::<Vec<_>>();
        let expected = Workload::new([
            "(1 1)", "(1 2)", "(1 3)", "(2 1)", "(2 2)", "(2 3)", "(3 1)", "(3 2)", "(3 3)",
        ]).force();


        // now, lets do the peg thing but with iterators only
         
        let actual: Vec<Sexp> = x.plug("x", &pegs);
        println!("x is {x:?}");
        println!("actual is {actual:?}");
        println!("expected is {:?}", expected.collect::<Vec<_>>());
        // we have an iterator over the pegs, which will be an iterator over sexps
    }

    #[test]
    fn plug_cross_product() {
        let term = Workload::new(["(x x)"]);
        let pegs = Workload::new(["1", "2", "3"]);
        let actual = Workload::Plug(Box::new(term), "x".to_string(), Box::new(pegs)).force().collect::<Vec<_>>();
        // .force().collect::<Vec<_>>();
        let expected = Workload::new([
            "(1 1)", "(1 2)", "(1 3)", "(2 2)", "(2 3)", "(3 3)",
        ])
        .force().collect::<Vec<_>>();
        // let actual = "(x x)".parse::<Sexp>().unwrap().plug("x", &Workload::new(["1", "2", "3"]).force().collect::<Vec<_>>());
        println!("expected: {expected:?} \nactual: {actual:?}");
        assert_eq!(actual, expected);
    }

    // only run this when in canon mode
    #[test]
    fn plug_cross_product_canon() {
        let term = "(x x)";
        let pegs = Workload::new(["1", "2", "3"]).force().collect::<Vec<_>>();
        let expected = Workload::new([
            "(1 1)", "(1 2)", "(1 3)", "(2 2)", "(2 3)", "(3 3)",
        ])
        .force().collect::<Vec<_>>();
        let actual = term.parse::<Sexp>().unwrap().plug("x", &pegs);
        println!("expected: {expected:?} \nactual: {actual:?}");
        assert_eq!(actual, expected);
    }

    #[test]
    fn multi_plug() {
        let wkld = Workload::new(["(a b)", "(a)", "(b)"]);
        let a_s = Workload::new(["1", "2", "3"]);
        let b_s = Workload::new(["x", "y"]);
        // let actual = wkld.clone().plug("a", &a_s).plug("b", &b_s).force();
        let actual: Vec<Sexp> = wkld.plug("a", &a_s).plug("b", &b_s).force().collect::<Vec<_>>();
        let expected = Workload::new([
            "(1 x)", "(1 y)", "(2 x)", "(2 y)", "(3 x)", "(3 y)", "(1)", "(2)", "(3)", "(x)", "(y)",
        ])
        .force().collect::<Vec<_>>();
        assert_eq!(actual, expected)
    }

    #[test]
    fn canon() {
        let inputs = Workload::new([
            "(+ (/ c b) a)",
            "(+ (- c c) (/ a a))",
            "a",
            "b",
            "x",
            "(+ a a)",
            "(+ b b)",
            "(+ a b)",
            "(+ b a)",
            "(+ a x)",
            "(+ x a)",
            "(+ b x)",
            "(+ x b)",
            "(+ a (+ b c))",
            "(+ a (+ c b))",
        ])
        .force();
        let expecteds = Workload::new([
            "(+ (/ a b) c)",
            "(+ (- a a) (/ b b))",
            "a",
            "a",
            "x",
            "(+ a a)",
            "(+ a a)",
            "(+ a b)",
            "(+ a b)",
            "(+ a x)",
            "(+ x a)",
            "(+ a x)",
            "(+ x a)",
            "(+ a (+ b c))",
            "(+ a (+ b c))",
        ])
        .force();
        for (test, expected) in inputs.zip(expecteds) {
            assert_eq!(
                test.canon(vec!["a".into(), "b".into(), "c".into()].as_ref()),
                expected
            );
        }
    }
}
