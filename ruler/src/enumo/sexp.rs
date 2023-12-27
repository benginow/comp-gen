use std::{str::FromStr, iter::FromIterator};
use std::str::FromStr;
use std::{collections::VecDeque, fmt::Display};


use super::*;

#[derive(Clone, Debug)]
pub struct SexpSubstIter<I, F>
where
    I: Iterator<Item = Sexp>,
    F: Fn() -> I,
{
    needle: String,
    spawn_iterator: F,
    stack: VecDeque<(Sexp, I)>,
}

impl<I, F> SexpSubstIter<I, F>
where
    I: Iterator<Item = Sexp>,
    F: Fn() -> I,
{
    pub(crate) fn new<S: ToString>(inital_sexp: Sexp, needle: S, spawn_iterator: F) -> Self {
        let initial_iter = spawn_iterator();
        SexpSubstIter {
            needle: needle.to_string(),
            spawn_iterator,
            stack: VecDeque::from([(inital_sexp, initial_iter)]),
        }
    }
}

impl<I, F> Iterator for SexpSubstIter<I, F>
where
    I: Iterator<Item = Sexp>,
    F: Fn() -> I,
{
    type Item = Sexp;

    /// Intuitively, the thing that we want to do is perform a traversal of the leaves
    /// of the following tree. Each level of the tree represents substituting the hole
    /// variable (`A` in this case), with every instance of some other iterator.
    ///
    /// ```
    ///             (+ A A)
    ///            /       \
    ///     (+ 0 A)         (+ 1 A)
    ///       / \             / \
    /// (+ 0 0) (+ 0 1) (+ 1 0) (+ 1 1)
    /// ```
    ///
    /// The thing that makes it tricky to write this traversal in a lazy way is that we
    /// don't know what this tree will look like up-front; it's lazily produced by
    /// another iterator filling in the values of `A`.
    ///
    /// The trick is that we can use a stack to represent where we are in this tree
    /// traversal, making sure that we have enough information to unfold the next layer
    /// of the tree. Specifically, we can store an iterator for each layer of the tree,
    /// and a template to generate the next layer deep in the tree.
    ///
    /// Pictorially, it will look something like this:
    ///
    /// ```
    /// 1.
    /// (+ A A)
    ///
    /// 2.
    /// (+ A A)
    ///    |
    /// (+ 0 A)
    ///
    /// 3.
    /// (+ A A)
    ///    |
    /// (+ 0 A)
    ///    |
    /// (+ 0 0)
    ///
    /// 4.
    ///     (+ A A)
    ///        |
    ///     (+ 0 A)
    ///      /  \
    /// (+ 0 0) (+ 0 1)
    /// ```
    ///
    /// We implement this by maintaining work on a stack. An item of work is a template
    /// expression along with an iterator. Each item of work represents the set of
    /// expressions obtained by replacing the first instance of the needle variable with
    /// every item of the iterator. For example, `(+ 0 A), [0, 1, 2]` represents the set
    /// of expressions `(+ 0 0) (+ 0 1) (+ 0 2)`. By moving through the iterator, you
    /// can lazily generate nodes of the tree in the layer below the template
    /// expression.
    ///
    /// In this way, we can use these items of work to keep track of where we have
    /// explored in our tree search so far: each item of work keeps track of where we
    /// are at each layer of the tree. Once there are no more instances of the needle
    /// variable, we can yield the item from the iterator.
    ///
    /// Here is the actual algorithm:
    /// Given an item of work, we
    ///
    /// 1. Try to progress the search horiztonally in the tree. We do this by checking
    ///    the iterator associated with an item of work. If there are no items left, we
    ///    have reached the end of this layer. We simply move onto the next item of
    ///    work. If there are items left in the iterator,
    /// 2. We try to spawn a deeper layer of the search. We do this by starting a new
    ///    iterator for the child of the previous layer. If we can't go any deeper, then
    ///    we know that we are at a leaf, and can yield this item. If we can, we make
    ///    sure to put this item at the front of the stack so that it is processed on
    ///    the next iterator. This results in a depth-first traversal of the tree.
    ///
    /// Let's walk through how this works for this workload: `(+ A A).plug(A, {0, 1, 2})`
    ///
    /// The stack starts off with
    ///
    /// ```
    /// (+ A A), [0, 1, 2]
    /// ```
    ///
    /// ```
    /// (+ 0 A) [0, 1, 2]
    /// (+ A A) [1, 2]
    /// ```
    ///
    /// ```
    /// (+ 0 0) [0, 1, 2]
    /// (+ 0 A) [1, 2]
    /// (+ A A) [1, 2]
    /// ```
    ///
    /// Produced!: `(+ 0 0)`
    ///
    /// ```
    /// (+ 0 A) [1, 2]
    /// (+ A A) [1, 2]
    /// ```
    ///
    /// ```
    /// (+ 0 1) [0, 1, 2]
    /// (+ 0 A) [2]
    /// (+ A A) [1, 2]
    /// ```
    ///
    /// Produced!: `(+ 0 1)`
    ///
    /// ```
    /// (+ 0 2) [0, 1, 2]
    /// (+ 0 A) []
    /// (+ A A) [1, 2]
    /// ```
    ///
    /// Produced!: `(+ 0 2)`
    fn next(&mut self) -> Option<Self::Item> {
        if let Some((parent_sexp, mut parent_iter)) = self.stack.pop_front() {
            // if there is juice left in the iterator
            if let Some(next_item) = parent_iter.next() {
                // try to go deeper one layer by replacing the first instance of the
                // needle with the item we got from the iterator
                if let Some(child_sexp) = parent_sexp.replace_first(&self.needle, &next_item) {
                    // there might be more juice in the parent_iter,
                    // so push it back on the stack so that we try
                    // to process it again
                    self.stack.push_front((parent_sexp, parent_iter));

                    // next we want to spawn a new iterator representing one layer
                    // deeper in the search. we want to make sure that this item
                    // is the next item processed on the stack so that we perform
                    // a depth-first traversal of the tree.
                    let child_iter = (self.spawn_iterator)();
                    self.stack.push_front((child_sexp, child_iter));

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

    // change this to the substitute function 
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


    // fn cartesian_product<'a>(iterators: Vec<Box<dyn Iterator<Item = Sexp>>>) -> Box<dyn Iterator<Item = Sexp>> {
    //     let thing = match iterators.split_first() {
    //         Some((first,rest)) => {
    //             Box::new(first.flat_map(
    //                 move |x| Self::cartesian_product(rest).map(
    //                     |sexp| Sexp::List([x.clone(), sexp].to_vec()))
    //             ).map(Sexp::List))
    //         }
    //         None => Box::new(std::iter::empty()),
    //     };
    //     return thing;
    // }


    // fn cartesian_product_sexps<'a>(iterators: &mut Vec<Box<dyn Iterator<Item = Sexp>>>) -> Box<dyn Iterator<Item = Sexp> + 'a> {
    //     let val = Self::cartesian_product(iterators)
    //     .map(|items| Sexp::List(items));
    //     Box::new(val)
    // }

    

    // This was my last implementation of cartesian product, I think
    fn cartesian_product<'a>(iterators: &'a mut Vec<Box<dyn Iterator<Item = Sexp> + 'a>>) -> Box<dyn Iterator<Item = Vec<Sexp>> + 'a> {
        // this is a vector of iterators over sexps.
        // we want a mapping that will make a cartesian product over those iterators
        if let Some(iter) = iterators.pop() {
            let current_iterator = iter.map(|val| vec![val]);
            let child_iterators = (Self::cartesian_product(iterators));
            let combined_iterators = current_iterator.flat_map(move |vec| { 
                
                let val = child_iterators.map(move |item| 
                    {
                        let mut vec_cloned = vec.clone();
                        let mut item_cloned = item.clone();
                        item_cloned.append(&mut vec_cloned);
                        item_cloned
                    });
                val 
            });
            Box::new(combined_iterators)
        }
        else {
            Box::new(std::iter::empty())
        }
    }

    

    // Iterator implementation of plug
    pub(crate) fn plug_iterator(&self, name: &str, pegs: Box<dyn Iterator<Item = Sexp>>) -> Box<dyn Iterator<Item = Sexp>> {
        match self {
            Sexp::Atom(s) if s == name => {return Box::new(pegs.map(|s| s.clone()))},
            Sexp::Atom(_) => {return Box::new(vec![self.clone()].into_iter())},
            Sexp::List(sexps) => 
            {
                let mut iterators = sexps
                .iter()
                .map(|x| x.plug(name, pegs))
                .map(|iterator| IterRestart::boxed(*iterator))
                .collect::<Vec<_>>();

                let products = Self::cartesian_product(&mut iterators);

                return Box::new(products);
            }
        };
    }

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
        let pegs = Workload::new(["1", "2", "3"]).force();
        let expected = vec![x.clone()];
        let actual = x.plug("a", pegs);
        assert_eq!(actual.collect::<Vec<_>>(), expected);

        let expected = pegs.collect::<Vec<_>>().clone();
        let actual = x.plug("x", pegs);
        assert_eq!(actual.collect::<Vec<_>>(), expected);
    }

    #[test]
    fn play_with_iterators() {
        let x = "(x x)".parse::<Sexp>().unwrap();
        let pegs = Workload::new(["1", "2", "3"]).force();
        let expected = Workload::new([
            "(1 1)", "(1 2)", "(1 3)", "(2 1)", "(2 2)", "(2 3)", "(3 1)", "(3 2)", "(3 3)",
        ]).force();


        // now, lets do the peg thing but with iterators only
         
        let actual: Vec<Sexp> = x.plug("x", pegs).collect();
        println!("x is {x:?}");
        println!("actual is {actual:?}");
        println!("expected is {:?}", expected.collect::<Vec<_>>());
        // we have an iterator over the pegs, which will be an iterator over sexps
        
    }

    #[test]
    fn plug_cross_product() {
        let term = "(x x)";
        let pegs = Workload::new(["1", "2", "3"]).force();
        let expected = Workload::new([
            "(1 1)", "(1 2)", "(1 3)", "(2 1)", "(2 2)", "(2 3)", "(3 1)", "(3 2)", "(3 3)",
        ])
        .force().collect::<Vec<_>>();
        let actual = term.parse::<Sexp>().unwrap().plug("x", pegs).collect::<Vec<_>>();
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
