use std::{str::FromStr, iter::FromIterator};

use super::*;

#[derive(PartialEq, Eq, Clone, Debug)]
pub enum Sexp {
    Atom(String),
    List(Vec<Self>),
}

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

    pub(crate) fn plug_original(&self, name: &str, pegs: &[Self]) -> Vec<Sexp> {
        use itertools::Itertools;
        match self {
            Sexp::Atom(s) if s == name => pegs.to_vec(),
            Sexp::Atom(_) => vec![self.clone()],
            Sexp::List(sexps) => sexps
                .iter()
                .map(|x| x.plug_original(name, pegs))
                .multi_cartesian_product()
                .map(Sexp::List)
                .collect(),
        }
    }


    // fn cartesian_product(iterators: &[impl Iterator<Item = T>]) -> Box<dyn Iterator<Item = Vec<T>>> {
    //     match iterators.split_first() {
    //         Some((first, rest)) => {
    //             let cloned_rest = rest.to_vec();
    //             Box::new(first.flat_map(move |x| cartesian_product(&cloned_rest, x.clone()).map(move |mut v| { v.push(x.clone()); v })))
    //         }
    //         None => Box::new(std::iter::once(vec![])),
    //     }
    // }

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

    pub(crate) fn plug<'a>(&self, name: &str, pegs: impl Iterator<Item = Sexp> + Clone) -> impl Iterator<Item = Sexp> + Clone {
        use itertools::iproduct;
        use itertools::cloned;
        use itertools::Itertools;

        let val = match self {
            Sexp::Atom(s) if s == name => pegs.map(|s| s.clone()).collect::<Vec<_>>().into_iter(),
            Sexp::Atom(_) => vec![self.clone()].into_iter().collect::<Vec<_>>().into_iter(),
            Sexp::List(sexps) => 
            {
                // we have sexps. we want to go through every sexp and plug it, which will result in nested iterators.

                // this is an iterator over sexps -> we want to take the cartesian product of all of these iterators

                //: Vec<Box<dyn Iterator<Item = Sexp>>>
                let iterators = sexps
                .iter()
                .map(|x| x.plug(name, pegs.clone()))
                .multi_cartesian_product()
                .map(|list|
                    {
                        // let new_list = list.into_iter().cloned().collect();
                        Sexp::List(list)
                })
                .collect::<Vec<_>>()
                .into_iter();

                iterators
            }
        };
        val
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
        let actual = x.plug("a", pegs.clone());
        assert_eq!(actual.collect::<Vec<_>>(), expected);

        let expected = pegs.clone().collect::<Vec<_>>().clone();
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
