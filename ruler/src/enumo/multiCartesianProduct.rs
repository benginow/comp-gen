use std::iter::once;

pub(crate) struct MultiCartesianProduct<I>
where
    I: Iterator,
{
    iterators: Vec<I>,
}

pub(crate) impl<I> MultiCartesianProduct<I>
where
    I: Iterator,
{
    fn new(iterators: Vec<I>) -> Self {
        MultiCartesianProduct { iterators }
    }
}

pub(crate) impl<I> Iterator for MultiCartesianProduct<I>
where
    I: Iterator,
    I::Item: Clone,
{
    type Item = Vec<I::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.iterators.is_empty() {
            return None;
        }

        let mut result = Vec::with_capacity(self.iterators.len());

        if let Some(mut first_iter) = self.iterators.pop() {
            if let Some(first_elem) = first_iter.next() {
                result.push(first_elem.clone());

                let remaining_product = MultiCartesianProduct::new(self.iterators.clone())
                    .map(|mut vec| {
                        vec.push(first_elem.clone());
                        vec
                    });

                result.extend(remaining_product);

                Some(result)
            } else {
                MultiCartesianProduct::new(self.iterators.clone()).next()
            }
        } else {
            Some(vec![])
        }
    }
}