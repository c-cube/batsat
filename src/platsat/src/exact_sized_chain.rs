use std::iter::Chain;

pub(crate) struct ExactSizedChain<I1, I2>(pub Chain<I1, I2>);

impl<I1: Iterator, I2: Iterator<Item = I1::Item>> Iterator for ExactSizedChain<I1, I2> {
    type Item = I1::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }

    fn fold<B, F>(self, init: B, f: F) -> B
    where
        Self: Sized,
        F: FnMut(B, Self::Item) -> B,
    {
        self.0.fold(init, f)
    }
}

impl<I1: ExactSizeIterator, I2: ExactSizeIterator<Item = I1::Item>> ExactSizeIterator
    for ExactSizedChain<I1, I2>
{
}
