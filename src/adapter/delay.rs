use crate::{BlockingMode, FutureMode, RetryMode};

#[doc(hidden)]
pub trait RetryDelay<Mode>
where
    Mode: RetryMode,
{
    type Wait;

    fn delay(&mut self, retry: usize) -> Self::Wait;
}

impl<T, E, D> RetryDelay<BlockingMode<T, E>> for D
where
    D: FnMut(usize),
{
    type Wait = ();

    #[inline]
    fn delay(&mut self, retry: usize) -> Self::Wait {
        self(retry);
    }
}

impl<T, E, Fut, D, Wait> RetryDelay<FutureMode<T, E, Fut>> for D
where
    D: FnMut(usize) -> Wait,
    Wait: Future<Output = ()>,
{
    type Wait = Wait;

    #[inline]
    fn delay(&mut self, retry: usize) -> Self::Wait {
        self(retry)
    }
}

#[doc(hidden)]
pub struct WithDelay<O, D> {
    pub(crate) operation: O,
    pub(crate) delay: D,
}
