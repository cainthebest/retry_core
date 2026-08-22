use {
    super::super::BlockingRetry,
    crate::{adapter::OnlyIf, storage::ErrorBuffer},
};

impl<O, P, T, E> BlockingRetry<T, E> for OnlyIf<O, P>
where
    O: BlockingRetry<T, E>,
    P: FnMut(&E) -> bool,
{
    type Errors<const ATTEMPTS: usize> = ErrorBuffer<E, ATTEMPTS>;

    #[inline]
    fn call(&mut self) -> Result<T, E> {
        self.operation.call()
    }

    #[inline]
    fn finish<const ATTEMPTS: usize>(errors: ErrorBuffer<E, ATTEMPTS>) -> Self::Errors<ATTEMPTS> {
        errors
    }

    #[inline]
    fn should_retry(&mut self, error: &E) -> bool {
        self.operation.should_retry(error) && (self.predicate)(error)
    }

    #[inline]
    fn inspect_retry(&mut self, retry: usize, error: &E) {
        self.operation.inspect_retry(retry, error);
    }

    #[inline]
    fn delay(&mut self, retry: usize) {
        self.operation.delay(retry);
    }
}
