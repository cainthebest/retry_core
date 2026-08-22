use {
    super::super::BlockingRetry,
    crate::{adapter::InspectRetry, storage::ErrorBuffer},
};

impl<O, I, T, E> BlockingRetry<T, E> for InspectRetry<O, I>
where
    O: BlockingRetry<T, E>,
    I: FnMut(usize, &E),
{
    type Errors<const ATTEMPTS: usize> = O::Errors<ATTEMPTS>;

    #[inline]
    fn call(&mut self) -> Result<T, E> {
        self.operation.call()
    }

    #[inline]
    fn finish<const ATTEMPTS: usize>(errors: ErrorBuffer<E, ATTEMPTS>) -> Self::Errors<ATTEMPTS> {
        O::finish(errors)
    }

    #[inline]
    fn should_retry(&mut self, error: &E) -> bool {
        self.operation.should_retry(error)
    }

    #[inline]
    fn inspect_retry(&mut self, retry: usize, error: &E) {
        self.operation.inspect_retry(retry, error);

        (self.inspect)(retry, error);
    }

    #[inline]
    fn delay(&mut self, retry: usize) {
        self.operation.delay(retry);
    }
}
