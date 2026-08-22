use {
    super::super::BlockingRetry,
    crate::{
        BlockingMode,
        adapter::{RetryDelay, WithDelay},
        storage::ErrorBuffer,
    },
};

impl<O, D, T, E> BlockingRetry<T, E> for WithDelay<O, D>
where
    O: BlockingRetry<T, E>,
    D: RetryDelay<BlockingMode<T, E>>,
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
    }

    #[inline]
    fn delay(&mut self, retry: usize) {
        self.operation.delay(retry);

        let _ = self.delay.delay(retry);
    }
}
