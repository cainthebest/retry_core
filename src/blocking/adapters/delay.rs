use {
    super::super::BlockingRetry,
    crate::{
        adapter::{RetryDelay, WithDelay},
        mode::BlockingMode,
    },
};

impl<O, D, T, E> BlockingRetry<T, E> for WithDelay<O, D>
where
    O: BlockingRetry<T, E>,
    D: RetryDelay<BlockingMode<T, E>>,
{
    #[inline]
    fn call(&mut self) -> Result<T, E> {
        self.operation.call()
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
