use {
    super::BlockingRetry,
    crate::{Retry, mode::BlockingMode},
};

impl<O, T, E> Retry<BlockingMode<T, E>> for O
where
    O: BlockingRetry<T, E>,
{
    type Output = T;

    type Error = E;

    type RetryResult<const ATTEMPTS: usize> = Result<T, [E; ATTEMPTS]>;

    type RetryOption<const ATTEMPTS: usize> = Option<T>;

    type RetryValue<const ATTEMPTS: usize, F>
        = T
    where
        F: FnOnce([E; ATTEMPTS]) -> T;

    #[inline]
    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS> {
        self.run::<ATTEMPTS>()
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS> {
        self.run_ok::<ATTEMPTS>()
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::RetryValue<ATTEMPTS, F>
    where
        F: FnOnce([E; ATTEMPTS]) -> T,
    {
        match self.run::<ATTEMPTS>() {
            Ok(value) => value,
            Err(errors) => fallback(errors),
        }
    }
}
