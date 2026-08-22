use {
    super::BlockingRetry,
    crate::{BlockingMode, Retry},
};

impl<O, T, E> Retry<BlockingMode<T, E>> for O
where
    O: BlockingRetry<T, E>,
{
    type Output = T;
    type Error = E;

    type Errors<const ATTEMPTS: usize> = O::Errors<ATTEMPTS>;

    type RetryResult<const ATTEMPTS: usize> = Result<T, Self::Errors<ATTEMPTS>>;

    type RetryOption<const ATTEMPTS: usize> = Option<T>;

    type RetryValue<const ATTEMPTS: usize, F>
        = T
    where
        F: FnOnce(Self::Errors<ATTEMPTS>) -> T;

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
        F: FnOnce(Self::Errors<ATTEMPTS>) -> T,
    {
        match self.run::<ATTEMPTS>() {
            Ok(value) => value,
            Err(errors) => fallback(errors),
        }
    }
}
