use crate::{BlockingMode, Retry, storage::AttemptErrorBuffer};

impl<F, T, E> Retry<BlockingMode<T, E>> for F
where
    F: FnMut() -> Result<T, E>,
{
    type Output = T;
    type Error = E;
    type AttemptErrors<const ATTEMPTS: usize> = [E; ATTEMPTS];

    type RetryResult<const ATTEMPTS: usize> = Result<T, Self::AttemptErrors<ATTEMPTS>>;
    type RetryOption<const ATTEMPTS: usize> = Option<T>;

    type RetryOrElse<const ATTEMPTS: usize, G>
        = T
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;

    #[inline]
    fn retry<const ATTEMPTS: usize>(mut self) -> Self::RetryResult<ATTEMPTS> {
        let mut errors = AttemptErrorBuffer::<E, ATTEMPTS>::new();

        for _ in 0..ATTEMPTS {
            match self() {
                Ok(value) => return Ok(value),
                Err(error) => errors.push(error),
            }
        }

        Err(errors.unwrap())
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(mut self) -> Self::RetryOption<ATTEMPTS> {
        for _ in 0..ATTEMPTS {
            if let Ok(value) = self() {
                return Some(value);
            }
        }

        None
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, G>(self, fallback: G) -> Self::RetryOrElse<ATTEMPTS, G>
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output,
    {
        match self.retry::<ATTEMPTS>() {
            Ok(value) => value,
            Err(errors) => fallback(errors),
        }
    }
}
