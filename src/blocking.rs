use crate::{BlockingMode, Retry, storage::ErrorBuffer};

impl<F, T, E> Retry<BlockingMode<T, E>> for F
where
    F: FnMut() -> Result<T, E>,
{
    type Output = T;

    type Error = E;

    type Storage<const ATTEMPTS: usize> = [Self::Error; ATTEMPTS];

    type Result<const ATTEMPTS: usize> = Result<Self::Output, Self::Storage<ATTEMPTS>>;

    type Option<const ATTEMPTS: usize> = Option<Self::Output>;

    type Value<const ATTEMPTS: usize, G>
        = Self::Output
    where
        G: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output;

    #[inline]
    fn retry<const ATTEMPTS: usize>(mut self) -> Self::Result<ATTEMPTS> {
        let mut errors = ErrorBuffer::<Self::Error, ATTEMPTS>::new();

        for _ in 0..ATTEMPTS {
            match self() {
                Ok(value) => return Ok(value),
                Err(error) => errors.push(error),
            }
        }

        Err(errors.take())
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(mut self) -> Self::Option<ATTEMPTS> {
        for _ in 0..ATTEMPTS {
            if let Ok(value) = self() {
                return Some(value);
            }
        }

        None
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, G>(self, fallback: G) -> Self::Value<ATTEMPTS, G>
    where
        G: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output,
    {
        match self.retry::<ATTEMPTS>() {
            Ok(value) => value,
            Err(errors) => fallback(errors),
        }
    }
}
