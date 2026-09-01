use crate::storage::ErrorBuffer;

mod adapters;
mod retry;

pub(crate) trait BlockingRetry<T, E>: Sized {
    fn call(&mut self) -> Result<T, E>;

    #[inline]
    fn inspect_retry(&mut self, _retry: usize, _error: &E) {}

    #[inline]
    fn delay(&mut self, _retry: usize) {}

    #[inline]
    fn run<const ATTEMPTS: usize>(mut self) -> Result<T, [E; ATTEMPTS]> {
        let mut errors = ErrorBuffer::<E, ATTEMPTS>::new();

        for retry in 1..ATTEMPTS {
            match self.call() {
                Ok(value) => return Ok(value),

                Err(error) => {
                    self.inspect_retry(retry, &error);

                    errors.push(error);

                    self.delay(retry);
                }
            }
        }

        if ATTEMPTS == 0 {
            return Err(errors.take());
        }

        match self.call() {
            Ok(value) => Ok(value),

            Err(error) => {
                errors.push(error);

                Err(errors.take())
            }
        }
    }

    #[inline]
    fn run_ok<const ATTEMPTS: usize>(mut self) -> Option<T> {
        for retry in 1..ATTEMPTS {
            match self.call() {
                Ok(value) => return Some(value),

                Err(error) => {
                    self.inspect_retry(retry, &error);

                    self.delay(retry);
                }
            }
        }

        if ATTEMPTS == 0 {
            return None;
        }

        self.call().ok()
    }
}

impl<F, T, E> BlockingRetry<T, E> for F
where
    F: FnMut() -> Result<T, E>,
{
    #[inline]
    fn call(&mut self) -> Result<T, E> {
        self()
    }
}
