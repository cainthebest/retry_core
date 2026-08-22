use crate::storage::ErrorBuffer;

mod adapters;
mod retry;

pub trait BlockingRetry<T, E>: Sized {
    type Errors<const ATTEMPTS: usize>;

    fn call(&mut self) -> Result<T, E>;

    fn finish<const ATTEMPTS: usize>(errors: ErrorBuffer<E, ATTEMPTS>) -> Self::Errors<ATTEMPTS>;

    #[inline]
    fn should_retry(&mut self, _error: &E) -> bool {
        true
    }

    #[inline]
    fn inspect_retry(&mut self, _retry: usize, _error: &E) {}

    #[inline]
    fn delay(&mut self, _retry: usize) {}

    #[inline]
    fn run<const ATTEMPTS: usize>(mut self) -> Result<T, Self::Errors<ATTEMPTS>> {
        let mut errors = ErrorBuffer::<E, ATTEMPTS>::new();

        for retry in 1..ATTEMPTS {
            match self.call() {
                Ok(value) => return Ok(value),

                Err(error) => {
                    if !self.should_retry(&error) {
                        errors.push(error);

                        return Err(Self::finish(errors));
                    }

                    self.inspect_retry(retry, &error);
                    errors.push(error);
                    self.delay(retry);
                }
            }
        }

        if ATTEMPTS == 0 {
            return Err(Self::finish(errors));
        }

        match self.call() {
            Ok(value) => Ok(value),

            Err(error) => {
                errors.push(error);

                Err(Self::finish(errors))
            }
        }
    }

    #[inline]
    fn run_ok<const ATTEMPTS: usize>(mut self) -> Option<T> {
        for retry in 1..ATTEMPTS {
            match self.call() {
                Ok(value) => return Some(value),

                Err(error) => {
                    if !self.should_retry(&error) {
                        return None;
                    }

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
    type Errors<const ATTEMPTS: usize> = [E; ATTEMPTS];

    #[inline]
    fn call(&mut self) -> Result<T, E> {
        self()
    }

    #[inline]
    fn finish<const ATTEMPTS: usize>(
        mut errors: ErrorBuffer<E, ATTEMPTS>,
    ) -> Self::Errors<ATTEMPTS> {
        errors.take()
    }
}
