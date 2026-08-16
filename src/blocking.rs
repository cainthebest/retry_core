use crate::{
    BlockingMode, Retry,
    adapter::{InspectRetry, OnlyIf, RetryDelay, WithDelay},
    storage::ErrorBuffer,
};

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
