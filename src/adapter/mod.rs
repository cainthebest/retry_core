use {
    crate::{Retry, RetryMode},
    core::marker::PhantomData,
};

mod delay;
mod inspect;

pub(crate) use {
    delay::{RetryDelay, WithDelay},
    inspect::InspectRetry,
};

#[doc(hidden)]
pub struct RetryPolicy<O, Mode> {
    pub(crate) operation: O,
    pub(crate) _mode: PhantomData<fn() -> Mode>,
}

impl<O, Mode> RetryPolicy<O, Mode>
where
    Mode: RetryMode,
    O: Retry<Mode>,
{
    #[inline]
    pub fn with_delay<D>(self, delay: D) -> RetryPolicy<WithDelay<O, D>, Mode>
    where
        D: RetryDelay<Mode>,
    {
        RetryPolicy {
            operation: WithDelay {
                operation: self.operation,
                delay,
            },
            _mode: PhantomData,
        }
    }

    #[inline]
    pub fn inspect_retry<I>(self, inspect: I) -> RetryPolicy<InspectRetry<O, I>, Mode>
    where
        I: FnMut(usize, &O::Error),
    {
        RetryPolicy {
            operation: InspectRetry {
                operation: self.operation,
                inspect,
            },
            _mode: PhantomData,
        }
    }

    #[inline]
    pub fn retry<const ATTEMPTS: usize>(self) -> O::RetryResult<ATTEMPTS> {
        self.operation.retry::<ATTEMPTS>()
    }

    #[inline]
    pub fn retry_ok<const ATTEMPTS: usize>(self) -> O::RetryOption<ATTEMPTS> {
        self.operation.retry_ok::<ATTEMPTS>()
    }

    #[inline]
    pub fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> O::RetryValue<ATTEMPTS, F>
    where
        F: FnOnce([O::Error; ATTEMPTS]) -> O::Output,
    {
        self.operation.retry_or_else::<ATTEMPTS, F>(fallback)
    }
}
