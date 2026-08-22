#![no_std]

use {crate::adapter::RetryPolicy, core::marker::PhantomData};

pub(crate) mod adapter;
pub(crate) mod storage;

mod blocking;
mod future;
mod private {
    pub trait Sealed {}
}

#[doc(hidden)]
pub trait RetryMode: private::Sealed {}

#[doc(hidden)]
pub struct BlockingMode<T, E> {
    _output: PhantomData<fn() -> T>,
    _error: PhantomData<fn() -> E>,
}

#[doc(hidden)]
pub struct FutureMode<T, E, Fut> {
    _output: PhantomData<fn() -> T>,
    _error: PhantomData<fn() -> E>,
    _future: PhantomData<fn() -> Fut>,
}

impl<T, E> private::Sealed for BlockingMode<T, E> {}

impl<T, E, Fut> private::Sealed for FutureMode<T, E, Fut> {}

impl<T, E> RetryMode for BlockingMode<T, E> {}

impl<T, E, Fut> RetryMode for FutureMode<T, E, Fut> {}

pub trait Retry<Mode>: Sized
where
    Mode: RetryMode,
{
    type Output;
    type Error;

    type Errors<const ATTEMPTS: usize>;

    type RetryResult<const ATTEMPTS: usize>;

    type RetryOption<const ATTEMPTS: usize>;

    type RetryValue<const ATTEMPTS: usize, F>
    where
        F: FnOnce(Self::Errors<ATTEMPTS>) -> Self::Output;

    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS>;

    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS>;

    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::RetryValue<ATTEMPTS, F>
    where
        F: FnOnce(Self::Errors<ATTEMPTS>) -> Self::Output;

    #[inline]
    fn retry_policy(self) -> RetryPolicy<Self, Mode> {
        RetryPolicy {
            operation: self,
            _mode: PhantomData,
        }
    }
}
