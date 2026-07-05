#![no_std]

use core::marker::PhantomData;

pub(crate) mod storage;

mod blocking;
mod future;
mod private {
    pub trait Sealed {}
}

pub trait RetryMode: private::Sealed {}

pub struct BlockingMode<T, E> {
    _output: PhantomData<fn() -> T>,
    _error: PhantomData<fn() -> E>,
}

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

    type AttemptErrors<const ATTEMPTS: usize>;

    type RetryResult<const ATTEMPTS: usize>;

    type RetryOption<const ATTEMPTS: usize>;

    type RetryOrElse<const ATTEMPTS: usize, F>
    where
        F: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;

    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS>;

    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS>;

    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::RetryOrElse<ATTEMPTS, F>
    where
        F: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;
}
