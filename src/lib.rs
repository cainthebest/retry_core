#![no_std]

use core::marker::PhantomData;

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

    type Storage<const ATTEMPTS: usize>;

    type Result<const ATTEMPTS: usize>;

    type Option<const ATTEMPTS: usize>;

    type Value<const ATTEMPTS: usize, F>
    where
        F: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output;

    fn retry<const ATTEMPTS: usize>(self) -> Self::Result<ATTEMPTS>;

    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::Option<ATTEMPTS>;

    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::Value<ATTEMPTS, F>
    where
        F: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output;
}
