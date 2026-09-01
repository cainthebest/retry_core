use core::marker::PhantomData;

mod private {
    pub trait Sealed {}
}

/// A sealed marker selecting the retry execution mode.
///
/// This trait is an implementation detail used to share the public [`Retry`]
/// interface between blocking and asynchronous operations.
#[doc(hidden)]
pub trait RetryMode: private::Sealed {}

/// Retry mode for a blocking `FnMut() -> Result<T, E>` operation.
#[doc(hidden)]
pub struct BlockingMode<T, E> {
    _output: PhantomData<fn() -> T>,
    _error: PhantomData<fn() -> E>,
}

/// Retry mode for an asynchronous operation returning `Fut`.
#[doc(hidden)]
pub struct FutureMode<T, E, Fut> {
    _output: PhantomData<fn() -> T>,
    _error: PhantomData<fn() -> E>,
    _future: PhantomData<fn() -> Fut>,
}

impl<T, E> RetryMode for BlockingMode<T, E> {}
impl<T, E> private::Sealed for BlockingMode<T, E> {}

impl<T, E, Fut> RetryMode for FutureMode<T, E, Fut> {}
impl<T, E, Fut> private::Sealed for FutureMode<T, E, Fut> {}
