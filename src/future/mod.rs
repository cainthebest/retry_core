use {
    crate::storage::ErrorBuffer,
    core::{
        future::Future,
        task::{Context, Poll},
    },
};

mod adapters;
mod delay;
mod retry;

pub(crate) use delay::DelayState;

const MAX_READY_RETRIES_PER_POLL: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Phase {
    Operation,
    Delay,
}

#[doc(hidden)]
pub trait FutureRetry<T, E, Fut>: Sized
where
    Fut: Future<Output = Result<T, E>>,
{
    type Errors<const ATTEMPTS: usize>;

    type DelayState;

    fn call(&mut self) -> Fut;

    fn finish<const ATTEMPTS: usize>(errors: ErrorBuffer<E, ATTEMPTS>) -> Self::Errors<ATTEMPTS>;

    fn delay_state() -> Self::DelayState;

    #[inline]
    fn should_retry(&mut self, _error: &E) -> bool {
        true
    }

    #[inline]
    fn inspect_retry(&mut self, _retry: usize, _error: &E) {}

    #[inline]
    fn poll_delay(
        &mut self,
        _state: &mut Self::DelayState,
        _retry: usize,
        _cx: &mut Context<'_>,
    ) -> Poll<()> {
        Poll::Ready(())
    }
}

impl<F, T, E, Fut> FutureRetry<T, E, Fut> for F
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    type Errors<const ATTEMPTS: usize> = [E; ATTEMPTS];

    type DelayState = ();

    #[inline]
    fn call(&mut self) -> Fut {
        self()
    }

    #[inline]
    fn finish<const ATTEMPTS: usize>(
        mut errors: ErrorBuffer<E, ATTEMPTS>,
    ) -> Self::Errors<ATTEMPTS> {
        errors.take()
    }

    #[inline]
    fn delay_state() {}
}
