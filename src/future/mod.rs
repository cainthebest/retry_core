use core::{
    future::Future,
    task::{Context, Poll},
};

mod adapters;
mod delay;
mod retry;

pub(crate) use delay::DelayState;

const MAX_READY_RETRIES_PER_POLL: usize = 64;

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
    type DelayState;

    const HAS_DELAY: bool = false;

    fn call(&mut self) -> Fut;

    fn delay_state() -> Self::DelayState;

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
    type DelayState = ();

    #[inline]
    fn call(&mut self) -> Fut {
        self()
    }

    #[inline]
    fn delay_state() {}
}
