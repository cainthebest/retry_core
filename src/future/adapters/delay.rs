use {
    super::super::{DelayState, FutureRetry},
    crate::{
        adapter::{RetryDelay, WithDelay},
        mode::FutureMode,
    },
    core::{
        future::Future,
        pin::Pin,
        task::{Context, Poll, ready},
    },
};

impl<T, E, Fut, D, Wait> RetryDelay<FutureMode<T, E, Fut>> for D
where
    D: FnMut(usize) -> Wait,
    Wait: Future<Output = ()>,
{
    type Wait = Wait;

    #[inline]
    fn delay(&mut self, retry: usize) -> Self::Wait {
        self(retry)
    }
}

impl<O, D, T, E, Fut> FutureRetry<T, E, Fut> for WithDelay<O, D>
where
    O: FutureRetry<T, E, Fut>,
    D: RetryDelay<FutureMode<T, E, Fut>>,
    D::Wait: Future<Output = ()>,
    Fut: Future<Output = Result<T, E>>,
{
    type DelayState = DelayState<O::DelayState, D::Wait>;

    const HAS_DELAY: bool = true;

    #[inline]
    fn call(&mut self) -> Fut {
        self.operation.call()
    }

    #[inline]
    fn delay_state() -> Self::DelayState {
        DelayState::new(O::delay_state())
    }

    #[inline]
    fn inspect_retry(&mut self, retry: usize, error: &E) {
        self.operation.inspect_retry(retry, error);
    }

    #[inline]
    fn poll_delay(
        &mut self,
        state: Pin<&mut Self::DelayState>,
        retry: usize,
        cx: &mut Context<'_>,
    ) -> Poll<()> {
        // SAFETY:
        //
        // `state` is pinned. `inner` and `future` are treated as
        // structurally pinned and are never moved through `state`.
        let state = unsafe { state.get_unchecked_mut() };

        if state.future.is_empty() {
            // SAFETY:
            //
            // `inner` is structurally pinned by the pinned `DelayState`.
            let inner = unsafe { Pin::new_unchecked(&mut state.inner) };

            ready!(self.operation.poll_delay(inner, retry, cx));

            // SAFETY:
            //
            // `future` is structurally pinned by the pinned `DelayState`.
            let future = unsafe { Pin::new_unchecked(&mut state.future) };

            future.ensure_active(|| self.delay.delay(retry));
        }

        // SAFETY:
        //
        // `future` is structurally pinned by the pinned `DelayState`.
        let mut future = unsafe { Pin::new_unchecked(&mut state.future) };

        ready!(future.as_mut().poll(cx));

        future.clear_ready_future();

        Poll::Ready(())
    }
}
