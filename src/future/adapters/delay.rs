use {
    super::super::{DelayState, FutureRetry},
    crate::{
        adapter::{RetryDelay, WithDelay},
        mode::FutureMode,
    },
    core::{
        future::Future,
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
        state: &mut Self::DelayState,
        retry: usize,
        cx: &mut Context<'_>,
    ) -> Poll<()> {
        if state.future.is_empty() {
            ready!(self.operation.poll_delay(&mut state.inner, retry, cx));

            state.future.ensure_active(|| self.delay.delay(retry));
        }

        ready!(state.future.poll(cx));

        state.future.clear_ready_future();

        Poll::Ready(())
    }
}
