use {
    super::super::FutureRetry,
    crate::adapter::InspectRetry,
    core::{
        future::Future,
        task::{Context, Poll},
    },
};

impl<O, I, T, E, Fut> FutureRetry<T, E, Fut> for InspectRetry<O, I>
where
    O: FutureRetry<T, E, Fut>,
    I: FnMut(usize, &E),
    Fut: Future<Output = Result<T, E>>,
{
    type DelayState = O::DelayState;

    const HAS_DELAY: bool = O::HAS_DELAY;

    #[inline]
    fn call(&mut self) -> Fut {
        self.operation.call()
    }

    #[inline]
    fn delay_state() -> Self::DelayState {
        O::delay_state()
    }

    #[inline]
    fn inspect_retry(&mut self, retry: usize, error: &E) {
        self.operation.inspect_retry(retry, error);
        (self.inspect)(retry, error);
    }

    #[inline]
    fn poll_delay(
        &mut self,
        state: &mut Self::DelayState,
        retry: usize,
        cx: &mut Context<'_>,
    ) -> Poll<()> {
        self.operation.poll_delay(state, retry, cx)
    }
}
