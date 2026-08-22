use {
    super::super::FutureRetry,
    crate::{adapter::OnlyIf, storage::ErrorBuffer},
    core::{
        future::Future,
        task::{Context, Poll},
    },
};

impl<O, P, T, E, Fut> FutureRetry<T, E, Fut> for OnlyIf<O, P>
where
    O: FutureRetry<T, E, Fut>,
    P: FnMut(&E) -> bool,
    Fut: Future<Output = Result<T, E>>,
{
    type Errors<const ATTEMPTS: usize> = ErrorBuffer<E, ATTEMPTS>;

    type DelayState = O::DelayState;

    #[inline]
    fn call(&mut self) -> Fut {
        self.operation.call()
    }

    #[inline]
    fn finish<const ATTEMPTS: usize>(errors: ErrorBuffer<E, ATTEMPTS>) -> Self::Errors<ATTEMPTS> {
        errors
    }

    #[inline]
    fn delay_state() -> Self::DelayState {
        O::delay_state()
    }

    #[inline]
    fn should_retry(&mut self, error: &E) -> bool {
        self.operation.should_retry(error) && (self.predicate)(error)
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
        self.operation.poll_delay(state, retry, cx)
    }
}
