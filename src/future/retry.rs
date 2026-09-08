use {
    super::{FutureRetry, MAX_READY_RETRIES_PER_POLL, Phase},
    crate::{
        Retry,
        mode::FutureMode,
        storage::{ErrorBuffer, FutureSlot},
    },
    core::{
        future::Future,
        hint::cold_path,
        marker::PhantomData,
        pin::Pin,
        task::{Context, Poll, ready},
    },
};

#[must_use = "futures do nothing unless awaited or polled"]
#[doc(hidden)]
pub struct AsyncRetry<O, Fut, S, E, const ATTEMPTS: usize> {
    operation: O,
    future: FutureSlot<Fut>,
    delay: S,
    errors: ErrorBuffer<E, ATTEMPTS>,
    phase: Phase,
}

impl<O, Fut, S, T, E, const ATTEMPTS: usize> Future for AsyncRetry<O, Fut, S, E, ATTEMPTS>
where
    O: FutureRetry<T, E, Fut, DelayState = S>,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = Result<T, [E; ATTEMPTS]>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY:
        //
        // No pinned field is moved through `this`.
        let this = unsafe { self.get_unchecked_mut() };

        if this.future.is_complete() {
            cold_path();

            panic!("retry future polled after completion");
        }

        if ATTEMPTS == 0 {
            this.future.complete();

            return Poll::Ready(Err(this.errors.take()));
        }

        let mut ready_retries = 0;

        loop {
            if O::HAS_DELAY && matches!(this.phase, Phase::Delay) {
                ready!(
                    this.operation
                        .poll_delay(&mut this.delay, this.errors.len(), cx)
                );

                this.phase = Phase::Operation;

                if ATTEMPTS > MAX_READY_RETRIES_PER_POLL {
                    ready_retries += 1;

                    if ready_retries == MAX_READY_RETRIES_PER_POLL {
                        cx.waker().wake_by_ref();

                        return Poll::Pending;
                    }
                }
            }

            this.future.ensure_active(|| this.operation.call());

            match ready!(this.future.poll(cx)) {
                Ok(value) => {
                    this.future.complete();

                    return Poll::Ready(Ok(value));
                }

                Err(error) => {
                    let retry = this.errors.len() + 1;

                    if retry == ATTEMPTS {
                        this.errors.push(error);
                        this.future.complete();

                        return Poll::Ready(Err(this.errors.take()));
                    }

                    this.future.clear_ready_future();

                    this.operation.inspect_retry(retry, &error);
                    this.errors.push(error);

                    if O::HAS_DELAY {
                        this.phase = Phase::Delay;
                    } else if ATTEMPTS > MAX_READY_RETRIES_PER_POLL {
                        ready_retries += 1;

                        if ready_retries == MAX_READY_RETRIES_PER_POLL {
                            cx.waker().wake_by_ref();

                            return Poll::Pending;
                        }
                    }
                }
            }
        }
    }
}

#[must_use = "futures do nothing unless awaited or polled"]
#[doc(hidden)]
pub struct AsyncRetryOk<O, Fut, S, E, const ATTEMPTS: usize> {
    operation: O,
    future: FutureSlot<Fut>,
    delay: S,
    attempts: usize,
    phase: Phase,
    _error: PhantomData<fn() -> E>,
}

impl<O, Fut, S, T, E, const ATTEMPTS: usize> Future for AsyncRetryOk<O, Fut, S, E, ATTEMPTS>
where
    O: FutureRetry<T, E, Fut, DelayState = S>,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = Option<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY:
        //
        // No pinned field is moved through `this`.
        let this = unsafe { self.get_unchecked_mut() };

        if this.future.is_complete() {
            cold_path();

            panic!("retry future polled after completion");
        }

        if ATTEMPTS == 0 {
            this.future.complete();

            return Poll::Ready(None);
        }

        let mut ready_retries = 0;

        loop {
            if O::HAS_DELAY && matches!(this.phase, Phase::Delay) {
                ready!(
                    this.operation
                        .poll_delay(&mut this.delay, this.attempts, cx)
                );

                this.phase = Phase::Operation;

                if ATTEMPTS > MAX_READY_RETRIES_PER_POLL {
                    ready_retries += 1;

                    if ready_retries == MAX_READY_RETRIES_PER_POLL {
                        cx.waker().wake_by_ref();

                        return Poll::Pending;
                    }
                }
            }

            this.future.ensure_active(|| this.operation.call());

            match ready!(this.future.poll(cx)) {
                Ok(value) => {
                    this.future.complete();

                    return Poll::Ready(Some(value));
                }

                Err(error) => {
                    this.attempts += 1;

                    if this.attempts == ATTEMPTS {
                        this.future.complete();

                        return Poll::Ready(None);
                    }

                    this.future.clear_ready_future();

                    this.operation.inspect_retry(this.attempts, &error);

                    if O::HAS_DELAY {
                        this.phase = Phase::Delay;
                    } else if ATTEMPTS > MAX_READY_RETRIES_PER_POLL {
                        ready_retries += 1;

                        if ready_retries == MAX_READY_RETRIES_PER_POLL {
                            cx.waker().wake_by_ref();

                            return Poll::Pending;
                        }
                    }
                }
            }
        }
    }
}

#[must_use = "futures do nothing unless awaited or polled"]
#[doc(hidden)]
pub struct AsyncRetryOrElse<O, Fut, S, E, F, const ATTEMPTS: usize> {
    retry: AsyncRetry<O, Fut, S, E, ATTEMPTS>,
    fallback: Option<F>,
}

impl<O, Fut, S, T, E, F, const ATTEMPTS: usize> Future
    for AsyncRetryOrElse<O, Fut, S, E, F, ATTEMPTS>
where
    O: FutureRetry<T, E, Fut, DelayState = S>,
    Fut: Future<Output = Result<T, E>>,
    F: FnOnce([E; ATTEMPTS]) -> T,
{
    type Output = T;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY:
        //
        // `retry` is not moved through `this`.
        let this = unsafe { self.get_unchecked_mut() };

        // SAFETY:
        //
        // `retry` remains structurally pinned by `AsyncRetryOrElse`.
        let retry = unsafe { Pin::new_unchecked(&mut this.retry) };

        match ready!(retry.poll(cx)) {
            Ok(value) => {
                this.fallback = None;

                Poll::Ready(value)
            }

            Err(errors) => {
                let fallback = this
                    .fallback
                    .take()
                    .expect("retry fallback was already consumed");

                Poll::Ready(fallback(errors))
            }
        }
    }
}

impl<O, T, E, Fut> Retry<FutureMode<T, E, Fut>> for O
where
    O: FutureRetry<T, E, Fut>,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = T;
    type Error = E;

    type RetryResult<const ATTEMPTS: usize> = AsyncRetry<O, Fut, O::DelayState, E, ATTEMPTS>;

    type RetryOption<const ATTEMPTS: usize> = AsyncRetryOk<O, Fut, O::DelayState, E, ATTEMPTS>;

    type RetryValue<const ATTEMPTS: usize, F>
        = AsyncRetryOrElse<O, Fut, O::DelayState, E, F, ATTEMPTS>
    where
        F: FnOnce([E; ATTEMPTS]) -> T;

    #[inline]
    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS> {
        AsyncRetry {
            operation: self,
            future: FutureSlot::new(),
            delay: O::delay_state(),
            errors: ErrorBuffer::new(),
            phase: Phase::Operation,
        }
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS> {
        AsyncRetryOk {
            operation: self,
            future: FutureSlot::new(),
            delay: O::delay_state(),
            attempts: 0,
            phase: Phase::Operation,
            _error: PhantomData,
        }
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::RetryValue<ATTEMPTS, F>
    where
        F: FnOnce([E; ATTEMPTS]) -> T,
    {
        AsyncRetryOrElse {
            retry: AsyncRetry {
                operation: self,
                future: FutureSlot::new(),
                delay: O::delay_state(),
                errors: ErrorBuffer::new(),
                phase: Phase::Operation,
            },
            fallback: Some(fallback),
        }
    }
}
