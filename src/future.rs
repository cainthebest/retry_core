use {
    crate::{
        FutureMode, Retry,
        storage::{ErrorBuffer, FutureSlot},
    },
    core::{
        hint::cold_path,
        marker::PhantomPinned,
        pin::Pin,
        task::{Context, Poll},
    },
};

const MAX_READY_FAILURES_PER_POLL: usize = 64;

#[must_use = "futures do nothing unless awaited or polled"]
pub struct AsyncRetry<F, Fut, E, const ATTEMPTS: usize> {
    operation: F,
    future: FutureSlot<Fut>,
    errors: ErrorBuffer<E, ATTEMPTS>,
    _pin: PhantomPinned,
}

impl<F, Fut, T, E, const ATTEMPTS: usize> Future for AsyncRetry<F, Fut, E, ATTEMPTS>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = Result<T, [E; ATTEMPTS]>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY:
        // We never move the active future stored inside `future`. Other fields
        // are not structurally pinned and may be accessed mutably.
        let this = unsafe { self.get_unchecked_mut() };

        if this.future.is_complete() {
            cold_path();

            panic!("retry future polled after completion");
        }

        let mut remaining = MAX_READY_FAILURES_PER_POLL;

        loop {
            if this.errors.is_full() {
                this.future.complete();

                return Poll::Ready(Err(this.errors.take()));
            }

            this.future.ensure_active(|| (this.operation)());

            match this.future.poll_result(cx) {
                Poll::Ready(Ok(value)) => {
                    this.future.complete();

                    return Poll::Ready(Ok(value));
                }

                Poll::Ready(Err(error)) => {
                    this.future.clear_ready_future();
                    this.errors.push(error);

                    if this.errors.is_full() {
                        this.future.complete();

                        return Poll::Ready(Err(this.errors.take()));
                    }

                    if ATTEMPTS > MAX_READY_FAILURES_PER_POLL {
                        remaining -= 1;

                        if remaining == 0 {
                            cx.waker().wake_by_ref();

                            return Poll::Pending;
                        }
                    }
                }

                Poll::Pending => return Poll::Pending,
            }
        }
    }
}

#[must_use = "futures do nothing unless awaited or polled"]
pub struct AsyncRetryOk<F, Fut, const ATTEMPTS: usize> {
    operation: F,
    future: FutureSlot<Fut>,
    attempts: usize,
    _pin: PhantomPinned,
}

impl<F, Fut, T, E, const ATTEMPTS: usize> Future for AsyncRetryOk<F, Fut, ATTEMPTS>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = Option<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY:
        // We never move the active future stored inside `future`. Other fields
        // are not structurally pinned and may be accessed mutably.
        let this = unsafe { self.get_unchecked_mut() };

        if this.future.is_complete() {
            cold_path();

            panic!("retry future polled after completion");
        }

        let mut remaining = MAX_READY_FAILURES_PER_POLL;

        loop {
            if this.attempts >= ATTEMPTS {
                this.future.complete();

                return Poll::Ready(None);
            }

            this.future.ensure_active(|| (this.operation)());

            match this.future.poll_result(cx) {
                Poll::Ready(Ok(value)) => {
                    this.future.complete();

                    return Poll::Ready(Some(value));
                }

                Poll::Ready(Err(_)) => {
                    this.future.clear_ready_future();
                    this.attempts += 1;

                    if this.attempts >= ATTEMPTS {
                        this.future.complete();

                        return Poll::Ready(None);
                    }

                    if ATTEMPTS > MAX_READY_FAILURES_PER_POLL {
                        remaining -= 1;

                        if remaining == 0 {
                            cx.waker().wake_by_ref();

                            return Poll::Pending;
                        }
                    }
                }

                Poll::Pending => return Poll::Pending,
            }
        }
    }
}

#[must_use = "futures do nothing unless awaited or polled"]
pub struct AsyncRetryOrElse<F, Fut, E, G, const ATTEMPTS: usize> {
    operation: F,
    future: FutureSlot<Fut>,
    errors: ErrorBuffer<E, ATTEMPTS>,
    fallback: Option<G>,
    _pin: PhantomPinned,
}

impl<F, Fut, T, E, G, const ATTEMPTS: usize> Future for AsyncRetryOrElse<F, Fut, E, G, ATTEMPTS>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    G: FnOnce([E; ATTEMPTS]) -> T,
{
    type Output = T;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // SAFETY:
        // We never move the active future stored inside `future`. Other fields
        // are not structurally pinned and may be accessed mutably.
        let this = unsafe { self.get_unchecked_mut() };

        if this.future.is_complete() {
            cold_path();
            panic!("retry future polled after completion");
        }

        if ATTEMPTS == 0 {
            this.future.complete();

            let fallback = this
                .fallback
                .take()
                .expect("retry fallback was already consumed");

            return Poll::Ready(fallback(this.errors.take()));
        }

        let mut remaining = MAX_READY_FAILURES_PER_POLL;

        loop {
            this.future.ensure_active(|| (this.operation)());

            match this.future.poll_result(cx) {
                Poll::Ready(Ok(value)) => {
                    this.future.complete();
                    this.fallback = None;

                    return Poll::Ready(value);
                }

                Poll::Ready(Err(error)) => {
                    this.future.clear_ready_future();
                    this.errors.push(error);

                    if this.errors.is_full() {
                        this.future.complete();

                        let fallback = this
                            .fallback
                            .take()
                            .expect("retry fallback was already consumed");

                        return Poll::Ready(fallback(this.errors.take()));
                    }

                    if ATTEMPTS > MAX_READY_FAILURES_PER_POLL {
                        remaining -= 1;

                        if remaining == 0 {
                            cx.waker().wake_by_ref();

                            return Poll::Pending;
                        }
                    }
                }

                Poll::Pending => return Poll::Pending,
            }
        }
    }
}

impl<F, T, E, Fut> Retry<FutureMode<T, E, Fut>> for F
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = T;

    type Error = E;

    type Storage<const ATTEMPTS: usize> = [Self::Error; ATTEMPTS];

    type Result<const ATTEMPTS: usize> = AsyncRetry<F, Fut, E, ATTEMPTS>;

    type Option<const ATTEMPTS: usize> = AsyncRetryOk<F, Fut, ATTEMPTS>;

    type Value<const ATTEMPTS: usize, G>
        = AsyncRetryOrElse<F, Fut, E, G, ATTEMPTS>
    where
        G: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output;

    #[inline]
    fn retry<const ATTEMPTS: usize>(self) -> Self::Result<ATTEMPTS> {
        AsyncRetry {
            operation: self,
            future: FutureSlot::new(),
            errors: ErrorBuffer::new(),
            _pin: PhantomPinned,
        }
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::Option<ATTEMPTS> {
        AsyncRetryOk {
            operation: self,
            future: FutureSlot::new(),
            attempts: 0,
            _pin: PhantomPinned,
        }
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, G>(self, fallback: G) -> Self::Value<ATTEMPTS, G>
    where
        G: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output,
    {
        AsyncRetryOrElse {
            operation: self,
            future: FutureSlot::new(),
            errors: ErrorBuffer::new(),
            fallback: Some(fallback),
            _pin: PhantomPinned,
        }
    }
}
