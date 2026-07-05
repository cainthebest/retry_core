use {
    crate::{
        FutureMode, Retry,
        storage::{AttemptErrorBuffer, FutureSlot},
    },
    core::{
        hint::cold_path,
        marker::PhantomPinned,
        pin::Pin,
        task::{Context, Poll},
    },
};

#[inline(always)]
fn unlikely(condition: bool) -> bool {
    if condition {
        cold_path();
    }

    condition
}

#[cold]
#[inline(never)]
fn panic_polled_after_completion() -> ! {
    panic!("retry future polled after completion");
}

#[must_use = "futures do nothing unless awaited or polled"]
pub struct AsyncRetry<F, Fut, E, const ATTEMPTS: usize> {
    operation: F,
    future: FutureSlot<Fut>,
    errors: AttemptErrorBuffer<E, ATTEMPTS>,
    _pin: PhantomPinned,
}

impl<F, Fut, E, const ATTEMPTS: usize> AsyncRetry<F, Fut, E, ATTEMPTS> {
    #[inline]
    pub(super) fn new(operation: F) -> Self {
        Self {
            operation,
            future: FutureSlot::new(),
            errors: AttemptErrorBuffer::new(),
            _pin: PhantomPinned,
        }
    }
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

        loop {
            if unlikely(this.future.is_complete()) {
                panic_polled_after_completion();
            }

            if this.errors.is_full() {
                this.future.complete();
                return Poll::Ready(Err(this.errors.unwrap()));
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

impl<F, Fut, const ATTEMPTS: usize> AsyncRetryOk<F, Fut, ATTEMPTS> {
    #[inline]
    pub(super) fn new(operation: F) -> Self {
        Self {
            operation,
            future: FutureSlot::new(),
            attempts: 0,
            _pin: PhantomPinned,
        }
    }
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

        loop {
            if unlikely(this.future.is_complete()) {
                panic_polled_after_completion();
            }

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
    errors: AttemptErrorBuffer<E, ATTEMPTS>,
    fallback: Option<G>,
    _pin: PhantomPinned,
}

impl<F, Fut, E, G, const ATTEMPTS: usize> AsyncRetryOrElse<F, Fut, E, G, ATTEMPTS> {
    #[inline]
    pub(super) fn new(operation: F, fallback: G) -> Self {
        Self {
            operation,
            future: FutureSlot::new(),
            errors: AttemptErrorBuffer::new(),
            fallback: Some(fallback),
            _pin: PhantomPinned,
        }
    }
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

        loop {
            if unlikely(this.future.is_complete()) {
                panic_polled_after_completion();
            }

            if this.errors.is_full() {
                this.future.complete();

                let errors = this.errors.unwrap();

                let fallback = this
                    .fallback
                    .take()
                    .expect("retry fallback was already consumed");

                return Poll::Ready(fallback(errors));
            }

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
    type AttemptErrors<const ATTEMPTS: usize> = [E; ATTEMPTS];

    type RetryResult<const ATTEMPTS: usize> = AsyncRetry<F, Fut, E, ATTEMPTS>;
    type RetryOption<const ATTEMPTS: usize> = AsyncRetryOk<F, Fut, ATTEMPTS>;

    type RetryOrElse<const ATTEMPTS: usize, G>
        = AsyncRetryOrElse<F, Fut, E, G, ATTEMPTS>
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;

    #[inline]
    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS> {
        AsyncRetry::new(self)
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS> {
        AsyncRetryOk::new(self)
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, G>(self, fallback: G) -> Self::RetryOrElse<ATTEMPTS, G>
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output,
    {
        AsyncRetryOrElse::new(self, fallback)
    }
}
