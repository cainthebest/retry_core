use core::{
    future::Future,
    marker::{PhantomData, PhantomPinned},
    mem,
    pin::Pin,
    task::{Context, Poll, ready},
};

use crate::{
    FutureMode, Retry,
    adapter::{InspectRetry, OnlyIf, RetryDelay, WithDelay},
    storage::{ErrorBuffer, FutureSlot},
};

const MAX_READY_RETRIES_PER_POLL: usize = 64;

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Phase {
    Operation,
    Delay,
}

#[doc(hidden)]
pub struct DelayState<S, Fut> {
    inner: S,
    future: FutureSlot<Fut>,
}

impl<S, Fut> DelayState<S, Fut> {
    #[inline]
    const fn new(inner: S) -> Self {
        Self {
            inner,
            future: FutureSlot::new(),
        }
    }
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

impl<O, D, T, E, Fut> FutureRetry<T, E, Fut> for WithDelay<O, D>
where
    O: FutureRetry<T, E, Fut>,
    D: RetryDelay<FutureMode<T, E, Fut>>,
    D::Wait: Future<Output = ()>,
    Fut: Future<Output = Result<T, E>>,
{
    type Errors<const ATTEMPTS: usize> = O::Errors<ATTEMPTS>;

    type DelayState = DelayState<O::DelayState, D::Wait>;

    #[inline]
    fn call(&mut self) -> Fut {
        self.operation.call()
    }

    #[inline]
    fn finish<const ATTEMPTS: usize>(errors: ErrorBuffer<E, ATTEMPTS>) -> Self::Errors<ATTEMPTS> {
        O::finish(errors)
    }

    #[inline]
    fn delay_state() -> Self::DelayState {
        DelayState::new(O::delay_state())
    }

    #[inline]
    fn should_retry(&mut self, error: &E) -> bool {
        self.operation.should_retry(error)
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
            ready!(self.operation.poll_delay(&mut state.inner, retry, cx,));

            state.future.ensure_active(|| self.delay.delay(retry));
        }

        ready!(state.future.poll(cx));

        state.future.clear_ready_future();

        Poll::Ready(())
    }
}

impl<O, I, T, E, Fut> FutureRetry<T, E, Fut> for InspectRetry<O, I>
where
    O: FutureRetry<T, E, Fut>,
    I: FnMut(usize, &E),
    Fut: Future<Output = Result<T, E>>,
{
    type Errors<const ATTEMPTS: usize> = O::Errors<ATTEMPTS>;

    type DelayState = O::DelayState;

    #[inline]
    fn call(&mut self) -> Fut {
        self.operation.call()
    }

    #[inline]
    fn finish<const ATTEMPTS: usize>(errors: ErrorBuffer<E, ATTEMPTS>) -> Self::Errors<ATTEMPTS> {
        O::finish(errors)
    }

    #[inline]
    fn delay_state() -> Self::DelayState {
        O::delay_state()
    }

    #[inline]
    fn should_retry(&mut self, error: &E) -> bool {
        self.operation.should_retry(error)
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

#[must_use = "futures do nothing unless awaited or polled"]
#[doc(hidden)]
pub struct AsyncRetry<O, Fut, S, E, const ATTEMPTS: usize> {
    operation: O,
    future: FutureSlot<Fut>,
    delay: S,
    errors: ErrorBuffer<E, ATTEMPTS>,
    attempts: usize,
    phase: Phase,
    _pin: PhantomPinned,
}

impl<O, Fut, S, E, const ATTEMPTS: usize> AsyncRetry<O, Fut, S, E, ATTEMPTS> {
    #[inline]
    const fn new(operation: O, delay: S) -> Self {
        Self {
            operation,
            future: FutureSlot::new(),
            delay,
            errors: ErrorBuffer::new(),
            attempts: 0,
            phase: Phase::Operation,
            _pin: PhantomPinned,
        }
    }

    #[inline]
    fn take_errors(&mut self) -> ErrorBuffer<E, ATTEMPTS> {
        mem::replace(&mut self.errors, ErrorBuffer::new())
    }
}

impl<O, Fut, S, T, E, const ATTEMPTS: usize> Future for AsyncRetry<O, Fut, S, E, ATTEMPTS>
where
    O: FutureRetry<T, E, Fut, DelayState = S>,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = Result<T, O::Errors<ATTEMPTS>>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };

        if this.future.is_complete() {
            panic!("retry future polled after completion");
        }

        if ATTEMPTS == 0 {
            this.future.complete();

            let errors = this.take_errors();

            return Poll::Ready(Err(O::finish(errors)));
        }

        let mut ready_retries = 0;

        loop {
            match this.phase {
                Phase::Operation => {
                    this.future.ensure_active(|| this.operation.call());

                    match ready!(this.future.poll(cx)) {
                        Ok(value) => {
                            this.future.complete();

                            this.errors = ErrorBuffer::new();

                            return Poll::Ready(Ok(value));
                        }

                        Err(error) => {
                            this.future.clear_ready_future();

                            this.attempts += 1;

                            if this.attempts == ATTEMPTS {
                                this.errors.push(error);

                                this.future.complete();

                                let errors = this.take_errors();

                                return Poll::Ready(Err(O::finish(errors)));
                            }

                            if !this.operation.should_retry(&error) {
                                this.errors.push(error);

                                this.future.complete();

                                let errors = this.take_errors();

                                return Poll::Ready(Err(O::finish(errors)));
                            }

                            this.operation.inspect_retry(this.attempts, &error);

                            this.errors.push(error);

                            this.phase = Phase::Delay;
                        }
                    }
                }

                Phase::Delay => {
                    ready!(
                        this.operation
                            .poll_delay(&mut this.delay, this.attempts, cx,)
                    );

                    this.phase = Phase::Operation;

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

#[must_use = "futures do nothing unless awaited or polled"]
#[doc(hidden)]
pub struct AsyncRetryOk<O, Fut, S, E, const ATTEMPTS: usize> {
    operation: O,
    future: FutureSlot<Fut>,
    delay: S,
    attempts: usize,
    phase: Phase,
    _error: PhantomData<fn() -> E>,
    _pin: PhantomPinned,
}

impl<O, Fut, S, E, const ATTEMPTS: usize> AsyncRetryOk<O, Fut, S, E, ATTEMPTS> {
    #[inline]
    const fn new(operation: O, delay: S) -> Self {
        Self {
            operation,
            future: FutureSlot::new(),
            delay,
            attempts: 0,
            phase: Phase::Operation,
            _error: PhantomData,
            _pin: PhantomPinned,
        }
    }
}

impl<O, Fut, S, T, E, const ATTEMPTS: usize> Future for AsyncRetryOk<O, Fut, S, E, ATTEMPTS>
where
    O: FutureRetry<T, E, Fut, DelayState = S>,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = Option<T>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };

        if this.future.is_complete() {
            panic!("retry future polled after completion");
        }

        if ATTEMPTS == 0 {
            this.future.complete();

            return Poll::Ready(None);
        }

        let mut ready_retries = 0;

        loop {
            match this.phase {
                Phase::Operation => {
                    this.future.ensure_active(|| this.operation.call());

                    match ready!(this.future.poll(cx)) {
                        Ok(value) => {
                            this.future.complete();

                            return Poll::Ready(Some(value));
                        }

                        Err(error) => {
                            this.future.clear_ready_future();

                            this.attempts += 1;

                            if this.attempts == ATTEMPTS {
                                this.future.complete();

                                return Poll::Ready(None);
                            }

                            if !this.operation.should_retry(&error) {
                                this.future.complete();

                                return Poll::Ready(None);
                            }

                            this.operation.inspect_retry(this.attempts, &error);

                            this.phase = Phase::Delay;
                        }
                    }
                }

                Phase::Delay => {
                    ready!(
                        this.operation
                            .poll_delay(&mut this.delay, this.attempts, cx,)
                    );

                    this.phase = Phase::Operation;

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

#[must_use = "futures do nothing unless awaited or polled"]
#[doc(hidden)]
pub struct AsyncRetryOrElse<O, Fut, S, E, F, const ATTEMPTS: usize> {
    retry: AsyncRetry<O, Fut, S, E, ATTEMPTS>,
    fallback: Option<F>,
}

impl<O, Fut, S, E, F, const ATTEMPTS: usize> AsyncRetryOrElse<O, Fut, S, E, F, ATTEMPTS> {
    #[inline]
    const fn new(retry: AsyncRetry<O, Fut, S, E, ATTEMPTS>, fallback: F) -> Self {
        Self {
            retry,
            fallback: Some(fallback),
        }
    }
}

impl<O, Fut, S, T, E, F, const ATTEMPTS: usize> Future
    for AsyncRetryOrElse<O, Fut, S, E, F, ATTEMPTS>
where
    O: FutureRetry<T, E, Fut, DelayState = S>,
    Fut: Future<Output = Result<T, E>>,
    F: FnOnce(O::Errors<ATTEMPTS>) -> T,
{
    type Output = T;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.get_unchecked_mut() };

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

    type Errors<const ATTEMPTS: usize> = O::Errors<ATTEMPTS>;

    type RetryResult<const ATTEMPTS: usize> = AsyncRetry<O, Fut, O::DelayState, E, ATTEMPTS>;

    type RetryOption<const ATTEMPTS: usize> = AsyncRetryOk<O, Fut, O::DelayState, E, ATTEMPTS>;

    type RetryValue<const ATTEMPTS: usize, F>
        = AsyncRetryOrElse<O, Fut, O::DelayState, E, F, ATTEMPTS>
    where
        F: FnOnce(Self::Errors<ATTEMPTS>) -> T;

    #[inline]
    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS> {
        let delay = O::delay_state();

        AsyncRetry::new(self, delay)
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS> {
        let delay = O::delay_state();

        AsyncRetryOk::new(self, delay)
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::RetryValue<ATTEMPTS, F>
    where
        F: FnOnce(Self::Errors<ATTEMPTS>) -> T,
    {
        let delay = O::delay_state();

        AsyncRetryOrElse::new(AsyncRetry::new(self, delay), fallback)
    }
}
