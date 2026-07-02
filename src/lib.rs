#![no_std]
#![deny(unsafe_op_in_unsafe_fn)]

//! `no_std` retry helper for fallible blocking and async operations.
//!
//! This crate adds a small [`Retry`] extension trait to zero argument
//! operations that return [`Result`]. It works with both blocking operations and
//! async operations, does not allocate, and stores all failed attempt errors in a
//! fixed size array when every attempt fails.
//!
//! # Quick start
//!
//! Import [`Retry`] and call one of the retry methods on an operation.
//!
//! A no argument function that already returns [`Result`] can be retried
//! directly:
//!
//! ```
//! use retry_core::Retry;
//!
//! fn operation() -> Result<&'static str, &'static str> {
//!     Ok("ready")
//! }
//!
//! let value = operation.retry::<3>();
//!
//! assert_eq!(value, Ok("ready"));
//! ```
//!
//! A closure can also be retried directly:
//!
//! ```
//! use retry_core::Retry;
//!
//! let mut failures_left = 2;
//!
//! let result = (|| {
//!     if failures_left == 0 {
//!         Ok("connected")
//!     } else {
//!         failures_left -= 1;
//!         Err("not ready")
//!     }
//! })
//! .retry::<5>();
//!
//! assert_eq!(result, Ok("connected"));
//! assert_eq!(failures_left, 0);
//! ```
//!
//! Wrap a function call in a closure when the function needs arguments, borrows
//! values, captures state, or needs to create a fresh async future on every
//! attempt:
//!
//! ```
//! use retry_core::Retry;
//!
//! fn fetch_user(user_id: u64) -> Result<&'static str, &'static str> {
//!     if user_id == 42 {
//!         Ok("user")
//!     } else {
//!         Err("missing")
//!     }
//! }
//!
//! let user_id = 42;
//! let value = (|| fetch_user(user_id)).retry::<3>();
//!
//! assert_eq!(value, Ok("user"));
//! ```
//!
//! # What is an attempt?
//!
//! The const generic parameter is the total number of attempts, not the number
//! of retries after the first attempt. For example, `retry::<3>()` may call the
//! operation up to three times total.
//!
//! `retry::<0>()` is allowed. It never calls the operation and immediately
//! returns an empty error array:
//!
//! ```
//! use retry_core::Retry;
//!
//! let mut calls = 0;
//! let result: Result<(), [u8; 0]> = (|| {
//!     calls += 1;
//!     Ok(())
//! })
//! .retry::<0>();
//!
//! assert_eq!(result, Err([]));
//! assert_eq!(calls, 0);
//! ```
//!
//! # Choosing a retry method
//!
//! Use [`Retry::retry`] when failed attempt errors matter:
//!
//! ```
//! use retry_core::Retry;
//!
//! let mut calls = 0;
//!
//! let result: Result<(), [usize; 3]> = (|| {
//!     calls += 1;
//!     Err(calls)
//! })
//! .retry::<3>();
//!
//! assert_eq!(result, Err([1, 2, 3]));
//! ```
//!
//! Use [`Retry::retry_ok`] when only success or failure matters and individual
//! errors can be discarded:
//!
//! ```
//! use retry_core::Retry;
//!
//! let value = (|| Err::<usize, _>("offline")).retry_ok::<2>();
//!
//! assert_eq!(value, None);
//! ```
//!
//! Use [`Retry::retry_or_else`] when total failure should produce a fallback
//! value:
//!
//! ```
//! use retry_core::Retry;
//!
//! let value = (|| Err::<usize, _>(1)).retry_or_else::<3, _>(|errors| {
//!     errors.into_iter().sum()
//! });
//!
//! assert_eq!(value, 3);
//! ```
//!
//! # Async operations
//!
//! Async operations use the same methods. The operation must create a fresh
//! future each time it is called, which usually means wrapping the async call in
//! a closure.
//!
//! ```
//! use retry_core::Retry;
//!
//! async fn fetch() -> Result<&'static str, &'static str> {
//!     Ok("body")
//! }
//!
//! # async fn example() {
//! let body = (|| fetch()).retry::<3>().await;
//!
//! assert_eq!(body, Ok("body"));
//! # }
//! ```
//!
//! Async functions with arguments follow the same closure pattern:
//!
//! ```
//! use retry_core::Retry;
//!
//! async fn fetch_user(user_id: u64) -> Result<&'static str, &'static str> {
//!     if user_id == 42 {
//!         Ok("user")
//!     } else {
//!         Err("missing")
//!     }
//! }
//!
//! # async fn example() {
//! let user_id = 42;
//! let user = (|| fetch_user(user_id)).retry::<3>().await;
//!
//! assert_eq!(user, Ok("user"));
//! # }
//! ```
//!
//! Async `retry_ok` and `retry_or_else` are also available:
//!
//! ```
//! use retry_core::Retry;
//!
//! async fn maybe_ready() -> Result<&'static str, &'static str> {
//!     Err("not ready")
//! }
//!
//! # async fn example() {
//! let optional = (|| maybe_ready()).retry_ok::<2>().await;
//! let fallback = (|| maybe_ready())
//!     .retry_or_else::<2, _>(|errors| errors[0])
//!     .await;
//!
//! assert_eq!(optional, None);
//! assert_eq!(fallback, "not ready");
//! # }
//! ```

#[cfg(test)]
extern crate std;

use core::{future::Future, result::Result};

/// Extension trait for retrying fallible operations.
///
/// This trait is implemented for operations with one of these shapes:
///
/// - blocking: `FnMut() -> Result<T, E>`;
/// - async: `FnMut() -> Fut` where `Fut: Future<Output = Result<T, E>>`.
///
/// In practice, that means a retryable operation is usually either a
/// no argument function that returns [`Result`] or a closure that calls your real
/// function with the arguments it needs.
///
/// `Mode` is an implementation detail used to distinguish blocking operations
/// from async operations while keeping the same method names for both.
///
/// # Attempts
///
/// The const generic parameter on the retry methods is the total number of
/// attempts. `retry::<0>()` never calls the operation.
///
/// # Failure errors
///
/// When all attempts fail, [`Retry::retry`] returns every failed attempt error in
/// attempt order as a fixed size array.
///
/// # Examples
///
/// Retry a no argument function directly:
///
/// ```
/// use retry_core::Retry;
///
/// fn operation() -> Result<&'static str, &'static str> {
///     Ok("ok")
/// }
///
/// assert_eq!(operation.retry::<3>(), Ok("ok"));
/// ```
///
/// Retry a function call with arguments by wrapping it in a closure:
///
/// ```
/// use retry_core::Retry;
///
/// fn parse_port(port: &str) -> Result<u16, core::num::ParseIntError> {
///     port.parse()
/// }
///
/// let port = "8080";
/// let parsed = (|| parse_port(port)).retry::<2>();
///
/// assert_eq!(parsed, Ok(8080));
/// ```
pub trait Retry<Mode>: Sized {
    /// Successful value produced by one attempt.
    type Output;

    /// Error value produced by one failed attempt.
    type Error;

    /// Errors collected after all attempts fail.
    type AttemptErrors<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry`].
    type RetryResult<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry_ok`].
    type RetryOption<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry_or_else`].
    type RetryOrElse<const ATTEMPTS: usize, F>
    where
        F: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;

    /// Run the operation up to `ATTEMPTS` times.
    ///
    /// Returns the first successful value, or all failed attempt errors if every
    /// attempt fails.
    ///
    /// This is the most informative retry method because it preserves every
    /// error produced by failed attempts.
    ///
    /// # Examples
    ///
    /// Call `.retry()` directly on a no argument operation that returns
    /// [`Result`]:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// fn operation() -> Result<&'static str, &'static str> {
    ///     Ok("ok")
    /// }
    ///
    /// let value = operation.retry::<3>();
    ///
    /// assert_eq!(value, Ok("ok"));
    /// ```
    ///
    /// Wrap a function call in a closure when it needs arguments or captures:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// fn operation(input: u8) -> Result<u8, &'static str> {
    ///     input.checked_add(1).ok_or("overflow")
    /// }
    ///
    /// let input = 41;
    /// let result = (|| operation(input)).retry::<2>();
    ///
    /// assert_eq!(result, Ok(42));
    /// ```
    ///
    /// Closures may mutate captured state because retry operations are `FnMut`:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// let mut calls = 0;
    ///
    /// let result = (|| {
    ///     calls += 1;
    ///
    ///     if calls == 2 {
    ///         Ok("ready")
    ///     } else {
    ///         Err("try again")
    ///     }
    /// })
    /// .retry::<3>();
    ///
    /// assert_eq!(result, Ok("ready"));
    /// assert_eq!(calls, 2);
    /// ```
    ///
    /// If every attempt fails, every failed attempt error is returned in order:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// let result = (|| Err::<(), _>("failed")).retry::<2>();
    ///
    /// assert_eq!(result, Err(["failed", "failed"]));
    /// ```
    ///
    /// Async operations use the same method and are awaited:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// async fn operation() -> Result<&'static str, &'static str> {
    ///     Ok("ok")
    /// }
    ///
    /// # async fn example() {
    /// let value = (|| operation()).retry::<3>().await;
    ///
    /// assert_eq!(value, Ok("ok"));
    /// # }
    /// ```
    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS>;

    /// Run the operation up to `ATTEMPTS` times and discard failed attempt errors.
    ///
    /// Returns the first successful value, or `None` if every attempt fails.
    ///
    /// Use this when the caller only needs to know whether the operation ever
    /// succeeded.
    ///
    /// # Examples
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// let result = (|| Err::<(), _>("failed")).retry_ok::<2>();
    ///
    /// assert_eq!(result, None);
    /// ```
    ///
    /// `retry_ok` still stops at the first success:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// let mut calls = 0;
    ///
    /// let result = (|| {
    ///     calls += 1;
    ///
    ///     if calls == 3 {
    ///         Ok("ok")
    ///     } else {
    ///         Err("not yet")
    ///     }
    /// })
    /// .retry_ok::<5>();
    ///
    /// assert_eq!(result, Some("ok"));
    /// assert_eq!(calls, 3);
    /// ```
    ///
    /// Async operations are supported as well:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// async fn operation() -> Result<&'static str, &'static str> {
    ///     Err("offline")
    /// }
    ///
    /// # async fn example() {
    /// let result = (|| operation()).retry_ok::<2>().await;
    ///
    /// assert_eq!(result, None);
    /// # }
    /// ```
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS>;

    /// Run the operation up to `ATTEMPTS` times and call `fallback` if every
    /// attempt fails.
    ///
    /// The fallback receives all failed attempt errors in attempt order and must
    /// produce the same successful output type as the operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// let value = (|| Err::<usize, _>(2)).retry_or_else::<3, _>(|errors| {
    ///     errors.into_iter().sum()
    /// });
    ///
    /// assert_eq!(value, 6);
    /// ```
    ///
    /// The fallback is not called if an attempt succeeds:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// let mut fallback_called = false;
    ///
    /// let value = (|| Ok::<_, &'static str>("ok")).retry_or_else::<3, _>(|_| {
    ///     fallback_called = true;
    ///     "fallback"
    /// });
    ///
    /// assert_eq!(value, "ok");
    /// assert!(!fallback_called);
    /// ```
    ///
    /// Async operations can use a fallback too:
    ///
    /// ```
    /// use retry_core::Retry;
    ///
    /// async fn operation() -> Result<usize, usize> {
    ///     Err(10)
    /// }
    ///
    /// # async fn example() {
    /// let value = (|| operation())
    ///     .retry_or_else::<2, _>(|errors| errors.into_iter().sum())
    ///     .await;
    ///
    /// assert_eq!(value, 20);
    /// # }
    /// ```
    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::RetryOrElse<ATTEMPTS, F>
    where
        F: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;
}

impl<F, T, E> Retry<sealed::BlockingMode<T, E>> for F
where
    F: FnMut() -> Result<T, E>,
{
    type Output = T;
    type Error = E;
    type AttemptErrors<const ATTEMPTS: usize> = [E; ATTEMPTS];

    type RetryResult<const ATTEMPTS: usize> = Result<T, Self::AttemptErrors<ATTEMPTS>>;
    type RetryOption<const ATTEMPTS: usize> = Option<T>;

    type RetryOrElse<const ATTEMPTS: usize, G>
        = T
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;

    #[inline]
    fn retry<const ATTEMPTS: usize>(mut self) -> Self::RetryResult<ATTEMPTS> {
        let mut errors = sealed::AttemptErrorBuffer::<E, ATTEMPTS>::new();

        while !errors.is_full() {
            match self() {
                Ok(value) => return Ok(value),
                Err(error) => errors.push(error),
            }
        }

        Err(errors.into_full_array())
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(mut self) -> Self::RetryOption<ATTEMPTS> {
        let mut attempts = 0;

        while attempts < ATTEMPTS {
            match self() {
                Ok(value) => return Some(value),
                Err(_) => attempts += 1,
            }
        }

        None
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, G>(self, fallback: G) -> Self::RetryOrElse<ATTEMPTS, G>
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output,
    {
        match self.retry::<ATTEMPTS>() {
            Ok(value) => value,
            Err(errors) => fallback(errors),
        }
    }
}

impl<F, T, E, Fut> Retry<sealed::AsyncMode<T, E, Fut>> for F
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    type Output = T;
    type Error = E;
    type AttemptErrors<const ATTEMPTS: usize> = [E; ATTEMPTS];

    type RetryResult<const ATTEMPTS: usize> = sealed::AsyncRetry<F, Fut, E, ATTEMPTS>;
    type RetryOption<const ATTEMPTS: usize> = sealed::AsyncRetryOk<F, Fut, ATTEMPTS>;

    type RetryOrElse<const ATTEMPTS: usize, G>
        = sealed::AsyncRetryOrElse<F, Fut, E, G, ATTEMPTS>
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output;

    #[inline]
    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS> {
        sealed::AsyncRetry::new(self)
    }

    #[inline]
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS> {
        sealed::AsyncRetryOk::new(self)
    }

    #[inline]
    fn retry_or_else<const ATTEMPTS: usize, G>(self, fallback: G) -> Self::RetryOrElse<ATTEMPTS, G>
    where
        G: FnOnce(Self::AttemptErrors<ATTEMPTS>) -> Self::Output,
    {
        sealed::AsyncRetryOrElse::new(self, fallback)
    }
}

/// Implementation details for [`Retry`].
///
/// This module is public only because its marker and future types appear in
/// public associated types. The contents are not intended to be named directly.
#[doc(hidden)]
pub mod sealed {
    use core::{
        future::Future,
        marker::{PhantomData, PhantomPinned},
        mem::MaybeUninit,
        pin::Pin,
        result::Result,
        task::{Context, Poll},
    };

    /// Marker type for blocking retry operations.
    #[doc(hidden)]
    pub struct BlockingMode<T, E> {
        _output: PhantomData<fn() -> T>,
        _error: PhantomData<fn() -> E>,
    }

    /// Marker type for async retry operations.
    #[doc(hidden)]
    pub struct AsyncMode<T, E, Fut> {
        _output: PhantomData<fn() -> T>,
        _error: PhantomData<fn() -> E>,
        _future: PhantomData<fn() -> Fut>,
    }

    /// Append only storage for failed attempts.
    ///
    /// # Invariants
    ///
    /// - entries `0..len` are initialized;
    /// - entries `len..ATTEMPTS` are uninitialized;
    /// - initialized entries are dropped exactly once.
    #[doc(hidden)]
    pub(super) struct AttemptErrorBuffer<E, const ATTEMPTS: usize> {
        values: [MaybeUninit<E>; ATTEMPTS],
        len: usize,
    }

    impl<E, const ATTEMPTS: usize> AttemptErrorBuffer<E, ATTEMPTS> {
        #[inline]
        pub(super) fn new() -> Self {
            Self {
                values: core::array::from_fn(|_| MaybeUninit::uninit()),
                len: 0,
            }
        }

        #[inline]
        pub(super) fn is_full(&self) -> bool {
            self.len == ATTEMPTS
        }

        #[inline]
        pub(super) fn push(&mut self, error: E) {
            assert!(self.len < ATTEMPTS, "attempt error buffer is full");

            self.values[self.len].write(error);
            self.len += 1;
        }

        #[inline]
        pub(super) fn into_full_array(mut self) -> [E; ATTEMPTS] {
            let errors = self.take_full_array();
            self.len = 0;
            errors
        }

        #[inline]
        pub(super) fn take_full_array(&mut self) -> [E; ATTEMPTS] {
            assert_eq!(
                self.len, ATTEMPTS,
                "attempt error buffer must be full before conversion"
            );

            let errors = core::array::from_fn(|index| {
                // SAFETY:
                // The assertion above guarantees every entry is initialized. Each
                // entry is read exactly once, and `len` is reset below so `Drop`
                // will not drop moved out entries.
                unsafe { self.values[index].assume_init_read() }
            });

            // The values were moved into `errors`, prevent `Drop` from dropping them.
            self.len = 0;

            errors
        }
    }

    impl<E, const ATTEMPTS: usize> Default for AttemptErrorBuffer<E, ATTEMPTS> {
        #[inline]
        fn default() -> Self {
            Self::new()
        }
    }

    impl<E, const ATTEMPTS: usize> Drop for AttemptErrorBuffer<E, ATTEMPTS> {
        fn drop(&mut self) {
            for index in 0..self.len {
                // SAFETY:
                // Every entry below `len` is initialized and has not been moved out.
                unsafe {
                    self.values[index].assume_init_drop();
                }
            }
        }
    }

    #[derive(Clone, Copy, PartialEq, Eq)]
    #[repr(u8)]
    enum FutureSlotState {
        Empty,
        Active,
        Complete,
    }

    /// Storage for one in flight future.
    ///
    /// # Invariants
    ///
    /// - `Empty` means `future` is uninitialized;
    /// - `Active` means `future` is initialized;
    /// - `Complete` means `future` is uninitialized and the slot is complete;
    /// - an active pending future is never moved after being polled;
    /// - an initialized future is dropped exactly once.
    #[doc(hidden)]
    struct FutureSlot<Fut> {
        future: MaybeUninit<Fut>,
        state: FutureSlotState,
    }

    impl<Fut> FutureSlot<Fut> {
        #[inline]
        fn new() -> Self {
            Self {
                future: MaybeUninit::uninit(),
                state: FutureSlotState::Empty,
            }
        }

        #[inline]
        fn is_complete(&self) -> bool {
            self.state == FutureSlotState::Complete
        }

        #[inline]
        fn ensure_active(&mut self, future: impl FnOnce() -> Fut) {
            if self.state == FutureSlotState::Empty {
                self.future.write(future());
                self.state = FutureSlotState::Active;
            }
        }

        #[inline]
        fn complete(&mut self) {
            match self.state {
                FutureSlotState::Empty => {
                    self.state = FutureSlotState::Complete;
                }

                FutureSlotState::Active => {
                    self.drop_active_future_and_set(FutureSlotState::Complete);
                }

                FutureSlotState::Complete => {}
            }
        }

        #[inline]
        fn clear_ready_future(&mut self) {
            if self.state == FutureSlotState::Active {
                self.drop_active_future_and_set(FutureSlotState::Empty);
            }
        }

        #[inline]
        fn poll_result<T, E>(&mut self, cx: &mut Context<'_>) -> Poll<Result<T, E>>
        where
            Fut: Future<Output = Result<T, E>>,
        {
            assert!(
                self.state == FutureSlotState::Active,
                "future slot must be active before polling"
            );

            // SAFETY:
            // `Active` means `future` is initialized. The owning retry future is
            // pinned before polling and is `!Unpin`, so this active future will not
            // be moved after being polled.
            let future = unsafe { Pin::new_unchecked(self.future.assume_init_mut()) };

            future.poll(cx)
        }

        #[inline]
        fn drop_active_future_and_set(&mut self, next_state: FutureSlotState) {
            assert!(self.state == FutureSlotState::Active);

            // Set the new state before dropping. If `Fut::drop` panics, `Drop` for
            // `FutureSlot` will not double drop the future during unwinding.
            self.state = next_state;

            // SAFETY:
            // This method is called only when the previous state was `Active`.
            unsafe {
                self.future.assume_init_drop();
            }
        }
    }

    impl<Fut> Default for FutureSlot<Fut> {
        #[inline]
        fn default() -> Self {
            Self::new()
        }
    }

    impl<Fut> Drop for FutureSlot<Fut> {
        fn drop(&mut self) {
            if self.state == FutureSlotState::Active {
                self.drop_active_future_and_set(FutureSlotState::Complete);
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn panic_polled_after_completion() -> ! {
        panic!("retry future polled after completion");
    }

    /// Future returned by async [`Retry::retry`](super::Retry::retry).
    #[doc(hidden)]
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
                if this.future.is_complete() {
                    panic_polled_after_completion();
                }

                if this.errors.is_full() {
                    this.future.complete();
                    return Poll::Ready(Err(this.errors.take_full_array()));
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

    /// Future returned by async [`Retry::retry_ok`](super::Retry::retry_ok).
    #[doc(hidden)]
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
                if this.future.is_complete() {
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

    /// Future returned by async [`Retry::retry_or_else`](super::Retry::retry_or_else).
    #[doc(hidden)]
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
                if this.future.is_complete() {
                    panic_polled_after_completion();
                }

                if this.errors.is_full() {
                    this.future.complete();
                    let errors = this.errors.take_full_array();

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
}

#[cfg(test)]
mod tests {
    use super::Retry;
    use core::{
        future::Future,
        pin::Pin,
        task::{Context, Poll},
    };
    use std::boxed::Box;

    fn block_on<F>(future: F) -> F::Output
    where
        F: Future,
    {
        let waker = std::task::Waker::noop();
        let mut cx = Context::from_waker(waker);
        let mut future = Box::pin(future);

        loop {
            match Pin::as_mut(&mut future).poll(&mut cx) {
                Poll::Ready(value) => return value,
                Poll::Pending => std::thread::yield_now(),
            }
        }
    }

    #[test]
    fn blocking_retry_returns_first_success() {
        let mut attempts = 0;

        let result = (|| {
            attempts += 1;

            if attempts == 3 {
                Ok("ok")
            } else {
                Err(attempts)
            }
        })
        .retry::<5>();

        assert_eq!(result, Ok("ok"));
        assert_eq!(attempts, 3);
    }

    #[test]
    fn blocking_retry_returns_all_errors_in_order() {
        let mut attempts = 0;

        let result: Result<(), [usize; 3]> = (|| {
            attempts += 1;
            Err(attempts)
        })
        .retry::<3>();

        assert_eq!(result, Err([1, 2, 3]));
        assert_eq!(attempts, 3);
    }

    #[test]
    fn blocking_retry_zero_attempts_never_calls_operation() {
        let mut attempts = 0;

        let result: Result<(), [usize; 0]> = (|| {
            attempts += 1;
            Ok(())
        })
        .retry::<0>();

        assert_eq!(result, Err([]));
        assert_eq!(attempts, 0);
    }

    #[test]
    fn blocking_retry_ok_discards_errors() {
        let mut attempts = 0;

        let result = (|| {
            attempts += 1;
            Err::<(), _>(attempts)
        })
        .retry_ok::<2>();

        assert_eq!(result, None);
        assert_eq!(attempts, 2);
    }

    #[test]
    fn blocking_retry_or_else_receives_all_errors() {
        let mut attempts = 0;

        let result = (|| {
            attempts += 1;
            Err::<usize, _>(attempts)
        })
        .retry_or_else::<3, _>(|errors| errors.iter().sum());

        assert_eq!(result, 6);
    }

    #[test]
    fn async_retry_returns_first_success() {
        let mut attempts = 0;

        let result = block_on(
            (|| {
                attempts += 1;
                let attempt = attempts;

                async move { if attempt == 3 { Ok("ok") } else { Err(attempt) } }
            })
            .retry::<5>(),
        );

        assert_eq!(result, Ok("ok"));
        assert_eq!(attempts, 3);
    }

    #[test]
    fn async_retry_returns_all_errors_in_order() {
        let mut attempts = 0;

        let result: Result<(), [usize; 3]> = block_on(
            (|| {
                attempts += 1;
                let attempt = attempts;

                async move { Err(attempt) }
            })
            .retry::<3>(),
        );

        assert_eq!(result, Err([1, 2, 3]));
        assert_eq!(attempts, 3);
    }

    #[test]
    fn async_retry_or_else_receives_all_errors() {
        let mut attempts = 0;

        let result = block_on(
            (|| {
                attempts += 1;
                let attempt = attempts;

                async move { Err::<usize, _>(attempt) }
            })
            .retry_or_else::<3, _>(|errors| errors.iter().sum()),
        );

        assert_eq!(result, 6);
    }

    #[test]
    fn blocking_retry_ok_returns_first_success() {
        let mut attempts = 0;

        let result = (|| {
            attempts += 1;

            if attempts == 2 {
                Ok("ok")
            } else {
                Err(attempts)
            }
        })
        .retry_ok::<4>();

        assert_eq!(result, Some("ok"));
        assert_eq!(attempts, 2);
    }

    #[test]
    fn blocking_retry_or_else_does_not_call_fallback_on_success() {
        let mut attempts = 0;
        let mut fallback_called = false;

        let result = (|| {
            attempts += 1;
            Ok::<_, usize>("ok")
        })
        .retry_or_else::<3, _>(|_| {
            fallback_called = true;
            "fallback"
        });

        assert_eq!(result, "ok");
        assert_eq!(attempts, 1);
        assert!(!fallback_called);
    }

    #[test]
    fn async_retry_zero_attempts_never_calls_operation() {
        let mut attempts = 0;

        let result: Result<(), [usize; 0]> = block_on(
            (|| {
                attempts += 1;
                async { Ok(()) }
            })
            .retry::<0>(),
        );

        assert_eq!(result, Err([]));
        assert_eq!(attempts, 0);
    }

    #[test]
    fn async_retry_ok_returns_first_success() {
        let mut attempts = 0;

        let result = block_on(
            (|| {
                attempts += 1;
                let attempt = attempts;

                async move { if attempt == 2 { Ok("ok") } else { Err(attempt) } }
            })
            .retry_ok::<4>(),
        );

        assert_eq!(result, Some("ok"));
        assert_eq!(attempts, 2);
    }

    #[test]
    fn async_retry_ok_returns_none_after_all_failures() {
        let mut attempts = 0;

        let result = block_on(
            (|| {
                attempts += 1;
                let attempt = attempts;

                async move { Err::<(), _>(attempt) }
            })
            .retry_ok::<3>(),
        );

        assert_eq!(result, None);
        assert_eq!(attempts, 3);
    }

    #[test]
    fn async_retry_or_else_does_not_call_fallback_on_success() {
        let mut attempts = 0;
        let mut fallback_called = false;

        let result = block_on(
            (|| {
                attempts += 1;
                async { Ok::<_, usize>("ok") }
            })
            .retry_or_else::<3, _>(|_| {
                fallback_called = true;
                "fallback"
            }),
        );

        assert_eq!(result, "ok");
        assert_eq!(attempts, 1);
        assert!(!fallback_called);
    }

    #[test]
    fn async_retry_panics_when_polled_after_completion() {
        let mut future = Box::pin((|| async { Ok::<_, usize>("ok") }).retry::<1>());
        let waker = std::task::Waker::noop();
        let mut cx = Context::from_waker(waker);

        assert_eq!(
            Pin::as_mut(&mut future).poll(&mut cx),
            Poll::Ready(Ok("ok"))
        );

        let second_poll = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _ = Pin::as_mut(&mut future).poll(&mut cx);
        }));

        assert!(second_poll.is_err());
    }
}
