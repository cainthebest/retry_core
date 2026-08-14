#![no_std]

//! # Retry Core
//!
//! Retry fallible blocking and asynchronous operations
//!
//! `retry_core` exposes a single [`Retry`] trait. The implementation is selected
//! from the callable's return type:
//!
//! - `FnMut() -> Result<T, E>` for blocking operations.
//! - `FnMut() -> Fut` where `Fut: Future<Output = Result<T, E>>` for async
//!   operations.
//!
//! The crate is `no_std` and does not require `alloc`. Retry bookkeeping uses
//! fixed size inline storage.
//!
//! ## Quick start
//!
//! Zero argument functions can be retried directly:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! fn load() -> Result<u32, &'static str> {
//!     Ok(42)
//! }
//!
//! assert_eq!(load.retry::<3>(), Ok(42));
//! ```
//!
//! Async functions use the same API:
//!
//! ```rust,no_run
//! use retry_core::Retry;
//!
//! async fn load() -> Result<u32, &'static str> {
//!     Ok(42)
//! }
//!
//! async fn example() {
//!     assert_eq!(load.retry::<3>().await, Ok(42));
//! }
//! ```
//!
//! ## Adapting arguments and state
//!
//! A retry operation is called as `FnMut()`, so functions that require
//! arguments are adapted with a closure:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! fn load(id: u32) -> Result<u32, ()> {
//!     Ok(id)
//! }
//!
//! let id = 42;
//! assert_eq!((|| load(id)).retry::<3>(), Ok(42));
//! ```
//!
//! The same closure value is reused for every attempt, so blocking operations
//! can keep mutable state across calls:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let mut calls = 0;
//!
//! let result = (|| {
//!     calls += 1;
//!
//!     if calls == 3 {
//!         Ok(42)
//!     } else {
//!         Err(())
//!     }
//! })
//! .retry::<3>();
//!
//! assert_eq!(result, Ok(42));
//! assert_eq!(calls, 3);
//! ```
//!
//! For async operations, state that must live across an `.await` should be
//! owned by the returned future or accessed through an appropriate shared
//! handle. A useful pattern is to update closure state before creating the
//! future, then move a per attempt snapshot into it:
//!
//! ```rust,no_run
//! use retry_core::Retry;
//!
//! async fn example() {
//!     let mut calls = 0;
//!
//!     let result = (|| {
//!         calls += 1;
//!         let call = calls;
//!
//!         async move {
//!             if call == 3 {
//!                 Ok(42)
//!             } else {
//!                 Err(call)
//!             }
//!         }
//!     })
//!     .retry::<3>()
//!     .await;
//!
//!     assert_eq!(result, Ok(42));
//! }
//! ```
//!
//! ## Choosing a method
//!
//! | Method | Success | Exhausted attempts | Keeps errors |
//! |---|---|---|---|
//! | [`Retry::retry`] | `T` | `[E; ATTEMPTS]` | Yes |
//! | [`Retry::retry_ok`] | `Some(T)` | `None` | No |
//! | [`Retry::retry_or_else`] | `T` | result of fallback | Yes |
//!
//! In async mode, the same values are produced by the returned future.
//!
//! ### `retry`
//!
//! Use [`Retry::retry`] when every failure is useful:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let mut attempt = 0;
//!
//! let result = (|| -> Result<(), usize> {
//!     attempt += 1;
//!     Err(attempt)
//! })
//! .retry::<3>();
//!
//! assert_eq!(result, Err([1, 2, 3]));
//! ```
//!
//! ### `retry_ok`
//!
//! Use [`Retry::retry_ok`] when only success matters:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let result = (|| -> Result<u32, ()> {
//!     Err(())
//! })
//! .retry_ok::<3>();
//!
//! assert_eq!(result, None);
//! ```
//!
//! `retry_ok` does not retain an `[E; ATTEMPTS]` buffer.
//!
//! ### `retry_or_else`
//!
//! Use [`Retry::retry_or_else`] when exhaustion should produce a fallback value:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let value = (|| -> Result<u32, &'static str> {
//!     Err("failed")
//! })
//! .retry_or_else::<3, _>(|errors| {
//!     assert_eq!(errors, ["failed", "failed", "failed"]);
//!     0
//! });
//!
//! assert_eq!(value, 0);
//! ```
//!
//! ## Attempt semantics
//!
//! `ATTEMPTS` is the maximum **total number of operation calls**, not the
//! number of retries after an extra initial call.
//!
//! ```text
//! retry::<0>() -> 0 calls
//! retry::<1>() -> at most 1 call
//! retry::<3>() -> at most 3 calls
//! ```
//!
//! The first successful attempt completes the retry immediately.
//!
//! `ATTEMPTS == 0` is valid:
//!
//! | Method | Result when `ATTEMPTS == 0` |
//! |---|---|
//! | [`Retry::retry`] | `Err([])` |
//! | [`Retry::retry_ok`] | `None` |
//! | [`Retry::retry_or_else`] | fallback receives `[]` |
//!
//! The operation itself is never called in any of those cases. For async
//! `retry_or_else`, the fallback runs when the returned future is first polled.
//!
//! ## Storage and allocation
//!
//! [`Retry::retry`] and [`Retry::retry_or_else`] preserve errors in attempt
//! order using:
//!
//! ```text
//! [E; ATTEMPTS]
//! ```
//!
//! Errors are moved into the storage; `E` does not need to implement `Clone`.
//!
//! Because the storage is inline, the size of a blocking retry frame or async
//! retry future can grow significantly when either `E` or `ATTEMPTS` is large.
//! Prefer [`Retry::retry_ok`] when the individual errors are not needed.
//!
//! ## Async behavior
//!
//! Async attempts are **sequential**. A retry operation never has more than one
//! attempt future active at a time.
//!
//! - `Poll::Pending` keeps the current attempt active.
//! - `Poll::Ready(Ok(value))` completes the retry.
//! - `Poll::Ready(Err(error))` drops the completed attempt and allows the next
//!   attempt to be created.
//!
//! A pending attempt therefore does not start another attempt.
//!
//! ### Executor fairness
//!
//! Futures can fail immediately without ever returning `Poll::Pending`. With a
//! very large attempt limit, processing every immediately ready failure in one
//! `poll` could monopolize an executor thread.
//!
//! To avoid that, async retries currently use a ready failure budget. When
//! `ATTEMPTS > 64`, at most 64 immediately ready failures are processed in one
//! call to `poll`. The retry future then calls `wake_by_ref()`, returns
//! `Poll::Pending`, and continues on a later poll.
//!
//! This is an executor fairness mechanism, **not timed backoff**. It does not
//! sleep or wait for a duration, and the executor may poll the retry future
//! again immediately.
//!
//! The exact budget is an implementation detail and should not be used as a
//! timing or scheduling guarantee.
//!
//! ### Runtime independence
//!
//! Async retries use only `core::future::Future` and `core::task`. No specific
//! executor or timer runtime is required.
//!
//! ### Pinning and completion
//!
//! Async retry values are `!Unpin` because an active attempt future is kept in
//! pinned inline storage. Normal `.await` usage handles this automatically.
//!
//! After an async retry returns `Poll::Ready`, polling it again panics.
//!
//! Dropping an in progress retry drops the currently active attempt future and
//! any retained errors. Dropping an unfinished [`Retry::retry_or_else`] future
//! does not call its fallback.
//!
//! The fallback passed to [`Retry::retry_or_else`] is synchronous. In async
//! mode it runs inside the retry future's `poll` after the final failed attempt,
//! so expensive or blocking fallback work also blocks that executor thread.
//!
//! ## Retry policy
//!
//! `retry_core` does not provide timed retry policy such as:
//!
//! - delay;
//! - exponential or linear backoff;
//! - jitter;
//! - rate limiting;
//! - timeout handling.
//!
//! Blocking attempts may run back to back. Async attempts may also start
//! immediately after a ready failure, subject only to the executor fairness
//! behavior described above.
//!
//! If timing policy is needed, put it inside the operation/future being
//! retried.

use core::marker::PhantomData;

pub(crate) mod storage;

mod blocking;
mod future;

mod private {
    pub trait Sealed {}
}

/// Internal execution mode marker used by [`Retry`].
#[doc(hidden)]
pub trait RetryMode: private::Sealed {}

/// Internal marker for blocking operations.
#[doc(hidden)]
pub struct BlockingMode<T, E> {
    _output: PhantomData<fn() -> T>,
    _error: PhantomData<fn() -> E>,
}

/// Internal marker for asynchronous operations.
#[doc(hidden)]
pub struct FutureMode<T, E, Fut> {
    _output: PhantomData<fn() -> T>,
    _error: PhantomData<fn() -> E>,
    _future: PhantomData<fn() -> Fut>,
}

impl<T, E> private::Sealed for BlockingMode<T, E> {}
impl<T, E, Fut> private::Sealed for FutureMode<T, E, Fut> {}

impl<T, E> RetryMode for BlockingMode<T, E> {}
impl<T, E, Fut> RetryMode for FutureMode<T, E, Fut> {}

/// Retry a compatible blocking or asynchronous callable.
///
/// Implemented for:
///
/// - `FnMut() -> Result<T, E>`
/// - `FnMut() -> Fut` where `Fut: Future<Output = Result<T, E>>`
///
/// Zero argument functions can be used directly. Functions requiring
/// arguments or state can be adapted with a closure.
///
/// `ATTEMPTS` on each method is the maximum total number of calls to the
/// operation. See the crate level documentation for execution semantics,
/// async fairness behavior, and memory considerations.
pub trait Retry<Mode>: Sized
where
    Mode: RetryMode,
{
    /// The successful output type.
    type Output;

    /// The error type produced by one failed attempt.
    type Error;

    /// Error storage used when all attempts fail.
    ///
    /// The built in blocking and async implementations use
    /// `[Self::Error; ATTEMPTS]`.
    type Storage<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry`].
    ///
    /// Blocking mode returns `Result<Self::Output, Self::Storage<ATTEMPTS>>`.
    /// Async mode returns a future with that output.
    type Result<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry_ok`].
    ///
    /// Blocking mode returns `Option<Self::Output>`. Async mode returns a
    /// future with that output.
    type Option<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry_or_else`].
    ///
    /// Blocking mode returns [`Self::Output`] directly. Async mode returns a
    /// future with that output.
    type Value<const ATTEMPTS: usize, F>
    where
        F: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output;

    /// Retry until the first success or until all attempts fail.
    ///
    /// Returns the first successful output. If all `ATTEMPTS` calls fail,
    /// returns every error in attempt order.
    ///
    /// # Example
    ///
    /// ```rust
    /// use retry_core::Retry;
    ///
    /// let mut calls = 0;
    ///
    /// let result = (|| {
    ///     calls += 1;
    ///
    ///     if calls == 2 {
    ///         Ok(42)
    ///     } else {
    ///         Err(calls)
    ///     }
    /// })
    /// .retry::<3>();
    ///
    /// assert_eq!(result, Ok(42));
    /// ```
    ///
    /// With `ATTEMPTS == 0`, the operation is not called and the exhausted
    /// error storage is empty.
    fn retry<const ATTEMPTS: usize>(self) -> Self::Result<ATTEMPTS>;

    /// Retry until success while discarding failed errors.
    ///
    /// Returns `Some(value)` on the first success and `None` if every attempt
    /// fails.
    ///
    /// This method does not retain an `[E; ATTEMPTS]` error buffer.
    ///
    /// # Example
    ///
    /// ```rust
    /// use retry_core::Retry;
    ///
    /// let value = (|| -> Result<u32, ()> {
    ///     Ok(42)
    /// })
    /// .retry_ok::<3>();
    ///
    /// assert_eq!(value, Some(42));
    /// ```
    ///
    /// With `ATTEMPTS == 0`, the operation is not called and the result is
    /// `None`.
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::Option<ATTEMPTS>;

    /// Retry until success, then use `fallback` only if every attempt fails.
    ///
    /// `fallback` is called exactly once with all errors in attempt order. It
    /// is not called if an attempt succeeds.
    ///
    /// In async mode, the fallback itself is synchronous and executes inside
    /// the retry future's final `poll`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use retry_core::Retry;
    ///
    /// let value = (|| -> Result<u32, &'static str> {
    ///     Err("failed")
    /// })
    /// .retry_or_else::<3, _>(|errors| {
    ///     assert_eq!(errors, ["failed", "failed", "failed"]);
    ///     42
    /// });
    ///
    /// assert_eq!(value, 42);
    /// ```
    ///
    /// With `ATTEMPTS == 0`, the operation is not called and `fallback`
    /// receives empty error storage.
    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::Value<ATTEMPTS, F>
    where
        F: FnOnce(Self::Storage<ATTEMPTS>) -> Self::Output;
}