#![no_std]

//! # Retry Core
//!
//! Retry fallible blocking and asynchronous operations
//! with composable, allocation free retry policies.
//!
//! `retry_core` exposes a single [`Retry`] trait.
//! The implementation is selected from the callable's return type:
//!
//! | Mode     | Operation                                                   |
//! | -------- | ----------------------------------------------------------- |
//! | Blocking | `FnMut() -> Result<T, E>`                                   |
//! | Async    | `FnMut() -> Fut` where `Fut: Future<Output = Result<T, E>>` |
//!
//! Simple retries can be executed directly with [`Retry::retry`],
//! [`Retry::retry_ok`], or [`Retry::retry_or_else`].
//!
//! More advanced behavior is configured by using a retry policy with [`Retry::retry_policy`].
//!
//! The crate is `no_std`, does not require `alloc` and does not depend on an async runtime.
//!
//! ## Quick start
//!
//! Zero argument blocking functions can be retried directly:
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
//! Functions that take arguments can be retried by wrapping the call in a closure:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! fn load(id: u32) -> Result<u32, ()> {
//!     Ok(id)
//! }
//!
//! let id = 42;
//!
//! assert_eq!(
//!     (|| load(id)).retry::<3>(),
//!     Ok(42),
//! );
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
//! async fn load_id(id: u32) -> Result<u32, &'static str> {
//!     Ok(id)
//! }
//!
//! async fn example() {
//!     assert_eq!(load.retry::<3>().await, Ok(42));
//!
//!     let id = 42;
//!     assert_eq!((|| load_id(id)).retry::<3>().await, Ok(42));
//! }
//! ```
//!
//! ## Retry policy
//!
//! Retry behavior is configured through [`Retry::retry_policy`].
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let mut calls = 0;
//! let mut inspected = 0;
//! let mut delayed = 0;
//!
//! let result = (|| {
//!     calls += 1;
//!
//!     if calls == 3 {
//!         Ok(42)
//!     } else {
//!         Err(calls)
//!     }
//! })
//! .retry_policy()
//! .inspect_retry(|retry, error| {
//!     inspected += 1;
//!     assert_eq!(retry, *error);
//! })
//! .with_delay(|retry| {
//!     delayed += 1;
//!     assert!(retry < 3);
//! })
//! .retry::<5>();
//!
//! assert!(matches!(result, Ok(42)));
//! assert_eq!(calls, 3);
//! assert_eq!(inspected, 2);
//! assert_eq!(delayed, 2);
//! ```
//!
//! Policy adapters are deliberately unavailable directly on the operation.
//!
//! Entering a policy makes the distinction between executing a simple retry:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let operation = || Ok::<_, ()>(42);
//!
//! assert_eq!(operation.retry::<3>(), Ok(42));
//! ```
//!
//! and configuring retry behavior explicit:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let operation = || Ok::<_, ()>(42);
//!
//! let result = operation
//!     .retry_policy()
//!     .inspect_retry(|_, _| {})
//!     .with_delay(|_| {})
//!     .retry::<3>();
//!
//! assert!(matches!(result, Ok(42)));
//! ```
//!
//! ### `inspect_retry`
//!
//! [`RetryPolicy::inspect_retry`] runs a callback whenever another retry is about to occur.
//!
//! This is useful for:
//!
//! - logging
//! - tracing
//! - metrics
//! - counters
//! - diagnostics
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let mut calls = 0;
//! let mut retries = 0;
//!
//! let result = (|| {
//!     calls += 1;
//!
//!     if calls == 3 {
//!         Ok(42)
//!     } else {
//!         Err(calls)
//!     }
//! })
//! .retry_policy()
//! .inspect_retry(|retry, error| {
//!     retries += 1;
//!     assert_eq!(retry, *error);
//! })
//! .retry::<3>();
//!
//! assert!(matches!(result, Ok(42)));
//! assert_eq!(retries, 2);
//! ```
//!
//! The callback receives:
//!
//! | Argument | Value                                               |
//! | -------- | --------------------------------------------------- |
//! | `retry`  | Retry number, starting at `1`                       |
//! | `error`  | Shared reference to the error that caused the retry |
//!
//! The callback is only invoked when another attempt will be made.
//!
//! It is not called after a successful attempt or after the final failed attempt.
//!
//! Multiple `inspect_retry` adapters can be composed.
//! Their callbacks run in nested adapter order.
//!
//! ### `with_delay`
//!
//! [`RetryPolicy::with_delay`] inserts caller-provided work between failed attempts.
//!
//! The crate intentionally does not provide a clock, timer, backoff algorithm,
//! or runtime. The caller decides what a delay means.
//!
//! For blocking operations, the delay is a `FnMut(usize)`:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let mut calls = 0;
//! let mut delays = 0;
//!
//! let result = (|| {
//!     calls += 1;
//!
//!     if calls == 2 {
//!         Ok(42)
//!     } else {
//!         Err(())
//!     }
//! })
//! .retry_policy()
//! .with_delay(|retry| {
//!     delays += 1;
//!     assert_eq!(retry, 1);
//! })
//! .retry::<3>();
//!
//! assert!(matches!(result, Ok(42)));
//! assert_eq!(delays, 1);
//! ```
//!
//! A `std` application could use the callback to call `std::thread::sleep`.
//! Embedded code can use its own timing facilities.
//!
//! For async operations, the callback returns a future whose output is `()`:
//!
//! ```rust,no_run
//! use core::future::ready;
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
//!             if call == 2 {
//!                 Ok(42)
//!             } else {
//!                 Err(())
//!             }
//!         }
//!     })
//!     .retry_policy()
//!     .with_delay(|retry| {
//!         assert_eq!(retry, 1);
//!         ready(())
//!     })
//!     .retry::<3>()
//!     .await;
//!
//!     assert!(matches!(result, Ok(42)));
//! }
//! ```
//!
//! Real applications can return a timer future supplied by their executor, platform, HAL, or another crate.
//!
//! Multiple delay adapters may be composed.
//! They run sequentially in nested adapter order.
//! Async delay adapters may return different concrete future types.
//!
//! ## Choosing a method
//!
//! | Method                   | Success   | Exhausted attempts | Keeps errors |
//! | ------------------------ | --------- | ------------------ | ------------ |
//! | [`Retry::retry`]         | `T`       | `[E; ATTEMPTS]`    | Yes          |
//! | [`Retry::retry_ok`]      | `Some(T)` | `None`             | No           |
//! | [`Retry::retry_or_else`] | `T`       | result of fallback | Yes          |
//!
//! A [`RetryPolicy`] exposes the same three operations.
//!
//! Async mode produces the same logical outputs through a returned future.
//!
//! ## Attempt semantics
//!
//! `ATTEMPTS` is the maximum **total number of operation calls**, not the number
//! of retries after an additional initial call.
//!
//! ```text
//! retry::<0>() -> 0 calls
//! retry::<1>() -> at most 1 call
//! retry::<3>() -> at most 3 calls
//! ```
//!
//! A retry index represents the transition to the next attempt:
//!
//! ```text
//! attempt 1 fails -> retry index 1 -> attempt 2
//! attempt 2 fails -> retry index 2 -> attempt 3
//! attempt 3 fails -> retry index 3 -> attempt 4
//! ```
//!
//! `inspect_retry` and `with_delay` receive this retry index.
//!
//! The first successful attempt completes the retry immediately.
//!
//! `ATTEMPTS == 0` is valid.
//!
//! For a direct retry:
//!
//! | Method                   | Result when `ATTEMPTS == 0` |
//! | ------------------------ | --------------------------- |
//! | [`Retry::retry`]         | `Err([])`                   |
//! | [`Retry::retry_ok`]      | `None`                      |
//! | [`Retry::retry_or_else`] | fallback receives `[]`      |
//!
//! The operation itself is never called.
//!
//! In async `retry_or_else`, the fallback runs when the returned future is
//! polled and determines that no operation attempts are available.
//!
//! ## Storage and allocation
//!
//! Error storage is fixed size and inline.
//!
//! A retry retaining failures reserves capacity for:
//!
//! ```text
//! ATTEMPTS * size_of::<E>()
//! ```
//!
//! plus small bookkeeping overhead for the internal error buffer.
//!
//! Errors are moved into storage, `E` does not need to implement `Clone`.
//!
//! Policy adapters also store their closures and state inline as concrete generic fields.
//!
//! Async delay futures are stored inline as concrete future types.
//! Multiple heterogeneous delay adapters do not require boxing.
//!
//! Consequently, the size of a blocking retry frame or async retry future can
//! grow significantly when:
//!
//! - `E` is large
//! - `ATTEMPTS` is large
//! - the operation future is large
//! - adapter closures capture large values
//! - async delay futures are large
//! - many adapters are composed
//!
//! Prefer [`Retry::retry_ok`] when individual errors are not required.
//!
//! ## Async behavior
//!
//! Async operation attempts are sequential.
//!
//! A retry never starts the next operation while the current operation future is pending.
//!
//! When async delay adapters are present, their futures are also polled
//! sequentially. The next operation is not created until the entire delay chain
//! has completed.
//!
//! No operation attempt and its successor are active concurrently.
//!
//! ### Executor fairness
//!
//! Operation futures and delay futures can both complete immediately without
//! ever returning `Poll::Pending`.
//!
//! With a very large attempt limit, processing every immediately ready retry in
//! one call to `poll` could monopolize an executor thread.
//!
//! To avoid this, async retries currently use a "ready retry" budget.
//!
//! After `64` completely ready retry transitions in one call to `poll`, the retry future:
//!
//! 1.  calls `wake_by_ref()`;
//! 2.  returns `Poll::Pending`;
//! 3.  continues on a later poll.
//!
//! A naturally pending operation or delay already yields to the executor and
//! therefore does not need this artificial yield.
//!
//! This fairness mechanism is **not timed backoff**. It does not sleep, wait for
//! a duration, or guarantee when the next poll occurs.
//!
//! The exact "ready retry" budget is an implementation detail and must not be
//! used as a timing or scheduling guarantee.
//!
//! ### Pinning and completion
//!
//! Async retry values are `!Unpin` because active operation and delay futures
//! can be retained in pinned inline storage.
//!
//! Normal `.await` usage handles this automatically.
//!
//! After an async retry returns `Poll::Ready`, polling it again panics.
//!
//! Dropping an in progress retry drops:
//!
//! - the currently active operation future, if any
//! - the currently active delay future, if any
//! - retained errors
//! - policy adapter state
//!
//! Dropping an unfinished `retry_or_else` future does not execute its fallback.
//!
//! The fallback passed to `retry_or_else` is synchronous. In async mode it runs
//! inside the retry future's `poll`, so expensive or blocking fallback work
//! also blocks that executor thread.
//!
//! ## Timing and backoff policy
//!
//! `retry_core` intentionally does not implement a particular timing strategy.
//!
//! It does not provide built-in:
//!
//! - fixed delay
//! - linear backoff
//! - exponential backoff
//! - jitter
//! - randomness
//! - rate limiting
//! - timeout handling
//!
//! Instead, [`RetryPolicy::with_delay`] is the integration point for external timing policy.
//!
//! This keeps the crate `no_std`, runtime independent, and usable with blocking,
//! async, embedded, and custom execution environments.

use {
    crate::{adapter::RetryPolicy, mode::RetryMode},
    core::marker::PhantomData,
};

pub(crate) mod mode;

pub(crate) mod adapter;
pub(crate) mod storage;

mod blocking;
mod future;

/// Retries a fallible blocking or asynchronous operation.
///
/// `Retry` is implemented automatically for compatible callable types:
///
/// - `FnMut() -> Result<T, E>` for blocking operations;
/// - `FnMut() -> Fut` where `Fut: Future<Output = Result<T, E>>` for
///   asynchronous operations.
///
/// The const generic `ATTEMPTS` used by the terminal methods is the maximum
/// total number of calls to the operation.
///
/// # Direct retries
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
///         Err(())
///     }
/// })
/// .retry::<3>();
///
/// assert_eq!(result, Ok(42));
/// ```
///
/// # Retry policies
///
/// Call [`Retry::retry_policy`] before adding delay or inspection behavior:
///
/// ```rust
/// use retry_core::Retry;
///
/// let operation = || Ok::<_, ()>(42);
///
/// let result = operation
///     .retry_policy()
///     .with_delay(|_| {})
///     .inspect_retry(|_, _| {})
///     .retry::<3>();
///
/// assert!(matches!(result, Ok(42)));
/// ```
pub trait Retry<Mode>: Sized
where
    Mode: RetryMode,
{
    /// The successful output produced by the operation.
    type Output;

    /// The error produced by a failed operation attempt.
    type Error;

    /// Return type of [`Retry::retry`].
    ///
    /// Blocking operations produce a `Result` directly.
    /// Async operations produce a future resolving to the corresponding `Result`.
    type RetryResult<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry_ok`].
    ///
    /// Blocking operations produce an `Option` directly. Async operations
    /// produce a future resolving to the corresponding `Option`.
    type RetryOption<const ATTEMPTS: usize>;

    /// Return type of [`Retry::retry_or_else`].
    ///
    /// Blocking operations produce [`Retry::Output`](Self::Output) directly.
    /// Async operations produce a future resolving to that value.
    type RetryValue<const ATTEMPTS: usize, F>
    where
        F: FnOnce([Self::Error; ATTEMPTS]) -> Self::Output;

    /// Retries the operation up to `ATTEMPTS` total calls.
    ///
    /// The first successful attempt returns immediately.
    ///
    /// If all permitted attempts fail, the retained errors are returned in
    /// attempt order.
    ///
    /// `ATTEMPTS == 0` is valid and does not call the operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use retry_core::Retry;
    ///
    /// let mut attempt = 0;
    ///
    /// let result = (|| -> Result<(), usize> {
    ///     attempt += 1;
    ///     Err(attempt)
    /// })
    /// .retry::<3>();
    ///
    /// assert_eq!(result, Err([1, 2, 3]));
    /// ```
    fn retry<const ATTEMPTS: usize>(self) -> Self::RetryResult<ATTEMPTS>;

    /// Retries the operation while discarding failed errors.
    ///
    /// Returns the first successful value as `Some(T)`, or `None` if no
    /// successful attempt occurs.
    ///
    /// Unlike [`Retry::retry`], this method does not retain an error buffer.
    ///
    /// `ATTEMPTS == 0` returns `None` without calling the operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use retry_core::Retry;
    ///
    /// let result = (|| -> Result<u32, ()> {
    ///     Err(())
    /// })
    /// .retry_ok::<3>();
    ///
    /// assert_eq!(result, None);
    /// ```
    fn retry_ok<const ATTEMPTS: usize>(self) -> Self::RetryOption<ATTEMPTS>;

    /// Retries the operation and invokes `fallback` if retrying terminates
    /// without success.
    ///
    /// The fallback receives the retained error storage and is called exactly once.
    ///
    /// In async mode the fallback itself is synchronous and executes inside
    /// the retry future's `poll`.
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
    ///     assert_eq!(
    ///         errors,
    ///         ["failed", "failed", "failed"],
    ///     );
    ///
    ///     0
    /// });
    ///
    /// assert_eq!(value, 0);
    /// ```
    fn retry_or_else<const ATTEMPTS: usize, F>(self, fallback: F) -> Self::RetryValue<ATTEMPTS, F>
    where
        F: FnOnce([Self::Error; ATTEMPTS]) -> Self::Output;

    /// Begins configuration of a retry policy.
    ///
    /// Policy adapters are only available after calling this method.
    ///
    /// A policy can compose:
    ///
    /// - [`RetryPolicy::with_delay`] to run caller-provided work between attempts
    /// - [`RetryPolicy::inspect_retry`] to observe retries for logging, tracing, metrics, or other side effects.
    ///
    /// Adapters may be repeated and composed in arbitrary order.
    ///
    /// Calling this method does not execute the operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use retry_core::Retry;
    ///
    /// let operation = || Ok::<_, ()>(42);
    ///
    /// let result = operation
    ///     .retry_policy()
    ///     .with_delay(|_| {})
    ///     .inspect_retry(|_, _| {})
    ///     .retry::<5>();
    ///
    /// assert!(matches!(result, Ok(42)));
    /// ```
    #[inline]
    fn retry_policy(self) -> RetryPolicy<Self, Mode> {
        RetryPolicy {
            operation: self,
            _mode: PhantomData,
        }
    }
}
