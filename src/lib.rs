#![no_std]
//! A no_std retry library for synchronous and asynchronous fallible operations.
//!
//! # Overview
//!
//! This crate provides two traits:
//!
//! - [`Retry`] for **synchronous** closures returning `Result<T, E>`
//! - [`RetryFut`] for **asynchronous** closures returning `Future<Output = Result<T, E>>`
//!
//! Both traits add a `retry::<N>()` method that:
//!
//! - calls the closure up to `N` times,
//! - returns `Ok(T)` immediately on the first success,
//! - if all `N` attempts fail, returns `Err([Option<E>; N])` containing
//!   each captured error in order.
//!
//! Unused slots in the error array (after a successful attempt) remain `None`.

use core::{array, future::Future};

/// Retry a fallible **synchronous** operation up to a fixed number of times.
///
/// This trait is implemented for any `FnMut() -> Result<T, E>`.
///
/// The [`retry`](Retry::retry) method:
///
/// - Invokes the closure up to `N` times.
/// - Returns `Ok(T)` on the first successful attempt.
/// - If all `N` attempts fail, returns an `Err([Option<E>; N])` containing
///   each captured error in order.
///
/// Unused array slots (after a successful attempt) remain `None`.
///
/// ## Notes
///
/// - `N` may be zero. In that case, the closure is never called and an
///   empty error array is returned.
pub trait Retry<T, E> {
    /// Retry the operation at most `N` times.
    ///
    /// See the trait-level docs for details and examples.
    fn retry<const N: usize>(self) -> Result<T, [Option<E>; N]>;
}

impl<T, E, F> Retry<T, E> for F
where
    F: FnMut() -> Result<T, E>,
{
    #[inline]
    fn retry<const N: usize>(mut self) -> Result<T, [Option<E>; N]> {
        let mut errors: [Option<E>; N] = array::from_fn(|_| None);

        for slot in &mut errors {
            match self() {
                Ok(value) => return Ok(value),
                Err(err) => *slot = Some(err),
            }
        }

        Err(errors)
    }
}

/// Retry a fallible **asynchronous** operation up to a fixed number of times.
///
/// This trait is implemented for any `FnMut() -> Fut` where
/// `Fut: Future<Output = Result<T, E>>`.
///
/// The [`retry`](RetryFut::retry) method:
///
/// - Builds a future that will invoke the closure up to `N` times.
/// - Returns `Ok(T)` on the first successful awaited attempt.
/// - If all `N` attempts fail, returns `Err([Option<E>; N])` with the
///   captured errors.
///
/// Unused array slots (after a successful attempt) remain `None`.
///
/// ## Notes
///
/// - `N` may be zero. In that case, the returned future will immediately
///   resolve to `Err([])` without calling the closure.

pub trait RetryFut<T, E> {
    /// Build a future that retries the asynchronous operation at most `N` times.
    ///
    /// See the trait-level docs for details and examples.
    fn retry<const N: usize>(self) -> impl Future<Output = Result<T, [Option<E>; N]>>;
}

impl<T, E, F, Fut> RetryFut<T, E> for F
where
    F: FnMut() -> Fut + Sized,
    Fut: Future<Output = Result<T, E>>,
{
    #[inline]
    #[allow(clippy::manual_async_fn)]
    fn retry<const N: usize>(mut self) -> impl Future<Output = Result<T, [Option<E>; N]>> {
        async move {
            let mut errors: [Option<E>; N] = array::from_fn(|_| None);

            for slot in &mut errors {
                match self().await {
                    Ok(value) => return Ok(value),
                    Err(err) => *slot = Some(err),
                }
            }

            Err(errors)
        }
    }
}
