#![no_std]
//! A lightweight retry mechanism for **synchronous**, **fallible**
//! operations in `no_std` environments.
//!
//! # Overview
//!
//! This crate provides the [`Retry`] trait, which extends synchronous
//! closures returning a `Result<T, E>` with simple, deterministic retry
//! behavior.
//!
//! The core idea is:
//!
//! - you call `.retry::<N>()` on a closure,
//! - the closure is invoked up to `N` times,
//! - if any attempt returns `Ok(t)`, retrying stops immediately,
//! - if all attempts fail, you receive an **aggregated error value**
//!   containing information about each failure.
//!
//! By default, the aggregation type is `[Option<E>; N]`:
//!
//! - each slot contains `Some(err)` for that attempt,
//! - unused slots (after success) are `None`.
//!
//! This makes the retry process transparent—a caller can inspect every
//! intermediate error without losing any information.
//!
//! # Examples
//!
//! Basic retrying:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let mut count = 0;
//!
//! let result = (|| {
//!     count += 1;
//!     if count == 3 {
//!         Ok("success")
//!     } else {
//!         Err("not yet")
//!     }
//! })
//! .retry::<5>();
//!
//! assert_eq!(result, Ok("success"));
//! ```
//!
//! All attempts fail:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let result = (|| Err::<(), _>("fail")).retry::<3>();
//!
//! assert_eq!(
//!     result,
//!     Err([Some("fail"), Some("fail"), Some("fail")])
//! );
//! ```
//!
//! Using a fallback (like `Result::unwrap_or_else`):
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let value = (|| Err::<u32, _>("nope"))
//!     .retry_or_else::<3, _>(|_errs| {
//!         // inspect all errors if you like
//!         42
//!     });
//!
//! assert_eq!(value, 42);
//! ```
//!
//! Getting an `Option` like `Result::ok()`:
//!
//! ```rust
//! use retry_core::Retry;
//!
//! let v = (|| Err::<u32, _>("err")).retry_ok::<5>();
//! assert_eq!(v, None);
//! ```

use core::result::Result;

/// A trait for retrying synchronous fallible operations.
///
/// This trait is automatically implemented for *any* closure of the form:
///
/// ```ignore
/// FnMut() -> Result<T, E>
/// ```
///
/// The associated type [`Error`] controls how all failed attempts are
/// aggregated into a single error value.
pub trait Retry {
    /// The success value type of a single attempt.
    type Ok;

    /// The error value type of a single attempt.
    type Err;

    /// The aggregated error type after retrying at most `N` times.
    ///
    /// Typical implementations store all errors, for example:
    ///
    /// ```ignore
    /// type Error<const N: usize> = [Option<Self::Err>; N];
    /// ```
    ///
    /// This allows callers to inspect every failure that occurred.
    type Error<const N: usize>;

    /// Retry the operation at most `N` times.
    ///
    /// - Stops and returns `Ok(t)` on the first successful attempt.
    /// - If all attempts fail, returns an aggregated error value.
    ///
    /// # Behavior
    ///
    /// - The closure is called **at most** `N` times.
    /// - If a success occurs early, remaining error slots may be left
    ///   uninitialized (commonly `None`).
    fn retry<const N: usize>(self) -> Result<Self::Ok, Self::Error<N>>
    where
        Self: Sized;

    /// Retry up to `N` times; if all attempts fail, call the fallback
    /// function with the aggregated error.
    ///
    /// This behaves similarly to `Result::unwrap_or_else`, but for
    /// multi-attempt operations.
    #[inline]
    fn retry_or_else<const N: usize, F>(self, f: F) -> Self::Ok
    where
        Self: Sized,
        F: FnOnce(Self::Error<N>) -> Self::Ok,
    {
        match self.retry::<N>() {
            Ok(v) => v,
            Err(e) => f(e),
        }
    }

    /// Retry up to `N` times and return `Some(value)` on success, or
    /// `None` if all attempts fail.
    ///
    /// This is equivalent to calling `.retry::<N>().ok()`.
    #[inline]
    fn retry_ok<const N: usize>(self) -> Option<Self::Ok>
    where
        Self: Sized,
    {
        match self.retry::<N>() {
            Ok(v) => Some(v),
            Err(_) => None,
        }
    }
}

impl<T, E, F> Retry for F
where
    F: FnMut() -> Result<T, E>,
{
    type Ok = T;
    type Err = E;

    /// Aggregated error type: stores all `N` errors in order.
    type Error<const N: usize> = [Option<Self::Err>; N];

    #[inline]
    fn retry<const N: usize>(mut self) -> Result<Self::Ok, Self::Error<N>> {
        let mut error: [Option<Self::Err>; N] = core::array::from_fn(|_| None);

        for slot in &mut error {
            match self() {
                Ok(value) => return Ok(value),
                Err(err) => *slot = Some(err),
            }
        }

        Err(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn retry_succeeds_on_first_attempt() {
        let mut calls = 0;

        let result = (|| {
            calls += 1;
            Ok::<_, &'static str>(42)
        })
        .retry::<3>();

        assert_eq!(result, Ok(42));
        assert_eq!(calls, 1);
    }

    #[test]
    fn retry_succeeds_after_some_failures() {
        let mut attempts = 0;

        let result = (|| {
            attempts += 1;
            if attempts < 3 {
                Err::<u32, _>("not yet")
            } else {
                Ok(7)
            }
        })
        .retry::<5>();

        assert_eq!(result, Ok(7));
        assert_eq!(attempts, 3);
    }

    #[test]
    fn retry_all_attempts_fail_collects_all_errors() {
        let mut calls = 0;

        let result = (|| {
            calls += 1;
            Err::<u32, _>("fail")
        })
        .retry::<3>();

        assert_eq!(calls, 3);
        assert_eq!(result, Err([Some("fail"), Some("fail"), Some("fail")]));
    }

    #[test]
    fn retry_partial_success_leaves_trailing_nones() {
        let mut attempts = 0;

        let result = (|| {
            attempts += 1;
            if attempts == 3 {
                Ok::<u32, &'static str>(99)
            } else {
                Err("err")
            }
        })
        .retry::<5>();

        assert_eq!(attempts, 3);
        assert_eq!(result, Ok(99));
    }

    #[test]
    fn retry_with_zero_attempts_never_calls_closure() {
        let mut calls = 0;

        let result: Result<u32, [Option<&'static str>; 0]> = (|| {
            calls += 1;
            Err::<u32, _>("fail")
        })
        .retry::<0>();

        assert_eq!(calls, 0);
        assert_eq!(result, Err([]));
    }

    #[test]
    fn retry_or_else_success_does_not_call_fallback() {
        let mut attempts = 0;
        let mut fallback_called = false;

        let value = (|| {
            attempts += 1;
            if attempts == 1 {
                Ok::<u32, &'static str>(10)
            } else {
                Err("should not happen")
            }
        })
        .retry_or_else::<3, _>(|_errs| {
            fallback_called = true;
            0
        });

        assert_eq!(value, 10);
        assert_eq!(attempts, 1);
        assert!(!fallback_called);
    }

    #[test]
    fn retry_or_else_failure_calls_fallback() {
        let mut called = false;

        let value = (|| Err::<u32, _>("e")).retry_or_else::<2, _>(|errs| {
            assert_eq!(errs, [Some("e"), Some("e")]);
            called = true;
            99
        });

        assert_eq!(value, 99);
        assert!(called);
    }

    #[test]
    fn retry_ok_returns_some_on_success() {
        let value = (|| Ok::<u32, &'static str>(5)).retry_ok::<3>();
        assert_eq!(value, Some(5));
    }

    #[test]
    fn retry_ok_returns_none_on_failure() {
        let value = (|| Err::<u32, &'static str>("err")).retry_ok::<3>();
        assert_eq!(value, None);
    }

    #[test]
    fn retry_works_with_static_err_type() {
        let mut attempts: u8 = 0;

        let result = (|| -> Result<u32, u8> {
            attempts += 1;
            Err(attempts)
        })
        .retry::<3>();

        match result {
            Err([Some(e1), Some(e2), Some(e3)]) => {
                assert_eq!(e1, 1);
                assert_eq!(e2, 2);
                assert_eq!(e3, 3);
            }
            other => panic!("unexpected result: {:?}", other),
        }
    }
}
