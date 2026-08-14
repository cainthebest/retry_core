//! Synchronous zero argument example
//!
//! This example demonstrates that `retry_core` can retry zero argument
//! synchronous function items directly. No wrapper closure is required when
//! the function already has the shape:
//!
//! ```text
//! fn() -> Result<T, E>
//! ```
//!
//! It covers all three retry strategies:
//!
//! - [`Retry::retry`]: return the first success or every failed error.
//! - [`Retry::retry_ok`]: return the first success and discard errors.
//! - [`Retry::retry_or_else`]: return the first success or invoke a fallback.
//!
//! Run this example with:
//!
//! ```text
//! cargo run --example sync_zero_arg
//! ```

use {
    retry_core::Retry,
    std::sync::atomic::{AtomicUsize, Ordering},
};

/// Number of times [`connect_service`] has been called.
///
/// The counter provides state while keeping `connect_service` itself
/// zero argument, allowing the function item to be retried directly.
static CONNECT_ATTEMPTS: AtomicUsize = AtomicUsize::new(0);

/// Simulates a service that becomes available on the third attempt.
fn connect_service() -> Result<&'static str, &'static str> {
    let attempt = CONNECT_ATTEMPTS.fetch_add(1, Ordering::Relaxed) + 1;

    if attempt < 3 {
        Err("service unavailable")
    } else {
        Ok("connected")
    }
}

/// Simulates an operation that succeeds immediately.
fn read_cache() -> Result<u32, &'static str> {
    Ok(42)
}

/// Simulates an operation that fails on every attempt.
fn fetch_primary() -> Result<&'static str, &'static str> {
    Err("primary unavailable")
}

fn main() {
    // `retry` preserves every failed error if all attempts are exhausted.
    //
    // `connect_service` fails twice and succeeds on the third call, so the
    // successful value is returned and the earlier errors are discarded.
    let connection = connect_service.retry::<3>();

    assert_eq!(connection, Ok("connected"));
    println!("retry: {connection:?}");

    // `retry_ok` ignores individual errors and returns
    // only whether an attempt eventually produced a value.
    let cached = read_cache.retry_ok::<3>();

    assert_eq!(cached, Some(42));
    println!("retry_ok: {cached:?}");

    // `retry_or_else` collects all failed errors and
    // gives them to the fallback after the final attempt fails.
    let primary = fetch_primary.retry_or_else::<3, _>(|errors| {
        assert_eq!(
            errors,
            [
                "primary unavailable",
                "primary unavailable",
                "primary unavailable",
            ]
        );

        "fallback"
    });

    assert_eq!(primary, "fallback");
    println!("retry_or_else: {primary:?}");
}
