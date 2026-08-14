//! Synchronous argument example
//!
//! This example demonstrates how to retry functions that require arguments.
//!
//! `Retry` operates on zero argument callables:
//!
//! ```text
//! FnMut() -> Result<T, E>
//! ```
//!
//! A function with arguments therefore cannot be retried directly. Instead,
//! wrap the call in a closure that captures or supplies those arguments.
//!
//! This example covers all three retry strategies:
//!
//! - [`Retry::retry`]: return the first success or every failed error.
//! - [`Retry::retry_ok`]: return the first success and discard errors.
//! - [`Retry::retry_or_else`]: return the first success or invoke a fallback.
//!
//! Run this example with:
//!
//! ```text
//! cargo run --example sync_args
//! ```

use retry_core::Retry;

/// Simulates connecting to a service.
///
/// `attempt` is passed explicitly so the example can demonstrate retries
/// without requiring global state.
fn connect_service(endpoint: &str, attempt: usize) -> Result<&'static str, &'static str> {
    println!("connecting to {endpoint} (attempt {attempt})");

    if attempt < 3 {
        Err("service unavailable")
    } else {
        Ok("connected")
    }
}

/// Simulates reading a value from a cache.
fn read_cache(key: &str) -> Result<u32, &'static str> {
    println!("reading cache key: {key}");

    Ok(42)
}

/// Simulates fetching a value from a primary region that is unavailable.
fn fetch_primary(region: &str) -> Result<&'static str, &'static str> {
    println!("fetching from region: {region}");

    Err("primary unavailable")
}

fn main() {
    let endpoint = "https://example.com";
    let mut attempts = 0;

    // `connect_service` takes arguments, so it cannot be used as:
    //
    // connect_service.retry::<3>()
    //
    // Instead, a closure supplies the arguments for each attempt.
    //
    // The closure is `FnMut`, so it can also maintain state between attempts.
    let connection = (|| {
        attempts += 1;
        connect_service(endpoint, attempts)
    })
    .retry::<3>();

    assert_eq!(connection, Ok("connected"));
    assert_eq!(attempts, 3);

    println!("retry: {connection:?}");

    // Arguments that do not change between attempts can simply be captured
    let cached = (|| read_cache("user:42")).retry_ok::<3>();

    assert_eq!(cached, Some(42));

    println!("retry_ok: {cached:?}");

    let region = "eu-west";

    // `retry_or_else` retries the wrapped function and passes every error to
    // the fallback if all attempts are exhausted.
    let primary = (|| fetch_primary(region)).retry_or_else::<3, _>(|errors| {
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
