//! Tokio argument example
//!
//! This example demonstrates how to retry async functions that require
//! arguments.
//!
//! `Retry` operates on zero argument callables:
//!
//! ```text
//! FnMut() -> Future<Output = Result<T, E>>
//! ```
//!
//! An async function with arguments therefore cannot be retried directly.
//! Instead, wrap the call in a closure that captures or supplies the arguments
//! for each attempt.
//!
//! This example covers all three retry strategies:
//!
//! - [`Retry::retry`]: return the first success or every failed error.
//! - [`Retry::retry_ok`]: return the first success and discard errors.
//! - [`Retry::retry_or_else`]: return the first success or invoke a fallback.
//!
//! The crate itself is runtime independent
//! Tokio is used here only to drive the returned futures.
//!
//! Run this example with:
//!
//! ```text
//! cargo run --example tokio_args
//! ```

use retry_core::Retry;

/// Simulates connecting to a service.
///
/// The attempt number is passed explicitly so retry state can remain in the
/// wrapping closure rather than using global state.
async fn connect_service(endpoint: &str, attempt: usize) -> Result<&'static str, &'static str> {
    println!("connecting to {endpoint} (attempt {attempt})");

    // Yield once only to demonstrate a real async suspension point.
    // Real async work will usually suspend naturally.
    //
    // `retry_core` keeps the same attempt active while it is pending.
    tokio::task::yield_now().await;

    if attempt < 3 {
        Err("service unavailable")
    } else {
        Ok("connected")
    }
}

/// Simulates asynchronously reading a cached value.
async fn read_cache(key: &str) -> Result<u32, &'static str> {
    println!("reading cache key: {key}");

    // Yield once only to demonstrate a real async suspension point.
    // Real async work will usually suspend naturally.
    //
    // `retry_core` keeps the same attempt active while it is pending.
    tokio::task::yield_now().await;

    Ok(42)
}

/// Simulates asynchronously fetching from an unavailable primary region.
async fn fetch_primary(region: &str) -> Result<&'static str, &'static str> {
    println!("fetching from region: {region}");

    // Yield once only to demonstrate a real async suspension point.
    // Real async work will usually suspend naturally.
    //
    // `retry_core` keeps the same attempt active while it is pending.
    tokio::task::yield_now().await;

    Err("primary unavailable")
}

#[tokio::main(flavor = "current_thread")]
async fn main() {
    let endpoint = "https://example.com";
    let mut attempts = 0;

    // `connect_service` takes arguments, so this would not work:
    //
    // connect_service.retry::<3>()
    //
    // Instead, the closure supplies the arguments for every attempt.
    //
    // State can also be updated before creating the attempt future. The
    // attempt number is copied into `attempt`, then moved into that future.
    let connection = (|| {
        attempts += 1;
        let attempt = attempts;

        connect_service(endpoint, attempt)
    })
    .retry::<3>()
    .await;

    assert_eq!(connection, Ok("connected"));
    assert_eq!(attempts, 3);

    println!("retry: {connection:?}");

    // Arguments that remain unchanged across attempts can simply be captured
    let cached = (|| read_cache("user:42")).retry_ok::<3>().await;

    assert_eq!(cached, Some(42));

    println!("retry_ok: {cached:?}");

    let region = "eu-west";

    // `retry_or_else` retries the async operation and gives every failed error
    // to the fallback after the final attempt is exhausted.
    let primary = (|| fetch_primary(region))
        .retry_or_else::<3, _>(|errors| {
            assert_eq!(
                errors,
                [
                    "primary unavailable",
                    "primary unavailable",
                    "primary unavailable",
                ]
            );

            "fallback"
        })
        .await;

    assert_eq!(primary, "fallback");

    println!("retry_or_else: {primary:?}");
}
