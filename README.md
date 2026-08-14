# retry_core

A fast, zero-allocation, `#![no_std]`-compatible retry primitive for Rust.

`retry_core` provides synchronous and asynchronous retry capabilities for closures and `Future`s with compile-time bounded attempt limits and zero heap allocations.

## Features

- **`#![no_std]` Support**: Works in bare-metal and embedded environments without the standard library or an allocator.
- **Zero Allocations**: Error tracking and future state use fixed-size stack buffers parameterized by const generics (`const ATTEMPTS: usize`).
- **Sync & Async**: Seamless retry ergonomics for both synchronous closures (`FnMut() -> Result<T, E>`) and asynchronous operations (`FnMut() -> impl Future<Output = Result<T, E>>`).
- **Flexible Results**:
  - `retry::<N>()` — Collects all errors into an array `[E; N]` if all attempts fail.
  - `retry_ok::<N>()` — Discards error details and returns `Option<T>`.
  - `retry_or_else::<N>(fallback)` — Executes a fallback function on total failure to return `T`.

## Installation

Add to your `Cargo.toml`:

```toml
[dependencies]
retry_core = "0.1"
```

## Usage

### Synchronous Retries

```rust
use retry_core::Retry;

fn unreliable_operation() -> Result<u32, &'static str> {
    // ...
    Ok(42)
}

fn main() {
    // 1. Retry up to 3 times, returning Result<T, [E; 3]>
    let result = unreliable_operation.retry::<3>();
    match result {
        Ok(val) => println!("Success: {val}"),
        Err(errors) => println!("Failed after 3 attempts: {errors:?}"),
    }

    // 2. Retry up to 3 times, returning Option<T>
    let maybe_val = unreliable_operation.retry_ok::<3>();

    // 3. Retry with a fallback closure receiving the collected errors
    let val = unreliable_operation.retry_or_else::<3, _>(|errors| {
        eprintln!("All attempts failed: {errors:?}");
        0 // default fallback
    });
}
```

### Asynchronous Retries

```rust
use retry_core::Retry;

async fn fetch_data() -> Result<String, &'static str> {
    // async network call
    Ok("data".to_string())
}

#[tokio::main]
async fn main() {
    // Retry async operation up to 5 times
    let result = (|| fetch_data()).retry::<5>().await;

    match result {
        Ok(data) => println!("Fetched: {data}"),
        Err(errors) => println!("Failed after 5 attempts: {errors:?}"),
    }
}
```

## API Overview

| Method | Return Type (Sync) | Return Type (Async) | Behavior |
|---|---|---|---|
| `.retry::<N>()` | `Result<T, [E; N]>` | `impl Future<Output = Result<T, [E; N]>>` | Attempts operation up to `N` times; collects all errors upon failure. |
| `.retry_ok::<N>()` | `Option<T>` | `impl Future<Output = Option<T>>` | Returns `Some(val)` on first success or `None` after `N` failed attempts. |
| `.retry_or_else::<N>(fn)` | `T` | `impl Future<Output = T>` | Returns `val` on success or invokes fallback with `[E; N]` to produce default `T`. |

## License

Licensed under the MIT License or Apache 2.0 at your option.
