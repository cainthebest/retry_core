//! A closure returns a *new* future on each call. The returned
//! future must **not** borrow from stack locals owned by the test function
//! (e.g., `&mut calls`), because that reference would escape the closure body.
//!
//! To avoid this lifetime issue, these tests use `static` atomics to track
//! state (like the number of calls) instead of stack locals.

use retry_core::RetryFut;

use std::{
    future::Future,
    pin::Pin,
    sync::atomic::{AtomicI32, AtomicUsize, Ordering},
    task::{Context, Poll, RawWaker, RawWakerVTable, Waker},
};

/// Minimal `block_on` using the standard library.
///
/// - Pins the future
/// - Creates a dummy `Waker`
/// - Polls in a loop until `Poll::Ready`
fn block_on<F: Future>(mut fut: F) -> F::Output {
    // SAFETY: we pin `fut` once here and never move it again.
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };

    fn noop_clone(_: *const ()) -> RawWaker {
        RawWaker::new(core::ptr::null(), &VTABLE)
    }

    fn noop(_: *const ()) {}

    static VTABLE: RawWakerVTable = RawWakerVTable::new(noop_clone, noop, noop, noop);

    let raw_waker = RawWaker::new(core::ptr::null(), &VTABLE);
    let waker = unsafe { Waker::from_raw(raw_waker) };
    let mut cx = Context::from_waker(&waker);

    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(val) => return val,
            Poll::Pending => continue,
        }
    }
}

/// Succeeds on the very first async attempt.
///
/// Uses a static atomic to track how many times the closure is invoked.
#[test]
fn async_success_first_try() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        CALLS.fetch_add(1, Ordering::SeqCst);
        Ok::<u32, &'static str>(42)
    })
    .retry::<3>();

    let res = block_on(fut);

    assert_eq!(res, Ok(42));
    assert_eq!(CALLS.load(Ordering::SeqCst), 1);
}

/// Succeeds on a middle attempt (2nd out of 4).
///
/// Checks that retries stop immediately after the first successful future.
#[test]
fn async_success_middle_attempt() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        let call_no = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
        if call_no == 2 {
            Ok::<u32, &'static str>(7)
        } else {
            Err("nope")
        }
    })
    .retry::<4>();

    let res = block_on(fut);

    assert_eq!(res, Ok(7));
    assert_eq!(CALLS.load(Ordering::SeqCst), 2);
}

/// Succeeds on the last allowed attempt (4th out of 4).
///
/// Ensures all attempts are tried up to `N` when the last one is the first success.
#[test]
fn async_success_last_attempt() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        let call_no = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
        if call_no == 4 {
            Ok::<u32, &'static str>(9)
        } else {
            Err("retry")
        }
    })
    .retry::<4>();

    let res = block_on(fut);

    assert_eq!(res, Ok(9));
    assert_eq!(CALLS.load(Ordering::SeqCst), 4);
}

/// All async attempts fail with the same error value.
///
/// Verifies that:
/// - the closure is called exactly `N` times
/// - the error array is fully populated with `Some(err)` values
#[test]
fn async_all_fail_same_error() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        CALLS.fetch_add(1, Ordering::SeqCst);
        Err::<u32, &'static str>("err")
    })
    .retry::<3>();

    let res = block_on(fut);

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(CALLS.load(Ordering::SeqCst), 3);
    assert_eq!(errs, [Some("err"), Some("err"), Some("err")]);
}

/// All async attempts fail with a *different* error per attempt.
///
/// Verifies that the error array preserves both **order** and **content**.
#[test]
fn async_all_fail_different_errors() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        let call_no = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
        match call_no {
            1 => Err::<u32, &'static str>("e1"),
            2 => Err("e2"),
            _ => Err("e3"),
        }
    })
    .retry::<3>();

    let res = block_on(fut);

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(CALLS.load(Ordering::SeqCst), 3);
    assert_eq!(errs, [Some("e1"), Some("e2"), Some("e3")]);
}

/// `N = 0` for async: the closure must never be called.
///
/// The returned future should resolve immediately to `Err([])`.
#[test]
fn async_zero_attempts() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        CALLS.fetch_add(1, Ordering::SeqCst);
        Ok::<u32, &'static str>(1)
    })
    .retry::<0>();

    let res = block_on(fut);

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(errs.len(), 0);
    assert_eq!(CALLS.load(Ordering::SeqCst), 0);
}

/// `N = 1`, success case.
///
/// Ensures that a single attempt is performed and that success is returned properly.
#[test]
fn async_one_attempt_success() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        CALLS.fetch_add(1, Ordering::SeqCst);
        Ok::<u32, &'static str>(5)
    })
    .retry::<1>();

    let res = block_on(fut);

    assert_eq!(res, Ok(5));
    assert_eq!(CALLS.load(Ordering::SeqCst), 1);
}

/// `N = 1`, failure case.
///
/// Ensures that a single failing attempt is recorded correctly.
#[test]
fn async_one_attempt_fail() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        CALLS.fetch_add(1, Ordering::SeqCst);
        Err::<u32, &'static str>("boom")
    })
    .retry::<1>();

    let res = block_on(fut);

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(CALLS.load(Ordering::SeqCst), 1);
    assert_eq!(errs, [Some("boom")]);
}

/// Async non-Copy, non-Clone error type (`String`).
///
/// This ensures the error type can be moved into the error array without
/// requiring `Copy` or `Clone`.
#[test]
fn async_non_copy_error_type() {
    static CALLS: AtomicUsize = AtomicUsize::new(0);
    CALLS.store(0, Ordering::SeqCst);

    let fut = (|| async {
        let call_no = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
        Err::<u32, String>(if call_no == 1 {
            String::from("first")
        } else {
            String::from("second")
        })
    })
    .retry::<2>();

    let res = block_on(fut);

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(CALLS.load(Ordering::SeqCst), 2);
    assert_eq!(errs[0].as_deref(), Some("first"));
    assert_eq!(errs[1].as_deref(), Some("second"));
}

/// Verifies that the async closure can mutate external *global* state
/// across attempts using atomics.
///
/// We track both the number of calls and a running sum derived from those calls.
#[test]
fn async_mutates_external_state() {
    static CALLS: AtomicI32 = AtomicI32::new(0);
    static SUM: AtomicI32 = AtomicI32::new(0);

    CALLS.store(0, Ordering::SeqCst);
    SUM.store(0, Ordering::SeqCst);

    let fut = (|| async {
        let call_no = CALLS.fetch_add(1, Ordering::SeqCst) + 1;
        SUM.fetch_add(call_no, Ordering::SeqCst);
        Err::<(), &'static str>("oops")
    })
    .retry::<3>();

    let res = block_on(fut);

    assert!(res.is_err());
    let _ = res.unwrap_err();

    assert_eq!(CALLS.load(Ordering::SeqCst), 3);
    assert_eq!(SUM.load(Ordering::SeqCst), 6);
}
