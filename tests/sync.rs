//! These tests cover:
//! - success on first/middle/last attempt
//! - all attempts failing (with same and different errors)
//! - edge cases for `N = 0` and `N = 1`
//! - non-Copy error types
//! - mutation of captured state across attempts

use retry_core::Retry;

/// Succeeds on the very first attempt.
///
/// Ensures that:
/// - the closure is called only once
/// - the returned result is `Ok(...)`
/// - no further attempts are made
#[test]
fn sync_success_first_try() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 3]> = (|| {
        calls += 1;
        Ok(10)
    })
    .retry::<3>();

    assert_eq!(res, Ok(10));
    assert_eq!(calls, 1);
}

/// Succeeds on a middle attempt (here, the 3rd out of 5).
///
/// Ensures that:
/// - the closure is retried until it succeeds
/// - the correct number of attempts are made (3)
/// - retries stop immediately after the first success
#[test]
fn sync_success_middle_attempt() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 5]> = (|| {
        calls += 1;
        if calls == 3 { Ok(42) } else { Err("fail") }
    })
    .retry::<5>();

    assert_eq!(res, Ok(42));
    assert_eq!(calls, 3);
}

/// Succeeds on the last allowed attempt.
///
/// Ensures that:
/// - all but the last attempts fail
/// - the closure is called exactly `N` times when success happens on the last attempt
#[test]
fn sync_success_last_attempt() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 4]> = (|| {
        calls += 1;
        if calls == 4 { Ok(99) } else { Err("nope") }
    })
    .retry::<4>();

    assert_eq!(res, Ok(99));
    assert_eq!(calls, 4);
}

/// All attempts fail, using the same error value each time.
///
/// Ensures that:
/// - the closure is called exactly `N` times
/// - the returned error array is fully populated with `Some(err)`
/// - no `None` slots remain if all attempts fail
#[test]
fn sync_all_fail_same_error() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 3]> = (|| {
        calls += 1;
        Err("err")
    })
    .retry::<3>();

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(calls, 3);
    assert_eq!(errs, [Some("err"), Some("err"), Some("err")]);
}

/// All attempts fail with different error values.
///
/// This checks that:
/// - errors are stored in order of attempts
/// - each attempt’s error is preserved separately
#[test]
fn sync_all_fail_different_errors() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 3]> = (|| {
        calls += 1;
        match calls {
            1 => Err("e1"),
            2 => Err("e2"),
            _ => Err("e3"),
        }
    })
    .retry::<3>();

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(calls, 3);
    assert_eq!(errs, [Some("e1"), Some("e2"), Some("e3")]);
}

/// `N = 0` is a corner case: no attempts should be made.
///
/// Ensures that:
/// - the closure is never called
/// - the result is `Err` with an empty error array
#[test]
fn sync_zero_attempts() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 0]> = (|| {
        calls += 1;
        Ok(1)
    })
    .retry::<0>();

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(errs.len(), 0);
    assert_eq!(calls, 0);
}

/// `N = 1` and success: a single allowed attempt that succeeds.
///
/// Ensures that:
/// - exactly one call is made
/// - the success path works even for the minimal `N`
#[test]
fn sync_one_attempt_success() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 1]> = (|| {
        calls += 1;
        Ok(5)
    })
    .retry::<1>();

    assert_eq!(res, Ok(5));
    assert_eq!(calls, 1);
}

/// `N = 1` and failure: a single allowed attempt that fails.
///
/// Ensures that:
/// - exactly one call is made
/// - the error is stored in the only slot
#[test]
fn sync_one_attempt_fail() {
    let mut calls = 0;

    let res: Result<u32, [Option<&'static str>; 1]> = (|| {
        calls += 1;
        Err("boom")
    })
    .retry::<1>();

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(calls, 1);
    assert_eq!(errs, [Some("boom")]);
}

/// Uses a non-Copy, non-Clone error type (`String`).
///
/// This test exists mainly to verify that:
/// - the error type does not need to implement `Copy` or `Clone`
/// - ownership of each error value is properly moved into the array
#[test]
fn sync_non_copy_error_type() {
    let mut calls = 0;

    let res: Result<u32, [Option<String>; 2]> = (|| {
        calls += 1;
        Err(String::from(if calls == 1 { "first" } else { "second" }))
    })
    .retry::<2>();

    assert!(res.is_err());
    let errs = res.unwrap_err();

    assert_eq!(calls, 2);
    assert_eq!(errs[0].as_deref(), Some("first"));
    assert_eq!(errs[1].as_deref(), Some("second"));
}

/// Verifies that the closure can mutate captured external state across attempts.
///
/// We track both:
/// - the number of calls
/// - a running sum derived from each call
///
/// This ensures that the closure is truly `FnMut` and not `Fn`.
#[test]
fn sync_mutates_external_state() {
    let mut sum = 0;
    let mut calls = 0;

    let res: Result<(), [Option<&'static str>; 3]> = (|| {
        calls += 1;
        sum += calls; // accumulate some state
        Err("oops")
    })
    .retry::<3>();

    assert!(res.is_err());
    // sum = 1 + 2 + 3 = 6
    assert_eq!(sum, 6);
    assert_eq!(calls, 3);
}
