use {
    super::RetryPolicy,
    crate::mode::BlockingMode,
    core::{cell::Cell, marker::PhantomData},
};

type Mode = BlockingMode<usize, usize>;

const VALUE: usize = 42;

fn policy<O>(operation: O) -> RetryPolicy<O, Mode> {
    RetryPolicy {
        operation,
        _mode: PhantomData,
    }
}

fn operation(
    calls: &Cell<usize>,
    succeed_on: Option<usize>,
) -> impl FnMut() -> Result<usize, usize> + '_ {
    move || {
        let call = calls.get() + 1;

        calls.set(call);

        if succeed_on == Some(call) {
            Ok(VALUE)
        } else {
            Err(call)
        }
    }
}

#[test]
fn retry_forwards_to_operation() {
    let calls = Cell::new(0);

    let result = policy(operation(&calls, Some(2))).retry::<2>();

    assert_eq!(result, Ok(VALUE));
    assert_eq!(calls.get(), 2);
}

#[test]
fn retry_ok_forwards_to_operation() {
    let calls = Cell::new(0);

    let result = policy(operation(&calls, None)).retry_ok::<3>();

    assert_eq!(result, None);
    assert_eq!(calls.get(), 3);
}

#[test]
fn retry_or_else_forwards_to_operation_and_fallback() {
    let calls = Cell::new(0);
    let fallback_calls = Cell::new(0);

    let result = policy(operation(&calls, None)).retry_or_else::<3, _>(|errors| {
        fallback_calls.set(fallback_calls.get() + 1);

        assert_eq!(errors, [1, 2, 3]);

        VALUE
    });

    assert_eq!(result, VALUE);
    assert_eq!(calls.get(), 3);
    assert_eq!(fallback_calls.get(), 1);
}

#[test]
fn with_delay_wraps_operation() {
    let calls = Cell::new(0);
    let delays = Cell::new(0);

    let result = policy(operation(&calls, Some(3)))
        .with_delay(|retry| {
            assert_eq!(retry, delays.get() + 1);

            delays.set(retry);
        })
        .retry::<3>();

    assert_eq!(result, Ok(VALUE));
    assert_eq!(calls.get(), 3);
    assert_eq!(delays.get(), 2);
}

#[test]
fn inspect_retry_wraps_operation() {
    let calls = Cell::new(0);
    let inspections = Cell::new(0);

    let result = policy(operation(&calls, Some(3)))
        .inspect_retry(|retry, error| {
            assert_eq!(retry, inspections.get() + 1);
            assert_eq!(*error, retry);

            inspections.set(retry);
        })
        .retry::<3>();

    assert_eq!(result, Ok(VALUE));
    assert_eq!(calls.get(), 3);
    assert_eq!(inspections.get(), 2);
}

#[test]
fn adapters_can_be_chained() {
    let calls = Cell::new(0);
    let inspections = Cell::new(0);
    let delays = Cell::new(0);

    let result = policy(operation(&calls, Some(3)))
        .inspect_retry(|retry, error| {
            assert_eq!(*error, retry);

            inspections.set(inspections.get() + 1);
        })
        .with_delay(|retry| {
            assert_eq!(retry, delays.get() + 1);

            delays.set(retry);
        })
        .retry::<3>();

    assert_eq!(result, Ok(VALUE));
    assert_eq!(calls.get(), 3);
    assert_eq!(inspections.get(), 2);
    assert_eq!(delays.get(), 2);
}
