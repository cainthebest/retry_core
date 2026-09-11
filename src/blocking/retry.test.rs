use {super::super::BlockingRetry, crate::Retry, core::cell::Cell, std::rc::Rc};

struct Operation {
    calls: Rc<Cell<usize>>,
    succeed_on: Option<usize>,
}

impl Operation {
    fn new(calls: &Rc<Cell<usize>>, succeed_on: Option<usize>) -> Self {
        Self {
            calls: Rc::clone(calls),
            succeed_on,
        }
    }
}

impl BlockingRetry<usize, usize> for Operation {
    fn call(&mut self) -> Result<usize, usize> {
        let attempt = self.calls.get() + 1;
        self.calls.set(attempt);

        if self.succeed_on == Some(attempt) {
            Ok(42)
        } else {
            Err(attempt)
        }
    }
}

fn fallback(errors: [usize; 3]) -> usize {
    assert_eq!(errors, [1, 2, 3]);

    99
}

#[test]
fn retry_returns_success() {
    let calls = Rc::new(Cell::new(0));

    let result = Operation::new(&calls, Some(2)).retry::<3>();

    assert_eq!(result, Ok(42));
    assert_eq!(calls.get(), 2);
}

#[test]
fn retry_returns_all_errors_on_exhaustion() {
    let calls = Rc::new(Cell::new(0));

    let result = Operation::new(&calls, None).retry::<3>();

    assert_eq!(result, Err([1, 2, 3]));
    assert_eq!(calls.get(), 3);
}

#[test]
fn retry_ok_returns_success() {
    let calls = Rc::new(Cell::new(0));

    let result = Operation::new(&calls, Some(2)).retry_ok::<3>();

    assert_eq!(result, Some(42));
    assert_eq!(calls.get(), 2);
}

#[test]
fn retry_ok_returns_none_on_exhaustion() {
    let calls = Rc::new(Cell::new(0));

    let result = Operation::new(&calls, None).retry_ok::<3>();

    assert_eq!(result, None);
    assert_eq!(calls.get(), 3);
}

#[test]
fn retry_or_else_returns_success_without_fallback() {
    let calls = Rc::new(Cell::new(0));
    let fallback: fn([usize; 3]) -> usize = fallback;

    let result = Operation::new(&calls, Some(2)).retry_or_else::<3, _>(fallback);

    assert_eq!(result, 42);
    assert_eq!(calls.get(), 2);
}

#[test]
fn retry_or_else_calls_fallback_on_exhaustion() {
    let calls = Rc::new(Cell::new(0));
    let fallback: fn([usize; 3]) -> usize = fallback;

    let result = Operation::new(&calls, None).retry_or_else::<3, _>(fallback);

    assert_eq!(result, 99);
    assert_eq!(calls.get(), 3);
}
