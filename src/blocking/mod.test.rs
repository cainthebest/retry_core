use {super::BlockingRetry, core::cell::Cell};

const VALUE: u8 = 42;

struct State {
    calls: Cell<usize>,
    inspected: Cell<usize>,
    delayed: Cell<usize>,
}

impl State {
    const fn new() -> Self {
        Self {
            calls: Cell::new(0),
            inspected: Cell::new(0),
            delayed: Cell::new(0),
        }
    }
}

struct RetrySpy<'a> {
    state: &'a State,
    success_on: Option<usize>,
}

impl<'a> RetrySpy<'a> {
    const fn new(state: &'a State, success_on: Option<usize>) -> Self {
        Self { state, success_on }
    }
}

impl BlockingRetry<u8, usize> for RetrySpy<'_> {
    fn call(&mut self) -> Result<u8, usize> {
        let call = self.state.calls.get() + 1;

        self.state.calls.set(call);

        if self.success_on == Some(call) {
            Ok(VALUE)
        } else {
            Err(call)
        }
    }

    fn inspect_retry(&mut self, retry: usize, error: &usize) {
        assert_eq!(retry, *error);

        self.state.inspected.set(self.state.inspected.get() + 1);
    }

    fn delay(&mut self, retry: usize) {
        assert_eq!(retry, self.state.delayed.get() + 1);

        self.state.delayed.set(self.state.delayed.get() + 1);
    }
}

fn assert_state(state: &State, calls: usize, inspected: usize, delayed: usize) {
    assert_eq!(state.calls.get(), calls);
    assert_eq!(state.inspected.get(), inspected);
    assert_eq!(state.delayed.get(), delayed);
}

#[test]
fn run_zero_attempts_does_nothing() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(1)).run::<0>(), Err([]),);

    assert_state(&state, 0, 0, 0);
}

#[test]
fn run_one_attempt_can_succeed() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(1)).run::<1>(), Ok(VALUE),);

    assert_state(&state, 1, 0, 0);
}

#[test]
fn run_one_attempt_can_fail() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, None).run::<1>(), Err([1]),);

    assert_state(&state, 1, 0, 0);
}

#[test]
fn run_can_succeed_on_first_attempt() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(1)).run::<3>(), Ok(VALUE),);

    assert_state(&state, 1, 0, 0);
}

#[test]
fn run_can_succeed_after_retry() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(2)).run::<3>(), Ok(VALUE),);

    assert_state(&state, 2, 1, 1);
}

#[test]
fn run_can_succeed_on_final_attempt() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(3)).run::<3>(), Ok(VALUE),);

    assert_state(&state, 3, 2, 2);
}

#[test]
fn run_returns_every_error_in_order() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, None).run::<3>(), Err([1, 2, 3]),);

    assert_state(&state, 3, 2, 2);
}

#[test]
fn run_ok_zero_attempts_does_nothing() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(1)).run_ok::<0>(), None,);

    assert_state(&state, 0, 0, 0);
}

#[test]
fn run_ok_one_attempt_can_succeed() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(1)).run_ok::<1>(), Some(VALUE),);

    assert_state(&state, 1, 0, 0);
}

#[test]
fn run_ok_one_attempt_can_fail() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, None).run_ok::<1>(), None,);

    assert_state(&state, 1, 0, 0);
}

#[test]
fn run_ok_can_succeed_on_first_attempt() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(1)).run_ok::<3>(), Some(VALUE),);

    assert_state(&state, 1, 0, 0);
}

#[test]
fn run_ok_can_succeed_after_retry() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(2)).run_ok::<3>(), Some(VALUE),);

    assert_state(&state, 2, 1, 1);
}

#[test]
fn run_ok_can_succeed_on_final_attempt() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, Some(3)).run_ok::<3>(), Some(VALUE),);

    assert_state(&state, 3, 2, 2);
}

#[test]
fn run_ok_returns_none_after_all_attempts_fail() {
    let state = State::new();

    assert_eq!(RetrySpy::new(&state, None).run_ok::<3>(), None,);

    assert_state(&state, 3, 2, 2);
}

#[test]
fn fn_mut_implementation_and_default_hooks_work() {
    let calls = Cell::new(0);

    let operation = || {
        let call = calls.get() + 1;

        calls.set(call);

        if call == 2 { Ok(VALUE) } else { Err(call) }
    };

    assert_eq!(operation.run::<3>(), Ok(VALUE));
    assert_eq!(calls.get(), 2);
}
