use {
    super::super::super::BlockingRetry,
    crate::{
        adapter::{RetryDelay, WithDelay},
        mode::BlockingMode,
    },
    core::cell::Cell,
    std::{cell::RefCell, rc::Rc, vec, vec::Vec},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Event {
    Call,
    Inspect(usize, usize),
    Delay(usize),
    OuterDelay(usize),
}

struct Operation {
    events: Rc<RefCell<Vec<Event>>>,
    result: Result<usize, usize>,
}

impl BlockingRetry<usize, usize> for Operation {
    fn call(&mut self) -> Result<usize, usize> {
        self.events.borrow_mut().push(Event::Call);
        self.result
    }

    fn inspect_retry(&mut self, retry: usize, error: &usize) {
        self.events.borrow_mut().push(Event::Inspect(retry, *error));
    }

    fn delay(&mut self, retry: usize) {
        self.events.borrow_mut().push(Event::Delay(retry));
    }
}

#[test]
fn retry_delay_calls_closure_with_retry() {
    let seen = Cell::new(0);

    let mut delay = |retry| {
        seen.set(retry);
    };

    <_ as RetryDelay<BlockingMode<usize, usize>>>::delay(&mut delay, 3);

    assert_eq!(seen.get(), 3);
}

#[test]
fn call_forwards_to_inner_operation() {
    let events = Rc::new(RefCell::new(Vec::new()));

    let operation = Operation {
        events: Rc::clone(&events),
        result: Ok(42),
    };

    let mut with_delay = WithDelay {
        operation,
        delay: |_: usize| {},
    };

    assert_eq!(with_delay.call(), Ok(42));
    assert_eq!(*events.borrow(), vec![Event::Call]);
}

#[test]
fn inspect_retry_forwards_to_inner_operation() {
    let events = Rc::new(RefCell::new(Vec::new()));

    let operation = Operation {
        events: Rc::clone(&events),
        result: Ok(42),
    };

    let mut with_delay = WithDelay {
        operation,
        delay: |_: usize| {},
    };

    with_delay.inspect_retry(2, &7);

    assert_eq!(*events.borrow(), vec![Event::Inspect(2, 7)]);
}

#[test]
fn delay_runs_inner_delay_before_outer_delay() {
    let events = Rc::new(RefCell::new(Vec::new()));

    let operation = Operation {
        events: Rc::clone(&events),
        result: Ok(42),
    };

    let outer_events = Rc::clone(&events);

    let mut with_delay = WithDelay {
        operation,
        delay: move |retry| {
            outer_events.borrow_mut().push(Event::OuterDelay(retry));
        },
    };

    with_delay.delay(3);

    assert_eq!(
        *events.borrow(),
        vec![Event::Delay(3), Event::OuterDelay(3),]
    );
}

#[test]
fn delay_forwards_retry_to_both_layers() {
    let events = Rc::new(RefCell::new(Vec::new()));

    let operation = Operation {
        events: Rc::clone(&events),
        result: Ok(42),
    };

    let outer_events = Rc::clone(&events);

    let mut with_delay = WithDelay {
        operation,
        delay: move |retry| {
            outer_events.borrow_mut().push(Event::OuterDelay(retry));
        },
    };

    with_delay.delay(7);

    assert_eq!(
        *events.borrow(),
        vec![Event::Delay(7), Event::OuterDelay(7),]
    );
}

#[test]
fn stacked_delays_run_in_adapter_order() {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum DelayEvent {
        Inner(usize),
        First(usize),
        Second(usize),
    }

    struct Inner {
        events: Rc<RefCell<Vec<DelayEvent>>>,
    }

    impl BlockingRetry<usize, usize> for Inner {
        fn call(&mut self) -> Result<usize, usize> {
            Ok(42)
        }

        fn delay(&mut self, retry: usize) {
            self.events.borrow_mut().push(DelayEvent::Inner(retry));
        }
    }

    let events = Rc::new(RefCell::new(Vec::new()));

    let first_events = Rc::clone(&events);
    let second_events = Rc::clone(&events);

    let first = WithDelay {
        operation: Inner {
            events: Rc::clone(&events),
        },
        delay: move |retry| {
            first_events.borrow_mut().push(DelayEvent::First(retry));
        },
    };

    let mut second = WithDelay {
        operation: first,
        delay: move |retry| {
            second_events.borrow_mut().push(DelayEvent::Second(retry));
        },
    };

    second.delay(4);

    assert_eq!(
        *events.borrow(),
        vec![
            DelayEvent::Inner(4),
            DelayEvent::First(4),
            DelayEvent::Second(4),
        ]
    );
}
