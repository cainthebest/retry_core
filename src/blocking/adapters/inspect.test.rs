use {
    super::super::super::BlockingRetry,
    crate::adapter::InspectRetry,
    std::{cell::RefCell, rc::Rc, vec, vec::Vec},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Event {
    Call,
    InnerInspect(usize, usize),
    OuterInspect(usize, usize),
    Delay(usize),
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
        self.events
            .borrow_mut()
            .push(Event::InnerInspect(retry, *error));
    }

    fn delay(&mut self, retry: usize) {
        self.events.borrow_mut().push(Event::Delay(retry));
    }
}

#[test]
fn call_forwards_to_inner_operation() {
    let events = Rc::new(RefCell::new(Vec::new()));

    let operation = Operation {
        events: Rc::clone(&events),
        result: Ok(42),
    };

    let mut inspect = InspectRetry {
        operation,
        inspect: |_: usize, _: &usize| {},
    };

    assert_eq!(inspect.call(), Ok(42));
    assert_eq!(*events.borrow(), vec![Event::Call]);
}

#[test]
fn inspect_retry_runs_inner_before_outer() {
    let events = Rc::new(RefCell::new(Vec::new()));

    let operation = Operation {
        events: Rc::clone(&events),
        result: Ok(42),
    };

    let outer_events = Rc::clone(&events);

    let mut inspect = InspectRetry {
        operation,
        inspect: move |retry, error: &usize| {
            outer_events
                .borrow_mut()
                .push(Event::OuterInspect(retry, *error));
        },
    };

    inspect.inspect_retry(2, &7);

    assert_eq!(
        *events.borrow(),
        vec![Event::InnerInspect(2, 7), Event::OuterInspect(2, 7),]
    );
}

#[test]
fn delay_forwards_to_inner_operation() {
    let events = Rc::new(RefCell::new(Vec::new()));

    let operation = Operation {
        events: Rc::clone(&events),
        result: Ok(42),
    };

    let mut inspect = InspectRetry {
        operation,
        inspect: |_: usize, _: &usize| {},
    };

    inspect.delay(3);

    assert_eq!(*events.borrow(), vec![Event::Delay(3)]);
}

#[test]
fn stacked_inspectors_run_in_adapter_order() {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum InspectEvent {
        Inner(usize, usize),
        First(usize, usize),
        Second(usize, usize),
    }

    struct Inner {
        events: Rc<RefCell<Vec<InspectEvent>>>,
    }

    impl BlockingRetry<usize, usize> for Inner {
        fn call(&mut self) -> Result<usize, usize> {
            Ok(42)
        }

        fn inspect_retry(&mut self, retry: usize, error: &usize) {
            self.events
                .borrow_mut()
                .push(InspectEvent::Inner(retry, *error));
        }
    }

    let events = Rc::new(RefCell::new(Vec::new()));

    let first_events = Rc::clone(&events);
    let second_events = Rc::clone(&events);

    let first = InspectRetry {
        operation: Inner {
            events: Rc::clone(&events),
        },
        inspect: move |retry, error: &usize| {
            first_events
                .borrow_mut()
                .push(InspectEvent::First(retry, *error));
        },
    };

    let mut second = InspectRetry {
        operation: first,
        inspect: move |retry, error: &usize| {
            second_events
                .borrow_mut()
                .push(InspectEvent::Second(retry, *error));
        },
    };

    second.inspect_retry(4, &9);

    assert_eq!(
        *events.borrow(),
        vec![
            InspectEvent::Inner(4, 9),
            InspectEvent::First(4, 9),
            InspectEvent::Second(4, 9),
        ]
    );
}
