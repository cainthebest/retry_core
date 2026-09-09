use {
    super::ErrorBuffer,
    core::cell::Cell,
    std::{
        panic::{AssertUnwindSafe, catch_unwind},
        rc::Rc,
        string::String,
    },
};

#[derive(Debug)]
struct DropSpy {
    value: usize,
    drops: Rc<Cell<usize>>,
}

impl DropSpy {
    fn new(value: usize, drops: &Rc<Cell<usize>>) -> Self {
        Self {
            value,
            drops: Rc::clone(drops),
        }
    }
}

impl Drop for DropSpy {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

#[test]
fn new_is_empty() {
    let buffer = ErrorBuffer::<u8, 3>::new();

    assert_eq!(buffer.len(), 0);
}

#[test]
fn push_increases_len() {
    let mut buffer = ErrorBuffer::<u8, 3>::new();

    buffer.push(1);
    assert_eq!(buffer.len(), 1);

    buffer.push(2);
    assert_eq!(buffer.len(), 2);

    buffer.push(3);
    assert_eq!(buffer.len(), 3);
}

#[test]
fn take_preserves_insertion_order() {
    let mut buffer = ErrorBuffer::<String, 3>::new();

    buffer.push(String::from("first"));
    buffer.push(String::from("second"));
    buffer.push(String::from("third"));

    let errors = buffer.take();

    assert_eq!(
        errors,
        [
            String::from("first"),
            String::from("second"),
            String::from("third"),
        ]
    );
    assert_eq!(buffer.len(), 0);
}

#[test]
fn take_transfers_ownership_without_double_drop() {
    let drops = Rc::new(Cell::new(0));
    let mut buffer = ErrorBuffer::<DropSpy, 3>::new();

    buffer.push(DropSpy::new(1, &drops));
    buffer.push(DropSpy::new(2, &drops));
    buffer.push(DropSpy::new(3, &drops));

    let errors = buffer.take();

    assert_eq!(buffer.len(), 0);
    assert_eq!(drops.get(), 0);

    drop(buffer);

    assert_eq!(drops.get(), 0);

    drop(errors);

    assert_eq!(drops.get(), 3);
}

#[test]
fn buffer_can_be_reused_after_take() {
    let mut buffer = ErrorBuffer::<String, 2>::new();

    buffer.push(String::from("a"));
    buffer.push(String::from("b"));

    let first = buffer.take();

    assert_eq!(first, [String::from("a"), String::from("b")]);
    assert_eq!(buffer.len(), 0);

    buffer.push(String::from("c"));
    buffer.push(String::from("d"));

    let second = buffer.take();

    assert_eq!(second, [String::from("c"), String::from("d")]);
    assert_eq!(buffer.len(), 0);
}

#[test]
fn dropping_empty_buffer_drops_nothing() {
    let drops = Rc::new(Cell::new(0));
    let buffer = ErrorBuffer::<DropSpy, 3>::new();

    drop(buffer);

    assert_eq!(drops.get(), 0);
}

#[test]
fn dropping_partial_buffer_drops_only_initialized_entries() {
    let drops = Rc::new(Cell::new(0));
    let mut buffer = ErrorBuffer::<DropSpy, 4>::new();

    buffer.push(DropSpy::new(1, &drops));
    buffer.push(DropSpy::new(2, &drops));

    assert_eq!(drops.get(), 0);

    drop(buffer);

    assert_eq!(drops.get(), 2);
}

#[test]
fn dropping_full_buffer_drops_every_entry() {
    let drops = Rc::new(Cell::new(0));
    let mut buffer = ErrorBuffer::<DropSpy, 3>::new();

    buffer.push(DropSpy::new(1, &drops));
    buffer.push(DropSpy::new(2, &drops));
    buffer.push(DropSpy::new(3, &drops));

    drop(buffer);

    assert_eq!(drops.get(), 3);
}

#[test]
fn failed_take_preserves_initialized_entries() {
    let drops = Rc::new(Cell::new(0));
    let mut buffer = ErrorBuffer::<DropSpy, 3>::new();

    buffer.push(DropSpy::new(1, &drops));
    buffer.push(DropSpy::new(2, &drops));

    let result = catch_unwind(AssertUnwindSafe(|| {
        let _ = buffer.take();
    }));

    assert!(result.is_err());
    assert_eq!(buffer.len(), 2);
    assert_eq!(drops.get(), 0);

    drop(buffer);

    assert_eq!(drops.get(), 2);
}

#[test]
fn failed_push_preserves_existing_entries() {
    let drops = Rc::new(Cell::new(0));
    let mut buffer = ErrorBuffer::<DropSpy, 1>::new();

    buffer.push(DropSpy::new(1, &drops));

    let result = catch_unwind(AssertUnwindSafe(|| {
        buffer.push(DropSpy::new(2, &drops));
    }));

    assert!(result.is_err());
    assert_eq!(drops.get(), 1);
    assert_eq!(buffer.len(), 1);

    let [error] = buffer.take();

    assert_eq!(error.value, 1);
    assert_eq!(drops.get(), 1);

    drop(buffer);

    assert_eq!(drops.get(), 1);

    drop(error);

    assert_eq!(drops.get(), 2);
}

#[test]
#[should_panic(expected = "attempt error buffer is full")]
fn push_panics_when_full() {
    let mut buffer = ErrorBuffer::<u8, 1>::new();

    buffer.push(1);
    buffer.push(2);
}

#[test]
#[should_panic(expected = "attempt error buffer must be full before unwrapping")]
fn take_panics_when_not_full() {
    let mut buffer = ErrorBuffer::<u8, 2>::new();

    buffer.push(1);

    let _ = buffer.take();
}

#[test]
fn zero_capacity_buffer_can_be_taken() {
    let mut buffer = ErrorBuffer::<u8, 0>::new();

    assert_eq!(buffer.len(), 0);

    let errors = buffer.take();

    assert_eq!(errors, []);
    assert_eq!(buffer.len(), 0);
}

#[test]
fn zero_capacity_push_panics_and_drops_value() {
    let drops = Rc::new(Cell::new(0));
    let mut buffer = ErrorBuffer::<DropSpy, 0>::new();

    let result = catch_unwind(AssertUnwindSafe(|| {
        buffer.push(DropSpy::new(1, &drops));
    }));

    assert!(result.is_err());
    assert_eq!(buffer.len(), 0);
    assert_eq!(drops.get(), 1);
}

#[test]
fn zero_sized_values_work() {
    #[derive(Debug, PartialEq, Eq)]
    struct Zst;

    let mut buffer = ErrorBuffer::<Zst, 3>::new();

    buffer.push(Zst);
    buffer.push(Zst);
    buffer.push(Zst);

    assert_eq!(buffer.len(), 3);

    let errors = buffer.take();

    assert_eq!(errors, [Zst, Zst, Zst]);
    assert_eq!(buffer.len(), 0);
}

#[test]
fn over_aligned_values_work() {
    #[repr(align(64))]
    #[derive(Debug, PartialEq, Eq)]
    struct Aligned(u8);

    let mut buffer = ErrorBuffer::<Aligned, 2>::new();

    buffer.push(Aligned(1));
    buffer.push(Aligned(2));

    assert_eq!(buffer.len(), 2);

    let errors = buffer.take();

    assert_eq!(errors, [Aligned(1), Aligned(2)]);
    assert_eq!(buffer.len(), 0);
}
