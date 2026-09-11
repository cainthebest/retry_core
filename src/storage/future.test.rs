use {
    super::FutureSlot,
    core::{
        cell::Cell,
        future::{Future, Pending, Ready, pending, ready},
        marker::PhantomPinned,
        pin::Pin,
        ptr,
        task::{Context, Poll, Waker},
    },
    std::{
        panic::{AssertUnwindSafe, catch_unwind},
        rc::Rc,
    },
};

struct DropFuture {
    value: usize,
    drops: Rc<Cell<usize>>,
}

impl DropFuture {
    fn new(value: usize, drops: &Rc<Cell<usize>>) -> Self {
        Self {
            value,
            drops: Rc::clone(drops),
        }
    }
}

impl Future for DropFuture {
    type Output = usize;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.as_ref().get_ref().value)
    }
}

impl Drop for DropFuture {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

struct PanicOnPoll {
    drops: Rc<Cell<usize>>,
}

impl Future for PanicOnPoll {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        panic!("poll panic");
    }
}

impl Drop for PanicOnPoll {
    fn drop(&mut self) {
        self.drops.set(self.drops.get() + 1);
    }
}

struct PinnedFuture {
    address: Cell<*const Self>,
    polls: Cell<usize>,
    ready_after: usize,
    drops: Rc<Cell<usize>>,
    _pin: PhantomPinned,
}

impl PinnedFuture {
    fn new(ready_after: usize, drops: &Rc<Cell<usize>>) -> Self {
        Self {
            address: Cell::new(ptr::null()),
            polls: Cell::new(0),
            ready_after,
            drops: Rc::clone(drops),
            _pin: PhantomPinned,
        }
    }

    fn check_address(&self) {
        let current = ptr::from_ref(self);
        let original = self.address.get();

        if original.is_null() {
            self.address.set(current);
        } else {
            assert_eq!(original, current, "pinned future moved after being polled");
        }
    }
}

impl Future for PinnedFuture {
    type Output = usize;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = self.as_ref().get_ref();

        this.check_address();

        let polls = this.polls.get() + 1;
        this.polls.set(polls);

        if polls >= this.ready_after {
            Poll::Ready(polls)
        } else {
            Poll::Pending
        }
    }
}

impl Drop for PinnedFuture {
    fn drop(&mut self) {
        let original = self.address.get();

        if !original.is_null() {
            assert_eq!(
                original,
                ptr::from_ref(self),
                "pinned future moved before being dropped"
            );
        }

        self.drops.set(self.drops.get() + 1);
    }
}

#[test]
fn new_is_empty_and_not_complete() {
    let slot = FutureSlot::<()>::new();

    assert!(slot.is_empty());
    assert!(!slot.is_complete());
}

#[test]
fn state_queries_work_in_const_context() {
    const IS_EMPTY: bool = FutureSlot::<()>::new().is_empty();
    const IS_COMPLETE: bool = FutureSlot::<()>::new().is_complete();

    assert!(IS_EMPTY);
    assert!(!IS_COMPLETE);
}

#[test]
fn ensure_active_initializes_empty_slot() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().ensure_active(|| ready(42));

    assert!(!slot.as_ref().get_ref().is_empty());
    assert!(!slot.as_ref().get_ref().is_complete());

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(42));
}

#[test]
fn ensure_active_does_not_replace_active_future() {
    use core::sync::atomic::{AtomicUsize, Ordering};

    static CALLS: AtomicUsize = AtomicUsize::new(0);

    fn make_future() -> Ready<usize> {
        let value = CALLS.fetch_add(1, Ordering::Relaxed) + 1;

        ready(value)
    }

    CALLS.store(0, Ordering::Relaxed);

    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    let make: fn() -> Ready<usize> = make_future;

    slot.as_mut().ensure_active(make);
    slot.as_mut().ensure_active(make);

    assert_eq!(CALLS.load(Ordering::Relaxed), 1);

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(1));
}

#[test]
fn ensure_active_does_not_initialize_complete_slot() {
    let calls = Cell::new(0);
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().complete();

    slot.as_mut().ensure_active(|| {
        calls.set(calls.get() + 1);
        ready(1)
    });

    assert_eq!(calls.get(), 0);
    assert!(slot.as_ref().get_ref().is_complete());
    assert!(!slot.as_ref().get_ref().is_empty());
}

#[test]
fn panic_while_creating_future_leaves_slot_empty() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    let result = catch_unwind(AssertUnwindSafe(|| {
        slot.as_mut().ensure_active(|| {
            panic!("constructor panic");
        });
    }));

    assert!(result.is_err());
    assert!(slot.as_ref().get_ref().is_empty());
    assert!(!slot.as_ref().get_ref().is_complete());
}

#[test]
fn poll_pending_keeps_future_active() {
    let mut slot = core::pin::pin!(FutureSlot::<Pending<usize>>::new());

    slot.as_mut().ensure_active(pending);

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Pending);
    assert!(!slot.as_ref().get_ref().is_empty());
    assert!(!slot.as_ref().get_ref().is_complete());
}

#[test]
fn poll_ready_keeps_future_active_until_cleared() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().ensure_active(|| ready(42));

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(42));
    assert!(!slot.as_ref().get_ref().is_empty());
    assert!(!slot.as_ref().get_ref().is_complete());

    slot.as_mut().clear_ready_future();

    assert!(slot.as_ref().get_ref().is_empty());
}

#[test]
#[should_panic(expected = "future slot must be active before polling")]
fn poll_empty_panics() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());
    let mut cx = Context::from_waker(Waker::noop());

    let _ = slot.as_mut().poll(&mut cx);
}

#[test]
#[should_panic(expected = "future slot must be active before polling")]
fn poll_complete_panics() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().complete();

    let mut cx = Context::from_waker(Waker::noop());

    let _ = slot.as_mut().poll(&mut cx);
}

#[test]
fn clear_ready_future_drops_active_future_once() {
    let drops = Rc::new(Cell::new(0));
    let mut slot = core::pin::pin!(FutureSlot::<DropFuture>::new());

    slot.as_mut().ensure_active(|| DropFuture::new(42, &drops));

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(42));
    assert_eq!(drops.get(), 0);

    slot.as_mut().clear_ready_future();

    assert_eq!(drops.get(), 1);
    assert!(slot.as_ref().get_ref().is_empty());
    assert!(!slot.as_ref().get_ref().is_complete());
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn clear_empty_slot_panics() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().clear_ready_future();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic]
fn clear_complete_slot_panics() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().complete();
    slot.as_mut().clear_ready_future();
}

#[test]
fn complete_empty_slot_sets_complete() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().complete();

    assert!(!slot.as_ref().get_ref().is_empty());
    assert!(slot.as_ref().get_ref().is_complete());
}

#[test]
fn complete_active_slot_drops_future_once() {
    let drops = Rc::new(Cell::new(0));
    let mut slot = core::pin::pin!(FutureSlot::<DropFuture>::new());

    slot.as_mut().ensure_active(|| DropFuture::new(42, &drops));

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(42));
    assert_eq!(drops.get(), 0);

    slot.as_mut().complete();

    assert_eq!(drops.get(), 1);
    assert!(slot.as_ref().get_ref().is_complete());
}

#[test]
fn complete_is_idempotent() {
    let mut slot = core::pin::pin!(FutureSlot::<Ready<usize>>::new());

    slot.as_mut().complete();
    slot.as_mut().complete();

    assert!(slot.as_ref().get_ref().is_complete());
}

#[test]
fn panic_during_poll_leaves_future_active_and_owned() {
    let drops = Rc::new(Cell::new(0));
    let mut slot = core::pin::pin!(FutureSlot::<PanicOnPoll>::new());

    slot.as_mut().ensure_active(|| PanicOnPoll {
        drops: Rc::clone(&drops),
    });

    let mut cx = Context::from_waker(Waker::noop());

    let result = catch_unwind(AssertUnwindSafe(|| {
        let _ = slot.as_mut().poll(&mut cx);
    }));

    assert!(result.is_err());
    assert_eq!(drops.get(), 0);
    assert!(!slot.as_ref().get_ref().is_empty());
    assert!(!slot.as_ref().get_ref().is_complete());

    slot.as_mut().complete();

    assert_eq!(drops.get(), 1);
    assert!(slot.as_ref().get_ref().is_complete());
}

#[test]
fn non_unpin_future_stays_at_same_address_across_polls() {
    let drops = Rc::new(Cell::new(0));
    let mut slot = core::pin::pin!(FutureSlot::<PinnedFuture>::new());

    slot.as_mut().ensure_active(|| PinnedFuture::new(2, &drops));

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Pending);
    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(2));

    assert_eq!(drops.get(), 0);

    slot.as_mut().clear_ready_future();

    assert_eq!(drops.get(), 1);
    assert!(slot.as_ref().get_ref().is_empty());
}

#[test]
fn clearing_non_unpin_future_drops_it_in_place() {
    let drops = Rc::new(Cell::new(0));
    let mut slot = core::pin::pin!(FutureSlot::<PinnedFuture>::new());

    slot.as_mut().ensure_active(|| PinnedFuture::new(1, &drops));

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(1));

    slot.as_mut().clear_ready_future();

    assert_eq!(drops.get(), 1);
    assert!(slot.as_ref().get_ref().is_empty());
}

#[test]
fn completing_non_unpin_future_drops_it_in_place() {
    let drops = Rc::new(Cell::new(0));
    let mut slot = core::pin::pin!(FutureSlot::<PinnedFuture>::new());

    slot.as_mut().ensure_active(|| PinnedFuture::new(1, &drops));

    let mut cx = Context::from_waker(Waker::noop());

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(1));

    slot.as_mut().complete();

    assert_eq!(drops.get(), 1);
    assert!(slot.as_ref().get_ref().is_complete());
}

#[test]
fn dropping_slot_drops_non_unpin_future_in_place() {
    let drops = Rc::new(Cell::new(0));

    {
        let mut slot = core::pin::pin!(FutureSlot::<PinnedFuture>::new());

        slot.as_mut().ensure_active(|| PinnedFuture::new(2, &drops));

        let mut cx = Context::from_waker(Waker::noop());

        assert_eq!(slot.as_mut().poll(&mut cx), Poll::Pending);
        assert_eq!(drops.get(), 0);
    }

    assert_eq!(drops.get(), 1);
}

#[test]
fn slot_can_reuse_storage_for_non_unpin_futures() {
    let drops = Rc::new(Cell::new(0));
    let mut slot = core::pin::pin!(FutureSlot::<PinnedFuture>::new());

    let mut cx = Context::from_waker(Waker::noop());

    slot.as_mut().ensure_active(|| PinnedFuture::new(1, &drops));

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(1));

    slot.as_mut().clear_ready_future();

    assert_eq!(drops.get(), 1);
    assert!(slot.as_ref().get_ref().is_empty());

    slot.as_mut().ensure_active(|| PinnedFuture::new(1, &drops));

    assert_eq!(slot.as_mut().poll(&mut cx), Poll::Ready(1));

    slot.as_mut().clear_ready_future();

    assert_eq!(drops.get(), 2);
    assert!(slot.as_ref().get_ref().is_empty());
}
