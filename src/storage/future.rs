use core::{
    future::Future,
    mem::MaybeUninit,
    pin::Pin,
    task::{Context, Poll},
};

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum FutureSlotState {
    Empty,
    Active,
    Complete,
}

pub(crate) struct FutureSlot<Fut> {
    future: MaybeUninit<Fut>,
    state: FutureSlotState,
}

impl<Fut> FutureSlot<Fut> {
    #[inline]
    pub(crate) const fn new() -> Self {
        Self {
            future: MaybeUninit::uninit(),
            state: FutureSlotState::Empty,
        }
    }

    #[inline]
    pub(crate) const fn is_empty(&self) -> bool {
        matches!(self.state, FutureSlotState::Empty)
    }

    #[inline]
    const fn is_active(&self) -> bool {
        matches!(self.state, FutureSlotState::Active)
    }

    #[inline]
    pub(crate) const fn is_complete(&self) -> bool {
        matches!(self.state, FutureSlotState::Complete)
    }

    #[inline]
    pub(crate) fn ensure_active<F>(&mut self, future: F)
    where
        F: FnOnce() -> Fut,
    {
        if self.is_empty() {
            self.future.write(future());
            self.state = FutureSlotState::Active;
        }
    }

    #[inline]
    pub(crate) fn complete(&mut self) {
        match self.state {
            FutureSlotState::Empty => {
                self.state = FutureSlotState::Complete;
            }

            FutureSlotState::Active => {
                self.drop_active_future_and_set(FutureSlotState::Complete);
            }

            FutureSlotState::Complete => {}
        }
    }

    #[inline]
    pub(crate) fn clear_ready_future(&mut self) {
        if self.is_active() {
            self.drop_active_future_and_set(FutureSlotState::Empty);
        }
    }

    #[inline]
    pub(crate) fn poll(&mut self, cx: &mut Context<'_>) -> Poll<Fut::Output>
    where
        Fut: Future,
    {
        assert!(
            self.is_active(),
            "future slot must be active before polling"
        );

        // SAFETY:
        //
        // `Active` means `future` is initialized.
        //
        // The owning retry future is pinned before polling and is `!Unpin`, so
        // this active future will not be moved after being polled.
        let future = unsafe { Pin::new_unchecked(self.future.assume_init_mut()) };

        future.poll(cx)
    }

    #[inline]
    fn drop_active_future_and_set(&mut self, next_state: FutureSlotState) {
        assert!(
            self.is_active(),
            "future slot must be active before dropping"
        );

        // Set the new state before dropping. If `Fut::drop` panics, `Drop` for
        // `FutureSlot` will not double-drop the future during unwinding.
        self.state = next_state;

        // SAFETY:
        //
        // Callers only enter this method when the previous state was `Active`,
        // meaning `future` is initialized.
        unsafe {
            self.future.assume_init_drop();
        }
    }
}

impl<Fut> Drop for FutureSlot<Fut> {
    fn drop(&mut self) {
        if self.is_active() {
            self.drop_active_future_and_set(FutureSlotState::Complete);
        }
    }
}
