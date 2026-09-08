use core::{
    future::Future,
    pin::Pin,
    task::{Context, Poll},
};

pub(crate) enum FutureSlot<Fut> {
    Empty,
    Active(Fut),
    Complete,
}

impl<Fut> FutureSlot<Fut> {
    #[inline]
    pub(crate) const fn new() -> Self {
        Self::Empty
    }

    #[inline]
    pub(crate) const fn is_empty(&self) -> bool {
        match self {
            Self::Empty => true,
            _ => false,
        }
    }

    #[inline]
    pub(crate) const fn is_complete(&self) -> bool {
        match self {
            Self::Complete => true,
            _ => false,
        }
    }

    #[inline]
    pub(crate) fn ensure_active<F>(mut self: Pin<&mut Self>, future: F)
    where
        F: FnOnce() -> Fut,
    {
        if self.as_ref().get_ref().is_empty() {
            self.set(Self::Active(future()));
        }
    }

    #[inline]
    pub(crate) fn clear_ready_future(mut self: Pin<&mut Self>) {
        debug_assert!(matches!(self.as_ref().get_ref(), Self::Active(_)));

        self.set(Self::Empty);
    }

    #[inline]
    pub(crate) fn complete(mut self: Pin<&mut Self>) {
        self.set(Self::Complete);
    }

    #[inline]
    pub(crate) fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Fut::Output>
    where
        Fut: Future,
    {
        // SAFETY:
        //
        // `FutureSlot` is pinned, and the active future is structurally
        // pinned by the slot. The future is never moved while active.
        let this = unsafe { self.get_unchecked_mut() };

        let Self::Active(future) = this else {
            panic!("future slot must be active before polling");
        };

        // SAFETY:
        //
        // `future` is structurally pinned by the pinned `FutureSlot`.
        unsafe { Pin::new_unchecked(future) }.poll(cx)
    }
}
