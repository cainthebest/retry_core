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
    pub(crate) fn ensure_active<F>(&mut self, future: F)
    where
        F: FnOnce() -> Fut,
    {
        if self.is_empty() {
            *self = Self::Active(future());
        }
    }

    #[inline]
    pub(crate) fn clear_ready_future(&mut self) {
        debug_assert!(matches!(self, Self::Active(_)));

        *self = Self::Empty;
    }

    #[inline]
    pub(crate) fn complete(&mut self) {
        *self = Self::Complete;
    }

    #[inline]
    pub(crate) fn poll(&mut self, cx: &mut Context<'_>) -> Poll<Fut::Output>
    where
        Fut: Future,
    {
        let Self::Active(future) = self else {
            panic!("future slot must be active before polling");
        };

        // SAFETY:
        //
        // The owning retry future is pinned before polling and remains pinned
        // for the lifetime of the active future, so the future is not moved
        // after it has been polled.
        unsafe { Pin::new_unchecked(future) }.poll(cx)
    }
}
