use crate::storage::FutureSlot;

#[doc(hidden)]
pub struct DelayState<S, Fut> {
    pub(crate) inner: S,
    pub(crate) future: FutureSlot<Fut>,
}

impl<S, Fut> DelayState<S, Fut> {
    #[inline]
    pub(crate) const fn new(inner: S) -> Self {
        Self {
            inner,
            future: FutureSlot::new(),
        }
    }
}
