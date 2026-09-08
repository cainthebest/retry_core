use crate::mode::RetryMode;

#[doc(hidden)]
pub trait RetryDelay<Mode>
where
    Mode: RetryMode,
{
    type Wait;

    fn delay(&mut self, retry: usize) -> Self::Wait;
}

#[doc(hidden)]
pub struct WithDelay<O, D> {
    pub(crate) operation: O,
    pub(crate) delay: D,
}
