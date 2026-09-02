#[doc(hidden)]
pub struct InspectRetry<O, I> {
    pub(crate) operation: O,
    pub(crate) inspect: I,
}
