#[doc(hidden)]
pub struct OnlyIf<O, P> {
    pub(crate) operation: O,
    pub(crate) predicate: P,
}
