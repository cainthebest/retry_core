use {super::super::BlockingRetry, crate::adapter::InspectRetry};

impl<O, I, T, E> BlockingRetry<T, E> for InspectRetry<O, I>
where
    O: BlockingRetry<T, E>,
    I: FnMut(usize, &E),
{
    #[inline]
    fn call(&mut self) -> Result<T, E> {
        self.operation.call()
    }

    #[inline]
    fn inspect_retry(&mut self, retry: usize, error: &E) {
        self.operation.inspect_retry(retry, error);

        (self.inspect)(retry, error);
    }

    #[inline]
    fn delay(&mut self, retry: usize) {
        self.operation.delay(retry);
    }
}
