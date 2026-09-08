use core::{mem::MaybeUninit, ptr};

pub(crate) struct ErrorBuffer<E, const ATTEMPTS: usize> {
    entries: [MaybeUninit<E>; ATTEMPTS],
    initialized: usize,
}

impl<E, const ATTEMPTS: usize> ErrorBuffer<E, ATTEMPTS> {
    #[inline]
    pub(crate) const fn new() -> Self {
        Self {
            entries: [const { MaybeUninit::uninit() }; ATTEMPTS],
            initialized: 0,
        }
    }

    #[inline]
    pub(crate) const fn len(&self) -> usize {
        self.initialized
    }

    #[inline]
    pub(crate) const fn push(&mut self, error: E) {
        assert!(self.initialized < ATTEMPTS, "attempt error buffer is full");

        self.entries[self.initialized].write(error);
        self.initialized += 1;
    }

    #[inline]
    pub(crate) const fn take(&mut self) -> [E; ATTEMPTS] {
        assert!(
            self.initialized == ATTEMPTS,
            "attempt error buffer must be full before unwrapping"
        );

        self.initialized = 0;

        // SAFETY: every entry was initialized and ownership is transferred.
        unsafe { ptr::read(self.entries.as_ptr().cast::<[E; ATTEMPTS]>()) }
    }
}

impl<E, const ATTEMPTS: usize> Drop for ErrorBuffer<E, ATTEMPTS> {
    #[inline]
    fn drop(&mut self) {
        for index in 0..self.initialized {
            unsafe {
                self.entries[index].assume_init_drop();
            }
        }
    }
}
