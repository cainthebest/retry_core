use core::{mem::MaybeUninit, ptr};

pub struct ErrorBuffer<E, const ATTEMPTS: usize> {
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

        let mut output = MaybeUninit::<[E; ATTEMPTS]>::uninit();

        unsafe {
            ptr::copy_nonoverlapping(
                self.entries.as_ptr(),
                output.as_mut_ptr().cast::<MaybeUninit<E>>(),
                ATTEMPTS,
            );
        }

        self.initialized = 0;

        unsafe { output.assume_init() }
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        for index in 0..self.initialized {
            unsafe {
                self.entries[index].assume_init_drop();
            }
        }

        self.initialized = 0;
    }
}

impl<E, const ATTEMPTS: usize> Drop for ErrorBuffer<E, ATTEMPTS> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}
