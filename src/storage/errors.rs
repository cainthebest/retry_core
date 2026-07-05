use core::{mem::MaybeUninit, ptr};

pub(crate) struct AttemptErrorBuffer<E, const ATTEMPTS: usize> {
    entries: [MaybeUninit<E>; ATTEMPTS],
    initialized: usize,
}

impl<E, const ATTEMPTS: usize> AttemptErrorBuffer<E, ATTEMPTS> {
    #[inline]
    pub(crate) const fn new() -> Self {
        Self {
            entries: [const { MaybeUninit::uninit() }; ATTEMPTS],
            initialized: 0,
        }
    }

    #[inline]
    pub(crate) const fn is_full(&self) -> bool {
        self.initialized == ATTEMPTS
    }

    #[inline]
    pub(crate) const fn push(&mut self, error: E) {
        assert!(self.initialized < ATTEMPTS, "attempt error buffer is full");

        self.entries[self.initialized].write(error);
        self.initialized += 1;
    }

    #[inline]
    pub(crate) const fn unwrap(&mut self) -> [E; ATTEMPTS] {
        assert!(
            self.initialized == ATTEMPTS,
            "attempt error buffer must be full before unwrapping"
        );

        let mut output = MaybeUninit::<[E; ATTEMPTS]>::uninit();

        // SAFETY:
        //
        // `initialized == ATTEMPTS` guarantees every source entry is initialized.
        // `self.entries` and `output` are distinct storage locations, so they do not overlap.
        //
        // Both pointers are properly aligned, including when `ATTEMPTS == 0`.
        // `copy_nonoverlapping` preserves initialization state exactly.
        //
        // This is a move, not a clone: after copying the bytes, `initialized` is set
        // to zero so the source entries are no longer dropped by this buffer.
        unsafe {
            ptr::copy_nonoverlapping(
                self.entries.as_ptr(),
                output.as_mut_ptr().cast::<MaybeUninit<E>>(),
                ATTEMPTS,
            );
        }

        self.initialized = 0;

        // SAFETY:
        //
        // The assertion above guarantees all `ATTEMPTS` entries were initialized,
        // and the copy above moved those initialized entries into `output`.
        unsafe { output.assume_init() }
    }
}

impl<E, const ATTEMPTS: usize> Drop for AttemptErrorBuffer<E, ATTEMPTS> {
    fn drop(&mut self) {
        for index in 0..self.initialized {
            // SAFETY:
            //
            // Every entry below `initialized` is initialized and has not been moved out.
            unsafe {
                self.entries[index].assume_init_drop();
            }
        }
    }
}
