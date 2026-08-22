use core::{mem::MaybeUninit, ptr, slice};

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
    pub const fn len(&self) -> usize {
        self.initialized
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.initialized == 0
    }

    #[inline]
    pub const fn is_full(&self) -> bool {
        self.initialized == ATTEMPTS
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        ATTEMPTS
    }

    #[inline]
    pub fn as_slice(&self) -> &[E] {
        unsafe { slice::from_raw_parts(self.entries.as_ptr().cast::<E>(), self.initialized) }
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
    pub(crate) const fn take_buffer(&mut self) -> Self {
        let buffer = unsafe { ptr::read(self) };

        self.initialized = 0;

        buffer
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

impl<E, const ATTEMPTS: usize> AsRef<[E]> for ErrorBuffer<E, ATTEMPTS> {
    #[inline]
    fn as_ref(&self) -> &[E] {
        self.as_slice()
    }
}

impl<E, const ATTEMPTS: usize> Drop for ErrorBuffer<E, ATTEMPTS> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}
