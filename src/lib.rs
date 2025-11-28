#![no_std]

use core::{array, future::Future};

pub trait Retry<T, E> {
    #[must_use = "retry executes the operation; ignoring the result means the operation was never run"]
    fn retry<const N: usize>(self) -> Result<T, [Option<E>; N]>;
}

impl<T, E, F> Retry<T, E> for F
where
    F: FnMut() -> Result<T, E>,
{
    #[inline]
    fn retry<const N: usize>(mut self) -> Result<T, [Option<E>; N]> {
        let mut errors: [Option<E>; N] = array::from_fn(|_| None);

        for slot in &mut errors {
            match self() {
                Ok(value) => return Ok(value),
                Err(err) => *slot = Some(err),
            }
        }

        Err(errors)
    }
}

pub trait RetryFut<T, E> {
    #[must_use = "retry executes the async operation; ignoring the result means the operation was never awaited"]
    fn retry<const N: usize>(self) -> impl Future<Output = Result<T, [Option<E>; N]>>;
}

impl<T, E, F, Fut> RetryFut<T, E> for F
where
    F: FnMut() -> Fut + Sized,
    Fut: Future<Output = Result<T, E>>,
{
    #[inline]
    #[allow(clippy::manual_async_fn)]
    fn retry<const N: usize>(mut self) -> impl Future<Output = Result<T, [Option<E>; N]>> {
        async move {
            let mut errors: [Option<E>; N] = array::from_fn(|_| None);

            for slot in &mut errors {
                match self().await {
                    Ok(value) => return Ok(value),
                    Err(err) => *slot = Some(err),
                }
            }

            Err(errors)
        }
    }
}
