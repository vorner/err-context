use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};

pub type AnyError = Box<dyn Error + Send + Sync>;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(transparent)]
pub struct Wrapped<T>(T);

impl<T: Display> Display for Wrapped<T> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        self.0.fmt(fmt)
    }
}

impl<T: Error + ?Sized> Error for Wrapped<Box<T>> {
    fn description(&self) -> &str {
        self.0.description()
    }
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.0.source()
    }
}

pub struct Context<M, E> {
    msg: M,
    inner: E,
}

impl<M: Display, E> Display for Context<M, E> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        self.msg.fmt(fmt)
    }
}

impl<M: Debug, E: Debug> Debug for Context<M, E> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        fmt.debug_struct("Context")
            .field("msg", &self.msg)
            .field("inner", &self.inner)
            .finish()
    }
}

impl<M: Debug + Display, E: Error + 'static> Error for Context<M, E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&self.inner)
    }
}

impl<M, E> Context<M, E> {
    pub fn new(msg: M, error: E) -> Self {
        Self {
            msg,
            inner: error,
        }
    }

    pub fn into_inner(self) -> E {
        self.inner
    }
}

#[cfg(feature = "failure")]
impl<M> Context<M, failure::Compat<failure::Error>> {
    pub fn from_failure(msg: M, failure: failure::Error) -> Self {
        Self::new(msg, failure.compat())
    }
}

impl<M, E: ?Sized> Context<M, Wrapped<Box<E>>> {
    pub fn from_boxed(msg: M, error: Box<E>) -> Self {
        Self {
            msg,
            inner: Wrapped(error),
        }
    }
}

pub trait ErrorExt: Sized {
    fn context<M: Display>(self, msg: M) -> Context<M, Self>;
}

impl<E: Error> ErrorExt for E {
    fn context<M: Display>(self, msg: M) -> Context<M, Self> {
        Context::new(msg, self)
    }
}

pub trait AnyErrorExt: Sized {
    fn context<M: Display>(self, msg: M) -> Context<M, Wrapped<Self>>;
}

impl<E: Error + ?Sized> AnyErrorExt for Box<E> {
    fn context<M: Display>(self, msg: M) -> Context<M, Wrapped<Box<E>>> {
        Context::from_boxed(msg, self)
    }
}

pub trait ResultExt<T, E>: Sized {
    fn context<M>(self, msg: M) -> Result<T, Context<M, E>>
    where
        M: Display;

    fn with_context<F, M>(self, f: F) -> Result<T, Context<M, E>>
    where
        F: FnOnce(&E) -> M,
        M: Display;
}

impl<T, E: Error> ResultExt<T, E> for Result<T, E> {
    fn context<M>(self, msg: M) -> Result<T, Context<M, E>>
    where
        M: Display
    {
        self.map_err(|e| e.context(msg))
    }

    fn with_context<F, M>(self, f: F) -> Result<T, Context<M, E>>
    where
        F: FnOnce(&E) -> M,
        M: Display
    {
        self.map_err(|e| {
            let msg = f(&e);
            e.context(msg)
        })
    }
}

pub trait AnyResultExt<T, E: ?Sized> {
    fn context<M>(self, msg: M) -> Result<T, Context<M, Wrapped<Box<E>>>>
    where
        M: Display;

    fn with_context<F, M>(self, f: F) -> Result<T, Context<M, Wrapped<Box<E>>>>
    where
        F: FnOnce(&Box<E>) -> M,
        M: Display;
}

macro_rules! any_result_impl {
    ($ty: ty) => {
        impl<T> AnyResultExt<T, $ty> for Result<T, Box<$ty>> {
            fn context<M>(self, msg: M) -> Result<T, Context<M, Wrapped<Box<$ty>>>>
            where
                M: Display
            {
                self.map_err(|e| e.context(msg))
            }

            fn with_context<F, M>(self, f: F) -> Result<T, Context<M, Wrapped<Box<$ty>>>>
            where
                F: FnOnce(&Box<$ty>) -> M,
                M: Display
            {
                self.map_err(|e| {
                    let msg = f(&e);
                    e.context(msg)
                })
            }
        }
    }
}

any_result_impl!(dyn Error + Send + Sync);
any_result_impl!(dyn Error + Send);
any_result_impl!(dyn Error + Sync);
any_result_impl!(dyn Error);

pub mod prelude {
    pub use crate::ErrorExt as _;
    pub use crate::AnyErrorExt as _;
    pub use crate::ResultExt as _;
    pub use crate::AnyResultExt as _;
}

#[cfg(test)]
mod tests {
    use std::io::{Error as IoError, Read};
    use super::*;

    fn _wrapped_any_error() -> impl Error {
        let e: AnyError = IoError::last_os_error().into();
        Wrapped(e)
    }

    fn _context_error() -> impl Error {
        IoError::last_os_error().context("Hello")
    }

    fn _context_any_error() -> impl Error {
        let e: AnyError = IoError::last_os_error().into();
        e.context(42)
    }

    fn _context_result() -> Result<(), AnyError> {
        let mut buf = [0];
        std::io::stdin().read(&mut buf).context("Failed to read line")?;
        Ok(())
    }

    fn _double_context() -> Result<(), AnyError> {
        _context_result().with_context(|e| format!("Hey: {}", e))?;
        Ok(())
    }
}
