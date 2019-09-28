#![doc(
    html_root_url = "https://docs.rs/err-context/0.1.0/err-context/",
    test(attr(deny(warnings)))
)]
#![forbid(unsafe_code)]
#![warn(missing_docs)]

use std::error::Error;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::mem;

pub type AnyError = Box<dyn Error + Send + Sync>;

#[derive(Copy, Clone, Debug)]
pub struct Chain<'a>(Option<&'a (dyn Error + 'static)>);

impl<'a> Iterator for Chain<'a> {
    type Item = &'a (dyn Error + 'static);
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.0.take();
        if let Some(current) = current {
            self.0 = current.source();
        }
        current
    }
}

#[derive(Copy, Clone, Debug)]
pub struct DisplayChain<'a, S> {
    chain: Chain<'a>,
    separator: S,
}

impl<S: Display> Display for DisplayChain<'_, S> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        let mut started = false;
        // Note: iteration takes &mut, but Chain is copy, so we iterate over a copy.
        for level in self.chain {
            if mem::replace(&mut started, true) {
                write!(fmt, "{}", self.separator)?;
            }
            write!(fmt, "{}", level)?;
        }
        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Context<M, E> {
    msg: M,
    inner: E,
}

impl<M: Display, E> Display for Context<M, E> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        self.msg.fmt(fmt)
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

#[derive(Debug)]
pub struct BoxContext<M, E: ?Sized> {
    msg: M,
    inner: Box<E>,
}

impl<M, E: ?Sized> BoxContext<M, E> {
    pub fn new(msg: M, error: Box<E>) -> Self {
        Self {
            msg,
            inner: error,
        }
    }

    pub fn into_inner(self) -> Box<E> {
        self.inner
    }
}

impl<M: Display, E: ?Sized> Display for BoxContext<M, E> {
    fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
        self.msg.fmt(fmt)
    }
}

macro_rules! impl_err {
    ($ty: ty) => {
        impl<M: Debug + Display> Error for BoxContext<M, $ty> {
            fn source(&self) -> Option<&(dyn Error + 'static)> {
                Some(&*self.inner)
            }
        }
    }
}

impl_err!(dyn Error + Send + Sync);
impl_err!(dyn Error + Send);
impl_err!(dyn Error + Sync);
impl_err!(dyn Error);

#[cfg(feature = "failure")]
impl<M> Context<M, failure::Compat<failure::Error>> {
    pub fn from_failure(msg: M, failure: failure::Error) -> Self {
        Self::new(msg, failure.compat())
    }
}

pub trait ErrorExt: Sized {
    fn context<M: Display>(self, msg: M) -> Context<M, Self>;
    fn chain(&self) -> Chain<'_>
    where
        Self: 'static;
    fn find_source<T: Error + 'static>(&self) -> Option<&T>
    where
        Self: 'static,
    {
        self.chain().find_map(|e| e.downcast_ref::<T>())
    }
    fn display<S: Display>(&self, separator: S) -> DisplayChain<'_, S>
    where
        Self: 'static,
    {
        DisplayChain {
            chain: self.chain(),
            separator,
        }
    }
}

impl<E: Error> ErrorExt for E {
    fn context<M: Display>(self, msg: M) -> Context<M, Self> {
        Context::new(msg, self)
    }
    fn chain(&self) -> Chain<'_>
    where
        Self: 'static
    {
        Chain(Some(self))
    }
}

pub trait AnyErrorExt<E: ?Sized>: Sized {
    fn context<M: Display>(self, msg: M) -> BoxContext<M, E>;
    fn chain(&self) -> Chain<'_>;
    fn find_source<T: Error + 'static>(&self) -> Option<&T> {
        self.chain().find_map(|e| e.downcast_ref::<T>())
    }
    fn display<S: Display>(&self, separator: S) -> DisplayChain<'_, S> {
        DisplayChain {
            chain: self.chain(),
            separator,
        }
    }
}

macro_rules! impl_any_error {
    ($ty: ty) => {
        impl AnyErrorExt<$ty> for Box<$ty> {
            fn context<M: Display>(self, msg: M) -> BoxContext<M, $ty> {
                BoxContext::new(msg, self)
            }
            fn chain(&self) -> Chain<'_> {
                Chain(Some(&**self))
            }
        }
    }
}

impl_any_error!(dyn Error + Send + Sync);
impl_any_error!(dyn Error + Send);
impl_any_error!(dyn Error + Sync);
impl_any_error!(dyn Error);

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
    fn context<M>(self, msg: M) -> Result<T, BoxContext<M, E>>
    where
        M: Display;

    fn with_context<F, M>(self, f: F) -> Result<T, BoxContext<M, E>>
    where
        F: FnOnce(&Box<E>) -> M,
        M: Display;
}

macro_rules! any_result_impl {
    ($ty: ty) => {
        impl<T> AnyResultExt<T, $ty> for Result<T, Box<$ty>> {
            fn context<M>(self, msg: M) -> Result<T, BoxContext<M, $ty>>
            where
                M: Display
            {
                self.map_err(|e| e.context(msg))
            }

            fn with_context<F, M>(self, f: F) -> Result<T, BoxContext<M, $ty>>
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

    #[derive(Copy, Clone, Debug)]
    struct Dummy;

    impl Display for Dummy {
        fn fmt(&self, fmt: &mut Formatter) -> FmtResult {
            write!(fmt, "Dummy error!")
        }
    }

    impl Error for Dummy {}

    fn get_chain() -> AnyError {
        Dummy.context("Sorry").into()
    }

    fn get_boxed() -> AnyError {
        Dummy.into()
    }

    fn get_boxed_chain() -> AnyError {
        let a = get_boxed().context("Sorry");
        a.into()
    }

    #[test]
    fn iter_chain() {
        assert_eq!(1, Dummy.chain().count());
        assert_eq!(2, get_chain().chain().count());
    }

    #[test]
    fn find_dummy() {
        assert!(Dummy.find_source::<Dummy>().is_some());
        assert!(get_chain().find_source::<Dummy>().is_some());
        assert!(get_boxed_chain().find_source::<Dummy>().is_some());
        assert!(get_chain().find_source::<IoError>().is_none());
    }

    #[test]
    fn display_chain() {
        let chain = get_chain();
        assert_eq!("Sorry", chain.to_string());
        assert_eq!("Sorry: Dummy error!", chain.display(": ").to_string());
    }
}
