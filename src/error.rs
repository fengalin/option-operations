//! Error type which can be returned by some [`OptionOperations`].

// Required for doc
#[allow(unused)]
use crate::OptionOperations;

/// Error type which can be returned by some [`OptionOperations`].
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Error {
    /// An [`OptionOperations`] overflowed.
    Overflow,
    /// Division by zero attempted with an [`OptionOperations`].
    DivisionByZero,
}

// FIXME add Error impl when std feature is selected

impl Error {
    /// Returns `true` if this [`Error`] results from an overflow.
    pub fn is_overflow(&self) -> bool {
        matches!(self, Error::Overflow)
    }

    /// Returns `true` if this [`Error`] results from a division by zero.
    pub fn is_division_by_zero(&self) -> bool {
        matches!(self, Error::DivisionByZero)
    }
}
