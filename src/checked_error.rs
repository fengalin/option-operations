/// TODO doc
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CheckedError {
    /// TODO doc
    Overflow,
}

// FIXME add Error impl when std feature is selected

impl CheckedError {
    /// TODO doc
    pub fn is_overflow(&self) -> bool {
        matches!(self, CheckedError::Overflow)
    }
}