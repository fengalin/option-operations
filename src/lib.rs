#![no_std]

pub trait OptionOperations {}

impl<T: OptionOperations> OptionOperations for &T {}
impl<T: OptionOperations> OptionOperations for &mut T {}

impl OptionOperations for usize {}
impl OptionOperations for u8 {}
impl OptionOperations for u64 {}
// FIXME impl for other numeric types
// FIXME impl for Duration & Instant

pub mod add;
pub use add::OptionAdd;

// TODO Eq

pub mod checked_error;
pub use checked_error::CheckedError;

pub mod ord;
pub use ord::OptionOrd;

pub mod min_max;
pub use min_max::OptionMinMax;

/*
/// Eq related operations.

/*
pub trait OptionEq<Rhs: Copy> {
    fn opt_eq(self, other: Rhs) -> Option<bool>;
    fn opt_ne(self, other: Rhs) -> Option<bool> {

     }
}
*/

/// Auto implementations for `Option<T>`.

impl<T: OptionOperations + PartialOrd> OptionOrd for Option<T> {
    type Inner = T;

    fn opt_cmp(self, other: impl Into<Option<Self::Inner>>) -> Option<Ordering> {
        match (self, other.into()) {
            (Some(this), Some(other)) => this.opt_cmp(other),
            (None, None) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

impl<T: OptionOperations + PartialOrd> OptionMinMax for Option<T> {
    fn opt_min(self, other: impl Into<Option<Self::Inner>>) -> Option<Self::Inner> {
        self.and_then(|this| this.opt_min(other))
    }

    fn opt_max(self, other: impl Into<Option<Self::Inner>>) -> Option<Self::Inner> {
        self.and_then(|this| this.opt_max(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
    struct MyInt(u64);

    impl OptionOperations for MyInt {}

    #[test]
    fn checks() {
        // FIXME separate in categories
        let some1 = Some(MyInt(1));
        let some2 = Some(MyInt(2));
        let none: Option<MyInt> = None;

        assert_eq!(some1.opt_cmp(some2), Some(Ordering::Less));
        assert_eq!(some1.opt_cmp(none), None);
        assert_eq!(none.opt_cmp(none), Some(Ordering::Equal));

        assert_eq!(some1.opt_lt(none), None);
        assert_eq!(none.opt_lt(some1), None);
        assert_eq!(none.opt_lt(none), Some(false));
        assert_eq!(none.opt_le(none), Some(true));

        assert_eq!(some1.opt_gt(none), None);
        assert_eq!(none.opt_gt(some1), None);
        assert_eq!(none.opt_gt(none), Some(false));
        assert_eq!(none.opt_ge(none), Some(true));

        assert_eq!(some1.opt_cmp(MyInt(2)), Some(Ordering::Less));
        assert_eq!(some2.opt_cmp(MyInt(1)), Some(Ordering::Greater));
        assert_eq!(MyInt(1).opt_cmp(none), None);

        assert_eq!(some1.opt_min(MyInt(2)), some1);
        assert_eq!(MyInt(1).opt_min(none), None);
        assert_eq!(none.opt_min(none), None);

        assert_eq!(some1.opt_max(MyInt(2)), some2);
        assert_eq!(MyInt(1).opt_max(none), None);
        assert_eq!(none.opt_max(none), None);

        assert_eq!(some1.opt_max(none).or(some1), some1);
    }
}
*/
