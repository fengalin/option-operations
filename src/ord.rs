use core::cmp::Ordering;

use crate::OptionOperations;

/// Trait for values and `Option`s that can be compared for a sort-order.
///
/// This implementation is mainly intended at working around the `PartialOrd`
/// implementation for `Option`, which compares `Option`
/// depending on the order of declaration in the `enum`.
///
/// ## `PartialOrd` implementation for `Option`
///
/// ```
/// # use core::cmp::Ordering;
/// let some1 = Some(1);
/// let none: Option<usize> = None;
///
/// assert_eq!(none.partial_cmp(&some1), Some(Ordering::Less));
/// assert_eq!(some1.partial_cmp(&none), Some(Ordering::Greater));
/// ```
///
/// ## Alternative behaviour
///
/// In some cases, we might consider the `None` reflects a value which is
/// not defined and thus can not be compared with `Some(_)`.
///
/// ```
/// # use option_operations::{OptionOperations, OptionOrd};
/// let some1 = Some(1);
/// let none: Option<usize> = None;
///
/// assert_eq!(none.opt_cmp(&some1), None);
/// assert_eq!(some1.opt_cmp(&none), None);
/// ```
///
/// ## Implementations
///
/// This `trait` is auto-implemented for all `PartialOrd` implementations
/// of types which also implement the [`OptionOperations`] trait.
pub trait OptionOrd<Rhs, InnerRhs = Rhs> {
    fn opt_cmp(&self, rhs: Rhs) -> Option<Ordering>;

    fn opt_lt(&self, rhs: Rhs) -> Option<bool> {
        self.opt_cmp(rhs).map(|ord| matches!(ord, Ordering::Less))
    }

    fn opt_le(&self, rhs: Rhs) -> Option<bool> {
        self.opt_cmp(rhs)
            .map(|ord| matches!(ord, Ordering::Less | Ordering::Equal))
    }

    fn opt_gt(&self, rhs: Rhs) -> Option<bool> {
        self.opt_cmp(rhs)
            .map(|ord| matches!(ord, Ordering::Greater))
    }

    fn opt_ge(&self, rhs: Rhs) -> Option<bool> {
        self.opt_cmp(rhs)
            .map(|ord| matches!(ord, Ordering::Greater | Ordering::Equal))
    }
}

impl<T, Rhs> OptionOrd<&Rhs, Rhs> for T
where
    T: OptionOperations + PartialOrd<Rhs>,
{
    fn opt_cmp(&self, rhs: &Rhs) -> Option<Ordering> {
        self.partial_cmp(rhs)
    }
}

impl<T, Rhs> OptionOrd<Rhs, Rhs> for T
where
    T: OptionOperations + for<'a> OptionOrd<&'a Rhs, Rhs>,
{
    fn opt_cmp(&self, rhs: Rhs) -> Option<Ordering> {
        self.opt_cmp(&rhs)
    }
}

impl<T, InnerRhs> OptionOrd<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + for<'a> OptionOrd<&'a InnerRhs, InnerRhs>,
{
    fn opt_cmp(&self, rhs: &Option<InnerRhs>) -> Option<Ordering> {
        rhs.as_ref().and_then(|inner_rhs| self.opt_cmp(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOrd<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + for<'a> OptionOrd<&'a InnerRhs, InnerRhs>,
{
    fn opt_cmp(&self, rhs: Option<InnerRhs>) -> Option<Ordering> {
        rhs.as_ref().and_then(|inner_rhs| self.opt_cmp(inner_rhs))
    }
}

impl<T, Rhs> OptionOrd<&Rhs, Rhs> for Option<T>
where
    T: OptionOperations + for<'a> OptionOrd<&'a Rhs, Rhs>,
{
    fn opt_cmp(&self, rhs: &Rhs) -> Option<Ordering> {
        self.as_ref().and_then(|inner_self| inner_self.opt_cmp(rhs))
    }
}

impl<T, Rhs> OptionOrd<Rhs, Rhs> for Option<T>
where
    T: OptionOperations + for<'a> OptionOrd<&'a Rhs, Rhs>,
{
    fn opt_cmp(&self, rhs: Rhs) -> Option<Ordering> {
        self.opt_cmp(&rhs)
    }
}

impl<T, InnerRhs> OptionOrd<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + for<'a> OptionOrd<&'a InnerRhs, InnerRhs>,
{
    fn opt_cmp(&self, rhs: &Option<InnerRhs>) -> Option<Ordering> {
        match (self, rhs) {
            (Some(inner_self), Some(inner_rhs)) => inner_self.opt_cmp(inner_rhs),
            (None, None) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

impl<T, InnerRhs> OptionOrd<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + for<'a> OptionOrd<&'a InnerRhs, InnerRhs>,
{
    fn opt_cmp(&self, rhs: Option<InnerRhs>) -> Option<Ordering> {
        match (self, rhs.as_ref()) {
            (Some(inner_self), Some(inner_rhs)) => inner_self.opt_cmp(inner_rhs),
            (None, None) => Some(Ordering::Equal),
            _ => None,
        }
    }
}

#[cfg(test)]
mod test {
    use core::cmp::Ordering;

    use super::OptionOrd;
    use crate::OptionOperations;

    #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
    struct MyInt(u64);

    impl OptionOperations for MyInt {}

    const MY_1: MyInt = MyInt(1);
    const MY_2: MyInt = MyInt(2);
    const SOME_1: Option<MyInt> = Some(MY_1);
    const SOME_2: Option<MyInt> = Some(MY_2);
    const NONE: Option<MyInt> = None;

    #[test]
    fn option_partial_ord_workaround() {
        // This is the default `partial_cmp` impl for `Option<T>`:
        assert_eq!(NONE.partial_cmp(&SOME_1), Some(Ordering::Less));
        assert_eq!(SOME_1.partial_cmp(&NONE), Some(Ordering::Greater));

        // This is what we expect:
        assert_eq!(NONE.opt_cmp(SOME_1), None);
        assert_eq!(SOME_1.opt_cmp(NONE), None);
    }

    #[test]
    fn opt_cmp() {
        assert_eq!(NONE.opt_cmp(NONE), Some(Ordering::Equal));
        assert_eq!(NONE.opt_cmp(&NONE), Some(Ordering::Equal));
        assert_eq!(SOME_1.opt_cmp(SOME_1), Some(Ordering::Equal));
        assert_eq!(SOME_1.opt_cmp(SOME_2), Some(Ordering::Less));
        assert_eq!(SOME_2.opt_cmp(SOME_1), Some(Ordering::Greater));

        assert_eq!(SOME_1.opt_lt(NONE), None);
        assert_eq!(NONE.opt_lt(SOME_1), None);
        assert_eq!(NONE.opt_lt(NONE), Some(false));
        assert_eq!(NONE.opt_le(NONE), Some(true));
        assert_eq!(SOME_2.opt_lt(SOME_1), Some(false));
        assert_eq!(SOME_1.opt_le(SOME_2), Some(true));

        assert_eq!(SOME_1.opt_gt(NONE), None);
        assert_eq!(NONE.opt_gt(SOME_1), None);
        assert_eq!(NONE.opt_gt(NONE), Some(false));
        assert_eq!(NONE.opt_ge(NONE), Some(true));
        assert_eq!(SOME_1.opt_gt(SOME_2), Some(false));
        assert_eq!(SOME_2.opt_ge(SOME_1), Some(true));

        assert_eq!(SOME_1.opt_cmp(MY_2), Some(Ordering::Less));
        assert_eq!(SOME_1.opt_cmp(MY_1), Some(Ordering::Equal));
        assert_eq!(SOME_2.opt_cmp(MY_1), Some(Ordering::Greater));
        assert_eq!(SOME_2.opt_cmp(&MY_1), Some(Ordering::Greater));

        assert_eq!(MY_1.opt_cmp(NONE), None);
        assert_eq!(MY_1.opt_cmp(&NONE), None);
        assert_eq!(MY_1.opt_cmp(MY_2), Some(Ordering::Less));
        assert_eq!(MY_1.opt_cmp(MY_1), Some(Ordering::Equal));
        assert_eq!(MY_2.opt_cmp(MY_1), Some(Ordering::Greater));
        assert_eq!(MY_2.opt_cmp(&MY_1), Some(Ordering::Greater));
    }
}
