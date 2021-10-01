use core::cmp::{Ordering, PartialEq, PartialOrd};

use crate::OptionOperations;

/// TODO doc
#[derive(Debug)]
pub enum OptionChecked<T> {
    /// TODO doc
    Some(T),
    /// TODO doc
    None,
    /// TODO doc
    Overflow,
}

impl<T> OptionChecked<T> {
    /// TODO doc
    pub fn is_some(&self) -> bool {
        matches!(self, OptionChecked::Some(_))
    }

    /// TODO doc
    pub fn is_none(&self) -> bool {
        matches!(self, OptionChecked::None)
    }

    /// TODO doc
    pub fn is_overflow(&self) -> bool {
        matches!(self, OptionChecked::Overflow)
    }

    /// TODO doc, incl. panic section
    pub fn expect(self, msg: &str) -> T {
        if let OptionChecked::Some(inner) = self {
            inner
        } else {
            // FIXME replicate the message from `Option`
            panic!("{}", msg)
        }
    }

    /// TODO doc, incl. panic section
    pub fn unwrap(self) -> T {
        use OptionChecked::*;
        match self {
            Some(inner) => inner,
            // FIXME replicate the message from `Option`
            None => panic!("unwrapped OptionChecked::None"),
            Overflow => panic!("unwrapped OptionChecked::Overflow"),
        }
    }

    /// TODO doc
    pub fn unwrap_or(self, default: T) -> T {
        if let OptionChecked::Some(inner) = self {
            inner
        } else {
            default
        }
    }

    /// TODO doc
    pub fn unwrap_or_else<F>(self, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        if let OptionChecked::Some(inner) = self {
            inner
        } else {
            f()
        }
    }

    /// TODO doc
    pub fn and<U>(self, optcb: OptionChecked<U>) -> OptionChecked<U> {
        use OptionChecked::*;
        match self {
            Some(_) => optcb,
            None => None,
            Overflow => Overflow,
        }
    }

    /// TODO doc
    pub fn and_then<U, F>(self, f: F) -> OptionChecked<U>
    where
        F: FnOnce(T) -> OptionChecked<U>,
    {
        use OptionChecked::*;
        match self {
            Some(inner) => f(inner),
            None => None,
            Overflow => Overflow,
        }
    }

    /// TODO doc
    pub fn ok_or<E>(self, err: E) -> Result<T, E> {
        if let OptionChecked::Some(inner_self) = self {
            Ok(inner_self)
        } else {
            Err(err)
        }
    }

    /// TODO doc
    pub fn ok_or_else<E, F>(self, err: F) -> Result<T, E>
    where
        F: FnOnce() -> E,
    {
        if let OptionChecked::Some(inner_self) = self {
            Ok(inner_self)
        } else {
            Err(err())
        }
    }

    /// TODO doc
    pub fn or(self, optcb: OptionChecked<T>) -> OptionChecked<T> {
        if self.is_some() {
            self
        } else {
            optcb
        }
    }

    /// TODO doc
    pub fn or_else<F>(self, f: F) -> OptionChecked<T>
    where
        F: FnOnce() -> OptionChecked<T>,
    {
        if self.is_some() {
            self
        } else {
            f()
        }
    }

    /// TODO doc
    pub fn map<U, F>(self, f: F) -> OptionChecked<U>
    where
        F: FnOnce(T) -> U,
    {
        use OptionChecked::*;
        match self {
            Some(inner) => Some(f(inner)),
            None => None,
            Overflow => Overflow,
        }
    }

    /// TODO doc
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        if let OptionChecked::Some(inner) = self {
            f(inner)
        } else {
            default
        }
    }

    /// TODO doc
    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        F: FnOnce(T) -> U,
        D: FnOnce() -> U,
    {
        if let OptionChecked::Some(inner) = self {
            f(inner)
        } else {
            default()
        }
    }

    /// TODO doc
    pub fn zip<U>(self, optcb: OptionChecked<U>) -> OptionChecked<(T, U)> {
        use OptionChecked::*;
        match (self, optcb) {
            (Some(inner_self), Some(inner_optcb)) => Some((inner_self, inner_optcb)),
            (Overflow, _) | (_, Overflow) => Overflow,
            _ => None,
        }
    }
}

impl<T> OptionChecked<T>
where
    T: Default,
{
    pub fn unwrap_or_default(self) -> T {
        if let OptionChecked::Some(inner) = self {
            inner
        } else {
            T::default()
        }
    }
}

#[allow(clippy::from_over_into)]
impl<T: OptionOperations> Into<Option<T>> for OptionChecked<T> {
    fn into(self) -> Option<T> {
        if let OptionChecked::Some(inner) = self {
            Some(inner)
        } else {
            None
        }
    }
}

impl<T: OptionOperations> From<Option<T>> for OptionChecked<T> {
    fn from(opt: Option<T>) -> Self {
        if let Option::Some(inner) = opt {
            OptionChecked::Some(inner)
        } else {
            OptionChecked::None
        }
    }
}

impl<T: OptionOperations> From<T> for OptionChecked<T> {
    fn from(val: T) -> Self {
        OptionChecked::Some(val)
    }
}

impl<T, InnerRhs> PartialEq<OptionChecked<InnerRhs>> for OptionChecked<T>
where
    T: OptionOperations + PartialEq<InnerRhs>,
{
    fn eq(&self, other: &OptionChecked<InnerRhs>) -> bool {
        use OptionChecked::*;
        match (self, other) {
            (Some(inner_self), Some(inner_other)) => inner_self.eq(inner_other),
            (None, None) => true,
            (Overflow, Overflow) => true,
            _ => false,
        }
    }
}

impl<T, InnerRhs> PartialOrd<OptionChecked<InnerRhs>> for OptionChecked<T>
where
    T: OptionOperations + PartialOrd<InnerRhs>,
{
    fn partial_cmp(&self, other: &OptionChecked<InnerRhs>) -> Option<Ordering> {
        use OptionChecked::*;
        match (self, other) {
            (Some(inner_self), Some(inner_other)) => inner_self.partial_cmp(inner_other),
            (None, None) => Option::Some(Ordering::Equal),
            (Overflow, Overflow) => Option::Some(Ordering::Equal),
            _ => Option::None,
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    const SOME_0: OptionChecked<u64> = OptionChecked::Some(0);
    const SOME_1: OptionChecked<u64> = OptionChecked::Some(1);
    const SOME_2: OptionChecked<u64> = OptionChecked::Some(2);
    const NONE: OptionChecked<u64> = OptionChecked::None;
    const OVERFLOW: OptionChecked<u64> = OptionChecked::Overflow;

    #[test]
    fn is_getters() {
        assert!(SOME_1.is_some());
        assert!(NONE.is_none());
        assert!(OVERFLOW.is_overflow());
    }

    #[test]
    fn unwrap() {
        assert_eq!(SOME_1.unwrap(), 1);
        assert_eq!(SOME_1.expect("should pass"), 1);
        assert_eq!(SOME_1.unwrap_or(2), 1);
        assert_eq!(NONE.unwrap_or(2), 2);
        assert_eq!(SOME_1.unwrap_or_default(), 1);
        assert_eq!(NONE.unwrap_or_default(), 0);
        assert_eq!(SOME_1.unwrap_or_else(|| 2), 1);
        assert_eq!(NONE.unwrap_or_else(|| 2), 2);
    }

    #[should_panic]
    #[test]
    fn unwrap_none() {
        NONE.unwrap();
    }

    #[should_panic]
    #[test]
    fn expect_none() {
        NONE.expect("should panic");
    }

    #[test]
    fn and() {
        assert_eq!(SOME_1.and(SOME_2), SOME_2);
        assert!(NONE.and(SOME_2).is_none());
        assert!(OVERFLOW.and(SOME_2).is_overflow());

        assert_eq!(SOME_1.and_then(|val| OptionChecked::Some(val + 1)), SOME_2);
        assert!(SOME_1.and_then(|_| OptionChecked::<u8>::None).is_none());
        assert!(NONE.and_then(|val| OptionChecked::Some(val + 1)).is_none());
        assert!(OVERFLOW
            .and_then(|val| OptionChecked::Some(val + 1))
            .is_overflow());
    }

    #[test]
    fn ok_or() {
        #[derive(Debug, PartialEq)]
        struct MyError;

        assert_eq!(SOME_1.ok_or(MyError), Ok(1));
        assert_eq!(NONE.ok_or(MyError), Err(MyError));
        assert_eq!(OVERFLOW.ok_or(MyError), Err(MyError));

        assert_eq!(SOME_1.ok_or_else(|| MyError), Ok(1));
        assert_eq!(NONE.ok_or_else(|| MyError), Err(MyError));
        assert_eq!(OVERFLOW.ok_or_else(|| MyError), Err(MyError));
    }

    #[test]
    fn or() {
        assert_eq!(SOME_1.or(SOME_2), SOME_1);
        assert_eq!(NONE.or(SOME_2), SOME_2);
        assert_eq!(OVERFLOW.or(SOME_2), SOME_2);

        assert_eq!(SOME_1.or_else(|| SOME_2), SOME_1);
        assert_eq!(NONE.or_else(|| SOME_2), SOME_2);
        assert_eq!(OVERFLOW.or_else(|| SOME_2), SOME_2);
    }

    #[test]
    fn map() {
        assert_eq!(SOME_1.map(|one| one + 1), SOME_2);
        assert!(NONE.map(|one| one + 1).is_none());
        assert!(OVERFLOW.map(|one| one + 1).is_overflow());

        assert_eq!(
            SOME_1.map_or(SOME_0, |one| OptionChecked::Some(one + 1)),
            SOME_2
        );
        assert_eq!(
            NONE.map_or(SOME_0, |one| OptionChecked::Some(one + 1)),
            SOME_0
        );
        assert_eq!(
            OVERFLOW.map_or(SOME_0, |one| OptionChecked::Some(one + 1)),
            SOME_0
        );

        assert_eq!(
            SOME_1.map_or_else(|| Some(0).into(), |one| OptionChecked::Some(one + 1)),
            SOME_2
        );
        assert_eq!(
            NONE.map_or_else(|| Some(0).into(), |one| OptionChecked::Some(one + 1)),
            SOME_0
        );
        assert_eq!(
            OVERFLOW.map_or_else(|| Some(0).into(), |one| OptionChecked::Some(one + 1)),
            SOME_0
        );
    }

    #[test]
    fn zip() {
        assert_eq!(SOME_1.zip(SOME_2).unwrap(), (1, 2));

        assert!(SOME_1.zip(NONE).is_none());
        assert!(NONE.zip(SOME_1).is_none());
        assert!(NONE.zip(NONE).is_none());

        assert!(SOME_1.zip(OVERFLOW).is_overflow());
        assert!(OVERFLOW.zip(SOME_1).is_overflow());
        assert!(OVERFLOW.zip(NONE).is_overflow());
    }

    #[test]
    fn partial_ord() {
        assert_eq!(SOME_1.partial_cmp(&SOME_2), Some(Ordering::Less));
        assert_eq!(SOME_1.partial_cmp(&SOME_1), Some(Ordering::Equal));
        assert_eq!(SOME_2.partial_cmp(&SOME_1), Some(Ordering::Greater));

        assert_eq!(NONE.partial_cmp(&NONE), Some(Ordering::Equal));
        assert_eq!(SOME_1.partial_cmp(&NONE), None);
        assert_eq!(NONE.partial_cmp(&SOME_1), None);
        assert_eq!(NONE.partial_cmp(&OVERFLOW), None);
        assert_eq!(OVERFLOW.partial_cmp(&NONE), None);

        assert_eq!(OVERFLOW.partial_cmp(&OVERFLOW), Some(Ordering::Equal));
        assert_eq!(SOME_1.partial_cmp(&OVERFLOW), None);
        assert_eq!(OVERFLOW.partial_cmp(&SOME_1), None);
    }

    #[test]
    fn from_into() {
        let some_1: OptionChecked<u64> = 1u64.into();
        assert_eq!(some_1, OptionChecked::Some(1));

        let some_1: Option<u64> = some_1.into();
        assert_eq!(some_1, Option::Some(1));

        let some_2: OptionChecked<u64> = Some(2u64).into();
        assert_eq!(some_2, OptionChecked::Some(2));

        let none: OptionChecked<u64> = None.into();
        assert!(none.is_none());

        let none: Option<u64> = none.into();
        assert!(none.is_none());
    }
}
