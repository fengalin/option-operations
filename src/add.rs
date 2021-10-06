use core::ops::{Add, AddAssign};

use crate::{Error, OptionOperations};

/// TODO: doc
pub trait OptionAdd<Rhs, InnerRhs = Rhs> {
    type Output;

    fn opt_add(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, Rhs> OptionAdd<Rhs> for T
where
    T: OptionOperations + Add<Rhs>,
{
    type Output = <T as Add<Rhs>>::Output;

    fn opt_add(self, rhs: Rhs) -> Option<Self::Output> {
        Some(self.add(rhs))
    }
}

impl<T, InnerRhs> OptionAdd<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Add<InnerRhs>,
{
    type Output = <T as Add<InnerRhs>>::Output;

    fn opt_add(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.map(|inner_rhs| self.add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionAdd<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Add<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Add<InnerRhs>>::Output;

    fn opt_add(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref().map(|inner_rhs| self.add(*inner_rhs))
    }
}

impl<T, Rhs> OptionAdd<Rhs> for Option<T>
where
    T: OptionOperations + Add<Rhs>,
{
    type Output = <T as Add<Rhs>>::Output;

    fn opt_add(self, rhs: Rhs) -> Option<Self::Output> {
        self.map(|inner_self| inner_self.add(rhs))
    }
}

impl<T, InnerRhs> OptionAdd<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Add<InnerRhs>,
{
    type Output = <T as Add<InnerRhs>>::Output;

    fn opt_add(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .map(|(inner_self, inner_rhs)| inner_self.add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionAdd<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Add<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Add<InnerRhs>>::Output;

    fn opt_add(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .map(|(inner_self, inner_rhs)| inner_self.add(*inner_rhs))
    }
}

/// TODO: doc
pub trait OptionAddAssign<Rhs, InnerRhs = Rhs> {
    fn opt_add_assign(&mut self, rhs: Rhs);
}

impl<T, Rhs> OptionAddAssign<Rhs> for T
where
    T: OptionOperations + AddAssign<Rhs>,
{
    fn opt_add_assign(&mut self, rhs: Rhs) {
        self.add_assign(rhs)
    }
}

impl<T, InnerRhs> OptionAddAssign<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + AddAssign<InnerRhs>,
{
    fn opt_add_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs {
            self.add_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionAddAssign<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + AddAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_add_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.add_assign(*inner_rhs)
        }
    }
}

impl<T, Rhs> OptionAddAssign<Rhs> for Option<T>
where
    T: OptionOperations + AddAssign<Rhs>,
{
    fn opt_add_assign(&mut self, rhs: Rhs) {
        if let Some(inner_self) = self {
            inner_self.add_assign(rhs)
        }
    }
}

impl<T, InnerRhs> OptionAddAssign<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + AddAssign<InnerRhs>,
{
    fn opt_add_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs) {
            inner_self.add_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionAddAssign<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + AddAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_add_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs.as_ref()) {
            inner_self.add_assign(*inner_rhs)
        }
    }
}

/// TODO: doc
pub trait OptionCheckedAdd<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_checked_add(self, rhs: Rhs) -> Result<Option<Self::Output>, Error>;
}

impl<T, InnerRhs> OptionCheckedAdd<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedAdd<InnerRhs>,
{
    type Output = <T as OptionCheckedAdd<InnerRhs>>::Output;

    fn opt_checked_add(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs {
            self.opt_checked_add(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedAdd<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedAdd<InnerRhs>>::Output;

    fn opt_checked_add(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.opt_checked_add(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, Rhs> OptionCheckedAdd<Rhs> for Option<T>
where
    T: OptionOperations + OptionCheckedAdd<Rhs>,
{
    type Output = <T as OptionCheckedAdd<Rhs>>::Output;

    fn opt_checked_add(self, rhs: Rhs) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_self) = self {
            inner_self.opt_checked_add(rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedAdd<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedAdd<InnerRhs>,
{
    type Output = <T as OptionCheckedAdd<InnerRhs>>::Output;

    fn opt_checked_add(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs) {
            inner_self.opt_checked_add(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedAdd<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedAdd<InnerRhs>>::Output;

    fn opt_checked_add(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs.as_ref()) {
            inner_self.opt_checked_add(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionOverflowingAdd<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_overflowing_add(self, rhs: Rhs) -> Option<(Self::Output, bool)>;
}

impl<T, InnerRhs> OptionOverflowingAdd<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingAdd<InnerRhs>,
{
    type Output = <T as OptionOverflowingAdd<InnerRhs>>::Output;

    fn opt_overflowing_add(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.and_then(|inner_rhs| self.opt_overflowing_add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingAdd<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingAdd<InnerRhs>>::Output;

    fn opt_overflowing_add(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_overflowing_add(*inner_rhs))
    }
}

impl<T, Rhs> OptionOverflowingAdd<Rhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingAdd<Rhs>,
{
    type Output = <T as OptionOverflowingAdd<Rhs>>::Output;

    fn opt_overflowing_add(self, rhs: Rhs) -> Option<(Self::Output, bool)> {
        self.and_then(|inner_self| inner_self.opt_overflowing_add(rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingAdd<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingAdd<InnerRhs>,
{
    type Output = <T as OptionOverflowingAdd<InnerRhs>>::Output;

    fn opt_overflowing_add(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingAdd<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingAdd<InnerRhs>>::Output;

    fn opt_overflowing_add(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_add(*inner_rhs))
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionSaturatingAdd<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_saturating_add(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, InnerRhs> OptionSaturatingAdd<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionSaturatingAdd<InnerRhs>,
{
    type Output = <T as OptionSaturatingAdd<InnerRhs>>::Output;

    fn opt_saturating_add(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.and_then(|inner_rhs| self.opt_saturating_add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingAdd<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionSaturatingAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionSaturatingAdd<InnerRhs>>::Output;

    fn opt_saturating_add(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_saturating_add(*inner_rhs))
    }
}

impl<T, Rhs> OptionSaturatingAdd<Rhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingAdd<Rhs>,
{
    type Output = <T as OptionSaturatingAdd<Rhs>>::Output;

    fn opt_saturating_add(self, rhs: Rhs) -> Option<Self::Output> {
        self.and_then(|inner_self| inner_self.opt_saturating_add(rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingAdd<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingAdd<InnerRhs>,
{
    type Output = <T as OptionSaturatingAdd<InnerRhs>>::Output;

    fn opt_saturating_add(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_saturating_add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingAdd<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionSaturatingAdd<InnerRhs>>::Output;

    fn opt_saturating_add(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_saturating_add(*inner_rhs))
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionWrappingAdd<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_wrapping_add(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, InnerRhs> OptionWrappingAdd<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingAdd<InnerRhs>,
{
    type Output = <T as OptionWrappingAdd<InnerRhs>>::Output;

    fn opt_wrapping_add(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.and_then(|inner_rhs| self.opt_wrapping_add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingAdd<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingAdd<InnerRhs>>::Output;

    fn opt_wrapping_add(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_wrapping_add(*inner_rhs))
    }
}

impl<T, Rhs> OptionWrappingAdd<Rhs> for Option<T>
where
    T: OptionOperations + OptionWrappingAdd<Rhs>,
{
    type Output = <T as OptionWrappingAdd<Rhs>>::Output;

    fn opt_wrapping_add(self, rhs: Rhs) -> Option<Self::Output> {
        self.and_then(|inner_self| inner_self.opt_wrapping_add(rhs))
    }
}

impl<T, InnerRhs> OptionWrappingAdd<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingAdd<InnerRhs>,
{
    type Output = <T as OptionWrappingAdd<InnerRhs>>::Output;

    fn opt_wrapping_add(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_add(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingAdd<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingAdd<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingAdd<InnerRhs>>::Output;

    fn opt_wrapping_add(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_add(*inner_rhs))
    }
}

// TODO impl on integers & time types

#[cfg(test)]
mod test {
    use super::*;
    use crate::OptionOperations;
    use core::ops::{Add, AddAssign};

    #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
    struct MyInt(u64);

    impl OptionOperations for MyInt {}

    impl Add<MyInt> for MyInt {
        type Output = MyInt;

        fn add(self, rhs: MyInt) -> MyInt {
            MyInt(self.0.add(rhs.0))
        }
    }

    impl Add<u64> for MyInt {
        type Output = MyInt;

        fn add(self, rhs: u64) -> MyInt {
            MyInt(self.0.add(rhs))
        }
    }

    impl AddAssign<MyInt> for MyInt {
        fn add_assign(&mut self, rhs: MyInt) {
            self.0.add_assign(rhs.0)
        }
    }

    impl AddAssign<u64> for MyInt {
        fn add_assign(&mut self, rhs: u64) {
            self.0.add_assign(rhs)
        }
    }

    const MY_0: MyInt = MyInt(0);
    const MY_1: MyInt = MyInt(1);
    const MY_2: MyInt = MyInt(2);
    const MY_MAX: MyInt = MyInt(u64::MAX);
    const SOME_0: Option<MyInt> = Some(MY_0);
    const SOME_1: Option<MyInt> = Some(MY_1);
    const SOME_2: Option<MyInt> = Some(MY_2);
    const SOME_MAX: Option<MyInt> = Some(MY_MAX);
    const NONE: Option<MyInt> = None;

    #[test]
    fn add_my() {
        assert_eq!(MY_1.opt_add(MY_1), SOME_2);
        assert_eq!(SOME_1.opt_add(MY_1), SOME_2);
        assert_eq!(MY_1.opt_add(SOME_1), SOME_2);
        assert_eq!(MY_1.opt_add(&SOME_1), SOME_2);
        assert_eq!(MY_1.opt_add(NONE), NONE);
        assert_eq!(NONE.opt_add(MY_1), NONE);
    }

    #[test]
    fn add_u64() {
        assert_eq!(MY_1.opt_add(1), SOME_2);
        assert_eq!(MY_1.opt_add(Some(1)), SOME_2);
        assert_eq!(SOME_1.opt_add(1), SOME_2);
        assert_eq!(SOME_1.opt_add(Some(1)), SOME_2);
        assert_eq!(SOME_1.opt_add(&Some(1)), SOME_2);
        assert_eq!(MY_1.opt_add(Option::<u64>::None), NONE);
        assert_eq!(Option::<MyInt>::None.opt_add(MY_0), NONE);
    }

    #[test]
    fn add_assign_my() {
        let mut my = MY_1;
        my.opt_add_assign(MY_1);
        assert_eq!(my, MY_2);

        let mut some = SOME_1;
        some.opt_add_assign(MY_1);
        assert_eq!(some, SOME_2);

        let mut my = MY_1;
        my.opt_add_assign(SOME_1);
        assert_eq!(my, MY_2);

        let mut my = MY_1;
        my.opt_add_assign(&SOME_1);
        assert_eq!(my, MY_2);

        let mut my = MY_1;
        my.opt_add_assign(NONE);
        assert_eq!(my, MY_1);

        let mut some = SOME_1;
        some.opt_add_assign(SOME_1);
        assert_eq!(some, SOME_2);

        let mut some = SOME_1;
        some.opt_add_assign(&SOME_1);
        assert_eq!(some, SOME_2);

        let mut some = SOME_1;
        some.opt_add_assign(NONE);
        assert_eq!(some, SOME_1);

        let mut none = NONE;
        none.opt_add_assign(SOME_1);
        assert_eq!(none, NONE);

        let mut none = NONE;
        none.opt_add_assign(NONE);
        assert_eq!(none, NONE);
    }

    #[test]
    fn add_assign_u64() {
        let mut my = MY_1;
        my.opt_add_assign(1);
        assert_eq!(my, MY_2);

        let mut some = SOME_1;
        some.opt_add_assign(1);
        assert_eq!(some, SOME_2);

        let mut my = MY_1;
        my.opt_add_assign(Some(1));
        assert_eq!(my, MY_2);

        let mut my = MY_1;
        my.opt_add_assign(&Some(1));
        assert_eq!(my, MY_2);

        let mut some = SOME_1;
        some.opt_add_assign(Some(1));
        assert_eq!(some, SOME_2);

        let mut some = SOME_1;
        some.opt_add_assign(&Some(1));
        assert_eq!(some, SOME_2);

        let mut none = NONE;
        none.opt_add_assign(Some(1));
        assert_eq!(none, NONE);
    }

    #[test]
    fn checked_add() {
        impl OptionCheckedAdd for MyInt {
            type Output = MyInt;

            fn opt_checked_add(self, rhs: MyInt) -> Result<Option<Self::Output>, Error> {
                self.0
                    .checked_add(rhs.0)
                    .ok_or(Error::Overflow)
                    .map(|val| Some(MyInt(val)))
            }
        }

        impl OptionCheckedAdd<u64> for MyInt {
            type Output = MyInt;

            fn opt_checked_add(self, rhs: u64) -> Result<Option<Self::Output>, Error> {
                self.0
                    .checked_add(rhs)
                    .ok_or(Error::Overflow)
                    .map(|val| Some(MyInt(val)))
            }
        }

        assert_eq!(MY_1.opt_checked_add(MY_1), Ok(SOME_2));
        assert_eq!(MY_1.opt_checked_add(SOME_1), Ok(SOME_2));
        assert_eq!(MY_1.opt_checked_add(&SOME_1), Ok(SOME_2));
        assert_eq!(MY_MAX.opt_checked_add(MY_1), Err(Error::Overflow));

        assert_eq!(SOME_1.opt_checked_add(MY_1), Ok(SOME_2));
        assert_eq!(SOME_1.opt_checked_add(SOME_1), Ok(SOME_2));
        assert_eq!(SOME_1.opt_checked_add(&SOME_1), Ok(SOME_2));

        assert_eq!(SOME_MAX.opt_checked_add(MY_1), Err(Error::Overflow));
        assert_eq!(SOME_MAX.opt_checked_add(1), Err(Error::Overflow));
        assert_eq!(SOME_MAX.opt_checked_add(Some(1)), Err(Error::Overflow));
        assert_eq!(MY_1.opt_checked_add(SOME_MAX), Err(Error::Overflow));
        assert_eq!(MY_MAX.opt_checked_add(NONE), Ok(None));
        assert_eq!(NONE.opt_checked_add(SOME_MAX), Ok(None));
    }

    #[test]
    fn saturating_add() {
        impl OptionSaturatingAdd for MyInt {
            type Output = MyInt;

            fn opt_saturating_add(self, rhs: MyInt) -> Option<Self::Output> {
                Some(MyInt(self.0.saturating_add(rhs.0)))
            }
        }

        impl OptionSaturatingAdd<u64> for MyInt {
            type Output = MyInt;

            fn opt_saturating_add(self, rhs: u64) -> Option<Self::Output> {
                Some(MyInt(self.0.saturating_add(rhs)))
            }
        }

        assert_eq!(MY_1.opt_saturating_add(MY_1), SOME_2);
        assert_eq!(MY_MAX.opt_saturating_add(MY_1), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_add(MY_1), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_add(1), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_add(Some(1)), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_add(&Some(1)), SOME_MAX);
        assert_eq!(MY_1.opt_saturating_add(SOME_MAX), SOME_MAX);
        assert_eq!(MY_1.opt_saturating_add(&SOME_MAX), SOME_MAX);
        assert_eq!(MY_MAX.opt_saturating_add(NONE), NONE);
        assert_eq!(NONE.opt_saturating_add(SOME_MAX), NONE);
    }

    #[test]
    fn overflowing_add() {
        impl OptionOverflowingAdd for MyInt {
            type Output = MyInt;

            fn opt_overflowing_add(self, rhs: MyInt) -> Option<(Self::Output, bool)> {
                let ret = self.0.overflowing_add(rhs.0);
                Some((MyInt(ret.0), ret.1))
            }
        }

        impl OptionOverflowingAdd<u64> for MyInt {
            type Output = MyInt;

            fn opt_overflowing_add(self, rhs: u64) -> Option<(Self::Output, bool)> {
                let ret = self.0.overflowing_add(rhs);
                Some((MyInt(ret.0), ret.1))
            }
        }

        assert_eq!(MY_1.opt_overflowing_add(MY_1), Some((MY_2, false)));
        assert_eq!(MY_MAX.opt_overflowing_add(MY_1), Some((MY_0, true)));
        assert_eq!(SOME_MAX.opt_overflowing_add(MY_1), Some((MY_0, true)));
        assert_eq!(SOME_MAX.opt_overflowing_add(1), Some((MY_0, true)));
        assert_eq!(SOME_MAX.opt_overflowing_add(Some(1)), Some((MY_0, true)));
        assert_eq!(SOME_MAX.opt_overflowing_add(&Some(1)), Some((MY_0, true)));
        assert_eq!(MY_1.opt_overflowing_add(SOME_MAX), Some((MY_0, true)));
        assert_eq!(MY_1.opt_overflowing_add(&SOME_MAX), Some((MY_0, true)));
        assert_eq!(MY_MAX.opt_overflowing_add(NONE), None);
        assert_eq!(NONE.opt_overflowing_add(SOME_MAX), None);
    }

    #[test]
    fn wrapping_add() {
        impl OptionWrappingAdd for MyInt {
            type Output = MyInt;

            fn opt_wrapping_add(self, rhs: MyInt) -> Option<Self::Output> {
                Some(MyInt(self.0.wrapping_add(rhs.0)))
            }
        }

        impl OptionWrappingAdd<u64> for MyInt {
            type Output = MyInt;

            fn opt_wrapping_add(self, rhs: u64) -> Option<Self::Output> {
                Some(MyInt(self.0.wrapping_add(rhs)))
            }
        }

        assert_eq!(MY_1.opt_wrapping_add(MY_1), SOME_2);
        assert_eq!(MY_MAX.opt_wrapping_add(MY_1), SOME_0);
        assert_eq!(SOME_MAX.opt_wrapping_add(MY_1), SOME_0);
        assert_eq!(SOME_MAX.opt_wrapping_add(1), SOME_0);
        assert_eq!(SOME_MAX.opt_wrapping_add(Some(1)), SOME_0);
        assert_eq!(SOME_MAX.opt_wrapping_add(&Some(1)), SOME_0);
        assert_eq!(MY_1.opt_wrapping_add(SOME_MAX), SOME_0);
        assert_eq!(MY_1.opt_wrapping_add(&SOME_MAX), SOME_0);
        assert_eq!(MY_MAX.opt_wrapping_add(NONE), NONE);
        assert_eq!(NONE.opt_wrapping_add(SOME_MAX), NONE);
    }
}
