use core::ops::{Sub, SubAssign};

use crate::{Error, OptionOperations};

/// TODO: doc
pub trait OptionSub<Rhs, InnerRhs = Rhs> {
    type Output;

    fn opt_sub(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, Rhs> OptionSub<Rhs> for T
where
    T: OptionOperations + Sub<Rhs>,
{
    type Output = <T as Sub<Rhs>>::Output;

    fn opt_sub(self, rhs: Rhs) -> Option<Self::Output> {
        Some(self.sub(rhs))
    }
}

impl<T, InnerRhs> OptionSub<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Sub<InnerRhs>,
{
    type Output = <T as Sub<InnerRhs>>::Output;

    fn opt_sub(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.map(|inner_rhs| self.sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSub<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Sub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Sub<InnerRhs>>::Output;

    fn opt_sub(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref().map(|inner_rhs| self.sub(*inner_rhs))
    }
}

impl<T, Rhs> OptionSub<Rhs> for Option<T>
where
    T: OptionOperations + Sub<Rhs>,
{
    type Output = <T as Sub<Rhs>>::Output;

    fn opt_sub(self, rhs: Rhs) -> Option<Self::Output> {
        self.map(|inner_self| inner_self.sub(rhs))
    }
}

impl<T, InnerRhs> OptionSub<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Sub<InnerRhs>,
{
    type Output = <T as Sub<InnerRhs>>::Output;

    fn opt_sub(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .map(|(inner_self, inner_rhs)| inner_self.sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSub<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Sub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Sub<InnerRhs>>::Output;

    fn opt_sub(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .map(|(inner_self, inner_rhs)| inner_self.sub(*inner_rhs))
    }
}

/// TODO: doc
pub trait OptionSubAssign<Rhs, InnerRhs = Rhs> {
    fn opt_sub_assign(&mut self, rhs: Rhs);
}

impl<T, Rhs> OptionSubAssign<Rhs> for T
where
    T: OptionOperations + SubAssign<Rhs>,
{
    fn opt_sub_assign(&mut self, rhs: Rhs) {
        self.sub_assign(rhs)
    }
}

impl<T, InnerRhs> OptionSubAssign<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + SubAssign<InnerRhs>,
{
    fn opt_sub_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs {
            self.sub_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionSubAssign<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + SubAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_sub_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.sub_assign(*inner_rhs)
        }
    }
}

impl<T, Rhs> OptionSubAssign<Rhs> for Option<T>
where
    T: OptionOperations + SubAssign<Rhs>,
{
    fn opt_sub_assign(&mut self, rhs: Rhs) {
        if let Some(inner_self) = self {
            inner_self.sub_assign(rhs)
        }
    }
}

impl<T, InnerRhs> OptionSubAssign<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + SubAssign<InnerRhs>,
{
    fn opt_sub_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs) {
            inner_self.sub_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionSubAssign<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + SubAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_sub_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs.as_ref()) {
            inner_self.sub_assign(*inner_rhs)
        }
    }
}

/// TODO: doc
pub trait OptionCheckedSub<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_checked_sub(self, rhs: Rhs) -> Result<Option<Self::Output>, Error>;
}

impl<T, InnerRhs> OptionCheckedSub<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedSub<InnerRhs>,
{
    type Output = <T as OptionCheckedSub<InnerRhs>>::Output;

    fn opt_checked_sub(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs {
            self.opt_checked_sub(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedSub<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedSub<InnerRhs>>::Output;

    fn opt_checked_sub(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.opt_checked_sub(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, Rhs> OptionCheckedSub<Rhs> for Option<T>
where
    T: OptionOperations + OptionCheckedSub<Rhs>,
{
    type Output = <T as OptionCheckedSub<Rhs>>::Output;

    fn opt_checked_sub(self, rhs: Rhs) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_self) = self {
            inner_self.opt_checked_sub(rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedSub<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedSub<InnerRhs>,
{
    type Output = <T as OptionCheckedSub<InnerRhs>>::Output;

    fn opt_checked_sub(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs) {
            inner_self.opt_checked_sub(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedSub<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedSub<InnerRhs>>::Output;

    fn opt_checked_sub(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs.as_ref()) {
            inner_self.opt_checked_sub(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionOverflowingSub<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_overflowing_sub(self, rhs: Rhs) -> Option<(Self::Output, bool)>;
}

impl<T, InnerRhs> OptionOverflowingSub<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingSub<InnerRhs>,
{
    type Output = <T as OptionOverflowingSub<InnerRhs>>::Output;

    fn opt_overflowing_sub(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.and_then(|inner_rhs| self.opt_overflowing_sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingSub<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingSub<InnerRhs>>::Output;

    fn opt_overflowing_sub(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_overflowing_sub(*inner_rhs))
    }
}

impl<T, Rhs> OptionOverflowingSub<Rhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingSub<Rhs>,
{
    type Output = <T as OptionOverflowingSub<Rhs>>::Output;

    fn opt_overflowing_sub(self, rhs: Rhs) -> Option<(Self::Output, bool)> {
        self.and_then(|inner_self| inner_self.opt_overflowing_sub(rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingSub<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingSub<InnerRhs>,
{
    type Output = <T as OptionOverflowingSub<InnerRhs>>::Output;

    fn opt_overflowing_sub(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingSub<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingSub<InnerRhs>>::Output;

    fn opt_overflowing_sub(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_sub(*inner_rhs))
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionSaturatingSub<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_saturating_sub(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, InnerRhs> OptionSaturatingSub<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionSaturatingSub<InnerRhs>,
{
    type Output = <T as OptionSaturatingSub<InnerRhs>>::Output;

    fn opt_saturating_sub(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.and_then(|inner_rhs| self.opt_saturating_sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingSub<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionSaturatingSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionSaturatingSub<InnerRhs>>::Output;

    fn opt_saturating_sub(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_saturating_sub(*inner_rhs))
    }
}

impl<T, Rhs> OptionSaturatingSub<Rhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingSub<Rhs>,
{
    type Output = <T as OptionSaturatingSub<Rhs>>::Output;

    fn opt_saturating_sub(self, rhs: Rhs) -> Option<Self::Output> {
        self.and_then(|inner_self| inner_self.opt_saturating_sub(rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingSub<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingSub<InnerRhs>,
{
    type Output = <T as OptionSaturatingSub<InnerRhs>>::Output;

    fn opt_saturating_sub(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_saturating_sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingSub<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionSaturatingSub<InnerRhs>>::Output;

    fn opt_saturating_sub(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_saturating_sub(*inner_rhs))
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionWrappingSub<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_wrapping_sub(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, InnerRhs> OptionWrappingSub<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingSub<InnerRhs>,
{
    type Output = <T as OptionWrappingSub<InnerRhs>>::Output;

    fn opt_wrapping_sub(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.and_then(|inner_rhs| self.opt_wrapping_sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingSub<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingSub<InnerRhs>>::Output;

    fn opt_wrapping_sub(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_wrapping_sub(*inner_rhs))
    }
}

impl<T, Rhs> OptionWrappingSub<Rhs> for Option<T>
where
    T: OptionOperations + OptionWrappingSub<Rhs>,
{
    type Output = <T as OptionWrappingSub<Rhs>>::Output;

    fn opt_wrapping_sub(self, rhs: Rhs) -> Option<Self::Output> {
        self.and_then(|inner_self| inner_self.opt_wrapping_sub(rhs))
    }
}

impl<T, InnerRhs> OptionWrappingSub<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingSub<InnerRhs>,
{
    type Output = <T as OptionWrappingSub<InnerRhs>>::Output;

    fn opt_wrapping_sub(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_sub(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingSub<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingSub<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingSub<InnerRhs>>::Output;

    fn opt_wrapping_sub(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_sub(*inner_rhs))
    }
}

// TODO impl on integers & time types

#[cfg(test)]
mod test {
    use super::*;
    use crate::OptionOperations;
    use core::ops::{Sub, SubAssign};

    #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
    struct MyInt(u64);

    impl OptionOperations for MyInt {}

    impl Sub<MyInt> for MyInt {
        type Output = MyInt;

        fn sub(self, rhs: MyInt) -> MyInt {
            MyInt(self.0.sub(rhs.0))
        }
    }

    impl Sub<u64> for MyInt {
        type Output = MyInt;

        fn sub(self, rhs: u64) -> MyInt {
            MyInt(self.0.sub(rhs))
        }
    }

    impl SubAssign<MyInt> for MyInt {
        fn sub_assign(&mut self, rhs: MyInt) {
            self.0.sub_assign(rhs.0)
        }
    }

    impl SubAssign<u64> for MyInt {
        fn sub_assign(&mut self, rhs: u64) {
            self.0.sub_assign(rhs)
        }
    }

    const MY_0: MyInt = MyInt(0);
    const MY_1: MyInt = MyInt(1);
    const MY_2: MyInt = MyInt(2);
    const MY_3: MyInt = MyInt(3);
    const MY_MAX: MyInt = MyInt(u64::MAX);
    const SOME_0: Option<MyInt> = Some(MY_0);
    const SOME_1: Option<MyInt> = Some(MY_1);
    const SOME_2: Option<MyInt> = Some(MY_2);
    const SOME_3: Option<MyInt> = Some(MY_3);
    const SOME_MAX: Option<MyInt> = Some(MY_MAX);
    const NONE: Option<MyInt> = None;

    #[test]
    fn sub_my() {
        assert_eq!(MY_3.opt_sub(MY_1), SOME_2);
        assert_eq!(SOME_3.opt_sub(MY_1), SOME_2);
        assert_eq!(MY_3.opt_sub(SOME_1), SOME_2);
        assert_eq!(MY_3.opt_sub(&SOME_1), SOME_2);
        assert_eq!(MY_3.opt_sub(NONE), NONE);
        assert_eq!(NONE.opt_sub(MY_3), NONE);
    }

    #[test]
    fn sub_u64() {
        assert_eq!(MY_3.opt_sub(1), SOME_2);
        assert_eq!(MY_3.opt_sub(Some(1)), SOME_2);
        assert_eq!(SOME_3.opt_sub(1), SOME_2);
        assert_eq!(SOME_3.opt_sub(Some(1)), SOME_2);
        assert_eq!(SOME_3.opt_sub(&Some(1)), SOME_2);
        assert_eq!(MY_3.opt_sub(Option::<u64>::None), NONE);
        assert_eq!(Option::<MyInt>::None.opt_sub(MY_0), NONE);
    }

    #[test]
    fn sub_assign_my() {
        let mut my = MY_3;
        my.opt_sub_assign(MY_1);
        assert_eq!(my, MY_2);

        let mut some = SOME_3;
        some.opt_sub_assign(MY_1);
        assert_eq!(some, SOME_2);

        let mut my = MY_3;
        my.opt_sub_assign(SOME_1);
        assert_eq!(my, MY_2);

        let mut my = MY_3;
        my.opt_sub_assign(&SOME_1);
        assert_eq!(my, MY_2);

        let mut my = MY_3;
        my.opt_sub_assign(NONE);
        assert_eq!(my, MY_3);

        let mut some = SOME_3;
        some.opt_sub_assign(SOME_1);
        assert_eq!(some, SOME_2);

        let mut some = SOME_3;
        some.opt_sub_assign(&SOME_1);
        assert_eq!(some, SOME_2);

        let mut some = SOME_3;
        some.opt_sub_assign(NONE);
        assert_eq!(some, SOME_3);

        let mut none = NONE;
        none.opt_sub_assign(SOME_1);
        assert_eq!(none, NONE);

        let mut none = NONE;
        none.opt_sub_assign(NONE);
        assert_eq!(none, NONE);
    }

    #[test]
    fn sub_assign_u64() {
        let mut my = MY_3;
        my.opt_sub_assign(1);
        assert_eq!(my, MY_2);

        let mut some = SOME_3;
        some.opt_sub_assign(1);
        assert_eq!(some, SOME_2);

        let mut my = MY_3;
        my.opt_sub_assign(Some(1));
        assert_eq!(my, MY_2);

        let mut my = MY_3;
        my.opt_sub_assign(&Some(1));
        assert_eq!(my, MY_2);

        let mut some = SOME_3;
        some.opt_sub_assign(Some(1));
        assert_eq!(some, SOME_2);

        let mut some = SOME_3;
        some.opt_sub_assign(&Some(1));
        assert_eq!(some, SOME_2);

        let mut none = NONE;
        none.opt_sub_assign(Some(1));
        assert_eq!(none, NONE);
    }

    #[test]
    fn checked_sub() {
        impl OptionCheckedSub for MyInt {
            type Output = MyInt;

            fn opt_checked_sub(self, rhs: MyInt) -> Result<Option<Self::Output>, Error> {
                self.0
                    .checked_sub(rhs.0)
                    .ok_or(Error::Overflow)
                    .map(|val| Some(MyInt(val)))
            }
        }

        impl OptionCheckedSub<u64> for MyInt {
            type Output = MyInt;

            fn opt_checked_sub(self, rhs: u64) -> Result<Option<Self::Output>, Error> {
                self.0
                    .checked_sub(rhs)
                    .ok_or(Error::Overflow)
                    .map(|val| Some(MyInt(val)))
            }
        }

        assert_eq!(MY_3.opt_checked_sub(MY_1), Ok(SOME_2));
        assert_eq!(MY_3.opt_checked_sub(SOME_1), Ok(SOME_2));
        assert_eq!(MY_3.opt_checked_sub(&SOME_1), Ok(SOME_2));
        assert_eq!(MY_0.opt_checked_sub(MY_1), Err(Error::Overflow));

        assert_eq!(SOME_3.opt_checked_sub(MY_1), Ok(SOME_2));
        assert_eq!(SOME_3.opt_checked_sub(SOME_1), Ok(SOME_2));
        assert_eq!(SOME_3.opt_checked_sub(&SOME_1), Ok(SOME_2));

        assert_eq!(SOME_0.opt_checked_sub(MY_1), Err(Error::Overflow));
        assert_eq!(SOME_0.opt_checked_sub(1), Err(Error::Overflow));
        assert_eq!(SOME_0.opt_checked_sub(Some(1)), Err(Error::Overflow));
        assert_eq!(MY_0.opt_checked_sub(SOME_1), Err(Error::Overflow));
        assert_eq!(MY_0.opt_checked_sub(NONE), Ok(None));
        assert_eq!(NONE.opt_checked_sub(MY_0), Ok(None));
    }

    #[test]
    fn saturating_sub() {
        impl OptionSaturatingSub for MyInt {
            type Output = MyInt;

            fn opt_saturating_sub(self, rhs: MyInt) -> Option<Self::Output> {
                Some(MyInt(self.0.saturating_sub(rhs.0)))
            }
        }

        impl OptionSaturatingSub<u64> for MyInt {
            type Output = MyInt;

            fn opt_saturating_sub(self, rhs: u64) -> Option<Self::Output> {
                Some(MyInt(self.0.saturating_sub(rhs)))
            }
        }

        assert_eq!(MY_3.opt_saturating_sub(MY_1), SOME_2);
        assert_eq!(MY_1.opt_saturating_sub(MY_2), SOME_0);
        assert_eq!(SOME_1.opt_saturating_sub(MY_2), SOME_0);
        assert_eq!(SOME_1.opt_saturating_sub(2), SOME_0);
        assert_eq!(SOME_1.opt_saturating_sub(Some(2)), SOME_0);
        assert_eq!(SOME_1.opt_saturating_sub(&Some(2)), SOME_0);
        assert_eq!(MY_1.opt_saturating_sub(SOME_2), SOME_0);
        assert_eq!(MY_1.opt_saturating_sub(&SOME_2), SOME_0);
        assert_eq!(MY_1.opt_saturating_sub(NONE), NONE);
        assert_eq!(NONE.opt_saturating_sub(MY_1), NONE);
    }

    #[test]
    fn overflowing_sub() {
        impl OptionOverflowingSub for MyInt {
            type Output = MyInt;

            fn opt_overflowing_sub(self, rhs: MyInt) -> Option<(Self::Output, bool)> {
                let ret = self.0.overflowing_sub(rhs.0);
                Some((MyInt(ret.0), ret.1))
            }
        }

        impl OptionOverflowingSub<u64> for MyInt {
            type Output = MyInt;

            fn opt_overflowing_sub(self, rhs: u64) -> Option<(Self::Output, bool)> {
                let ret = self.0.overflowing_sub(rhs);
                Some((MyInt(ret.0), ret.1))
            }
        }

        assert_eq!(MY_3.opt_overflowing_sub(MY_1), Some((MY_2, false)));
        assert_eq!(MY_1.opt_overflowing_sub(MY_2), Some((MY_MAX, true)));
        assert_eq!(SOME_1.opt_overflowing_sub(MY_2), Some((MY_MAX, true)));
        assert_eq!(SOME_1.opt_overflowing_sub(2), Some((MY_MAX, true)));
        assert_eq!(SOME_1.opt_overflowing_sub(Some(2)), Some((MY_MAX, true)));
        assert_eq!(SOME_1.opt_overflowing_sub(&Some(2)), Some((MY_MAX, true)));
        assert_eq!(MY_1.opt_overflowing_sub(SOME_2), Some((MY_MAX, true)));
        assert_eq!(MY_1.opt_overflowing_sub(&SOME_2), Some((MY_MAX, true)));
        assert_eq!(MY_1.opt_overflowing_sub(NONE), None);
        assert_eq!(NONE.opt_overflowing_sub(MY_1), None);
    }

    #[test]
    fn wrapping_sub() {
        impl OptionWrappingSub for MyInt {
            type Output = MyInt;

            fn opt_wrapping_sub(self, rhs: MyInt) -> Option<Self::Output> {
                Some(MyInt(self.0.wrapping_sub(rhs.0)))
            }
        }

        impl OptionWrappingSub<u64> for MyInt {
            type Output = MyInt;

            fn opt_wrapping_sub(self, rhs: u64) -> Option<Self::Output> {
                Some(MyInt(self.0.wrapping_sub(rhs)))
            }
        }

        assert_eq!(MY_3.opt_wrapping_sub(MY_1), SOME_2);
        assert_eq!(MY_1.opt_wrapping_sub(MY_2), SOME_MAX);
        assert_eq!(SOME_1.opt_wrapping_sub(MY_2), SOME_MAX);
        assert_eq!(SOME_1.opt_wrapping_sub(2), SOME_MAX);
        assert_eq!(SOME_1.opt_wrapping_sub(Some(2)), SOME_MAX);
        assert_eq!(SOME_1.opt_wrapping_sub(&Some(2)), SOME_MAX);
        assert_eq!(MY_1.opt_wrapping_sub(SOME_2), SOME_MAX);
        assert_eq!(MY_1.opt_wrapping_sub(&SOME_2), SOME_MAX);
        assert_eq!(MY_1.opt_wrapping_sub(NONE), None);
        assert_eq!(NONE.opt_wrapping_sub(MY_1), None);
    }
}
