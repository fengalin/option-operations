use core::ops::{Div, DivAssign};

use crate::{Error, OptionOperations};

/// TODO: doc
pub trait OptionDiv<Rhs, InnerRhs = Rhs> {
    type Output;

    fn opt_div(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, Rhs> OptionDiv<Rhs> for T
where
    T: OptionOperations + Div<Rhs>,
{
    type Output = <T as Div<Rhs>>::Output;

    fn opt_div(self, rhs: Rhs) -> Option<Self::Output> {
        Some(self.div(rhs))
    }
}

impl<T, InnerRhs> OptionDiv<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Div<InnerRhs>,
{
    type Output = <T as Div<InnerRhs>>::Output;

    fn opt_div(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.map(|inner_rhs| self.div(inner_rhs))
    }
}

impl<T, InnerRhs> OptionDiv<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Div<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Div<InnerRhs>>::Output;

    fn opt_div(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref().map(|inner_rhs| self.div(*inner_rhs))
    }
}

impl<T, Rhs> OptionDiv<Rhs> for Option<T>
where
    T: OptionOperations + Div<Rhs>,
{
    type Output = <T as Div<Rhs>>::Output;

    fn opt_div(self, rhs: Rhs) -> Option<Self::Output> {
        self.map(|inner_self| inner_self.div(rhs))
    }
}

impl<T, InnerRhs> OptionDiv<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Div<InnerRhs>,
{
    type Output = <T as Div<InnerRhs>>::Output;

    fn opt_div(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .map(|(inner_self, inner_rhs)| inner_self.div(inner_rhs))
    }
}

impl<T, InnerRhs> OptionDiv<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Div<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Div<InnerRhs>>::Output;

    fn opt_div(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .map(|(inner_self, inner_rhs)| inner_self.div(*inner_rhs))
    }
}

/// TODO: doc
pub trait OptionDivAssign<Rhs, InnerRhs = Rhs> {
    fn opt_div_assign(&mut self, rhs: Rhs);
}

impl<T, Rhs> OptionDivAssign<Rhs> for T
where
    T: OptionOperations + DivAssign<Rhs>,
{
    fn opt_div_assign(&mut self, rhs: Rhs) {
        self.div_assign(rhs)
    }
}

impl<T, InnerRhs> OptionDivAssign<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + DivAssign<InnerRhs>,
{
    fn opt_div_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs {
            self.div_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionDivAssign<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + DivAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_div_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.div_assign(*inner_rhs)
        }
    }
}

impl<T, Rhs> OptionDivAssign<Rhs> for Option<T>
where
    T: OptionOperations + DivAssign<Rhs>,
{
    fn opt_div_assign(&mut self, rhs: Rhs) {
        if let Some(inner_self) = self {
            inner_self.div_assign(rhs)
        }
    }
}

impl<T, InnerRhs> OptionDivAssign<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + DivAssign<InnerRhs>,
{
    fn opt_div_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs) {
            inner_self.div_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionDivAssign<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + DivAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_div_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs.as_ref()) {
            inner_self.div_assign(*inner_rhs)
        }
    }
}

/// TODO: doc
pub trait OptionCheckedDiv<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_checked_div(self, rhs: Rhs) -> Result<Option<Self::Output>, Error>;
}

impl<T, InnerRhs> OptionCheckedDiv<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedDiv<InnerRhs>,
{
    type Output = <T as OptionCheckedDiv<InnerRhs>>::Output;

    fn opt_checked_div(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs {
            self.opt_checked_div(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedDiv<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedDiv<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedDiv<InnerRhs>>::Output;

    fn opt_checked_div(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.opt_checked_div(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, Rhs> OptionCheckedDiv<Rhs> for Option<T>
where
    T: OptionOperations + OptionCheckedDiv<Rhs>,
{
    type Output = <T as OptionCheckedDiv<Rhs>>::Output;

    fn opt_checked_div(self, rhs: Rhs) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_self) = self {
            inner_self.opt_checked_div(rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedDiv<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedDiv<InnerRhs>,
{
    type Output = <T as OptionCheckedDiv<InnerRhs>>::Output;

    fn opt_checked_div(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs) {
            inner_self.opt_checked_div(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedDiv<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedDiv<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedDiv<InnerRhs>>::Output;

    fn opt_checked_div(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs.as_ref()) {
            inner_self.opt_checked_div(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionOverflowingDiv<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_overflowing_div(self, rhs: Rhs) -> Option<(Self::Output, bool)>;
}

impl<T, InnerRhs> OptionOverflowingDiv<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingDiv<InnerRhs>,
{
    type Output = <T as OptionOverflowingDiv<InnerRhs>>::Output;

    fn opt_overflowing_div(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.and_then(|inner_rhs| self.opt_overflowing_div(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingDiv<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingDiv<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingDiv<InnerRhs>>::Output;

    fn opt_overflowing_div(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_overflowing_div(*inner_rhs))
    }
}

impl<T, Rhs> OptionOverflowingDiv<Rhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingDiv<Rhs>,
{
    type Output = <T as OptionOverflowingDiv<Rhs>>::Output;

    fn opt_overflowing_div(self, rhs: Rhs) -> Option<(Self::Output, bool)> {
        self.and_then(|inner_self| inner_self.opt_overflowing_div(rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingDiv<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingDiv<InnerRhs>,
{
    type Output = <T as OptionOverflowingDiv<InnerRhs>>::Output;

    fn opt_overflowing_div(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_div(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingDiv<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingDiv<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingDiv<InnerRhs>>::Output;

    fn opt_overflowing_div(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_div(*inner_rhs))
    }
}

// TODO impl on integers & time types

/// TODO: doc
pub trait OptionWrappingDiv<Rhs = Self, InnerRhs = Rhs> {
    type Output;

    fn opt_wrapping_div(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, InnerRhs> OptionWrappingDiv<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingDiv<InnerRhs>,
{
    type Output = <T as OptionWrappingDiv<InnerRhs>>::Output;

    fn opt_wrapping_div(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.and_then(|inner_rhs| self.opt_wrapping_div(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingDiv<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingDiv<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingDiv<InnerRhs>>::Output;

    fn opt_wrapping_div(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_wrapping_div(*inner_rhs))
    }
}

impl<T, Rhs> OptionWrappingDiv<Rhs> for Option<T>
where
    T: OptionOperations + OptionWrappingDiv<Rhs>,
{
    type Output = <T as OptionWrappingDiv<Rhs>>::Output;

    fn opt_wrapping_div(self, rhs: Rhs) -> Option<Self::Output> {
        self.and_then(|inner_self| inner_self.opt_wrapping_div(rhs))
    }
}

impl<T, InnerRhs> OptionWrappingDiv<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingDiv<InnerRhs>,
{
    type Output = <T as OptionWrappingDiv<InnerRhs>>::Output;

    fn opt_wrapping_div(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_div(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingDiv<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingDiv<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingDiv<InnerRhs>>::Output;

    fn opt_wrapping_div(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_div(*inner_rhs))
    }
}

// TODO impl on integers & time types

#[cfg(test)]
mod test {
    use super::*;
    use crate::OptionOperations;
    use core::ops::{Div, DivAssign};

    #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
    struct MyInt(i64);

    impl OptionOperations for MyInt {}

    impl Div<MyInt> for MyInt {
        type Output = MyInt;

        fn div(self, rhs: MyInt) -> MyInt {
            MyInt(self.0.div(rhs.0))
        }
    }

    impl Div<i64> for MyInt {
        type Output = MyInt;

        fn div(self, rhs: i64) -> MyInt {
            MyInt(self.0.div(rhs))
        }
    }

    impl DivAssign<MyInt> for MyInt {
        fn div_assign(&mut self, rhs: MyInt) {
            self.0.div_assign(rhs.0)
        }
    }

    impl DivAssign<i64> for MyInt {
        fn div_assign(&mut self, rhs: i64) {
            self.0.div_assign(rhs)
        }
    }

    const MY_MINUS_1: MyInt = MyInt(-1);
    const MY_0: MyInt = MyInt(0);
    const MY_1: MyInt = MyInt(1);
    const MY_2: MyInt = MyInt(2);
    const MY_5: MyInt = MyInt(5);
    const MY_10: MyInt = MyInt(10);
    const MY_MIN: MyInt = MyInt(i64::MIN);
    const MY_HALF_MAX: MyInt = MyInt(i64::MAX / 2);
    const MY_MAX: MyInt = MyInt(i64::MAX);
    const SOME_MINUS_1: Option<MyInt> = Some(MY_MINUS_1);
    const SOME_0: Option<MyInt> = Some(MY_0);
    const SOME_1: Option<MyInt> = Some(MY_1);
    const SOME_2: Option<MyInt> = Some(MY_2);
    const SOME_5: Option<MyInt> = Some(MY_5);
    const SOME_10: Option<MyInt> = Some(MY_10);
    const SOME_MIN: Option<MyInt> = Some(MY_MIN);
    const SOME_HALF_MAX: Option<MyInt> = Some(MY_HALF_MAX);
    const SOME_MAX: Option<MyInt> = Some(MY_MAX);
    const NONE: Option<MyInt> = None;

    #[test]
    fn div_my() {
        assert_eq!(MY_5.opt_div(MY_1), SOME_5);
        assert_eq!(SOME_10.opt_div(MY_2), SOME_5);
        assert_eq!(MY_0.opt_div(SOME_1), SOME_0);
        assert_eq!(MY_MAX.opt_div(&SOME_2), SOME_HALF_MAX);
        assert_eq!(MY_1.opt_div(NONE), NONE);
        assert_eq!(NONE.opt_div(MY_1), NONE);
    }

    #[test]
    #[should_panic]
    fn div_by_zero_my() {
        let _ = SOME_10.opt_div(SOME_0);
    }

    #[test]
    fn div_i64() {
        assert_eq!(MY_5.opt_div(5), SOME_1);
        assert_eq!(SOME_10.opt_div(MY_2), SOME_5);
        assert_eq!(MY_0.opt_div(Some(1)), SOME_0);
        assert_eq!(MY_MAX.opt_div(Some(2)), SOME_HALF_MAX);
        assert_eq!(MY_1.opt_div(Option::<i64>::None), NONE);
        assert_eq!(Option::<MyInt>::None.opt_div(MY_1), NONE);
    }

    #[test]
    #[should_panic]
    fn div_by_zero_i64() {
        let _ = SOME_10.opt_div(Some(0));
    }

    #[test]
    fn div_assign_my() {
        let mut my = MY_5;
        my.opt_div_assign(MY_1);
        assert_eq!(my, MY_5);

        let mut some = SOME_10;
        some.opt_div_assign(MY_5);
        assert_eq!(some, SOME_2);

        let mut my = MY_0;
        my.opt_div_assign(SOME_1);
        assert_eq!(my, MY_0);

        let mut my = MY_MAX;
        my.opt_div_assign(&SOME_2);
        assert_eq!(my, MY_HALF_MAX);

        let mut my = MY_1;
        my.opt_div_assign(NONE);
        assert_eq!(my, MY_1);

        let mut some = SOME_2;
        some.opt_div_assign(SOME_1);
        assert_eq!(some, SOME_2);

        let mut some = SOME_10;
        some.opt_div_assign(&SOME_2);
        assert_eq!(some, SOME_5);

        let mut some = SOME_1;
        some.opt_div_assign(NONE);
        assert_eq!(some, SOME_1);

        let mut none = NONE;
        none.opt_div_assign(SOME_1);
        assert_eq!(none, NONE);

        let mut none = NONE;
        none.opt_div_assign(NONE);
        assert_eq!(none, NONE);
    }

    #[test]
    #[should_panic]
    fn div_assign_by_zero_my() {
        let mut some = SOME_10;
        some.opt_div_assign(SOME_0);
    }

    #[test]
    fn div_assign_i64() {
        let mut my = MY_5;
        my.opt_div_assign(1);
        assert_eq!(my, MY_5);

        let mut some = SOME_10;
        some.opt_div_assign(5);
        assert_eq!(some, SOME_2);

        let mut my = MY_0;
        my.opt_div_assign(1);
        assert_eq!(my, MY_0);

        let mut my = MY_MAX;
        my.opt_div_assign(2);
        assert_eq!(my, MY_HALF_MAX);

        let mut my = MY_1;
        my.opt_div_assign(Option::<i64>::None);
        assert_eq!(my, MY_1);

        let mut some = SOME_2;
        some.opt_div_assign(1);
        assert_eq!(some, SOME_2);

        let mut some = SOME_1;
        some.opt_div_assign(Option::<i64>::None);
        assert_eq!(some, SOME_1);

        let mut none = NONE;
        none.opt_div_assign(1);
        assert_eq!(none, NONE);

        let mut none = NONE;
        none.opt_div_assign(Option::<i64>::None);
        assert_eq!(none, NONE);
    }

    #[test]
    #[should_panic]
    fn div_assign_by_zero_i64() {
        let mut some = SOME_10;
        some.opt_div_assign(Some(0));
    }

    #[test]
    fn checked_div() {
        impl OptionCheckedDiv for MyInt {
            type Output = MyInt;

            fn opt_checked_div(self, rhs: MyInt) -> Result<Option<Self::Output>, Error> {
                if rhs.0 == 0 {
                    return Err(Error::DivisionByZero);
                }
                self.0
                    .checked_div(rhs.0)
                    .ok_or(Error::Overflow)
                    .map(|val| Some(MyInt(val)))
            }
        }

        impl OptionCheckedDiv<i64> for MyInt {
            type Output = MyInt;

            fn opt_checked_div(self, rhs: i64) -> Result<Option<Self::Output>, Error> {
                if rhs == 0 {
                    return Err(Error::DivisionByZero);
                }
                self.0
                    .checked_div(rhs)
                    .ok_or(Error::Overflow)
                    .map(|val| Some(MyInt(val)))
            }
        }

        assert_eq!(MY_2.opt_checked_div(MY_1), Ok(SOME_2));
        assert_eq!(MY_10.opt_checked_div(SOME_5), Ok(SOME_2));
        assert_eq!(MY_0.opt_checked_div(&SOME_1), Ok(SOME_0));
        assert_eq!(MY_MAX.opt_checked_div(MY_2), Ok(SOME_HALF_MAX));
        assert_eq!(MY_MAX.opt_checked_div(MY_0), Err(Error::DivisionByZero));
        assert_eq!(MY_MIN.opt_checked_div(MY_MINUS_1), Err(Error::Overflow));

        assert_eq!(SOME_2.opt_checked_div(MY_1), Ok(SOME_2));
        assert_eq!(SOME_10.opt_checked_div(SOME_2), Ok(SOME_5));
        assert_eq!(SOME_0.opt_checked_div(&SOME_1), Ok(SOME_0));

        assert_eq!(SOME_MAX.opt_checked_div(MY_2), Ok(SOME_HALF_MAX));
        assert_eq!(SOME_MAX.opt_checked_div(MY_0), Err(Error::DivisionByZero));
        assert_eq!(SOME_MIN.opt_checked_div(MY_MINUS_1), Err(Error::Overflow));
        assert_eq!(SOME_MAX.opt_checked_div(0), Err(Error::DivisionByZero));
        assert_eq!(SOME_MIN.opt_checked_div(-1), Err(Error::Overflow));
        assert_eq!(
            SOME_MAX.opt_checked_div(Some(0)),
            Err(Error::DivisionByZero)
        );
        assert_eq!(SOME_MIN.opt_checked_div(Some(-1)), Err(Error::Overflow));
        assert_eq!(SOME_MAX.opt_checked_div(SOME_0), Err(Error::DivisionByZero));
        assert_eq!(SOME_MIN.opt_checked_div(SOME_MINUS_1), Err(Error::Overflow));
        assert_eq!(MY_MIN.opt_checked_div(NONE), Ok(None));
        assert_eq!(NONE.opt_checked_div(SOME_MIN), Ok(None));
    }

    #[test]
    fn overflowing_div() {
        impl OptionOverflowingDiv for MyInt {
            type Output = MyInt;

            fn opt_overflowing_div(self, rhs: MyInt) -> Option<(Self::Output, bool)> {
                let ret = self.0.overflowing_div(rhs.0);
                Some((MyInt(ret.0), ret.1))
            }
        }

        impl OptionOverflowingDiv<i64> for MyInt {
            type Output = MyInt;

            fn opt_overflowing_div(self, rhs: i64) -> Option<(Self::Output, bool)> {
                let ret = self.0.overflowing_div(rhs);
                Some((MyInt(ret.0), ret.1))
            }
        }

        assert_eq!(MY_2.opt_overflowing_div(MY_1), Some((MY_2, false)));
        assert_eq!(MY_0.opt_overflowing_div(MY_1), Some((MY_0, false)));
        assert_eq!(MY_MAX.opt_overflowing_div(MY_2), Some((MY_HALF_MAX, false)));
        assert_eq!(MY_MIN.opt_overflowing_div(MY_MINUS_1), Some((MY_MIN, true)));
        assert_eq!(
            SOME_MIN.opt_overflowing_div(MY_MINUS_1),
            Some((MY_MIN, true))
        );
        assert_eq!(SOME_MIN.opt_overflowing_div(-1), Some((MY_MIN, true)));
        assert_eq!(SOME_MIN.opt_overflowing_div(Some(-1)), Some((MY_MIN, true)));
        assert_eq!(
            SOME_MIN.opt_overflowing_div(&Some(-1)),
            Some((MY_MIN, true))
        );
        assert_eq!(
            MY_MIN.opt_overflowing_div(SOME_MINUS_1),
            Some((MY_MIN, true))
        );
        assert_eq!(
            MY_MIN.opt_overflowing_div(&SOME_MINUS_1),
            Some((MY_MIN, true))
        );
        assert_eq!(MY_MIN.opt_overflowing_div(NONE), None);
        assert_eq!(NONE.opt_overflowing_div(MY_MIN), None);
    }

    #[test]
    fn wrapping_div() {
        impl OptionWrappingDiv for MyInt {
            type Output = MyInt;

            fn opt_wrapping_div(self, rhs: MyInt) -> Option<Self::Output> {
                Some(MyInt(self.0.wrapping_div(rhs.0)))
            }
        }

        impl OptionWrappingDiv<i64> for MyInt {
            type Output = MyInt;

            fn opt_wrapping_div(self, rhs: i64) -> Option<Self::Output> {
                Some(MyInt(self.0.wrapping_div(rhs)))
            }
        }

        assert_eq!(MY_2.opt_wrapping_div(MY_1), SOME_2);
        assert_eq!(MY_0.opt_wrapping_div(MY_1), SOME_0);
        assert_eq!(MY_MIN.opt_wrapping_div(MY_MINUS_1), SOME_MIN);
        assert_eq!(SOME_MIN.opt_wrapping_div(MY_MINUS_1), SOME_MIN);
        assert_eq!(SOME_MIN.opt_wrapping_div(-1), SOME_MIN);
        assert_eq!(SOME_MIN.opt_wrapping_div(Some(-1)), SOME_MIN);
        assert_eq!(SOME_MIN.opt_wrapping_div(&Some(-1)), SOME_MIN);
        assert_eq!(MY_MIN.opt_wrapping_div(SOME_MINUS_1), SOME_MIN);
        assert_eq!(MY_MIN.opt_wrapping_div(&SOME_MINUS_1), SOME_MIN);
        assert_eq!(MY_MIN.opt_wrapping_div(NONE), None);
        assert_eq!(NONE.opt_wrapping_div(MY_MIN), None);
    }
}
