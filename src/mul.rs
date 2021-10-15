//! Traits for the multiplication [`OptionOperations`].

use core::ops::{Mul, MulAssign};

use crate::{Error, OptionOperations};

/// Trait for values and `Option`s multiplication.
///
/// Implementing this type leads to the following auto-implementations:
///
/// - `OptionMul<Option<InnerRhs>>` for `T`.
/// - `OptionMul<Rhs>` for `Option<T>`.
/// - `OptionMul<Option<InnerRhs>>` for `Option<T>`.
/// - ... and some variants with references.
///
/// This trait is auto-implemented for [`OptionOperations`] types
/// implementing `Mul<Rhs>`.
pub trait OptionMul<Rhs, InnerRhs = Rhs> {
    /// The resulting inner type after applying the operation.
    type Output;

    /// Computes the multiplication.
    ///
    /// Returns `None` if at least one argument is `None`.
    #[must_use]
    fn opt_mul(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, Rhs> OptionMul<Rhs> for T
where
    T: OptionOperations + Mul<Rhs>,
{
    type Output = <T as Mul<Rhs>>::Output;

    fn opt_mul(self, rhs: Rhs) -> Option<Self::Output> {
        Some(self.mul(rhs))
    }
}

impl<T, InnerRhs> OptionMul<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Mul<InnerRhs>,
{
    type Output = <T as Mul<InnerRhs>>::Output;

    fn opt_mul(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.map(|inner_rhs| self.mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionMul<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + Mul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Mul<InnerRhs>>::Output;

    fn opt_mul(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref().map(|inner_rhs| self.mul(*inner_rhs))
    }
}

impl<T, Rhs> OptionMul<Rhs> for Option<T>
where
    T: OptionOperations + Mul<Rhs>,
{
    type Output = <T as Mul<Rhs>>::Output;

    fn opt_mul(self, rhs: Rhs) -> Option<Self::Output> {
        self.map(|inner_self| inner_self.mul(rhs))
    }
}

impl<T, InnerRhs> OptionMul<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Mul<InnerRhs>,
{
    type Output = <T as Mul<InnerRhs>>::Output;

    fn opt_mul(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .map(|(inner_self, inner_rhs)| inner_self.mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionMul<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + Mul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as Mul<InnerRhs>>::Output;

    fn opt_mul(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .map(|(inner_self, inner_rhs)| inner_self.mul(*inner_rhs))
    }
}

/// Trait for values and `Option`s multiplication assignment.
///
/// Implementing this type leads to the following auto-implementations:
///
/// - `OptionMulAssign<Option<InnerRhs>>` for `T`.
/// - `OptionMulAssign<Rhs>` for `Option<T>`.
/// - `OptionMulAssign<Option<InnerRhs>>` for `Option<T>`.
/// - ... and some variants with references.
///
/// This trait is auto-implemented for [`OptionOperations`] types
/// implementing `MulAssign<Rhs>`.
pub trait OptionMulAssign<Rhs, InnerRhs = Rhs> {
    /// Performs the multiplication assignment.
    ///
    /// `self` is unchanged if `rhs` is `None`.
    fn opt_mul_assign(&mut self, rhs: Rhs);
}

impl<T, Rhs> OptionMulAssign<Rhs> for T
where
    T: OptionOperations + MulAssign<Rhs>,
{
    fn opt_mul_assign(&mut self, rhs: Rhs) {
        self.mul_assign(rhs)
    }
}

impl<T, InnerRhs> OptionMulAssign<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + MulAssign<InnerRhs>,
{
    fn opt_mul_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs {
            self.mul_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionMulAssign<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + MulAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_mul_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.mul_assign(*inner_rhs)
        }
    }
}

impl<T, Rhs> OptionMulAssign<Rhs> for Option<T>
where
    T: OptionOperations + MulAssign<Rhs>,
{
    fn opt_mul_assign(&mut self, rhs: Rhs) {
        if let Some(inner_self) = self {
            inner_self.mul_assign(rhs)
        }
    }
}

impl<T, InnerRhs> OptionMulAssign<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + MulAssign<InnerRhs>,
{
    fn opt_mul_assign(&mut self, rhs: Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs) {
            inner_self.mul_assign(inner_rhs)
        }
    }
}

impl<T, InnerRhs> OptionMulAssign<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + MulAssign<InnerRhs>,
    InnerRhs: Copy,
{
    fn opt_mul_assign(&mut self, rhs: &Option<InnerRhs>) {
        if let Some((inner_self, inner_rhs)) = self.as_mut().zip(rhs.as_ref()) {
            inner_self.mul_assign(*inner_rhs)
        }
    }
}

/// Trait for values and `Option`s checked multiplication.
///
/// Implementing this type leads to the following auto-implementations:
///
/// - `OptionCheckedMul<Option<InnerRhs>>` for `T`.
/// - `OptionCheckedMul<Rhs>` for `Option<T>`.
/// - `OptionCheckedMul<Option<InnerRhs>>` for `Option<T>`.
/// - ... and some variants with references.
///
/// Note that since the `std` library doesn't define any `CheckedMul` trait,
/// users must provide the base implementation for the inner type.
pub trait OptionCheckedMul<Rhs = Self, InnerRhs = Rhs> {
    /// The resulting inner type after applying the operation.
    type Output;

    /// Computes the checked multiplication.
    ///
    /// - Returns `Ok(Some(result))` if `result` could be computed.
    /// - Returns `Ok(None)` if at least one argument is `None`.
    /// - Returns `Err(Error::Overflow)` if an overflow occured.
    fn opt_checked_mul(self, rhs: Rhs) -> Result<Option<Self::Output>, Error>;
}

impl<T, InnerRhs> OptionCheckedMul<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedMul<InnerRhs>,
{
    type Output = <T as OptionCheckedMul<InnerRhs>>::Output;

    fn opt_checked_mul(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs {
            self.opt_checked_mul(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedMul<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionCheckedMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedMul<InnerRhs>>::Output;

    fn opt_checked_mul(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_rhs) = rhs.as_ref() {
            self.opt_checked_mul(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, Rhs> OptionCheckedMul<Rhs> for Option<T>
where
    T: OptionOperations + OptionCheckedMul<Rhs>,
{
    type Output = <T as OptionCheckedMul<Rhs>>::Output;

    fn opt_checked_mul(self, rhs: Rhs) -> Result<Option<Self::Output>, Error> {
        if let Some(inner_self) = self {
            inner_self.opt_checked_mul(rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedMul<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedMul<InnerRhs>,
{
    type Output = <T as OptionCheckedMul<InnerRhs>>::Output;

    fn opt_checked_mul(self, rhs: Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs) {
            inner_self.opt_checked_mul(inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl<T, InnerRhs> OptionCheckedMul<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionCheckedMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionCheckedMul<InnerRhs>>::Output;

    fn opt_checked_mul(self, rhs: &Option<InnerRhs>) -> Result<Option<Self::Output>, Error> {
        if let (Some(inner_self), Some(inner_rhs)) = (self, rhs.as_ref()) {
            inner_self.opt_checked_mul(*inner_rhs)
        } else {
            Ok(None)
        }
    }
}

impl_for_ints!(OptionCheckedMul, {
    type Output = Self;
    fn opt_checked_mul(self, rhs: Self) -> Result<Option<Self::Output>, Error> {
        self.checked_mul(rhs).ok_or(Error::Overflow).map(Some)
    }
});

impl OptionCheckedMul<u32> for core::time::Duration {
    type Output = Self;
    fn opt_checked_mul(self, rhs: u32) -> Result<Option<Self::Output>, Error> {
        self.checked_mul(rhs).ok_or(Error::Overflow).map(Some)
    }
}

/// Trait for values and `Option`s overflowing multiplication.
///
/// Implementing this type leads to the following auto-implementations:
///
/// - `OptionOverflowingMul<Option<InnerRhs>>` for `T`.
/// - `OptionOverflowingMul<Rhs>` for `Option<T>`.
/// - `OptionOverflowingMul<Option<InnerRhs>>` for `Option<T>`.
/// - ... and some variants with references.
///
/// Note that since the `std` library doesn't define any `OverflowingMul`
/// trait, users must provide the base implementation for the inner type.
pub trait OptionOverflowingMul<Rhs = Self, InnerRhs = Rhs> {
    /// The resulting inner type after applying the operation.
    type Output;

    /// Returns a tuple of the multiplication along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// Returns `None` if at least one argument is `None`.
    #[must_use]
    fn opt_overflowing_mul(self, rhs: Rhs) -> Option<(Self::Output, bool)>;
}

impl<T, InnerRhs> OptionOverflowingMul<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingMul<InnerRhs>,
{
    type Output = <T as OptionOverflowingMul<InnerRhs>>::Output;

    fn opt_overflowing_mul(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.and_then(|inner_rhs| self.opt_overflowing_mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingMul<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionOverflowingMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingMul<InnerRhs>>::Output;

    fn opt_overflowing_mul(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_overflowing_mul(*inner_rhs))
    }
}

impl<T, Rhs> OptionOverflowingMul<Rhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingMul<Rhs>,
{
    type Output = <T as OptionOverflowingMul<Rhs>>::Output;

    fn opt_overflowing_mul(self, rhs: Rhs) -> Option<(Self::Output, bool)> {
        self.and_then(|inner_self| inner_self.opt_overflowing_mul(rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingMul<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingMul<InnerRhs>,
{
    type Output = <T as OptionOverflowingMul<InnerRhs>>::Output;

    fn opt_overflowing_mul(self, rhs: Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionOverflowingMul<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionOverflowingMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionOverflowingMul<InnerRhs>>::Output;

    fn opt_overflowing_mul(self, rhs: &Option<InnerRhs>) -> Option<(Self::Output, bool)> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_overflowing_mul(*inner_rhs))
    }
}

impl_for_ints!(OptionOverflowingMul, {
    type Output = Self;
    fn opt_overflowing_mul(self, rhs: Self) -> Option<(Self::Output, bool)> {
        Some(self.overflowing_mul(rhs))
    }
});

/// Trait for values and `Option`s saturating multiplication.
///
/// Implementing this type leads to the following auto-implementations:
///
/// - `OptionSaturatingMul<Option<InnerRhs>>` for `T`.
/// - `OptionSaturatingMul<Rhs>` for `Option<T>`.
/// - `OptionSaturatingMul<Option<InnerRhs>>` for `Option<T>`.
/// - ... and some variants with references.
///
/// Note that since the `std` library doesn't define any `SaturatingMul`
/// trait, users must provide the base implementation for the inner type.
pub trait OptionSaturatingMul<Rhs = Self, InnerRhs = Rhs> {
    /// The resulting inner type after applying the operation.
    type Output;

    /// Computes the multiplication, saturating at the numeric bounds instead of
    /// overflowing.
    ///
    /// Returns `None` if at least one argument is `None`.
    #[must_use]
    fn opt_saturating_mul(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, InnerRhs> OptionSaturatingMul<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionSaturatingMul<InnerRhs>,
{
    type Output = <T as OptionSaturatingMul<InnerRhs>>::Output;

    fn opt_saturating_mul(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.and_then(|inner_rhs| self.opt_saturating_mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingMul<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionSaturatingMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionSaturatingMul<InnerRhs>>::Output;

    fn opt_saturating_mul(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_saturating_mul(*inner_rhs))
    }
}

impl<T, Rhs> OptionSaturatingMul<Rhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingMul<Rhs>,
{
    type Output = <T as OptionSaturatingMul<Rhs>>::Output;

    fn opt_saturating_mul(self, rhs: Rhs) -> Option<Self::Output> {
        self.and_then(|inner_self| inner_self.opt_saturating_mul(rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingMul<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingMul<InnerRhs>,
{
    type Output = <T as OptionSaturatingMul<InnerRhs>>::Output;

    fn opt_saturating_mul(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_saturating_mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionSaturatingMul<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionSaturatingMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionSaturatingMul<InnerRhs>>::Output;

    fn opt_saturating_mul(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_saturating_mul(*inner_rhs))
    }
}

impl_for_ints!(OptionSaturatingMul, {
    type Output = Self;
    fn opt_saturating_mul(self, rhs: Self) -> Option<Self::Output> {
        Some(self.saturating_mul(rhs))
    }
});

impl OptionSaturatingMul<u32> for core::time::Duration {
    type Output = Self;
    fn opt_saturating_mul(self, rhs: u32) -> Option<Self::Output> {
        Some(self.saturating_mul(rhs))
    }
}

/// Trait for values and `Option`s wrapping multiplication.
///
/// Implementing this type leads to the following auto-implementations:
///
/// - `OptionWrappingMul<Option<InnerRhs>>` for `T`.
/// - `OptionWrappingMul<Rhs>` for `Option<T>`.
/// - `OptionWrappingMul<Option<InnerRhs>>` for `Option<T>`.
/// - ... and some variants with references.
///
/// Note that since the `std` library doesn't define any `WrappingMul`
/// trait, users must provide the base implementation for the inner type.
pub trait OptionWrappingMul<Rhs = Self, InnerRhs = Rhs> {
    /// The resulting inner type after applying the operation.
    type Output;

    /// Computes the multiplication, wrapping around at the numeric bounds
    /// instead of overflowing.
    ///
    /// Returns `None` if at least one argument is `None`.
    #[must_use]
    fn opt_wrapping_mul(self, rhs: Rhs) -> Option<Self::Output>;
}

impl<T, InnerRhs> OptionWrappingMul<Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingMul<InnerRhs>,
{
    type Output = <T as OptionWrappingMul<InnerRhs>>::Output;

    fn opt_wrapping_mul(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        rhs.and_then(|inner_rhs| self.opt_wrapping_mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingMul<&Option<InnerRhs>, InnerRhs> for T
where
    T: OptionOperations + OptionWrappingMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingMul<InnerRhs>>::Output;

    fn opt_wrapping_mul(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        rhs.as_ref()
            .and_then(|inner_rhs| self.opt_wrapping_mul(*inner_rhs))
    }
}

impl<T, Rhs> OptionWrappingMul<Rhs> for Option<T>
where
    T: OptionOperations + OptionWrappingMul<Rhs>,
{
    type Output = <T as OptionWrappingMul<Rhs>>::Output;

    fn opt_wrapping_mul(self, rhs: Rhs) -> Option<Self::Output> {
        self.and_then(|inner_self| inner_self.opt_wrapping_mul(rhs))
    }
}

impl<T, InnerRhs> OptionWrappingMul<Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingMul<InnerRhs>,
{
    type Output = <T as OptionWrappingMul<InnerRhs>>::Output;

    fn opt_wrapping_mul(self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs)
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_mul(inner_rhs))
    }
}

impl<T, InnerRhs> OptionWrappingMul<&Option<InnerRhs>, InnerRhs> for Option<T>
where
    T: OptionOperations + OptionWrappingMul<InnerRhs>,
    InnerRhs: Copy,
{
    type Output = <T as OptionWrappingMul<InnerRhs>>::Output;

    fn opt_wrapping_mul(self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
        self.zip(rhs.as_ref())
            .and_then(|(inner_self, inner_rhs)| inner_self.opt_wrapping_mul(*inner_rhs))
    }
}

impl_for_ints!(OptionWrappingMul, {
    type Output = Self;
    fn opt_wrapping_mul(self, rhs: Self) -> Option<Self::Output> {
        Some(self.wrapping_mul(rhs))
    }
});

#[cfg(test)]
mod test {
    use super::*;
    use crate::OptionOperations;
    use core::ops::{Mul, MulAssign};

    #[derive(Copy, Clone, Debug, PartialEq, PartialOrd)]
    struct MyInt(u64);

    impl OptionOperations for MyInt {}

    impl Mul<MyInt> for MyInt {
        type Output = MyInt;

        fn mul(self, rhs: MyInt) -> MyInt {
            MyInt(self.0.mul(rhs.0))
        }
    }

    impl Mul<u64> for MyInt {
        type Output = MyInt;

        fn mul(self, rhs: u64) -> MyInt {
            MyInt(self.0.mul(rhs))
        }
    }

    impl MulAssign<MyInt> for MyInt {
        fn mul_assign(&mut self, rhs: MyInt) {
            self.0.mul_assign(rhs.0)
        }
    }

    impl MulAssign<u64> for MyInt {
        fn mul_assign(&mut self, rhs: u64) {
            self.0.mul_assign(rhs)
        }
    }

    const MY_0: MyInt = MyInt(0);
    const MY_1: MyInt = MyInt(1);
    const MY_2: MyInt = MyInt(2);
    const MY_5: MyInt = MyInt(5);
    const MY_10: MyInt = MyInt(10);
    const MY_HALF_MAX: MyInt = MyInt(u64::MAX / 2);
    const MY_MAX_MINUS_1: MyInt = MyInt(u64::MAX - 1);
    // u64::MAX is an odd nb, so (u64::MAX / 2) * 2 == (u64::MAX - 1)
    const MY_MAX: MyInt = MyInt(u64::MAX);
    const SOME_0: Option<MyInt> = Some(MY_0);
    const SOME_1: Option<MyInt> = Some(MY_1);
    const SOME_2: Option<MyInt> = Some(MY_2);
    const SOME_5: Option<MyInt> = Some(MY_5);
    const SOME_10: Option<MyInt> = Some(MY_10);
    const SOME_HALF_MAX: Option<MyInt> = Some(MY_HALF_MAX);
    const SOME_MAX_MINUS_1: Option<MyInt> = Some(MY_MAX_MINUS_1);
    const SOME_MAX: Option<MyInt> = Some(MY_MAX);
    const NONE: Option<MyInt> = None;

    #[test]
    fn mul_my() {
        assert_eq!(MY_1.opt_mul(MY_5), SOME_5);
        assert_eq!(SOME_2.opt_mul(MY_5), SOME_10);
        assert_eq!(MY_0.opt_mul(SOME_1), SOME_0);
        // See comment in the const definitions
        assert_eq!(MY_HALF_MAX.opt_mul(&SOME_2), SOME_MAX_MINUS_1);
        assert_eq!(MY_1.opt_mul(NONE), NONE);
        assert_eq!(NONE.opt_mul(MY_1), NONE);
    }

    #[test]
    fn mul_u64() {
        assert_eq!(MY_1.opt_mul(5), SOME_5);
        assert_eq!(SOME_2.opt_mul(5), SOME_10);
        assert_eq!(MY_0.opt_mul(Some(1)), SOME_0);
        // See comment in the const definitions
        assert_eq!(MY_HALF_MAX.opt_mul(Some(2)), SOME_MAX_MINUS_1);
        assert_eq!(MY_1.opt_mul(Option::<u64>::None), NONE);
        assert_eq!(Option::<MyInt>::None.opt_mul(MY_1), NONE);
    }

    #[test]
    fn mul_assign_my() {
        let mut my = MY_1;
        my.opt_mul_assign(MY_5);
        assert_eq!(my, MY_5);

        let mut some = SOME_2;
        some.opt_mul_assign(MY_5);
        assert_eq!(some, SOME_10);

        let mut my = MY_0;
        my.opt_mul_assign(SOME_1);
        assert_eq!(my, MY_0);

        // See comment in the const definitions
        let mut my = MY_HALF_MAX;
        my.opt_mul_assign(&SOME_2);
        assert_eq!(my, MY_MAX_MINUS_1);

        let mut my = MY_1;
        my.opt_mul_assign(NONE);
        assert_eq!(my, MY_1);

        let mut some = SOME_1;
        some.opt_mul_assign(SOME_2);
        assert_eq!(some, SOME_2);

        let mut some = SOME_5;
        some.opt_mul_assign(&SOME_2);
        assert_eq!(some, SOME_10);

        let mut some = SOME_1;
        some.opt_mul_assign(NONE);
        assert_eq!(some, SOME_1);

        let mut none = NONE;
        none.opt_mul_assign(SOME_1);
        assert_eq!(none, NONE);

        let mut none = NONE;
        none.opt_mul_assign(NONE);
        assert_eq!(none, NONE);
    }

    #[test]
    fn mul_assign_u64() {
        let mut my = MY_1;
        my.opt_mul_assign(5);
        assert_eq!(my, MY_5);

        let mut some = SOME_2;
        some.opt_mul_assign(5);
        assert_eq!(some, SOME_10);

        let mut my = MY_0;
        my.opt_mul_assign(1);
        assert_eq!(my, MY_0);

        // See comment in the const definitions
        let mut my = MY_HALF_MAX;
        my.opt_mul_assign(2);
        assert_eq!(my, MY_MAX_MINUS_1);

        let mut my = MY_1;
        my.opt_mul_assign(Option::<u64>::None);
        assert_eq!(my, MY_1);

        let mut some = SOME_1;
        some.opt_mul_assign(2);
        assert_eq!(some, SOME_2);

        let mut some = SOME_1;
        some.opt_mul_assign(Option::<u64>::None);
        assert_eq!(some, SOME_1);

        let mut none = NONE;
        none.opt_mul_assign(1);
        assert_eq!(none, NONE);

        let mut none = NONE;
        none.opt_mul_assign(Option::<u64>::None);
        assert_eq!(none, NONE);
    }

    #[test]
    fn checked_mul() {
        impl OptionCheckedMul for MyInt {
            type Output = MyInt;
            fn opt_checked_mul(self, rhs: MyInt) -> Result<Option<Self::Output>, Error> {
                self.0.opt_checked_mul(rhs.0).map(|ok| ok.map(MyInt))
            }
        }

        impl OptionCheckedMul<u64> for MyInt {
            type Output = MyInt;
            fn opt_checked_mul(self, rhs: u64) -> Result<Option<Self::Output>, Error> {
                self.0.opt_checked_mul(rhs).map(|ok| ok.map(MyInt))
            }
        }

        assert_eq!(MY_1.opt_checked_mul(MY_2), Ok(SOME_2));
        assert_eq!(MY_2.opt_checked_mul(SOME_5), Ok(SOME_10));
        assert_eq!(MY_1.opt_checked_mul(&SOME_0), Ok(SOME_0));
        assert_eq!(MY_HALF_MAX.opt_checked_mul(MY_2), Ok(SOME_MAX_MINUS_1));
        assert_eq!(MY_HALF_MAX.opt_checked_mul(MY_5), Err(Error::Overflow));

        assert_eq!(SOME_1.opt_checked_mul(MY_2), Ok(SOME_2));
        assert_eq!(SOME_2.opt_checked_mul(SOME_5), Ok(SOME_10));
        assert_eq!(SOME_1.opt_checked_mul(&SOME_0), Ok(SOME_0));

        assert_eq!(SOME_HALF_MAX.opt_checked_mul(MY_2), Ok(SOME_MAX_MINUS_1));
        assert_eq!(SOME_HALF_MAX.opt_checked_mul(MY_5), Err(Error::Overflow));
        assert_eq!(SOME_MAX.opt_checked_mul(2), Err(Error::Overflow));
        assert_eq!(SOME_HALF_MAX.opt_checked_mul(Some(5)), Err(Error::Overflow));
        assert_eq!(SOME_MAX.opt_checked_mul(SOME_2), Err(Error::Overflow));
        assert_eq!(MY_MAX.opt_checked_mul(NONE), Ok(None));
        assert_eq!(NONE.opt_checked_mul(SOME_MAX), Ok(None));
    }

    #[test]
    fn saturating_mul() {
        impl OptionSaturatingMul for MyInt {
            type Output = MyInt;
            fn opt_saturating_mul(self, rhs: MyInt) -> Option<Self::Output> {
                self.0.opt_saturating_mul(rhs.0).map(MyInt)
            }
        }

        impl OptionSaturatingMul<u64> for MyInt {
            type Output = MyInt;
            fn opt_saturating_mul(self, rhs: u64) -> Option<Self::Output> {
                self.0.opt_saturating_mul(rhs).map(MyInt)
            }
        }

        assert_eq!(MY_1.opt_saturating_mul(MY_2), SOME_2);
        assert_eq!(MY_0.opt_saturating_mul(MY_2), SOME_0);
        assert_eq!(MY_MAX.opt_saturating_mul(MY_2), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_mul(MY_2), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_mul(2), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_mul(Some(2)), SOME_MAX);
        assert_eq!(SOME_MAX.opt_saturating_mul(&Some(2)), SOME_MAX);
        assert_eq!(MY_2.opt_saturating_mul(SOME_MAX), SOME_MAX);
        assert_eq!(MY_2.opt_saturating_mul(&SOME_MAX), SOME_MAX);
        assert_eq!(MY_MAX.opt_saturating_mul(NONE), NONE);
        assert_eq!(NONE.opt_saturating_mul(SOME_MAX), NONE);
    }

    #[test]
    fn overflowing_mul() {
        impl OptionOverflowingMul for MyInt {
            type Output = MyInt;
            fn opt_overflowing_mul(self, rhs: MyInt) -> Option<(Self::Output, bool)> {
                self.0
                    .opt_overflowing_mul(rhs.0)
                    .map(|(val, flag)| (MyInt(val), flag))
            }
        }

        impl OptionOverflowingMul<u64> for MyInt {
            type Output = MyInt;
            fn opt_overflowing_mul(self, rhs: u64) -> Option<(Self::Output, bool)> {
                self.0
                    .opt_overflowing_mul(rhs)
                    .map(|(val, flag)| (MyInt(val), flag))
            }
        }

        assert_eq!(MY_1.opt_overflowing_mul(MY_2), Some((MY_2, false)));
        assert_eq!(MY_1.opt_overflowing_mul(MY_0), Some((MY_0, false)));
        assert_eq!(
            MY_MAX.opt_overflowing_mul(MY_2),
            Some((MY_MAX_MINUS_1, true))
        );
        assert_eq!(
            SOME_MAX.opt_overflowing_mul(MY_2),
            Some((MY_MAX_MINUS_1, true))
        );
        assert_eq!(
            SOME_MAX.opt_overflowing_mul(2),
            Some((MY_MAX_MINUS_1, true))
        );
        assert_eq!(
            SOME_MAX.opt_overflowing_mul(Some(2)),
            Some((MY_MAX_MINUS_1, true))
        );
        assert_eq!(
            SOME_MAX.opt_overflowing_mul(&Some(2)),
            Some((MY_MAX_MINUS_1, true))
        );
        assert_eq!(
            MY_2.opt_overflowing_mul(SOME_MAX),
            Some((MY_MAX_MINUS_1, true))
        );
        assert_eq!(
            MY_2.opt_overflowing_mul(&SOME_MAX),
            Some((MY_MAX_MINUS_1, true))
        );
        assert_eq!(MY_MAX.opt_overflowing_mul(NONE), None);
        assert_eq!(NONE.opt_overflowing_mul(SOME_MAX), None);
    }

    #[test]
    fn wrapping_mul() {
        impl OptionWrappingMul for MyInt {
            type Output = MyInt;
            fn opt_wrapping_mul(self, rhs: MyInt) -> Option<Self::Output> {
                self.0.opt_wrapping_mul(rhs.0).map(MyInt)
            }
        }

        impl OptionWrappingMul<u64> for MyInt {
            type Output = MyInt;
            fn opt_wrapping_mul(self, rhs: u64) -> Option<Self::Output> {
                self.0.opt_wrapping_mul(rhs).map(MyInt)
            }
        }

        assert_eq!(MY_1.opt_wrapping_mul(MY_2), SOME_2);
        assert_eq!(MY_1.opt_wrapping_mul(MY_0), SOME_0);
        assert_eq!(MY_MAX.opt_wrapping_mul(MY_2), SOME_MAX_MINUS_1);
        assert_eq!(SOME_MAX.opt_wrapping_mul(MY_2), SOME_MAX_MINUS_1);
        assert_eq!(SOME_MAX.opt_wrapping_mul(2), SOME_MAX_MINUS_1);
        assert_eq!(SOME_MAX.opt_wrapping_mul(Some(2)), SOME_MAX_MINUS_1);
        assert_eq!(SOME_MAX.opt_wrapping_mul(&Some(2)), SOME_MAX_MINUS_1);
        assert_eq!(MY_2.opt_wrapping_mul(SOME_MAX), SOME_MAX_MINUS_1);
        assert_eq!(MY_2.opt_wrapping_mul(&SOME_MAX), SOME_MAX_MINUS_1);
        assert_eq!(MY_MAX.opt_wrapping_mul(NONE), None);
        assert_eq!(NONE.opt_wrapping_mul(SOME_MAX), None);
    }
}
