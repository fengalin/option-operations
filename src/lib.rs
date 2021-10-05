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
pub use add::{
    OptionAdd, OptionAddAssign, OptionCheckedAdd, OptionOverflowingAdd, OptionSaturatingAdd,
    OptionWrappingAdd,
};

pub mod checked_error;
pub use checked_error::CheckedError;

pub mod eq;
pub use eq::OptionEq;

pub mod min_max;
pub use min_max::OptionMinMax;

pub mod ord;
pub use ord::OptionOrd;

pub mod sub;
pub use sub::{
    OptionCheckedSub, OptionOverflowingSub, OptionSaturatingSub, OptionSub, OptionSubAssign,
    OptionWrappingSub,
};

pub mod prelude {
    pub use crate::add::{
        OptionAdd, OptionAddAssign, OptionCheckedAdd, OptionOverflowingAdd, OptionSaturatingAdd,
        OptionWrappingAdd,
    };
    pub use crate::min_max::OptionMinMax;
    pub use crate::ord::OptionOrd;
    pub use crate::sub::{
        OptionCheckedSub, OptionOverflowingSub, OptionSaturatingSub, OptionSub, OptionSubAssign,
        OptionWrappingSub,
    };
    pub use crate::OptionOperations;
}
