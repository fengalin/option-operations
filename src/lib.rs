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

pub mod min_max;
pub use min_max::OptionMinMax;

pub mod ord;
pub use ord::OptionOrd;

pub mod prelude {
    pub use super::OptionMinMax;
    pub use super::OptionOrd;
    pub use super::{
        OptionAdd, OptionAddAssign, OptionCheckedAdd, OptionOverflowingAdd, OptionSaturatingAdd,
        OptionWrappingAdd,
    };
}
