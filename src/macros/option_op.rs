macro_rules! option_op {
    ($op_trait:ident, $op:ident, $op_name:ident $(, $extra_doc:expr)? $(,)?) => {
        paste::paste! {
            #[doc = "Trait for values and `Option`s " $op_name "."]
            ///
            /// Implementing this trait leads to the following auto-implementations:
            ///
            #[doc = "- `" [<Option $op_trait>] "<Option<InnerRhs>>` for `T`."]
            #[doc = "- `" [<Option $op_trait>] "<Rhs>` for `Option<T>`."]
            #[doc = "- `" [<Option $op_trait>] "<Option<InnerRhs>>` for `Option<T>`."]
            /// - ... and some variants with references.
            ///
            /// This trait is auto-implemented for [`OptionOperations`] types implementing
            #[doc = "`" $op_trait "<Rhs>`."]
            pub trait [<Option $op_trait>]<Rhs= Self, InnerRhs = Rhs> {
                #[doc = "The resulting inner type after applying the " $op_name "."]
                type Output;

                #[doc = "Computes the " $op_name "."]
                ///
                /// Returns `None` if at least one argument is `None`.
                $(#[doc = $extra_doc])?
                #[must_use]
                fn [<opt_ $op>](self, rhs: Rhs) -> Option<Self::Output>;
            }

            impl<T, Rhs> [<Option $op_trait>]<Rhs> for T
            where
                T: OptionOperations + $op_trait<Rhs>,
            {
                type Output = <T as $op_trait<Rhs>>::Output;

                fn [<opt_ $op>](self, rhs: Rhs) -> Option<Self::Output> {
                    Some(self.$op(rhs))
                }
            }

            impl<T, InnerRhs> [<Option $op_trait>]<Option<InnerRhs>, InnerRhs> for T
            where
                T: OptionOperations + $op_trait<InnerRhs>,
            {
                type Output = <T as $op_trait<InnerRhs>>::Output;

                fn [<opt_ $op>](self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
                    rhs.map(|inner_rhs| self.$op(inner_rhs))
                }
            }

            impl<T, InnerRhs> [<Option $op_trait>]<&Option<InnerRhs>, InnerRhs> for T
            where
                T: OptionOperations + $op_trait<InnerRhs>,
                InnerRhs: Copy,
            {
                type Output = <T as $op_trait<InnerRhs>>::Output;

                fn [<opt_ $op>](self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
                    rhs.as_ref().map(|inner_rhs| self.$op(*inner_rhs))
                }
            }

            impl<T, Rhs> [<Option $op_trait>]<Rhs> for Option<T>
            where
                T: OptionOperations + $op_trait<Rhs>,
            {
                type Output = <T as $op_trait<Rhs>>::Output;

                fn [<opt_ $op>](self, rhs: Rhs) -> Option<Self::Output> {
                    self.map(|inner_self| inner_self.$op(rhs))
                }
            }

            impl<T, InnerRhs> [<Option $op_trait>]<Option<InnerRhs>, InnerRhs> for Option<T>
            where
                T: OptionOperations + $op_trait<InnerRhs>,
            {
                type Output = <T as $op_trait<InnerRhs>>::Output;

                fn [<opt_ $op>](self, rhs: Option<InnerRhs>) -> Option<Self::Output> {
                    self.zip(rhs)
                        .map(|(inner_self, inner_rhs)| inner_self.$op(inner_rhs))
                }
            }

            impl<T, InnerRhs> [<Option $op_trait>]<&Option<InnerRhs>, InnerRhs> for Option<T>
            where
                T: OptionOperations + $op_trait<InnerRhs>,
                InnerRhs: Copy,
            {
                type Output = <T as $op_trait<InnerRhs>>::Output;

                fn [<opt_ $op>](self, rhs: &Option<InnerRhs>) -> Option<Self::Output> {
                    self.zip(rhs.as_ref())
                        .map(|(inner_self, inner_rhs)| inner_self.$op(*inner_rhs))
                }
            }
        }
    };
}
