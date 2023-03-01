/// Generate implementations of `contextual_core`'s traits with minimal fuss.
///
/// The supported patterns are documented under the headings below. An invocation of this
/// macro may contain, in any order, as many of each of those patterns as you wish (provided
/// that at least one such pattern is present in aggregate).
///
/// Where a pattern matches a `$self:ident` metavariable, it is expected to match against
/// the token `self` (it is only a metavariable to satisfy macro hygiene constraints).
///
/// Any `#[$attr:meta]` that are matched will be added to the relevant `fn` item in the
/// macro's expansion.
///
/// 1. # `cmp`
///
///     ```
///     macro_rules! contextual {
///         (
///             $(#[$attr:meta])*
///             fn cmp(
///                 &$self:ident,
///                 $other:ident: &$ty:ty,
///                 $context:tt: &$context_ty:ty
///             ) -> Ordering
///             $compare:block
///             
///             $($rest:tt)*
///         ) => { ... };
///     }
///     ```
///
///     Implements for the type `$ty`:
///
///     1. [`ContextualOrd<$context_ty>`] (using the given body `$compare` for its [`contextual_cmp`]
///        method);
///     2. its supertraits [`ContextualPartialOrd<$context_ty>`], [`ContextualPartialEq<$context_ty>`]
///        and [`ContextualEq<$context_ty>`] (each delegating to the implementation above); and
///     3. no-op reflexive implementations of [`ContextualBorrowMut<Self, $context_ty>`] and
///        [`ContextualBorrow<Self, $context_ty>`].
///
/// 2. # `partial_cmp`
///
///     ```
///     macro_rules! contextual {
///         (
///             $(#[$attr:meta])*
///             fn partial_cmp(
///                 &$self:ident,
///                 $other:ident: &$ty:ty,
///                 $context:tt: &$context_ty:ty
///             ) -> Option<Ordering>
///             $compare:block
///             
///             $($rest:tt)*
///         ) => { ... };
///     }
///     ```
///
///     Implements for the type `$ty`:
///
///     1. [`ContextualPartialOrd<$context_ty>`] (using the given body `$compare` for its
///        [`contextual_partial_cmp`] method);
///     2. its supertrait [`ContextualPartialEq<$context_ty>`] (delegating to the implementation
///        above); and
///     2. no-op reflexive implementations of [`ContextualBorrowMut<Self, $context_ty>`] and
///        [`ContextualBorrow<Self, $context_ty>`].
///
/// 3. # `eq`
///
///     ```
///     macro_rules! contextual {
///         (
///             $(#[$attr:meta])*
///             fn eq(
///                 &$self:ident,
///                 $other:ident: &$ty:ty,
///                 $context:tt: &$context_ty:ty
///             ) -> bool
///             $compare:block
///             
///             $($rest:tt)*
///         ) => { ... };
///     }
///     ```
///     Implements for the type `$ty`:
///
///     1. [`ContextualPartialEq<$context_ty>`] (using the given body `$compare` for its [`contextual_eq`]
///        method); and
///     2. no-op reflexive implementations of [`ContextualBorrowMut<Self, $context_ty>`] and
///        [`ContextualBorrow<Self, $context_ty>`].
///
/// 4. # `borrow` with return type and body
///
///     ```
///     macro_rules! contextual {
///         (
///             $(#[$attr:meta])*
///             fn borrow(
///                 $self:ident: &$ty:ty,
///                 $context:tt: &$context_ty:ty
///             ) -> &$borrowed:ty
///             $(, delegating $XXX:ident)?
///             $borrow:block
///         
///             $($rest:tt)*
///         ) => { ... };
///     }
///     ```
///
///     Implements for the type `$ty`:
///
///     1. [`ContextualBorrow<$borrowed, $context_ty>`] (using the given body `$borrow` for its [`contextual_borrow`]
///        method); and
///     2. iff `, delegating XXX` appears between the function's return type and its body (where `XXX` is one of
///        `cmp`, `partial_cmp` or `eq`), then the respective comparison trait(s) are also implemented (by
///        delegating to those of `$borrowed`).
///
/// 5. # `borrow` without return type or body
///
///     ```
///     macro_rules! contextual {
///         (
///             $(#[$attr:meta])*
///             fn borrow(
///                 $self:ident: &$ty:ty,
///                 _: &$context_ty:ty
///             );
///         
///             $($rest:tt)*
///         ) => { ... };
///     }
///     ```
///
///     Implements for the type `$ty` no-op reflexive implementations of [`ContextualBorrowMut<Self, $context_ty>`]
///     and [`ContextualBorrow<Self, $context_ty>`].
///
/// [`ContextualBorrow<$borrowed, $context_ty>`]: crate::borrow::ContextualBorrow
/// [`ContextualBorrow<Self, $context_ty>`]: crate::borrow::ContextualBorrow
/// [`ContextualBorrowMut<Self, $context_ty>`]: crate::borrow::ContextualBorrowMut
/// [`ContextualEq<$context_ty>`]: crate::cmp::ContextualEq
/// [`ContextualOrd<$context_ty>`]: crate::cmp::ContextualOrd
/// [`ContextualPartialEq<$context_ty>`]: crate::cmp::ContextualPartialEq
/// [`ContextualPartialOrd<$context_ty>`]: crate::cmp::ContextualPartialOrd
/// [`contextual_borrow`]: crate::borrow::ContextualBorrow::contextual_borrow
/// [`contextual_cmp`]: crate::cmp::ContextualOrd::contextual_cmp
/// [`contextual_eq`]: crate::cmp::ContextualPartialEq::contextual_eq
/// [`contextual_partial_cmp`]: crate::cmp::ContextualPartialOrd::contextual_partial_cmp
#[cfg(doc)]
#[macro_export]
macro_rules! contextual {
    { ... } => {};
}

#[cfg(not(doc))]
#[doc(hidden)]
#[macro_export]
macro_rules! contextual {
    (
        $(#[$attr:meta])*
        fn borrow(
            $self:ident: &$ty:ty,
            $context:tt: &$context_ty:ty
        ) -> &$borrowed:ty
        $borrow:block

        $($($rest:tt)+)?
    ) => {
        impl $crate::borrow::ContextualBorrow<$borrowed, $context_ty> for $ty {
            $(#[$attr])*
            fn contextual_borrow(&$self, $context: &$context_ty) -> &$borrowed $borrow
        }

        $(contextual! { $($rest)+ })?
    };

    (
        $(#[$attr:meta])*
        fn borrow(
            $self:ident: &$ty:ty,
            _: &$context_ty:ty
        );

        $($rest:tt)*
    ) => {
        impl $crate::borrow::ContextualBorrowMut<$ty, $context_ty> for $ty {
            $(#[$attr])*
            fn contextual_borrow_mut(&mut self, _: &$context_ty) -> &mut $ty { self }
        }

        contextual! {
            $(#[$attr])*
            fn borrow(self: &$ty, _: &$context_ty) -> &$ty { self }

            $($rest)*
        }
    };

    (
        $(#[$attr:meta])*
        fn eq(
            &$self:ident,
            $other:ident: &$ty:ty,
            $context:tt: &$context_ty:ty
        ) -> bool
        $compare:block

        $($rest:tt)*
    ) => {
        impl $crate::cmp::ContextualPartialEq<$context_ty> for $ty {
            $(#[$attr])*
            fn contextual_eq(&$self, $other: &Self, $context: &$context_ty) -> bool $compare
        }

        contextual! {
            fn borrow(self: &$ty, _: &$context_ty);
            $($rest)*
        }
    };

    (
        $(#[$attr:meta])*
        fn partial_cmp(
            &$self:ident,
            $other:ident: &$ty:ty,
            $context:tt: &$context_ty:ty
        ) -> Option<Ordering>
        $compare:block

        $($rest:tt)*
    ) => {
        impl $crate::cmp::ContextualPartialOrd<$context_ty> for $ty {
            $(#[$attr])*
            fn contextual_partial_cmp(&$self, $other: &Self, $context: &$context_ty) -> ::core::option::Option<::core::cmp::Ordering> $compare
        }

        contextual! {
            #[inline(always)]
            fn eq(&self, other: &$ty, context: &$context_ty) -> bool {
                $crate::cmp::ContextualPartialOrd::contextual_partial_cmp(self, other, context) == ::core::option::Option::Some(::core::cmp::Ordering::Equal)
            }
            $($rest)*
        }
    };

    (
        $(#[$attr:meta])*
        fn cmp(
            &$self:ident,
            $other:ident: &$ty:ty,
            $context:tt: &$context_ty:ty
        ) -> Ordering
        $compare:block

        $($rest:tt)*
    ) => {
        impl $crate::cmp::ContextualEq<$context_ty> for $ty {}
        impl $crate::cmp::ContextualOrd<$context_ty> for $ty {
            $(#[$attr])*
            fn contextual_cmp(&$self, $other: &Self, $context: &$context_ty) -> ::core::cmp::Ordering $compare
        }

        contextual! {
            #[inline(always)]
            fn partial_cmp(&self, other: &$ty, context: &$context_ty) -> Option<Ordering> {
                ::core::option::Option::Some($crate::cmp::ContextualOrd::contextual_cmp(self, other, context))
            }
            $($rest)*
        }
    };

    (
        $(#[$attr:meta])*
        fn borrow(
            $self:ident: &$ty:ty,
            $context:tt: &$context_ty:ty
        ) -> &$borrowed:ty, delegating eq
        $borrow:block

        $($rest:tt)*
    ) => {
        contextual! {
            $(#[$attr])*
            fn borrow($self: &$ty, $context: &$context_ty) -> &$borrowed $borrow

            #[inline(always)]
            fn eq(&self, other: &$ty, context: &$context_ty) -> bool {
                let this = $crate::borrow::ContextualBorrow::<$borrowed, $context_ty>::contextual_borrow(self, context);
                let that = $crate::borrow::ContextualBorrow::<$borrowed, $context_ty>::contextual_borrow(other, context);

                $crate::cmp::ContextualPartialEq::contextual_eq(this, that, context)
            }

            $($rest)*
        }
    };

    (
        $(#[$attr:meta])*
        fn borrow(
            $self:ident: &$ty:ty,
            $context:tt: &$context_ty:ty
        ) -> &$borrowed:ty, delegating partial_cmp
        $borrow:block

        $($rest:tt)*
    ) => {
        contextual! {
            $(#[$attr])*
            fn borrow($self: &$ty, $context: &$context_ty) -> &$borrowed $borrow

            #[inline(always)]
            fn partial_cmp(&self, other: &$ty, context: &$context_ty) -> Option<Ordering> {
                let this = $crate::borrow::ContextualBorrow::<$borrowed, $context_ty>::contextual_borrow(self, context);
                let that = $crate::borrow::ContextualBorrow::<$borrowed, $context_ty>::contextual_borrow(other, context);

                $crate::cmp::ContextualPartialOrd::contextual_partial_cmp(this, that, context)
            }

            $($rest)*
        }
    };
    (
        $(#[$attr:meta])*
        fn borrow(
            $self:ident: &$ty:ty,
            $context:tt: &$context_ty:ty
        ) -> &$borrowed:ty, delegating cmp
        $borrow:block

        $($rest:tt)*
    ) => {
        contextual! {
            $(#[$attr])*
            fn borrow($self: &$ty, $context: &$context_ty) -> &$borrowed $borrow

            #[inline(always)]
            fn cmp(&self, other: &$ty, context: &$context_ty) -> Ordering {
                let this = $crate::borrow::ContextualBorrow::<$borrowed, $context_ty>::contextual_borrow(self, context);
                let that = $crate::borrow::ContextualBorrow::<$borrowed, $context_ty>::contextual_borrow(other, context);

                $crate::cmp::ContextualOrd::contextual_cmp(this, that, context)
            }

            $($rest)*
        }
    };
}
