#![cfg(test)]

use std::fmt;

#[cfg(not(feature = "assert_matches"))]
#[cfg_attr(feature = "allow_internal_unstable", allow_internal_unstable(core_panic))]
#[cfg_attr(feature = "rustc_attrs", rustc_macro_transparency = "semitransparent")]
macro_rules! assert_matches {
    ($left:expr, $(|)? $( $pattern:pat_param )|+ $( if $guard: expr )? $(,)?) => {
        match $left {
            $( $pattern )|+ $( if $guard )? => {}
            ref left_val => {
                $crate::polyfill::assert_matches_failed(
                    left_val,
                    core::stringify!($($pattern)|+ $(if $guard)?),
                    core::option::Option::None
                );
            }
        }
    };
    ($left:expr, $(|)? $( $pattern:pat_param )|+ $( if $guard: expr )?, $($arg:tt)+) => {
        match $left {
            $( $pattern )|+ $( if $guard )? => {}
            ref left_val => {
                $crate::polyfill::assert_matches_failed(
                    left_val,
                    core::stringify!($($pattern)|+ $(if $guard)?),
                    core::option::Option::Some(core::format_args!($($arg)+))
                );
            }
        }
    };
}

/// Internal function for `assert_match!`
#[cfg_attr(not(feature = "panic_immediate_abort"), inline(never), cold)]
#[cfg_attr(feature = "panic_immediate_abort", inline)]
#[track_caller]
#[doc(hidden)]
pub fn assert_matches_failed<T: fmt::Debug + ?Sized>(
    left: &T,
    right: &str,
    args: Option<fmt::Arguments<'_>>,
) -> ! {
    // The pattern is a string so it can be displayed directly.
    struct Pattern<'a>(&'a str);
    impl fmt::Debug for Pattern<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str(self.0)
        }
    }
    assert_failed_inner(&left, &Pattern(right), args);
}

/// Non-generic version of the above functions, to avoid code bloat.
#[cfg_attr(not(feature = "panic_immediate_abort"), inline(never), cold)]
#[cfg_attr(feature = "panic_immediate_abort", inline)]
#[track_caller]
pub fn assert_failed_inner(
    left: &dyn fmt::Debug,
    right: &dyn fmt::Debug,
    args: Option<fmt::Arguments<'_>>,
) -> ! {
    match args {
        Some(args) => panic!(
            r#"assertion failed: `(left matches right)`
  left: `{:?}`,
 right: `{:?}`: {}"#,
            left, right, args
        ),
        None => panic!(
            r#"assertion failed: `(left matches right)`
  left: `{:?}`,
 right: `{:?}`"#,
            left, right,
        ),
    }
}

#[cfg(not(feature = "assert_matches"))]
pub(crate) use assert_matches;

#[cfg(feature = "assert_matches")]
pub(crate) use std::assert_matches::assert_matches;
