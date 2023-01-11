#![allow(
    clippy::clone_on_copy,
    clippy::drop_non_drop,
    clippy::needless_borrow,
    clippy::type_complexity,
    clippy::unnecessary_mut_passed,
    missing_docs,
    unstable_name_collisions,
    unused_attributes
)]
#![cfg_attr(
    test,
    allow(
        clippy::bool_assert_comparison,
        clippy::bool_to_int_with_if,
        clippy::ifs_same_cond,
        clippy::needless_range_loop,
        clippy::redundant_clone,
        clippy::redundant_closure,
        clippy::single_char_add_str,
        clippy::useless_vec,
    )
)]

pub mod collections {
    mod btree;

    pub mod btree_map {
        //! An ordered map based on a B-Tree.
        pub use super::btree::map::*;
    }

    pub mod btree_set {
        //! An ordered set based on a B-Tree.
        pub use super::btree::set::*;
    }
}

#[cfg(test)]
mod testing;
