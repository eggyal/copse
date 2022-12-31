#[macro_use]
#[allow(unstable_name_collisions)]
mod definitions {
    #[cfg(not(all(feature = "allocator_api", feature = "new_uninit")))]
    use alloc::alloc::Layout;
    use cfg_if::cfg_if;
    use core::mem::MaybeUninit;

    cfg_if! {
        if #[cfg(feature = "allocator_api")] {
            pub use alloc::alloc::{Allocator, Global};
        } else {
            use core::ptr::NonNull;

            pub trait Allocator {
                #[inline]
                fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, ()> {
                    unsafe {
                        let len = layout.size();
                        let data = if len == 0 {
                            layout.align() as _
                        } else {
                            NonNull::new(alloc::alloc::alloc(layout)).ok_or(())?.as_ptr()
                        };
                        Ok(NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(
                            data, len,
                        )))
                    }
                }

                #[inline]
                unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                    if layout.size() != 0 {
                        unsafe { alloc::alloc::dealloc(ptr.as_ptr(), layout) }
                    }
                }
            }

            #[derive(Copy, Clone, Debug)]
            pub struct Global;

            impl Allocator for Global {}
        }
    }

    cfg_if! {
        if #[cfg(feature = "hasher_prefixfree_extras")] {
            pub use core::hash::Hasher;
        } else {
            pub trait Hasher: core::hash::Hasher {
                #[inline]
                fn write_length_prefix(&mut self, len: usize) {
                    self.write_usize(len);
                }
            }

            impl<H: core::hash::Hasher> Hasher for H {}
        }
    }

    cfg_if! {
        if #[cfg(feature = "core_intrinsics")] {
            pub use core::intrinsics;
        } else {
            pub mod intrinsics {
                pub fn abort() -> ! {
                    cfg_if::cfg_if! {
                        if #[cfg(feature = "std")] {
                            std::process::abort()
                        } else {
                            panic!()
                        }
                    }
                }
            }
        }
    }

    cfg_if! {
        if #[cfg(feature = "allocator_api")] {
            macro_rules! Box {
                ($t:ty$(, $a:ty)?) => { alloc::boxed::Box<$t$(, $a)?> };
            }
        } else {
            macro_rules! Box {
                ($t:ty$(, $a:ty)?) => { alloc::boxed::Box<$t> };
            }
        }
    }

    pub trait NewUninit<T, A: Allocator = Global> {
        type SelfWithAlloc<U: ?Sized, B: Allocator>;

        #[cfg(not(feature = "allocator_api"))]
        unsafe fn from_raw_in(ptr: *mut T, alloc: A) -> Self::SelfWithAlloc<T, Global>;

        fn new_uninit_in(alloc: A) -> Self::SelfWithAlloc<MaybeUninit<T>, A>;
        fn new_uninit() -> Self::SelfWithAlloc<MaybeUninit<T>, Global>;
    }

    pub trait AssumeInit<T, A: Allocator = Global>: NewUninit<MaybeUninit<T>, A> {
        unsafe fn assume_init(self) -> Self::SelfWithAlloc<T, A>;
    }

    impl<T, A: Allocator> NewUninit<T, A> for Box!(T, A) {
        type SelfWithAlloc<U: ?Sized, B: Allocator> = Box!(U, B);

        #[cfg(not(feature = "allocator_api"))]
        #[inline]
        unsafe fn from_raw_in(ptr: *mut T, _: A) -> Box!(T, Global) {
            Self::from_raw(ptr)
        }

        #[inline]
        fn new_uninit_in(alloc: A) -> Box!(MaybeUninit<T>, A) {
            cfg_if! {
                if #[cfg(feature = "new_uninit")] {
                    Self::new_uninit_in(alloc)
                } else {
                    unsafe {
                        let layout = Layout::new::<MaybeUninit<T>>();
                        match alloc.allocate(layout) {
                            Ok(ptr) => <Box!(_, _)>::from_raw_in(ptr.cast().as_ptr(), alloc),
                            Err(_) => alloc::alloc::handle_alloc_error(layout),
                        }
                    }
                }
            }
        }

        #[inline]
        fn new_uninit() -> Box!(MaybeUninit<T>) {
            cfg_if! {
                if #[cfg(feature = "new_uninit")] {
                    Self::new_uninit()
                } else {
                    <Box!(_)>::new_uninit_in(Global)
                }
            }
        }
    }

    #[cfg(not(feature = "new_uninit"))]
    cfg_if! {
        if #[cfg(feature = "allocator_api")] {
            impl<T, A: Allocator> AssumeInit<T, A> for Box!(MaybeUninit<T>, A) {
                #[inline]
                unsafe fn assume_init(self) -> Box!(T, A) {
                    let (raw, alloc) = Self::into_raw_with_allocator(self);
                    <Box!(_, _)>::from_raw_in(raw as *mut T, alloc)
                }
            }
        } else {
            impl<T> AssumeInit<T, Global> for Box!(MaybeUninit<T>) {
                #[inline]
                unsafe fn assume_init(self) -> Box!(T) {
                    let raw = Self::into_raw(self);
                    <Box!(_)>::from_raw(raw as *mut T)
                }
            }
        }
    }

    pub trait MaybeUninitSlice<T> {
        unsafe fn slice_assume_init_ref(slice: &[MaybeUninit<T>]) -> &[T];
    }

    #[cfg(not(feature = "maybe_uninit_slice"))]
    impl<T> MaybeUninitSlice<T> for MaybeUninit<T> {
        unsafe fn slice_assume_init_ref(slice: &[MaybeUninit<T>]) -> &[T] {
            &*(slice as *const [MaybeUninit<T>] as *const [T])
        }
    }

    pub trait SliceIndex<T: ?Sized>: core::slice::SliceIndex<T> {
        unsafe fn get_unchecked(self, slice: *const T) -> *const Self::Output;
        unsafe fn get_unchecked_mut(self, slice: *mut T) -> *mut Self::Output;
    }

    impl<T> SliceIndex<[T]> for usize {
        unsafe fn get_unchecked(self, slice: *const [T]) -> *const T {
            slice.as_ptr().add(self)
        }
        unsafe fn get_unchecked_mut(self, slice: *mut [T]) -> *mut T {
            slice.as_mut_ptr().add(self)
        }
    }

    #[allow(clippy::wrong_self_convention)]
    pub trait SlicePtrGet {
        type Item;
        fn as_ptr(self) -> *const Self::Item;
        unsafe fn get_unchecked<I>(self, index: I) -> *const I::Output
        where
            I: SliceIndex<[Self::Item]>;
    }

    #[allow(clippy::wrong_self_convention)]
    pub trait SlicePtrGetMut: SlicePtrGet {
        fn as_mut_ptr(self) -> *mut Self::Item;
        unsafe fn get_unchecked_mut<I>(self, index: I) -> *mut I::Output
        where
            I: SliceIndex<[Self::Item]>;
    }

    #[cfg(not(feature = "slice_ptr_get"))]
    impl<T> SlicePtrGet for *const [T] {
        type Item = T;
        fn as_ptr(self) -> *const T {
            self as *const T
        }
        unsafe fn get_unchecked<I>(self, index: I) -> *const I::Output
        where
            I: SliceIndex<[T]>,
        {
            index.get_unchecked(self)
        }
    }

    #[cfg(not(feature = "slice_ptr_get"))]
    impl<T> SlicePtrGet for *mut [T] {
        type Item = T;
        fn as_ptr(self) -> *const T {
            self as *const T
        }
        unsafe fn get_unchecked<I>(self, index: I) -> *const I::Output
        where
            I: SliceIndex<[T]>,
        {
            index.get_unchecked(self)
        }
    }

    #[cfg(not(feature = "slice_ptr_get"))]
    impl<T> SlicePtrGetMut for *mut [T] {
        fn as_mut_ptr(self) -> *mut T {
            self as *mut T
        }
        unsafe fn get_unchecked_mut<I>(self, index: I) -> *mut I::Output
        where
            I: SliceIndex<[T]>,
        {
            index.get_unchecked_mut(self)
        }
    }
}

pub use definitions::{
    intrinsics, Allocator, AssumeInit as _, Global, Hasher as _, MaybeUninitSlice as _,
    NewUninit as _, SlicePtrGet as _, SlicePtrGetMut as _,
};
