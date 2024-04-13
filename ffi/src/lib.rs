/* Description: C ABI interface to expose to C code such as emacs.

Copyright (C) 2024 Danny McClanahan <dmcC2@hypnicjerk.ai>
SPDX-License-Identifier: GPL-3.0-or-later

This file is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as
published by the Free Software Foundation; either version 3 of the
License, or (at your option) any later version.

This file is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>. */

#![warn(rustdoc::missing_crate_level_docs)]
// #![warn(missing_docs)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]
#![feature(allocator_api)]
#![feature(slice_ptr_get)]
#![feature(new_uninit)]
#![feature(core_intrinsics)]
#![feature(lang_items)]
#![allow(internal_features)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! C ABI interface to expose to C code such as emacs.

extern crate alloc;

/// Necessary rust-specific hooks to override when generating an output library.
#[cfg(not(test))]
pub mod lang_items {
  use core::{
    alloc::{GlobalAlloc, Layout},
    intrinsics::abort,
    panic::PanicInfo,
  };

  use ::alloc::alloc::handle_alloc_error;

  /// Even when compiled with `panic="abort"`, we need to define this method
  /// anyway for some reason to successfully compile this `no_std` crate. If
  /// this is ever called, it should have the same behavior as `panic="abort"`.
  #[panic_handler]
  pub fn panic(_info: &PanicInfo) -> ! { abort() }

  /// This method is called to perform stack unwinding, especially across
  /// language runtimes, and must be defined for our `librex.so` to link
  /// correctly. While we might like to be able to make use of rust's structured
  /// panic control flow features in this library, it would require a lot of
  /// work to make that portable, so instead we simply ignore/avoid any stack
  /// unwinding (and this entire crate workspace is compiled with
  /// `panic="abort"`).
  #[lang = "eh_personality"]
  pub fn rust_eh_personality() {}

  /// Empty struct to do nothing and immediately error. See [`ALLOCATOR`].
  pub struct ImmediatelyErrorAllocator;

  unsafe impl GlobalAlloc for ImmediatelyErrorAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { handle_alloc_error(layout) }
    unsafe fn dealloc(&self, _ptr: *mut u8, layout: Layout) { handle_alloc_error(layout) }
  }

  /// We need to provide a `#[global_allocator]` in order to produce a `no_std`
  /// binary, but we don't actually want to ever allocate dynamically in this
  /// crate without using an explicitly provided implementation of
  /// [`core::alloc::Allocator`]. So we provide this implementation which
  /// immediately panics at runtime if we ever attempt to use the global
  /// allocator.
  #[global_allocator]
  pub static ALLOCATOR: ImmediatelyErrorAllocator = ImmediatelyErrorAllocator;
}

pub mod objects {
  use core::{
    alloc::{AllocError, Allocator, Layout},
    ffi::c_void,
    mem::{self, MaybeUninit},
    ptr::{self, NonNull},
    slice,
  };

  use ::alloc::boxed::Box;

  #[derive(Default, Debug, Copy, Clone, PartialEq, Eq)]
  #[repr(u8)]
  pub enum RegexpError {
    #[default]
    None = 0,
    CompileError = 1,
    MatchError = 2,
  }

  impl RegexpError {
    #[inline(always)]
    pub fn wrap(f: impl FnOnce() -> Result<(), Self>) -> Self {
      match f() {
        Ok(()) => Self::None,
        Err(e) => {
          assert_ne!(
            e,
            Self::None,
            "regexp error of none was provided: this is a logic error"
          );
          e
        },
      }
    }
  }

  #[repr(C)]
  pub struct ForeignSlice {
    len: usize,
    data: *const c_void,
  }

  impl ForeignSlice {
    #[inline(always)]
    pub unsafe fn data(&self) -> &[u8] {
      let source: *const u8 = mem::transmute(self.data);
      slice::from_raw_parts(source, self.len)
    }
  }

  #[repr(C)]
  pub struct Pattern {
    pub data: ForeignSlice,
  }

  #[repr(C)]
  pub struct OwnedSlice {
    len: usize,
    data: NonNull<c_void>,
    alloc: CallbackAllocator,
  }

  impl OwnedSlice {
    #[inline(always)]
    pub fn data(&self) -> &[u8] {
      let source: *const u8 = unsafe { mem::transmute(self.data) };
      unsafe { slice::from_raw_parts(source, self.len) }
    }

    #[inline]
    pub fn from_data(data: &[u8], alloc: CallbackAllocator) -> Self {
      /* Allocate exactly enough space with the custom allocator. */
      let mut new_data: Box<[MaybeUninit<u8>], CallbackAllocator> =
        Box::new_uninit_slice_in(data.len(), alloc);

      /* Write the source data into the newly allocated region, initializing the
       * memory. */
      {
        let nd: &mut [MaybeUninit<u8>] = new_data.as_mut();
        let base: *mut u8 = unsafe { mem::transmute(nd.as_mut_ptr()) };
        unsafe {
          ptr::copy_nonoverlapping(data.as_ptr(), base, data.len());
        }
      }
      /* Get an initialized box for the newly initialized memory! */
      let new_data: Box<[u8], CallbackAllocator> = unsafe { new_data.assume_init() };

      /* Convert the box into a raw pointer so it can be FFIed. */
      let (new_data, alloc): (*mut [u8], CallbackAllocator) =
        Box::into_raw_with_allocator(new_data);

      /* Perform transmute type gymnastics to extract a c_void. */
      let new_data: *mut c_void = unsafe { mem::transmute(new_data.as_mut_ptr()) };
      let new_data: NonNull<c_void> = NonNull::new(new_data).unwrap();
      Self {
        len: data.len(),
        data: new_data,
        alloc,
      }
    }

    #[inline]
    pub fn box_data(self) -> Box<[u8], CallbackAllocator> {
      let Self { len, data, alloc } = self;
      let p: NonNull<u8> = unsafe { mem::transmute(data) };
      let p: NonNull<[u8]> = NonNull::slice_from_raw_parts(p, len);
      unsafe { Box::from_raw_in(mem::transmute(p), alloc) }
    }
  }

  #[derive(Copy, Clone)]
  #[repr(C)]
  pub struct CallbackAllocator {
    ctx: Option<NonNull<c_void>>,
    alloc: Option<unsafe extern "C" fn(Option<NonNull<c_void>>, usize) -> Option<NonNull<c_void>>>,
    free: Option<unsafe extern "C" fn(Option<NonNull<c_void>>, NonNull<c_void>) -> ()>,
  }

  unsafe impl Allocator for CallbackAllocator {
    #[inline(always)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
      assert_eq!(layout.align(), 1);
      match unsafe { self.alloc.unwrap()(self.ctx, layout.size()) } {
        None => Err(AllocError),
        Some(p) => {
          let p: NonNull<u8> = unsafe { mem::transmute(p) };
          Ok(NonNull::slice_from_raw_parts(p, layout.size()))
        },
      }
    }

    #[inline(always)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
      assert_eq!(layout.align(), 1);
      let p: NonNull<c_void> = mem::transmute(ptr);
      self.free.unwrap()(self.ctx, p);
    }
  }

  #[repr(C)]
  pub struct Matcher {
    pub data: OwnedSlice,
  }

  #[repr(C)]
  pub struct Input {
    pub data: ForeignSlice,
  }
}

pub mod methods {
  use core::{mem::MaybeUninit, ptr::addr_of_mut};

  use super::objects::{CallbackAllocator, Input, Matcher, OwnedSlice, Pattern, RegexpError};

  /// asdf
  #[no_mangle]
  pub extern "C" fn compile(
    pattern: &Pattern,
    alloc: &CallbackAllocator,
    out: &mut MaybeUninit<Matcher>,
  ) -> RegexpError {
    let alloc = *alloc;
    let out_d = unsafe { addr_of_mut!((*out.as_mut_ptr()).data) };
    RegexpError::wrap(move || {
      let p = unsafe { pattern.data.data() };

      let d = OwnedSlice::from_data(p, alloc);

      unsafe { out_d.write(d) };
      Ok(())
    })
  }

  #[no_mangle]
  pub extern "C" fn execute(
    matcher: &Matcher,
    alloc: &CallbackAllocator,
    input: &Input,
  ) -> RegexpError {
    RegexpError::wrap(|| {
      let i = unsafe { input.data.data() };
      let d = matcher.data.data();

      if i == d {
        Ok(())
      } else {
        Err(RegexpError::MatchError)
      }
    })
  }
}
