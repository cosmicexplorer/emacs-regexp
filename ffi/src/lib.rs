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
#![feature(core_intrinsics)]
#![feature(lang_items)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! C ABI interface to expose to C code such as emacs.

extern crate alloc;

use core::{
  alloc::{AllocError, Allocator, GlobalAlloc, Layout},
  ffi::c_void,
  intrinsics::abort,
  mem::{self, MaybeUninit},
  panic::PanicInfo,
  ptr::{addr_of_mut, NonNull},
  slice,
};

use ::alloc::{boxed::Box, vec::Vec};
use num_enum::{IntoPrimitive, TryFromPrimitive};

#[panic_handler]
fn panic(info: &PanicInfo) -> ! { abort() }

#[lang = "eh_personality"]
fn rust_eh_personality() {}

#[derive(Default, Copy, Clone, IntoPrimitive, TryFromPrimitive, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum RegexpError {
  #[default]
  None = 0,
  CompileError = 1,
  MatchError = 2,
}

#[repr(C)]
pub struct ForeignSlice {
  len: usize,
  data: *const c_void,
}

impl ForeignSlice {
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
  data: *mut c_void,
  alloc: CallbackAllocator,
}

impl OwnedSlice {
  pub fn data(&self) -> &[u8] {
    let source: *const u8 = unsafe { mem::transmute(self.data) };
    unsafe { slice::from_raw_parts(source, self.len) }
  }

  pub fn box_data(self) -> Box<[u8], CallbackAllocator> {
    let Self { len, data, alloc } = self;
    let p = NonNull::new(data).unwrap();
    let p: NonNull<u8> = unsafe { mem::transmute(p) };
    let p = unsafe { NonNull::slice_from_raw_parts(p, len) };
    unsafe { Box::from_raw_in(mem::transmute(p), alloc) }
  }
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct CallbackAllocator {
  alloc: Option<fn(usize) -> Option<NonNull<c_void>>>,
  free: Option<fn(NonNull<c_void>) -> ()>,
}

unsafe impl Allocator for CallbackAllocator {
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    assert_eq!(layout.align(), 1);
    match self.alloc.unwrap()(layout.size()) {
      None => Err(AllocError),
      Some(p) => {
        let p: NonNull<u8> = unsafe { mem::transmute(p) };
        Ok(unsafe { NonNull::slice_from_raw_parts(p, layout.size()) })
      },
    }
  }

  unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
    let p: NonNull<c_void> = unsafe { mem::transmute(ptr) };
    self.free.unwrap()(p);
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

struct NoOpAllocator;

unsafe impl GlobalAlloc for NoOpAllocator {
  unsafe fn alloc(&self, layout: Layout) -> *mut u8 { ::alloc::alloc::handle_alloc_error(layout) }
  unsafe fn dealloc(&self, _ptr: *mut u8, layout: Layout) {
    ::alloc::alloc::handle_alloc_error(layout)
  }
}

#[global_allocator]
static ALLOCATOR: NoOpAllocator = NoOpAllocator;

/// asdf
#[no_mangle]
pub extern "C" fn compile(
  pattern: &Pattern,
  alloc: &CallbackAllocator,
  out: &mut MaybeUninit<Matcher>,
) -> RegexpError {
  let p = unsafe { pattern.data.data() };

  let mut d: Vec<u8, CallbackAllocator> = Vec::with_capacity_in(p.len(), *alloc);
  d.extend_from_slice(p);
  let d = d.into_boxed_slice();
  let (d, alloc) = Box::into_raw_with_allocator(d);
  let d = OwnedSlice {
    len: p.len(),
    data: unsafe { mem::transmute(d.as_mut_ptr()) },
    alloc,
  };

  let out_d = unsafe { addr_of_mut!((*out.as_mut_ptr()).data) };
  unsafe { out_d.write(d) };

  RegexpError::None
}

#[no_mangle]
pub extern "C" fn execute(
  matcher: &Matcher,
  alloc: &CallbackAllocator,
  input: &Input,
) -> RegexpError {
  let i = unsafe { input.data.data() };
  let d = matcher.data.data();

  if i == d {
    RegexpError::None
  } else {
    RegexpError::MatchError
  }
}
