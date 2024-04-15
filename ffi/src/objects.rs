/* Description: FFI structs used to communicate over the C ABI.

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

//! FFI structs used to communicate over the C ABI.

use core::{
  alloc::{AllocError, Allocator, Layout},
  ffi::c_void,
  mem::{self, MaybeUninit},
  ptr::{self, NonNull},
  slice,
};

#[cfg(not(test))]
use ::alloc::boxed::Box;
use emacs_regexp::syntax::{ast::expr::Expr, encoding::ByteEncoding};

use crate::methods::BoxAllocator;

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq)]
#[must_use]
#[repr(u8)]
pub enum RegexpError {
  #[default]
  None = 0,
  ParseError = 1,
  CompileError = 2,
  MatchError = 3,
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

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(C)]
pub struct ForeignSlice {
  len: usize,
  data: *const c_void,
}

impl ForeignSlice {
  #[inline(always)]
  pub unsafe fn data(&self) -> &[u8] { slice::from_raw_parts(self.data.cast(), self.len) }

  #[cfg(test)]
  #[inline]
  pub fn from_data(data: &[u8]) -> Self {
    Self {
      len: data.len(),
      data: data.as_ptr().cast(),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub struct Pattern {
  pub data: ForeignSlice,
}

#[derive(Debug)]
#[repr(C)]
pub struct OwnedSlice {
  len: usize,
  data: NonNull<c_void>,
  alloc: CallbackAllocator,
}

impl OwnedSlice {
  #[inline(always)]
  pub fn data(&self) -> &[u8] {
    unsafe { slice::from_raw_parts(self.data.cast().as_ptr(), self.len) }
  }

  #[inline]
  pub fn from_data(data: &[u8], alloc: CallbackAllocator) -> Self {
    /* Initialize the allocation from the source data. */
    let new_data: Box<[u8], CallbackAllocator> = {
      /* Allocate exactly enough space with the custom allocator. */
      let mut new_data: Box<[MaybeUninit<u8>], CallbackAllocator> =
        Box::new_uninit_slice_in(data.len(), alloc);
      /* Copy from the source data. */
      MaybeUninit::copy_from_slice(new_data.as_mut(), data);
      /* The data is now initialized. */
      unsafe { new_data.assume_init() }
    };

    /* Convert the box into a raw pointer so it can be FFIed. */
    let (new_data, alloc): (*mut [u8], CallbackAllocator) = Box::into_raw_with_allocator(new_data);

    Self {
      len: data.len(),
      data: NonNull::new(new_data.as_mut_ptr()).unwrap().cast(),
      alloc,
    }
  }

  #[inline]
  pub fn into_box(self) -> Box<[u8], CallbackAllocator> {
    let Self { len, data, alloc } = self;
    let p: NonNull<[u8]> = NonNull::slice_from_raw_parts(data.cast(), len);
    unsafe { Box::from_raw_in(p.as_ptr(), alloc) }
  }
}

#[derive(Debug)]
#[repr(C)]
pub struct OwnedExpr {
  data: NonNull<c_void>,
  alloc: CallbackAllocator,
}

impl OwnedExpr {
  #[inline(always)]
  pub fn expr(&self) -> &Expr<ByteEncoding, BoxAllocator> {
    let p: *mut Expr<ByteEncoding, BoxAllocator> = self.data.cast().as_ptr();
    unsafe { &*p }
  }

  #[inline]
  pub fn from_expr(data: Expr<ByteEncoding, BoxAllocator>, alloc: CallbackAllocator) -> Self {
    /* Box the expr onto the heap. */
    let boxed: Box<Expr<ByteEncoding, BoxAllocator>, CallbackAllocator> = Box::new_in(data, alloc);
    /* Convert the box into a raw pointer so it can be FFIed. */
    let (box_data, alloc): (*mut Expr<ByteEncoding, BoxAllocator>, CallbackAllocator) =
      Box::into_raw_with_allocator(boxed);
    Self {
      data: NonNull::new(box_data).unwrap().cast(),
      alloc,
    }
  }

  #[inline]
  pub fn into_box(self) -> Box<Expr<ByteEncoding, BoxAllocator>, CallbackAllocator> {
    let Self { data, alloc } = self;
    let p: *mut Expr<ByteEncoding, BoxAllocator> = data.cast().as_ptr();
    unsafe { Box::from_raw_in(p, alloc) }
  }
}

#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct CallbackAllocator {
  ctx: Option<NonNull<c_void>>,
  alloc: Option<unsafe extern "C" fn(Option<NonNull<c_void>>, usize) -> Option<NonNull<c_void>>>,
  free: Option<unsafe extern "C" fn(Option<NonNull<c_void>>, NonNull<c_void>) -> ()>,
}

#[cfg(test)]
impl CallbackAllocator {
  #[inline]
  pub const fn new(
    ctx: Option<NonNull<c_void>>,
    alloc: unsafe extern "C" fn(Option<NonNull<c_void>>, usize) -> Option<NonNull<c_void>>,
    free: unsafe extern "C" fn(Option<NonNull<c_void>>, NonNull<c_void>) -> (),
  ) -> Self {
    Self {
      ctx,
      alloc: Some(alloc),
      free: Some(free),
    }
  }

  pub unsafe extern "C" fn libc_alloc(
    ctx: Option<NonNull<c_void>>,
    len: usize,
  ) -> Option<NonNull<c_void>> {
    assert!(ctx.is_none());
    assert!(len > 0);
    NonNull::new(libc::malloc(len))
  }

  pub unsafe extern "C" fn libc_free(ctx: Option<NonNull<c_void>>, p: NonNull<c_void>) {
    assert!(ctx.is_none());
    libc::free(mem::transmute(p));
  }

  pub const LIBC_ALLOC: Self = Self::new(None, Self::libc_alloc, Self::libc_free);
}

unsafe impl Allocator for CallbackAllocator {
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    let n = layout.pad_to_align().size();
    match unsafe { self.alloc.unwrap()(self.ctx, n) } {
      None => Err(AllocError),
      Some(p) => Ok(NonNull::slice_from_raw_parts(
        unsafe { mem::transmute(p) },
        n,
      )),
    }
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
    let p: NonNull<c_void> = mem::transmute(ptr);
    self.free.unwrap()(self.ctx, p);
  }
}

#[derive(Debug)]
#[repr(C)]
pub struct Matcher {
  pub data: OwnedSlice,
  pub expr: OwnedExpr,
}

impl Matcher {
  /// Get the offsets for each field within the allocated output space.
  #[inline]
  pub fn destructure_output_fields(
    out: &mut MaybeUninit<Self>,
  ) -> (&mut MaybeUninit<OwnedSlice>, &mut MaybeUninit<OwnedExpr>) {
    let o = out.as_mut_ptr();
    unsafe {
      let d: *mut OwnedSlice = ptr::addr_of_mut!((*o).data);
      let e: *mut OwnedExpr = ptr::addr_of_mut!((*o).expr);
      (
        d.as_uninit_mut().unwrap_unchecked(),
        e.as_uninit_mut().unwrap_unchecked(),
      )
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub struct Input {
  pub data: ForeignSlice,
}
