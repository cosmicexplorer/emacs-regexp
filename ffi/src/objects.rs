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
  mem,
  pin::Pin,
  ptr::NonNull,
  slice,
};

use crate::alloc_types::*;

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

impl Pattern {
  #[inline]
  pub unsafe fn as_pattern<'n>(&'n self) -> emacs_regexp::Pattern<'n> {
    let Self { data } = self;
    emacs_regexp::Pattern::new(data.data())
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
    libc::free(p.cast().as_ptr());
  }

  pub const LIBC_ALLOC: Self = Self::new(None, Self::libc_alloc, Self::libc_free);
}

unsafe impl Allocator for CallbackAllocator {
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    let p =
      unsafe { self.alloc.unwrap()(self.ctx, layout.pad_to_align().size()) }.ok_or(AllocError)?;
    Ok(NonNull::slice_from_raw_parts(p.cast(), layout.size()))
  }

  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
    self.free.unwrap()(self.ctx, ptr.cast());
  }
}

#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub(crate) struct SharedAllocator(pub *const CallbackAllocator);
static_assertions::assert_eq_size!(usize, SharedAllocator);

impl SharedAllocator {
  pub fn from_alloc(
    alloc: CallbackAllocator,
  ) -> (Self, NonNull<CallbackAllocator>, CallbackAllocator) {
    let boxed_alloc: Box<CallbackAllocator, CallbackAllocator> = Box::new_in(alloc, alloc);
    let (boxed_alloc, alloc) = Box::into_raw_with_allocator(boxed_alloc);
    let boxed_alloc: NonNull<CallbackAllocator> = unsafe { NonNull::new_unchecked(boxed_alloc) };
    (
      Self(unsafe { mem::transmute(boxed_alloc) }),
      boxed_alloc,
      alloc,
    )
  }
}

unsafe impl Allocator for SharedAllocator {
  #[inline(always)]
  fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
    unsafe { &*self.0 }.allocate(layout)
  }
  #[inline(always)]
  unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
    (&*self.0).deallocate(ptr, layout)
  }
}

#[derive(Debug, Copy, Clone)]
#[repr(C)]
pub struct Matcher {
  inner: NonNull<c_void>,
  alloc: CallbackAllocator,
  boxed_alloc: NonNull<CallbackAllocator>,
}

impl Matcher {
  #[inline]
  pub(crate) fn from_matcher(
    m: emacs_regexp::Matcher<CallbackAllocator, SharedAllocator>,
    alloc: CallbackAllocator,
    boxed_alloc: NonNull<CallbackAllocator>,
  ) -> Self {
    let m = Box::new_in(m, alloc);
    let (m, m_alloc) = Box::into_raw_with_allocator(m);
    let m: NonNull<c_void> = unsafe { NonNull::new_unchecked(m) }.cast();
    Self {
      inner: m,
      alloc: m_alloc,
      boxed_alloc,
    }
  }

  #[inline(always)]
  pub(crate) fn as_matcher(&self) -> &emacs_regexp::Matcher<CallbackAllocator, SharedAllocator> {
    let inner: *mut emacs_regexp::Matcher<CallbackAllocator, SharedAllocator> =
      self.inner.cast().as_ptr();
    unsafe { &*inner }
  }

  /// # Safety:
  /// The pinned box output must be dropped **AFTER** the boxed `Matcher`! This
  /// is because [`SharedAllocator`] is WILDLY unsafe and simply keeps track of
  /// a single pointer!
  pub(crate) unsafe fn into_boxed(
    self,
  ) -> (
    Box<emacs_regexp::Matcher<CallbackAllocator, SharedAllocator>, CallbackAllocator>,
    Pin<Box<CallbackAllocator, CallbackAllocator>>,
  ) {
    let Self {
      inner,
      alloc,
      boxed_alloc,
    } = self;
    let inner: *mut emacs_regexp::Matcher<CallbackAllocator, SharedAllocator> =
      inner.cast().as_ptr();
    let inner = Box::from_raw_in(inner, alloc);
    let shared_alloc = Box::into_pin(Box::from_raw_in(mem::transmute(boxed_alloc), alloc));
    (inner, shared_alloc)
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub struct Input {
  pub data: ForeignSlice,
}

impl Input {
  #[inline]
  pub unsafe fn as_input<'h>(&'h self) -> emacs_regexp::Input<'h> {
    let Self { data } = self;
    emacs_regexp::Input::new(data.data())
  }
}
