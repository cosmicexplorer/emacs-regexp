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
#![feature(ptr_as_uninit)]
#![feature(panic_info_message)]
#![feature(non_null_convenience)]
#![feature(alloc_layout_extra)]
#![feature(fmt_internals)]
#![feature(core_intrinsics)]
#![feature(lang_items)]
#![allow(internal_features)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! C ABI interface to expose to C code such as emacs.

extern crate alloc;

/// cbindgen:ignore
#[cfg(not(test))]
pub mod lang_items;

pub mod methods;
pub mod objects;

#[cfg(feature = "libc")]
pub mod libc_backend {
  use core::{
    alloc::{AllocError, Allocator, Layout},
    ffi::c_void,
    fmt::{self, Write as _},
    mem, ops,
    panic::PanicInfo,
    ptr::NonNull,
    slice,
  };

  #[derive(Debug, Copy, Clone, Default)]
  pub struct LibcAllocator;

  impl LibcAllocator {
    #[inline(always)]
    fn do_alloc<F: FnOnce(usize) -> *mut c_void>(
      layout: Layout,
      f: F,
    ) -> Result<NonNull<[u8]>, AllocError> {
      if layout.size() == 0 {
        return Ok(NonNull::slice_from_raw_parts(layout.dangling(), 0));
      }
      let alignment_padding = layout.padding_needed_for(layout.align());
      let p: NonNull<c_void> =
        NonNull::new(f(layout.size() + alignment_padding)).ok_or(AllocError)?;
      let p: NonNull<u8> = unsafe { p.byte_add(alignment_padding) }.cast();
      let p: NonNull<[u8]> = NonNull::slice_from_raw_parts(p, layout.size());
      Ok(p)
    }
  }

  unsafe impl Allocator for LibcAllocator {
    #[inline(always)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
      Self::do_alloc(layout, |n| unsafe { libc::malloc(n) })
    }

    #[inline(always)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
      if layout.size() == 0 {
        return;
      }
      libc::free(ptr.cast().as_ptr());
    }

    #[inline(always)]
    fn allocate_zeroed(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
      Self::do_alloc(layout, |n| unsafe { libc::calloc(n, mem::size_of::<u8>()) })
    }

    #[inline(always)]
    unsafe fn grow(
      &self,
      ptr: NonNull<u8>,
      old: Layout,
      new: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
      if old.size() == 0 {
        Self::do_alloc(new, |n| libc::malloc(n))
      } else {
        Self::do_alloc(new, |n| libc::realloc(ptr.cast().as_ptr(), n))
      }
    }

    #[inline(always)]
    unsafe fn grow_zeroed(
      &self,
      ptr: NonNull<u8>,
      old: Layout,
      new: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
      if old.size() == 0 {
        return Self::do_alloc(new, |n| libc::calloc(n, mem::size_of::<u8>()));
      }

      let ret: NonNull<[u8]> = Self::do_alloc(new, |n| libc::realloc(ptr.cast().as_ptr(), n))?;

      /* Set the new bytes to zero. */
      let uninitialized_base_address: *mut c_void =
        ret.as_non_null_ptr().byte_add(old.size()).cast().as_ptr();
      debug_assert!(new.size() >= old.size());
      let num_added_bytes = new.size() - old.size();
      libc::explicit_bzero(uninitialized_base_address, num_added_bytes);

      Ok(ret)
    }

    #[inline(always)]
    unsafe fn shrink(
      &self,
      ptr: NonNull<u8>,
      old: Layout,
      new: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
      if old.size() == 0 {
        assert_eq!(new.size(), 0);
        return Ok(NonNull::slice_from_raw_parts(ptr, 0));
      }
      if new.size() == 0 {
        libc::free(ptr.cast().as_ptr());
        return Ok(NonNull::slice_from_raw_parts(new.dangling(), 0));
      }
      Self::do_alloc(new, |n| libc::realloc(ptr.cast().as_ptr(), n))
    }
  }

  /// Mutable writable object that impls [`fmt::Write`].
  struct CallocWriter {
    src: NonNull<u8>,
    len: usize,
    used: usize,
  }

  impl CallocWriter {
    /// Call [`libc::calloc()`] to allocate some zeroed memory.
    pub fn calloc_for_len(len: usize) -> Option<Self> {
      let p: *mut u8 = unsafe { mem::transmute(libc::calloc(len, mem::size_of::<u8>())) };
      Some(Self {
        src: NonNull::new(p)?,
        len,
        used: 0,
      })
    }

    fn remaining(&self) -> usize { self.len - self.used }

    fn slice(&mut self) -> &mut [u8] {
      let rem = self.remaining();
      let shifted = unsafe { self.src.add(self.used) };
      unsafe { slice::from_raw_parts_mut(mem::transmute(shifted), rem) }
    }

    fn data(&self) -> &[u8] {
      unsafe { slice::from_raw_parts(mem::transmute(self.src), self.used) }
    }
  }

  impl ops::Drop for CallocWriter {
    fn drop(&mut self) {
      unsafe {
        libc::free(mem::transmute(self.src));
      }
    }
  }

  impl fmt::Write for CallocWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
      let s = s.as_bytes();
      let rem = self.slice();
      if s.len() > rem.len() {
        rem.copy_from_slice(&s[..rem.len()]);
        self.used += rem.len();
        Err(fmt::Error)
      } else {
        rem[..s.len()].copy_from_slice(s);
        self.used += s.len();
        Ok(())
      }
    }
  }

  fn abort_after_writing(s: &[u8]) -> ! {
    unsafe {
      /* In case the first time returns without blocking, try again (do not try
       * again upon error or success). */
      while libc::write(libc::STDERR_FILENO, mem::transmute(s.as_ptr()), s.len()) == 0 {}
      libc::abort()
    }
  }

  pub fn do_panic(info: &PanicInfo) -> ! {
    const MSG_ALLOC_LEN: usize = 4096;
    let mut w = match CallocWriter::calloc_for_len(MSG_ALLOC_LEN) {
      Some(w) => w,
      None => {
        let s = "could not allocate any memory!\n".as_bytes();
        abort_after_writing(s)
      },
    };

    if let Some(loc) = info.location() {
      let mut f = fmt::Formatter::new(&mut w);
      let _ = fmt::Display::fmt(loc, &mut f);
      let _ = w.write_str(": ");
    } else {
      let _ = w.write_str("<location unknown>: ");
    }

    if let Some(args) = info.message() {
      let _ = fmt::write(&mut w, *args);
    } else {
      let payload = info
        .payload()
        .downcast_ref::<&str>()
        .map(|s| *s)
        .unwrap_or("<could not parse panic payload>");
      let _ = w.write_str(payload);
    }
    let _ = w.write_char('\n');

    let s = w.data();
    abort_after_writing(s)
  }
}
