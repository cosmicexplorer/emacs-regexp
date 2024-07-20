/* Description: libc-specific implementation methods.

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

//! [`libc`]-specific implementation methods.

use core::{
  alloc::{AllocError, Allocator, Layout},
  ffi::c_void,
  fmt::Write as _,
  mem,
  panic::PanicInfo,
  ptr::NonNull,
};

#[derive(Debug, Copy, Clone, Default)]
pub struct LibcAllocator;
static_assertions::const_assert_eq!(0, mem::size_of::<LibcAllocator>());

impl LibcAllocator {
  #[inline(always)]
  fn do_alloc<F: FnOnce(usize) -> *mut c_void>(
    layout: Layout,
    f: F,
  ) -> Result<NonNull<[u8]>, AllocError> {
    if layout.size() == 0 {
      return Ok(NonNull::slice_from_raw_parts(layout.dangling(), 0));
    }
    let p: NonNull<c_void> = NonNull::new(f(layout.pad_to_align().size())).ok_or(AllocError)?;
    let p: NonNull<[u8]> = NonNull::slice_from_raw_parts(p.cast(), layout.size());
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

fn abort_after_writing(mut s: &[u8]) -> ! {
  loop {
    if s.is_empty() {
      /* We are done, now abort. */
      unsafe {
        libc::abort();
      }
    }
    match unsafe { libc::write(libc::STDERR_FILENO, s.as_ptr().cast(), s.len()) } {
      /* Abort immediately upon error. */
      rc if rc < 0 => unsafe { libc::abort() },
      rc => {
        /* Shift the input and try again. */
        s = &s[(rc as usize)..];
      },
    }
  }
}

#[cfg_attr(test, allow(dead_code))]
pub fn do_panic(info: &PanicInfo) -> ! {
  let mut w = crate::util::Writer::<LibcAllocator>::with_initial_capacity(4096);

  if let Some(loc) = info.location()
    && let Ok(loc) = crate::util::Writer::<LibcAllocator>::display(loc)
  {
    let _ = w.write_str(&loc);
    let _ = w.write_str(": ");
  } else {
    let _ = w.write_str("<location unknown>: ");
  }

  let _ = write!(&mut w, "panicked: {}", info.message());
  /* if let Some(args) = info.message() { */
  /* let _ = fmt::write(&mut w, *args); */
  /* } else { */
  /* let payload = info */
  /* .payload() */
  /* .downcast_ref::<&str>() */
  /* .map(|s| *s) */
  /* .unwrap_or("<could not parse panic payload>"); */
  /* let _ = w.write_str(payload); */
  /* } */
  let _ = w.write_char('\n');

  abort_after_writing(w.data())
}
