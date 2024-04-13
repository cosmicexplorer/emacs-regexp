/* Description: Necessary rust-specific hooks to override when generating an output library.

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

//! Necessary rust-specific hooks to override when generating an output library.

use core::{
  alloc::{GlobalAlloc, Layout},
  panic::PanicInfo,
};

use ::alloc::alloc::handle_alloc_error;
use cfg_if::cfg_if;

#[cfg(feature = "libc")]
mod libc_backend {
  use core::{
    fmt::{self, Write as _},
    mem, ops,
    ptr::NonNull,
    slice,
  };

  use super::PanicInfo;

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

cfg_if! {
  if #[cfg(feature = "libc")] {
    #[panic_handler]
    pub fn panic(info: &PanicInfo) -> ! { libc_backend::do_panic(info) }
  } else {
    #[panic_handler]
    pub fn panic(_info: &PanicInfo) -> ! { core::intrinsics::abort() }
  }
}

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
