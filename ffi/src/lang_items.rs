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
