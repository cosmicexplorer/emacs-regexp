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
#![feature(maybe_uninit_write_slice)]
#![feature(let_chains)]
#![feature(core_intrinsics)]
#![feature(lang_items)]
#![allow(internal_features)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! C ABI interface to expose to C code such as emacs.

#[cfg(not(test))]
extern crate alloc;

#[allow(unused_imports)]
mod alloc_types {
  /* no_std/no_main is enabled except for test environments, so we need to use
   * the special imports from the extern alloc crate. */
  cfg_if::cfg_if! {
    if #[cfg(test)] {
      pub use Box;
      pub use Vec;
      pub use std::sync::Arc;
    } else {
      pub use ::alloc::{boxed::Box, vec::Vec, sync::Arc};
    }
  }
}

/// cbindgen:ignore
#[cfg(not(test))]
pub mod lang_items;

pub mod methods;
pub mod objects;

/// cbindgen:ignore
#[cfg(feature = "libc")]
pub(crate) mod libc_backend;

/// cbindgen:ignore
pub(crate) use emacs_regexp::util;
