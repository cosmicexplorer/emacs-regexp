/* Description: ???

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
#![deny(unsafe_code)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]
#![feature(allocator_api)]
#![feature(trait_alias)]
#![feature(error_in_core)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! ???

#[cfg(not(test))]
extern crate alloc;

mod alloc_types {
  /* no_std/no_main is enabled except for test environments, so we need to use
   * the special imports from the extern alloc crate. */
  cfg_if::cfg_if! {
    if #[cfg(test)] {
      pub use Box;
      pub use Vec;
    } else {
      pub use ::alloc::{boxed::Box, vec::Vec};
    }
  }
}

pub mod ast;
pub mod parser;

pub mod encoding {
  use core::hash::Hash;

  pub trait LiteralRequirements = Eq+Ord+Clone+Hash;

  pub trait LiteralEncoding {
    type Single: LiteralRequirements+Copy;
    type String<'n>: LiteralRequirements+Copy;
  }

  pub struct ByteEncoding;
  impl LiteralEncoding for ByteEncoding {
    type Single = u8;
    type String<'n> = &'n [u8];
  }

  pub struct UnicodeEncoding;
  impl LiteralEncoding for UnicodeEncoding {
    type Single = char;
    type String<'n> = &'n str;
  }

  pub struct MultibyteEncoding;
  impl LiteralEncoding for MultibyteEncoding {
    /// emacs uses a 22 bit char encoding!
    type Single = u32;
    /// However, this is stored in a compressed representation, which may use a
    /// varying number of bits.
    type String<'n> = &'n [u8];
  }
}

/// stuff to do with the input string provided as the "pattern"
pub mod pattern {
  /* TODO: ??? */
}
