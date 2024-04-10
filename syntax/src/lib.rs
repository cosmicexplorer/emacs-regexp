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

//! ???

pub mod ast;
pub mod parser;

pub mod encoding {
  use core::hash::Hash;

  trait LiteralRequirements = Eq+Ord+Clone+Hash;

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
pub mod pattern {}

pub mod hir {
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum EscapeKind {
    /// A backslash escape applied to what would otherwise be interpreted as
    /// a regex meta-character, e.g. `\*` or `\[`.
    Meta,
    /// A backslash escape applied to a character which has no special
    /// interpretation and is therefore equivalent to the unescaped
    /// character, e.g. `\%` or `\/`.
    Superfluous,
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn literal() {
    let s = "asdf";
    assert_eq!(s, "asdf");
  }
}
