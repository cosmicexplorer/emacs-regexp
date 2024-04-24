/* Description: Support for encoding and decoding emacs multibyte strings.

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
#![feature(const_trait_impl)]
#![feature(effects)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! Support for encoding and decoding emacs multibyte strings.

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
    } else {
      pub use ::alloc::{boxed::Box, vec::Vec};
    }
  }
}
use core::alloc::Allocator;

use alloc_types::*;

#[allow(dead_code)]
const fn max_value_for_bit_width(bits: u8) -> u32 { (1u32 << (bits as u32)) - 1 }

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SingleChar(u32);
pub type Char = SingleChar;

impl SingleChar {
  pub const BITS: u8 = 22;
  pub const MAX_CHAR: u32 = 0x3FFFFF;

  #[inline(always)]
  pub const unsafe fn from_u32(x: u32) -> Self { Self(x) }

  #[inline(always)]
  pub const fn try_from_u32(x: u32) -> Result<Self, u32> {
    if x > Self::MAX_CHAR {
      Ok(unsafe { Self::from_u32(x) })
    } else {
      Err(x)
    }
  }

  pub const NULL: Self = Self(0);
}
static_assertions::const_assert_eq!(
  SingleChar::MAX_CHAR,
  max_value_for_bit_width(SingleChar::BITS)
);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PackedString<'a>(&'a [u8]);
static_assertions::assert_eq_size!(PackedString<'static>, &'static [u8]);
static_assertions::assert_eq_size!(PackedString<'static>, (usize, usize));
pub type Str<'a> = PackedString<'a>;

impl<'a> PackedString<'a> {
  #[inline(always)]
  pub const unsafe fn from_bytes(bytes: &'a [u8]) -> Self { Self(bytes) }

  pub fn try_from_bytes(bytes: &'a [u8]) -> Self { todo!() }

  pub fn iter_chars(&self) -> impl Iterator<Item=SingleChar> {
    todo!();
    #[allow(unreachable_code)]
    [].iter().copied()
  }
}

#[derive(Clone)]
#[repr(transparent)]
pub struct OwnedString<A: Allocator>(Box<[u8], A>);
pub type String<A> = OwnedString<A>;

impl<A> OwnedString<A>
where A: Allocator
{
  pub fn coalesce_chars(unpacked: &[SingleChar], alloc: A) -> Self { todo!() }

  #[inline(always)]
  pub const fn as_str(&self) -> PackedString {
    unsafe { PackedString::from_bytes(self.0.as_ref()) }
  }
}

#[cfg(test)]
mod test {
  #[test]
  fn ok() {
    assert!(true);
  }
}
