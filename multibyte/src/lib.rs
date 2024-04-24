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
#![feature(const_mut_refs)]
#![feature(const_maybe_uninit_write)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! Support for encoding and decoding emacs multibyte strings.

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
use alloc_types::*;

#[cfg(not(test))]
extern crate alloc;

use core::{alloc::Allocator, mem::MaybeUninit, num::NonZeroUsize};


#[allow(dead_code)]
const fn max_value_for_bit_width_32(bits: u8) -> u32 { max_value_for_bit_width_64(bits) as u32 }
const fn max_value_for_bit_width_64(bits: u8) -> u64 { (1u64 << (bits as u64)) - 1 }

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SingleChar(u32);
pub type Char = SingleChar;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ValueClass {
  One,
  Two,
  Three,
  Four,
  Five,
  /// TODO: This becomes 2 for some reason.
  PastFive,
}

impl ValueClass {
  #[inline(always)]
  pub const fn byte_width(&self) -> NonZeroUsize {
    match self {
      Self::One => SingleChar::NZ_1,
      Self::Two => SingleChar::NZ_2,
      Self::Three => SingleChar::NZ_3,
      Self::Four => SingleChar::NZ_4,
      Self::Five => SingleChar::NZ_5,
      Self::PastFive => SingleChar::NZ_2,
    }
  }
}

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

  #[inline(always)]
  pub const fn as_u32(&self) -> u32 {
    let Self(ref c) = self;
    *c
  }

  const MAX_UNICODE_CHAR: u32 = 0x10FFFF;

  const MAX_1_BYTE_CHAR: u32 = 0x7F;
  const MAX_2_BYTE_CHAR: u32 = 0x7FF;
  const MAX_3_BYTE_CHAR: u32 = 0xFFFF;
  const MAX_4_BYTE_CHAR: u32 = 0x1FFFFF;
  const MAX_5_BYTE_CHAR: u32 = 0x3FFF7F;

  #[inline(always)]
  pub const fn calculate_value_class(&self) -> ValueClass {
    let c = self.as_u32();
    debug_assert!(c <= Self::MAX_CHAR);
    if c <= Self::MAX_1_BYTE_CHAR {
      return ValueClass::One;
    }
    if c <= Self::MAX_2_BYTE_CHAR {
      return ValueClass::Two;
    }
    if c > Self::MAX_5_BYTE_CHAR {
      /* FIXME: why do this??? this is from CHAR_BYTES() in src/character.h, but
       * it's not clear why? */
      return ValueClass::PastFive;
    }
    if c > Self::MAX_4_BYTE_CHAR {
      return ValueClass::Five;
    }
    if c > Self::MAX_3_BYTE_CHAR {
      return ValueClass::Four;
    }
    debug_assert!(c > Self::MAX_2_BYTE_CHAR);
    ValueClass::Three
  }

  #[inline(always)]
  const fn assume_byte(x: u32) -> u8 {
    debug_assert!(x <= u8::MAX as u32);
    x as u8
  }

  #[inline(always)]
  const fn past_five_char_to_byte8(x: u32) -> u32 {
    debug_assert!(x > Self::MAX_5_BYTE_CHAR);
    x - 0x3FFF00
  }

  #[inline(always)]
  pub const fn calculate_leading_code(&self) -> u8 {
    let c = self.as_u32();
    let ret: u32 = match self.calculate_value_class() {
      ValueClass::One => c,
      ValueClass::Two => 0xC0 | (c >> 6),
      ValueClass::Three => 0xE0 | (c >> 12),
      ValueClass::Four => 0xF0 | (c >> 18),
      ValueClass::Five => 0xF8,
      ValueClass::PastFive => 0xC0 | ((Self::past_five_char_to_byte8(c) >> 6) & 0x01),
    };
    Self::assume_byte(ret)
  }

  const MAX_MULTIBYTE_LENGTH: usize = 5;

  const NZ_1: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(1) };
  const NZ_2: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(2) };
  const NZ_3: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(3) };
  const NZ_4: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(4) };
  const NZ_5: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(5) };

  pub const fn write_bytes(
    &self,
    out: &mut [MaybeUninit<u8>; Self::MAX_MULTIBYTE_LENGTH],
  ) -> NonZeroUsize {
    let c = self.as_u32();

    out[0].write(self.calculate_leading_code());

    match self.calculate_value_class() {
      ValueClass::One => Self::NZ_1,
      ValueClass::Two => {
        let c1: u32 = 0x80 | (c & 0x3F);
        out[1].write(Self::assume_byte(c1));
        Self::NZ_2
      },
      ValueClass::Three => {
        let c1: u32 = 0x80 | ((c >> 6) & 0x3F);
        out[1].write(Self::assume_byte(c1));
        let c2: u32 = 0x80 | (c & 0x3F);
        out[2].write(Self::assume_byte(c2));
        Self::NZ_3
      },
      ValueClass::Four => {
        let c1: u32 = 0x80 | ((c >> 12) & 0x3F);
        out[1].write(Self::assume_byte(c1));
        let c2: u32 = 0x80 | ((c >> 6) & 0x3F);
        out[2].write(Self::assume_byte(c2));
        let c3: u32 = 0x80 | (c & 0x3F);
        out[3].write(Self::assume_byte(c3));
        Self::NZ_4
      },
      ValueClass::Five => {
        let c1: u32 = 0x80 | ((c >> 18) & 0x0F);
        out[1].write(Self::assume_byte(c1));
        let c2: u32 = 0x80 | ((c >> 12) & 0x3F);
        out[2].write(Self::assume_byte(c2));
        let c3: u32 = 0x80 | ((c >> 6) & 0x3F);
        out[3].write(Self::assume_byte(c3));
        let c4: u32 = 0x80 | (c & 0x3F);
        out[4].write(Self::assume_byte(c4));
        Self::NZ_5
      },
      ValueClass::PastFive => {
        let c1: u32 = 0x80 | (Self::past_five_char_to_byte8(c) & 0x3F);
        out[1].write(Self::assume_byte(c1));
        Self::NZ_2
      },
    }
  }

  const MIN_MULTIBYTE_LEADING_CODE: u32 = 0xC0;
  const MAX_MULTIBYTE_LEADING_CODE: u32 = 0xF8;

  pub const NULL: Self = Self(0);
}
static_assertions::const_assert_eq!(
  SingleChar::MAX_CHAR,
  max_value_for_bit_width_32(SingleChar::BITS)
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
