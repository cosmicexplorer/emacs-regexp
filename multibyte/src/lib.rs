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
#![feature(const_mut_refs)]
#![feature(const_maybe_uninit_write)]
#![feature(const_try)]
#![feature(const_box)]
#![feature(effects)]
#![feature(ascii_char)]
#![feature(new_uninit)]
#![feature(slice_ptr_get)]
#![feature(layout_for_ptr)]
#![feature(maybe_uninit_fill)]
#![allow(incomplete_features)]
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

extern crate alloc;

use core::{
  alloc::Allocator,
  ascii, cmp, fmt, hash,
  mem::{self, MaybeUninit},
  str,
};

#[cfg(feature = "proptest")]
use proptest::{collection::vec, prelude::*};


#[allow(dead_code)]
const fn max_value_for_bit_width_32(bits: u8) -> u32 { max_value_for_bit_width_64(bits) as u32 }
const fn max_value_for_bit_width_64(bits: u8) -> u64 { (1u64 << (bits as u64)) - 1 }

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SingleChar(u32);
pub type Char = SingleChar;

#[cfg(feature = "proptest")]
impl Arbitrary for SingleChar {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  /* FIXME: how to handle non-unicode chars? */
  /* fn arbitrary_with(_args: ()) -> Self::Strategy {
   * (0u32..=Self::MAX_CHAR).prop_map(Self).boxed() } */
  fn arbitrary_with(_args: ()) -> Self::Strategy {
    any::<char>().prop_map(Self::from_unicode).boxed()
    /* (0u32..=Self::MAX_UNICODE_CHAR).prop_map(Self).boxed() */
  }
}

impl fmt::Debug for SingleChar {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self.try_as_unicode() {
      Some(c) => write!(f, "{:?}", c),
      None => write!(f, "SingleChar({:?})", self.as_u32()),
    }
  }
}
impl fmt::Display for SingleChar {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self.try_as_unicode() {
      Some(c) => write!(f, "{}", c),
      None => write!(f, "<SingleChar>({})", self.as_u32()),
    }
  }
}

#[inline(always)]
const fn assume_byte(x: u32) -> u8 {
  debug_assert!(x <= u8::MAX as u32);
  x as u8
}

#[inline(always)]
const fn past_five_char_to_byte8(x: u32) -> u32 {
  debug_assert!(x > SingleChar::MAX_5_BYTE_CHAR);
  x - 0x3FFF00
}

#[inline(always)]
const fn transpose_uninit_array<T, const N: usize>(
  x: &mut [MaybeUninit<T>; N],
) -> &mut MaybeUninit<[T; N]> {
  unsafe { mem::transmute(x) }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DecodeError {
  Empty,
  NotEnoughSpace { required: u8, available: u8 },
  InvalidWValue(u32),
  InvalidW1Value(u32),
  InvalidW2Value(u32),
  InvalidW3Value(u64),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum EncodeError {
  Empty,
  NotEnoughSpace { required: u8, available: u8 },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EncodedChar {
  One(ascii::Char),
  Two([u8; 2]),
  Three([u8; 3]),
  Four([u8; 4]),
  Five([u8; 5]),
  Raw([u8; 2]),
}

#[cfg(feature = "proptest")]
impl Arbitrary for EncodedChar {
  type Parameters = ();
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(_args: ()) -> Self::Strategy {
    /* Union::new([ */
    /* any::<ascii::Char>().prop_map(Self::One).boxed(), */
    /* ]) */
    any::<SingleChar>().prop_map(Self::from_uniform).boxed()
  }
}

impl EncodedChar {
  #[inline(always)]
  pub const fn from_uniform(x: SingleChar) -> Self {
    let c = x.as_u32();

    match x.calculate_value_class() {
      ValueClass::One => {
        debug_assert!(ascii::Char::from_u8(x.calculate_leading_code()).is_some());
        Self::One(unsafe { ascii::Char::from_u8_unchecked(x.calculate_leading_code()) })
      },
      ValueClass::Two => {
        let mut out = [0u8; 2];
        out[0] = x.calculate_leading_code();
        let c1: u32 = 0x80 | (c & 0x3F);
        out[1] = assume_byte(c1);
        Self::Two(out)
      },
      ValueClass::Three => {
        let mut out = [0u8; 3];
        out[0] = x.calculate_leading_code();
        let c1: u32 = 0x80 | ((c >> 6) & 0x3F);
        out[1] = assume_byte(c1);
        let c2: u32 = 0x80 | (c & 0x3F);
        out[2] = assume_byte(c2);
        Self::Three(out)
      },
      ValueClass::Four => {
        let mut out = [0u8; 4];
        out[0] = x.calculate_leading_code();
        let c1: u32 = 0x80 | ((c >> 12) & 0x3F);
        out[1] = assume_byte(c1);
        let c2: u32 = 0x80 | ((c >> 6) & 0x3F);
        out[2] = assume_byte(c2);
        let c3: u32 = 0x80 | (c & 0x3F);
        out[3] = assume_byte(c3);
        Self::Four(out)
      },
      ValueClass::Five => {
        let mut out = [0u8; 5];
        out[0] = x.calculate_leading_code();
        let c1: u32 = 0x80 | ((c >> 18) & 0x0F);
        out[1] = assume_byte(c1);
        let c2: u32 = 0x80 | ((c >> 12) & 0x3F);
        out[2] = assume_byte(c2);
        let c3: u32 = 0x80 | ((c >> 6) & 0x3F);
        out[3] = assume_byte(c3);
        let c4: u32 = 0x80 | (c & 0x3F);
        out[4] = assume_byte(c4);
        Self::Five(out)
      },
      ValueClass::Raw => {
        let mut out = [0u8; 2];
        out[0] = x.calculate_leading_code();
        let c1: u32 = 0x80 | (past_five_char_to_byte8(c) & 0x3F);
        out[1] = assume_byte(c1);
        Self::Raw(out)
      },
    }
  }

  #[inline(always)]
  pub const fn into_uniform(self) -> SingleChar {
    match self {
      Self::One(c) => SingleChar::from_ascii(c),
      Self::Two([c1, c2]) => {
        debug_assert!(c1 >= 0xC2);
        let d: u32 = ((c1 as u32) << 6) + (c2 as u32) - ((0xC0 << 6) + 0x80);
        unsafe { SingleChar::from_u32(d) }
      },
      Self::Three([c1, c2, c3]) => {
        let mut d: u32 = ((c1 as u32) << 6) + (c2 as u32) - ((0xC0 << 6) + 0x80);
        d = (d << 6) + (c3 as u32) - ((0x20 << 12) + 0x80);
        unsafe { SingleChar::from_u32(d) }
      },
      Self::Four([c1, c2, c3, c4]) => {
        let mut d: u32 = ((c1 as u32) << 6) + (c2 as u32) - ((0xC0 << 6) + 0x80);
        d = (d << 6) + (c3 as u32) - ((0x20 << 12) + 0x80);
        d = (d << 6) + (c4 as u32) - ((0x10 << 18) + 0x80);
        unsafe { SingleChar::from_u32(d) }
      },
      Self::Five([c1, c2, c3, c4, c5]) => {
        let mut d: u32 = ((c1 as u32) << 6) + (c2 as u32) - ((0xC0 << 6) + 0x80);
        d = (d << 6) + (c3 as u32) - ((0x20 << 12) + 0x80);
        d = (d << 6) + (c4 as u32) - ((0x10 << 18) + 0x80);
        d = (d << 6) + (c5 as u32) - ((0x08 << 24) + 0x80);
        unsafe { SingleChar::from_u32(d) }
      },
      Self::Raw([c1, c2]) => {
        debug_assert!(c1 < 0xC2);
        let d: u32 = ((c1 as u32) << 6) + (c2 as u32) - ((0xC0 << 6) + 0x80);
        unsafe { SingleChar::from_u32(d + 0x3FFF80) }
      },
    }
  }

  #[inline(always)]
  const fn bytes_by_char_head(byte: u8) -> usize {
    if (byte & 0x80) == 0 {
      1
    } else if (byte & 0x20) == 0 {
      2
    } else if (byte & 0x10) == 0 {
      3
    } else if (byte & 0x08) == 0 {
      4
    } else {
      5
    }
  }

  #[inline]
  pub fn try_parse(x: &[u8]) -> Result<(Self, &[u8]), DecodeError> {
    let (c, rest) = x.split_first().ok_or(DecodeError::Empty)?;
    let c = *c;
    let required = Self::bytes_by_char_head(c);
    if required > x.len() {
      assert!(required <= u8::MAX as usize);
      assert!(x.len() <= u8::MAX as usize);
      return Err(DecodeError::NotEnoughSpace {
        required: required as u8,
        available: x.len() as u8,
      });
    }
    Ok(match required {
      1 => {
        debug_assert_eq!(c & 0x80, 0);
        debug_assert!(ascii::Char::from_u8(c).is_some());
        (
          Self::One(unsafe { ascii::Char::from_u8_unchecked(c) }),
          &x[1..],
        )
      },
      2 => {
        let (d, rest) = rest.split_first().unwrap();
        let d = *d;
        let w: u32 = (((d as u32) & 0xC0) << 2) + (c as u32);
        if !(0x2C0..=0x2DF).contains(&w) {
          return Err(DecodeError::InvalidWValue(w));
        }
        let ret = if w < 0x2C2 {
          Self::Raw([c, d])
        } else {
          Self::Two([c, d])
        };
        (ret, rest)
      },
      3 => {
        let ([d, e], rest) = rest.split_first_chunk().unwrap();
        let d = *d;
        let e = *e;
        let mut w: u32 = (((d as u32) & 0xC0) << 2) + (c as u32);
        w += ((e as u32) & 0xC0) << 4;
        let w1: u32 = w | (((d as u32) & 0x20) >> 2);
        if !(0xAE1..=0xAEF).contains(&w1) {
          return Err(DecodeError::InvalidW1Value(w1));
        }
        (Self::Three([c, d, e]), rest)
      },
      4 => {
        let ([d, e, f], rest) = rest.split_first_chunk().unwrap();
        let d = *d;
        let e = *e;
        let f = *f;
        let mut w: u32 = (((d as u32) & 0xC0) << 2) + (c as u32);
        w += ((e as u32) & 0xC0) << 4;
        w += ((f as u32) & 0xC0) << 6;
        let w2: u32 = w | (((d as u32) & 0x30) >> 3);
        if !(0x2AF1..=0x2AF7).contains(&w2) {
          return Err(DecodeError::InvalidW2Value(w2));
        }
        (Self::Four([c, d, e, f]), rest)
      },
      5 => {
        let ([d, e, f, g], rest) = rest.split_first_chunk().unwrap();
        let d = *d;
        let e = *e;
        let f = *f;
        let g = *g;
        let mut w: u32 = (((d as u32) & 0xC0) << 2) + (c as u32);
        w += ((e as u32) & 0xC0) << 4;
        w += ((f as u32) & 0xC0) << 6;
        let lw: u64 = (w as u64) + (((g as u64) & 0xC0) << 8);
        let w3: u64 = (lw << 24) + ((d as u64) << 16) + ((d as u64) << 8) + (f as u64);
        if !(0xAAF8888080..=0xAAF88FBFBD).contains(&w3) {
          return Err(DecodeError::InvalidW3Value(w3));
        }
        (Self::Five([c, d, e, f, g]), rest)
      },
      _ => unreachable!("bytes_by_char_head() should never return any other value!"),
    })
  }

  #[inline(always)]
  pub const fn byte_len(&self) -> usize {
    match self {
      &Self::One(_) => 1,
      &Self::Two(_) | &Self::Raw(_) => 2,
      &Self::Three(_) => 3,
      &Self::Four(_) => 4,
      &Self::Five(_) => 5,
    }
  }

  #[inline]
  pub fn try_write<'a>(
    &self,
    x: &'a mut [MaybeUninit<u8>],
  ) -> Result<&'a mut [MaybeUninit<u8>], EncodeError> {
    if x.is_empty() {
      return Err(EncodeError::Empty);
    }
    let required = self.byte_len();
    if required > x.len() {
      assert!(required <= u8::MAX as usize);
      assert!(x.len() <= u8::MAX as usize);
      return Err(EncodeError::NotEnoughSpace {
        required: required as u8,
        available: x.len() as u8,
      });
    }
    Ok(match self {
      Self::One(c) => {
        let (head, rest) = x.split_first_mut().unwrap();
        head.write(c.to_u8());
        rest
      },
      Self::Two(data) => {
        let (head, rest): (&mut [MaybeUninit<u8>; 2], _) = x.split_first_chunk_mut().unwrap();
        let head: &mut MaybeUninit<[u8; 2]> = transpose_uninit_array(head);
        head.write(*data);
        rest
      },
      Self::Raw(data) => {
        let (head, rest): (&mut [MaybeUninit<u8>; 2], _) = x.split_first_chunk_mut().unwrap();
        let head: &mut MaybeUninit<[u8; 2]> = transpose_uninit_array(head);
        head.write(*data);
        rest
      },
      Self::Three(data) => {
        let (head, rest): (&mut [MaybeUninit<u8>; 3], _) = x.split_first_chunk_mut().unwrap();
        let head: &mut MaybeUninit<[u8; 3]> = transpose_uninit_array(head);
        head.write(*data);
        rest
      },
      Self::Four(data) => {
        let (head, rest): (&mut [MaybeUninit<u8>; 4], _) = x.split_first_chunk_mut().unwrap();
        let head: &mut MaybeUninit<[u8; 4]> = transpose_uninit_array(head);
        head.write(*data);
        rest
      },
      Self::Five(data) => {
        let (head, rest): (&mut [MaybeUninit<u8>; 5], _) = x.split_first_chunk_mut().unwrap();
        let head: &mut MaybeUninit<[u8; 5]> = transpose_uninit_array(head);
        head.write(*data);
        rest
      },
    })
  }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ValueClass {
  One,
  Two,
  Three,
  Four,
  Five,
  Raw,
}

impl SingleChar {
  #[allow(dead_code)]
  const BITS: u8 = 22;
  const MAX_CHAR: u32 = 0x3FFFFF;

  #[inline(always)]
  pub const fn from_byte(x: u8) -> Self {
    match ascii::Char::from_u8(x) {
      Some(c) => Self::from_ascii(c),
      None => unsafe { Self::from_u32((x as u32) + 0x3FFF00) },
    }
  }

  #[inline(always)]
  pub const fn from_ascii(c: ascii::Char) -> Self { Self(c.to_u8() as u32) }

  #[inline(always)]
  pub const fn try_as_ascii(&self) -> Option<ascii::Char> {
    match self.calculate_value_class() {
      ValueClass::One => {
        let c = assume_byte(self.as_u32());
        Some(unsafe { ascii::Char::from_u8_unchecked(c) })
      },
      _ => None,
    }
  }

  #[inline(always)]
  pub const fn from_unicode(c: char) -> Self { unsafe { Self(mem::transmute(c)) } }

  #[inline(always)]
  pub const fn try_as_unicode(&self) -> Option<char> {
    let c = self.as_u32();
    if c > Self::MAX_UNICODE_CHAR {
      None
    } else {
      Some(unsafe { char::from_u32_unchecked(c) })
    }
  }

  /// # Safety
  ///
  /// `x` MUST be greater than [`Self::MAX_CHAR`]!
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
  const fn calculate_value_class(&self) -> ValueClass {
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
      return ValueClass::Raw;
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
  pub const fn calculate_leading_code(&self) -> u8 {
    let c = self.as_u32();
    let ret: u32 = match self.calculate_value_class() {
      ValueClass::One => c,
      ValueClass::Two => 0xC0 | (c >> 6),
      ValueClass::Three => 0xE0 | (c >> 12),
      ValueClass::Four => 0xF0 | (c >> 18),
      ValueClass::Five => 0xF8,
      ValueClass::Raw => 0xC0 | ((past_five_char_to_byte8(c) >> 6) & 0x01),
    };
    assume_byte(ret)
  }

  const MAX_MULTIBYTE_LENGTH: usize = 5;

  pub const NULL: Self = Self(0);
  pub const A: Self = Self::from_ascii(unsafe { ascii::Char::from_u8_unchecked(b'A') });
}
static_assertions::const_assert_eq!(
  SingleChar::MAX_CHAR,
  max_value_for_bit_width_32(SingleChar::BITS)
);

struct CodepointIterator<'a> {
  data: &'a [u8],
}

impl<'a> Iterator for CodepointIterator<'a> {
  type Item = EncodedChar;

  #[inline(always)]
  fn next(&mut self) -> Option<EncodedChar> {
    if self.data.is_empty() {
      return None;
    }
    let (ret, new_data) = EncodedChar::try_parse(self.data).unwrap();
    self.data = new_data;
    Some(ret)
  }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PackedString<'a>(&'a [u8]);
static_assertions::assert_eq_size!(PackedString<'static>, &'static [u8]);
static_assertions::assert_eq_size!(PackedString<'static>, (usize, usize));
pub type Str<'a> = PackedString<'a>;

impl<'a> PackedString<'a> {
  /// # Safety
  ///
  /// `bytes` MUST be a valid multibyte string!
  #[inline(always)]
  pub const unsafe fn from_bytes(bytes: &'a [u8]) -> Self { Self(bytes) }

  #[inline(always)]
  pub const fn as_bytes(&self) -> &'a [u8] {
    let Self(data) = self;
    data
  }

  #[inline]
  pub fn try_from_bytes(bytes: &'a [u8]) -> Result<(Self, usize), DecodeError> {
    let mut remaining = bytes;
    let mut num_encoded_chars_seen: usize = 0;
    while !remaining.is_empty() {
      let (_encoded_char, new_remaining) = EncodedChar::try_parse(remaining)?;
      remaining = new_remaining;
      num_encoded_chars_seen += 1;
    }
    Ok((unsafe { Self::from_bytes(bytes) }, num_encoded_chars_seen))
  }

  /// A utf-8-encoded string is always a valid multibyte string, so simply
  /// accept it as it is.
  #[inline(always)]
  pub const fn from_str(s: &'a str) -> Self { Self(s.as_bytes()) }

  #[inline(always)]
  pub fn iter_encoded_chars(&self) -> impl Iterator<Item=EncodedChar>+'a {
    let Self(data) = self;
    CodepointIterator { data }
  }

  #[inline(always)]
  pub fn iter_uniform_chars(&self) -> impl Iterator<Item=SingleChar>+'a {
    self.iter_encoded_chars().map(EncodedChar::into_uniform)
  }
}

impl<'a> fmt::Debug for PackedString<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match str::from_utf8(self.as_bytes()) {
      Ok(s) => write!(f, "{:?}", s),
      Err(e) => todo!("non-utf8 string: {:?}", e),
    }
  }
}
impl<'a> fmt::Display for PackedString<'a> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match str::from_utf8(self.as_bytes()) {
      Ok(s) => write!(f, "{}", s),
      Err(e) => todo!("non-utf8 string: {:?}", e),
    }
  }
}

/* TODO: smallvec? */
#[derive(Clone)]
#[repr(transparent)]
pub struct OwnedString<A: Allocator>(Box<[u8], A>);
pub type String<A> = OwnedString<A>;

impl<A: Allocator> fmt::Debug for OwnedString<A> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{:?}", self.as_packed_str()) }
}
impl<A: Allocator> fmt::Display for OwnedString<A> {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_packed_str()) }
}

#[cfg(feature = "proptest")]
impl<A> Arbitrary for OwnedString<A>
where A: Allocator+Clone+Default+fmt::Debug+'static
{
  type Parameters = (usize, A);
  type Strategy = BoxedStrategy<Self>;

  fn arbitrary_with(args: (usize, A)) -> Self::Strategy {
    let (max_len, alloc) = args;
    (vec(any::<SingleChar>(), 0..=max_len), Just(alloc))
      .prop_map(|(chars, alloc)| Self::coalesce_chars(chars.into_iter(), alloc))
      .boxed()
  }
}

impl<A> OwnedString<A>
where A: Allocator
{
  #[inline]
  pub fn coalesce_chars(unpacked: impl Iterator<Item=SingleChar>, alloc: A) -> Self {
    let mut buf: Vec<u8, A> = Vec::new_in(alloc);

    for c in unpacked.map(EncodedChar::from_uniform) {
      let remaining = buf.spare_capacity_mut();
      match c.try_write(remaining) {
        Ok(_) => (),
        Err(_) => {
          debug_assert!(remaining.len() < SingleChar::MAX_MULTIBYTE_LENGTH);
          buf.reserve(c.byte_len());
          let _ = c
            .try_write(buf.spare_capacity_mut())
            .expect("encoding should work after reserve call");
        },
      }
      unsafe {
        buf.set_len(buf.len() + c.byte_len());
      }
    }

    unsafe { Self::from_bytes(buf.into_boxed_slice()) }
  }

  #[inline(always)]
  pub const fn allocator(&self) -> &A { Box::allocator(&self.0) }

  /// # Safety
  ///
  /// `s` MUST be a valid owned multibyte string!
  #[inline(always)]
  pub const unsafe fn from_bytes(s: Box<[u8], A>) -> Self { Self(s) }

  #[inline(always)]
  pub const fn as_packed_str(&self) -> PackedString {
    unsafe { PackedString::from_bytes(self.0.as_ref()) }
  }
}

impl<A: Allocator> PartialEq for OwnedString<A> {
  #[inline]
  fn eq(&self, other: &Self) -> bool { self.as_packed_str().eq(&other.as_packed_str()) }
}
impl<A: Allocator> Eq for OwnedString<A> {}

impl<A: Allocator> cmp::PartialOrd for OwnedString<A> {
  #[inline]
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}
impl<A: Allocator> cmp::Ord for OwnedString<A> {
  #[inline]
  fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_packed_str().cmp(&other.as_packed_str()) }
}

impl<A: Allocator> hash::Hash for OwnedString<A> {
  #[inline]
  fn hash<H: hash::Hasher>(&self, state: &mut H) { self.as_packed_str().hash(state); }
}

#[cfg(test)]
mod test {
  use core::str;
  use std::alloc::Global;

  use super::*;

  #[test]
  fn single_char() {
    let c = SingleChar::A;
    let e = EncodedChar::from_uniform(c);
    assert_eq!(e.into_uniform(), c);
  }

  #[test]
  fn ascii_string() {
    let s = b"asdf";
    let (p, n) = PackedString::try_from_bytes(s).unwrap();
    assert_eq!(n, 4);
    let p2 = PackedString::from_str(str::from_utf8(s).unwrap());
    assert_eq!(p, p2);
    assert_eq!(p2.iter_encoded_chars().count(), 4);
  }

  #[test]
  fn utf8_string() {
    let s = "aßdf";
    let (p, n) = PackedString::try_from_bytes(s.as_bytes()).unwrap();
    assert_eq!(n, 4);
    assert!(n < s.as_bytes().len());
    let p2 = PackedString::from_str(s);
    assert_eq!(p, p2);
    assert_eq!(p2.iter_encoded_chars().count(), 4);
  }

  #[test]
  fn three_byte_char() {
    let s = "aࠀdf";
    let (p, n) = PackedString::try_from_bytes(s.as_bytes()).unwrap();
    assert_eq!(n, 4);
    assert!(n < s.as_bytes().len());
    let p2 = PackedString::from_str(s);
    assert_eq!(p, p2);
    assert_eq!(p2.iter_encoded_chars().count(), 4);
  }

  #[test]
  fn mixed_length_chars() {
    let s = "aࠀßs\0d";
    assert_eq!(s.as_bytes().len(), 9);
    let (_, n) = PackedString::try_from_bytes(s.as_bytes()).unwrap();
    assert_eq!(n, s.chars().count());
  }

  #[test]
  fn raw_bytes() {
    let c = SingleChar::from_byte(128);
    assert_eq!(4194176, c.as_u32());
    let c = SingleChar::from_byte(u8::MAX);
    assert_eq!(SingleChar::MAX_CHAR, c.as_u32());
  }

  prop_compose! {
    fn gen_multibyte_chars(max_len: usize)
      (
        v in prop::collection::vec(
          any::<SingleChar>(),
          0..=max_len
        )
      ) -> Vec<SingleChar> {
        v
      }
  }
  prop_compose! {
    fn gen_utf8_chars(max_len: usize)
      (
        v in prop::collection::vec(
          any::<char>(),
          0..=max_len
        )
      ) -> Vec<char> {
        v
      }
  }
  prop_compose! {
    fn gen_single_ascii_char()(c in 0u8..=127) -> ascii::Char {
      ascii::Char::from_u8(c).unwrap()
    }
  }
  prop_compose! {
    fn gen_ascii_chars(max_len: usize)
      (
        v in prop::collection::vec(
          gen_single_ascii_char(),
          0..=max_len
        )
      ) -> Vec<ascii::Char> {
        v
      }
  }

  proptest! {
    #[test]
    fn single_char_roundtrip(c in any::<SingleChar>()) {
      let e = EncodedChar::from_uniform(c);
      prop_assert_eq!(e.into_uniform(), c);
    }

    #[test]
    fn multibyte_string_roundtrip(chars in gen_multibyte_chars(50)) {
      let s = OwnedString::coalesce_chars(chars.iter().copied(), Global);
      let new_chars: Vec<_> = s.as_packed_str().iter_uniform_chars().collect();
      prop_assert_eq!(chars, new_chars);
    }

    #[test]
    fn ascii_string_roundtrip(chars in gen_ascii_chars(50)) {
      let bytes: &[u8] = unsafe { mem::transmute(&chars[..]) };
      let (p, n) = PackedString::try_from_bytes(bytes).unwrap();
      prop_assert_eq!(n, chars.len());
      prop_assert_eq!(n, bytes.len());
      let s = str::from_utf8(bytes).unwrap();
      prop_assert_eq!(n, s.len());
      let p2 = PackedString::from_str(s);
      prop_assert_eq!(p, p2);
    }

    #[test]
    fn utf8_string_roundtrip(chars in gen_utf8_chars(50)) {
      let d: std::string::String = crate::util::string::coalesce_utf8_chars(
        chars.iter().copied(),
        Global,
      ).into();

      let (p, n) = PackedString::try_from_bytes(d.as_bytes()).unwrap();
      prop_assert_eq!(n, chars.len());
      prop_assert_eq!(n, d.chars().count());
      let p2 = PackedString::from_str(&d);
      prop_assert_eq!(p, p2);
    }
  }
}

pub mod util {
  pub mod string {
    use core::{alloc::Allocator, mem::MaybeUninit};

    use crate::alloc_types::*;

    #[inline]
    pub fn coalesce_utf8_chars<A: Allocator>(
      chars: impl Iterator<Item=char>,
      alloc: A,
    ) -> Box<str, A> {
      /* TODO: smallvec? */
      let mut buf: Vec<u8, A> = Vec::new_in(alloc);
      for c in chars {
        let mut remaining = buf.spare_capacity_mut();
        if remaining.len() < c.len_utf8() {
          buf.reserve(c.len_utf8());
          remaining = buf.spare_capacity_mut();
          debug_assert!(remaining.len() >= c.len_utf8());
        }
        let (target, _) = unsafe { remaining.split_at_mut_unchecked(c.len_utf8()) };
        let _ = c.encode_utf8(MaybeUninit::fill(target, 0u8));
        unsafe {
          buf.set_len(buf.len() + c.len_utf8());
        }
      }
      unsafe { super::boxing::box_into_string(buf.into_boxed_slice()) }
    }
  }

  pub mod boxing {
    use core::{
      alloc::{Allocator, Layout},
      ffi::c_char,
      mem,
      ptr::NonNull,
    };

    use crate::alloc_types::*;

    /// # Safety
    ///
    /// `b` MUST point to a valid [`str`] allocation!
    #[inline(always)]
    pub unsafe fn box_into_string<A: Allocator>(b: Box<[u8], A>) -> Box<str, A> {
      let (p, alloc): (*mut [u8], A) = Box::into_raw_with_allocator(b);
      let p = p as *mut str;
      unsafe { Box::from_raw_in(p, alloc) }
    }

    #[inline(always)]
    pub fn string_into_box<A: Allocator>(b: Box<str, A>) -> Box<[u8], A> {
      let (p, alloc): (*mut str, A) = Box::into_raw_with_allocator(b);
      let p = p as *mut [u8];
      unsafe { Box::from_raw_in(p, alloc) }
    }

    #[inline(always)]
    pub fn reallocate_with_trailing_null<A: Allocator>(b: Box<str, A>) -> Box<[u8], A> {
      let s = string_into_box(b);
      let (p, alloc) = Box::into_raw_with_allocator(s);
      unsafe {
        let p: NonNull<[u8]> = NonNull::new_unchecked(p);
        let p_const: *const [u8] = mem::transmute(p);
        let old_layout = Layout::for_value_raw(p_const);
        let new_layout =
          Layout::from_size_align_unchecked(old_layout.size() + 1, old_layout.align());
        let p_base: NonNull<u8> = p.as_non_null_ptr();
        let new_allocation: NonNull<[u8]> = match alloc.grow_zeroed(p_base, old_layout, new_layout)
        {
          Ok(p) => p,
          Err(_) => ::alloc::alloc::handle_alloc_error(new_layout),
        };
        Box::from_raw_in(new_allocation.as_ptr(), alloc)
      }
    }

    #[inline(always)]
    pub fn box_c_char<A: Allocator>(b: Box<[u8], A>) -> (NonNull<c_char>, A) {
      let (p, alloc) = Box::into_raw_with_allocator(b);
      let p: NonNull<[u8]> = unsafe { NonNull::new_unchecked(p) };
      let p: NonNull<u8> = p.as_non_null_ptr();
      (p.cast(), alloc)
    }

    #[cfg(test)]
    mod test {
      use super::*;

      #[test]
      fn add_null() {
        let s = "asdf";
        let b = s.as_bytes().to_vec().into_boxed_slice();
        let bs = unsafe { box_into_string(b) };
        assert_eq!(bs.as_ref(), s);
        let with_null = reallocate_with_trailing_null(bs);
        assert_eq!(with_null.as_ref(), b"asdf\0");
      }
    }
  }
}
