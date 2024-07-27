/* Description: Probabilistic set data structures.

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

/* FIXME: unused! */
#![allow(dead_code)]

//! Probabilistic set data structures.

use core::{array, simd::prelude::*};

#[derive(Debug)]
struct Filter {
  bits: u16,
}

impl Filter {
  pub const fn new() -> Self { Self { bits: 0 } }

  #[inline(always)]
  fn perfect_key(needle: [u8; 4]) -> u16 {
    let needle: Simd<u8, 4> = Simd::from_array(needle);

    /* [0000000|1, 0000000|0, 0000000|0, 0000000|1] */
    const LSHIFTS: Simd<u8, 4> = Simd::from_array([3, 2, 1, 0]);
    let lsb_mask: Simd<u8, 4> = Simd::splat(0b1);

    /* extract each "column" of bits from all of the 4 u8s (this is just a
     * transpose) */
    let h1: u8 = (((needle >> 7u8) & lsb_mask) << LSHIFTS).reduce_or();
    let h2: u8 = (((needle >> 6u8) & lsb_mask) << LSHIFTS).reduce_or();
    let h3: u8 = (((needle >> 5u8) & lsb_mask) << LSHIFTS).reduce_or();
    let h4: u8 = (((needle >> 4u8) & lsb_mask) << LSHIFTS).reduce_or();
    let h5: u8 = (((needle >> 3u8) & lsb_mask) << LSHIFTS).reduce_or();
    let h6: u8 = (((needle >> 2u8) & lsb_mask) << LSHIFTS).reduce_or();
    let h7: u8 = (((needle >> 1u8) & lsb_mask) << LSHIFTS).reduce_or();
    let h8: u8 = ((needle & lsb_mask) << LSHIFTS).reduce_or();

    /* technically a u4! */
    debug_assert!(h1 < 16);
    debug_assert!(h2 < 16);
    debug_assert!(h3 < 16);
    debug_assert!(h4 < 16);
    debug_assert!(h5 < 16);
    debug_assert!(h6 < 16);
    debug_assert!(h7 < 16);
    debug_assert!(h8 < 16);

    let widened_hashes: Simd<u16, 8> = Simd::from_array([
      h1 as u16, h2 as u16, h3 as u16, h4 as u16, h5 as u16, h6 as u16, h7 as u16, h8 as u16,
    ]);
    let init_bits: Simd<u16, 8> = Simd::splat(0b1);

    let shifted_bits: Simd<u16, 8> = init_bits << widened_hashes;
    let result: u16 = shifted_bits.reduce_or();
    result
  }

  pub fn insert_key(&mut self, needle: [u8; 4]) {
    let key = Self::perfect_key(needle);
    self.bits |= key;
  }

  pub fn test_key(&self, needle: [u8; 4]) -> bool {
    let key = Self::perfect_key(needle);
    (self.bits & key) == key
  }

  #[inline(always)]
  fn widen_u8(u8_hashes: [u8; 8]) -> [u16; 8] {
    array::from_fn(|i| *unsafe { u8_hashes.get_unchecked(i) } as u16)
  }

  #[inline(always)]
  fn adjacent_keys(needles: &[u8; 8]) -> (u16, u16) {
    let needles: Simd<u8, 8> = Simd::from_array(*needles);

    /* [0000000|1, 0000000|0, 0000000|0, 0000000|1] */
    const LSHIFTS: Simd<u8, 8> = Simd::from_array([7, 6, 5, 4, 3, 2, 1, 0]);
    let lsb_mask: Simd<u8, 8> = Simd::splat(0b1);

    let h: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| {
      (((needles >> (8u8 - ((i as u8) + 1u8))) & lsb_mask) << LSHIFTS).reduce_or()
    }));

    let right_bits: Simd<u8, 8> = Simd::splat(0b0000_1111);
    let left_hashes: [u8; 8] = (h >> 4).into();
    let right_hashes: [u8; 8] = (h & right_bits).into();

    let widened_left_hashes: Simd<u16, 8> = Simd::from_array(Self::widen_u8(left_hashes));
    let widened_right_hashes: Simd<u16, 8> = Simd::from_array(Self::widen_u8(right_hashes));

    let init_bits: Simd<u16, 8> = Simd::splat(0b1);

    let left_shifted_bits: Simd<u16, 8> = init_bits << widened_left_hashes;
    let right_shifted_bits: Simd<u16, 8> = init_bits << widened_right_hashes;
    let left_result: u16 = left_shifted_bits.reduce_or();
    let right_result: u16 = right_shifted_bits.reduce_or();
    (left_result, right_result)
  }

  #[inline(always)]
  fn all_adjacent_keys(needles: &[u8; 8]) -> ([u16; 5], [u8; 8]) {
    let needles: Simd<u8, 8> = Simd::from_array(*needles);

    /* [0000000|1, 0000000|0, 0000000|0, 0000000|1] */
    const LSHIFTS: Simd<u8, 8> = Simd::from_array([7, 6, 5, 4, 3, 2, 1, 0]);
    let lsb_mask: Simd<u8, 8> = Simd::splat(0b1);

    let h: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| {
      (((needles >> (8u8 - ((i as u8) + 1u8))) & lsb_mask) << LSHIFTS).reduce_or()
    }));

    let right_bits: Simd<u8, 8> = Simd::splat(0b0000_1111);
    let init_bits: Simd<u16, 8> = Simd::splat(0b1);

    let result: [u16; 5] = array::from_fn(|i| {
      let shift: u8 = 5 - ((i as u8) + 1);
      let hashes: Simd<u16, 8> =
        Simd::from_array(Self::widen_u8(((h >> shift) & right_bits).into()));
      (init_bits << hashes).reduce_or()
    });
    (result, h.into())
  }

  #[allow(unused_variables, dead_code)]
  pub fn rolling_matches(&self, haystack: &[u8]) {
    let h: Simd<u8, 8> = Simd::splat(0);
    let (prefix, middle, suffix): (&[u8], &[Simd<u8, 4>], &[u8]) = haystack.as_simd();
    /* TODO: support middle.len() == 1! */
    let (first, rest) = middle.split_first().unwrap();

    const LSHIFTS: Simd<u8, 8> = Simd::from_array([7, 6, 5, 4, 3, 2, 1, 0]);
    let lsb_mask: Simd<u8, 8> = Simd::splat(0b1);

    todo!();
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn insert_test() {
    let mut f = Filter::new();

    assert!(!f.test_key(*b"abcd"));
    f.insert_key(*b"abcd");
    assert!(f.test_key(*b"abcd"));
    assert!(!f.test_key(*b"asdf"));
  }

  #[test]
  fn adjacent() {
    let a = Filter::perfect_key(*b"abcd");
    let b = Filter::perfect_key(*b"asdf");
    let (a2, b2) = Filter::adjacent_keys(b"abcdasdf");
    assert_eq!(a, a2);
    assert_eq!(b, b2);
  }

  #[test]
  fn all_adjacent() {
    let a1 = Filter::perfect_key(*b"abcd");
    let a2 = Filter::perfect_key(*b"bcda");
    let a3 = Filter::perfect_key(*b"cdas");
    let a4 = Filter::perfect_key(*b"dasd");
    let a5 = Filter::perfect_key(*b"asdf");

    let (b, _) = Filter::all_adjacent_keys(b"abcdasdf");
    assert_eq!(b, [a1, a2, a3, a4, a5]);
  }
}
