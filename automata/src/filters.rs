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

    let widened_hashes: Simd<u16, 8> = Simd::from_array([h1, h2, h3, h4, h5, h6, h7, h8]).cast();
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
  fn adjacent_keys(needles: &[u8; 8]) -> (u16, u16) {
    let needles: Simd<u8, 8> = Simd::from_array(*needles);

    /* [0000000|1, 0000000|0, 0000000|0, 0000000|1] */
    /* = [7, 6, 5, 4, 3, 2, 1, 0] */
    let lshifts: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| 7u8 - i as u8));
    /* = [1, 1, 1, 1, 1, 1, 1, 1] */
    let lsb_mask: Simd<u8, 8> = Simd::splat(0b1);

    /* 8x8 matrix transpose */
    let h: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| {
      (((needles >> (8u8 - ((i as u8) + 1u8))) & lsb_mask) << lshifts).reduce_or()
    }));

    let right_bits: Simd<u8, 8> = Simd::splat(0b0000_1111);
    let left_hashes = h >> 4;
    let right_hashes = h & right_bits;

    let widened_left_hashes: Simd<u16, 8> = left_hashes.cast();
    let widened_right_hashes: Simd<u16, 8> = right_hashes.cast();

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
    /* = [7, 6, 5, 4, 3, 2, 1, 0] */
    let lshifts: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| 7u8 - i as u8));
    /* = [1, 1, 1, 1, 1, 1, 1, 1] */
    let lsb_mask: Simd<u8, 8> = Simd::splat(0b1);

    /* 8x8 matrix transpose */
    let h: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| {
      (((needles >> (8u8 - ((i as u8) + 1u8))) & lsb_mask) << lshifts).reduce_or()
    }));

    let right_bits: Simd<u8, 8> = Simd::splat(0b0000_1111);
    let init_bits: Simd<u16, 8> = Simd::splat(0b1);

    /* [1, 1, 1, 1] =
     *  [0b0000_0001, 0b0000_0001, 0b0000_0001, 0b0000_0001] => (transpose 4x8 ->
     * 8x4)    [0000, 0000, 0000, 0000, 0000, 0000, 0000, 1111] => (raise 1
     * << x)    [1, 1, 1, 1, 1, 1, 1, 2^15 - 1] */
    let result: [u16; 5] = array::from_fn(|i| {
      let shift: u8 = 5 - ((i as u8) + 1);

      /* this is a u4x8 of the current window of u8x4 (transposed earlier) */
      let hashes: Simd<u16, 8> = ((h >> shift) & right_bits).cast();
      /* u4 \in 0..16, so raising 1u16 << {x \in u4} will set exactly one bit of
       * the resulting u16, and we will OR the bits to get <= 8 bits set. */
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


  /* [1, 1, 1, 1] =
   * [0b0000_0001, 0b0000_0001, 0b0000_0001, 0b0000_0001] =
   *   (add (3 - i) * 83) [250, 167, 84, 1] =
   *                      [11111010, 10100111, 01010100, 00000001] =>
   *   (transpose 4x8 -> 8x4) [1100, 1010, 1100, 1010, 1000, 0110, 1100, 0101] =
   *                          [12,   10,   12,   10,   8,    6,    10,   5] =>
   *   (raise 1 << x)         [16,   4,    16,   4,    16,   4,    64,    32] */
  #[test]
  fn check_new_simd_hash() {
    let input: [u8; 4] = [1, 1, 1, 1];

    let v: Simd<u8, 4> = Simd::from_array(input);
    let factors: Simd<u8, 4> =
      Simd::from_array(array::from_fn(|i| 3u8 - i as u8)) * Simd::splat(85);
    let f: [u8; 4] = factors.into();
    assert_eq!(f, [255, 170, 85, 0]);
    let added: Simd<u8, 4> = v + factors;
    let a: [u8; 4] = added.into();
    assert_eq!(a, [0, 171, 86, 1]);
    assert_eq!(a, [0b00000000, 0b10101011, 0b01010110, 0b00000001]);

    let resized: Simd<u8, 8> = added.resize(0);

    let lshifts: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| 7u8 - i as u8));
    let lsb_mask: Simd<u8, 8> = Simd::splat(0b1);
    let matrix: Simd<u8, 8> = Simd::from_array(array::from_fn(|i| {
      (((resized >> (8u8 - ((i as u8) + 1u8))) & lsb_mask) << lshifts).reduce_or()
    }));

    let right_bits: Simd<u8, 8> = Simd::splat(0b0000_1111);
    let init_bits: Simd<u16, 8> = Simd::splat(0b1);
    let hashes: Simd<u16, 8> = ((matrix >> 4) & right_bits).cast();
    let h: [u16; 8] = hashes.into();
    assert_eq!(h, [4, 2, 4, 2, 4, 2, 6, 5]);
    let transposed: Simd<u16, 8> = init_bits << hashes;
    /* let hashed: u16 = transposed.reduce_or(); */

    let result: [u16; 8] = transposed.into();
    assert_eq!(result, [16, 4, 16, 4, 16, 4, 64, 32]);
  }
}
