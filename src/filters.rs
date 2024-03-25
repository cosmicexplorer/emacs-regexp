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

//! Probabilistic set data structures.

use core::simd::{num::SimdUint, Simd};

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
    const LSB_MASK: Simd<u8, 4> = Simd::from_array([0b1, 0b1, 0b1, 0b1]);

    /* technically a u4! */
    let h1: u8 = (((needle >> 7u8) & LSB_MASK) << LSHIFTS).reduce_or();
    let h2: u8 = (((needle >> 6u8) & LSB_MASK) << LSHIFTS).reduce_or();
    let h3: u8 = (((needle >> 5u8) & LSB_MASK) << LSHIFTS).reduce_or();
    let h4: u8 = (((needle >> 4u8) & LSB_MASK) << LSHIFTS).reduce_or();
    let h5: u8 = (((needle >> 3u8) & LSB_MASK) << LSHIFTS).reduce_or();
    let h6: u8 = (((needle >> 2u8) & LSB_MASK) << LSHIFTS).reduce_or();
    let h7: u8 = (((needle >> 1u8) & LSB_MASK) << LSHIFTS).reduce_or();
    let h8: u8 = ((needle & LSB_MASK) << LSHIFTS).reduce_or();
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
    const INIT_BITS: Simd<u16, 8> = Simd::from_array([0b1, 0b1, 0b1, 0b1, 0b1, 0b1, 0b1, 0b1]);

    let shifted_bits: Simd<u16, 8> = INIT_BITS << widened_hashes;
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
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn insert_test() {
    let mut f = Filter::new();

    dbg!(&f);
    assert!(!f.test_key(*b"abcd"));
    f.insert_key(*b"abcd");
    dbg!(&f);
    assert!(f.test_key(*b"abcd"));
    assert!(!f.test_key(*b"asdf"));
  }
}
