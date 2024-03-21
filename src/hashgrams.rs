/* Description: Rolling window hash iterators.

Copyright (C) 2024 Danny McClanahan <dmcC2@hypnicjerk.ai>
SPDX-License-Identifier: GPL-3.0-or-later

This file is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as
published by the Free Software Foundation; either version 3 of the
License, or (at your option) any later version.

This file is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>. */

//! Rolling window hash iterators.

pub mod hashing {
  use core::{iter, mem::MaybeUninit};

  use crate::{ComponentLen, ComponentOffset};

  type HashToken = u8;
  type HashLen = u64;

  #[derive(Debug, Copy, Clone, PartialEq, Eq)]
  #[repr(transparent)]
  pub struct Hash(pub(crate) HashLen);

  const SHIFT_FACTOR: u32 = 1;

  impl Hash {
    #[inline(always)]
    pub(crate) const fn new() -> Self { Self(0) }

    #[inline(always)]
    pub(crate) fn add(&mut self, byte: HashToken) {
      /* 8 + 3 * x (=? 19) > 64 */
      self.0 = self
        .0
        .wrapping_shl(SHIFT_FACTOR)
        .wrapping_add(HashLen::from(byte));
    }

    #[inline(always)]
    pub(crate) fn del(&mut self, factor: HashLen, byte: HashToken) {
      self.0 = self
        .0
        .wrapping_sub(HashLen::from(byte).wrapping_mul(factor));
    }

    #[inline(always)]
    pub(crate) fn roll(&mut self, factor: HashLen, old: HashToken, new: HashToken) {
      self.del(factor, old);
      self.add(new);
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum WindowDirection {
    Left,
    Right,
  }

  #[derive(Debug, Clone)]
  struct WindowFilter {
    state: u64,
  }

  const SIMD_HASH_WINDOW_LENGTH: ComponentLen = 4;

  #[derive(Debug, Clone)]
  struct SIMDHashWindow {
    hashes: [Hash; SIMD_HASH_WINDOW_LENGTH],
  }

  impl SIMDHashWindow {
    #[inline(always)]
    const fn calculate_div_factor() -> HashLen {
      1u64.wrapping_shl((SIMD_HASH_WINDOW_LENGTH as u32) - 1)
    }

    #[inline(always)]
    pub const fn blank() -> Self {
      Self {
        hashes: unsafe { MaybeUninit::zeroed().assume_init() },
      }
    }

    /* TODO: do this on the GPU! */
    #[inline]
    pub fn initialize(&mut self, window: &[HashToken; SIMD_HASH_WINDOW_LENGTH]) {
      for (i, b) in window.iter().copied().enumerate() {
        for h in self.hashes[0..=i].iter_mut() {
          h.add(b);
        }
      }
    }
  }

  #[derive(Debug, Clone)]
  struct HashWindow {
    hash: Hash,
    hash_2pow: HashLen,
  }

  impl HashWindow {
    #[inline(always)]
    pub const fn new() -> Self {
      Self {
        hash: Hash::new(),
        hash_2pow: 1,
      }
    }

    #[inline(always)]
    pub fn add_first_to_window(&mut self, first: HashToken) { self.hash.add(first); }

    #[inline(always)]
    pub fn add_next_to_window(&mut self, next: HashToken) {
      self.hash.add(next);
      self.hash_2pow = self.hash_2pow.wrapping_shl(SHIFT_FACTOR);
    }

    #[inline(always)]
    pub fn roll(&mut self, old: HashToken, new: HashToken) {
      self.hash.roll(self.hash_2pow, old, new);
    }

    #[inline(always)]
    pub fn get_hash(&self) -> Hash { self.hash }

    #[inline]
    pub fn initialize_window_at_border(
      &mut self,
      entire_input: &[HashToken],
      direction: WindowDirection,
      window_len: ComponentLen,
    ) -> ComponentOffset {
      assert!(
        (window_len as usize) <= entire_input.len(),
        "TODO: hash window must be no larger than input length!"
      );
      let mut offset = ComponentOffset::zero();
      assert_ne!(window_len, 0, "empty hash window not supported!");
      let (first, rest) = match direction {
        WindowDirection::Left => entire_input.split_first().unwrap(),
        WindowDirection::Right => entire_input.split_last().unwrap(),
      };
      self.add_first_to_window(*first);
      unsafe {
        offset.unchecked_increment();
      }
      match direction {
        WindowDirection::Left => {
          for b in rest.iter().copied().take((window_len as usize) - 1) {
            self.add_next_to_window(b);
            unsafe {
              offset.unchecked_increment();
            }
          }
        },
        WindowDirection::Right => {
          for b in rest.iter().rev().copied().take((window_len as usize) - 1) {
            self.add_next_to_window(b);
            unsafe {
              offset.unchecked_increment();
            }
          }
        },
      };
      debug_assert_eq!(offset.as_size(), window_len as usize);
      offset
    }
  }

  /* TODO: consider vectorized version! see e.g. https://github.com/ashvardanian/StringZilla/blob/bc1869a85293ff5aa6e5075475263002c43648eb/include/stringzilla/stringzilla.h#L3682-L3805 */
  pub struct HashWindowIt<'h> {
    input: &'h [HashToken],
    offset: Option<ComponentOffset>,
    direction: WindowDirection,
    window: HashWindow,
    window_len: Option<ComponentLen>,
  }
  impl<'h> HashWindowIt<'h> {
    #[inline(always)]
    pub fn empty_window(input: &'h [HashToken], direction: WindowDirection) -> Self {
      Self {
        input,
        offset: None,
        direction,
        window: HashWindow::new(),
        window_len: None,
      }
    }

    #[inline(always)]
    pub fn input_len(&self) -> ComponentLen {
      let ComponentOffset(len) = ComponentOffset::from_size(self.input.len());
      len
    }

    #[inline(always)]
    pub fn window_len(&self) -> ComponentLen { self.window_len.unwrap() }

    #[inline(always)]
    pub fn remaining(&self) -> ComponentLen {
      let offset = match self.offset {
        None => return 0,
        Some(ComponentOffset(offset)) => offset,
      };
      /* +1 because we will generate exactly one window at the end (e.g. when a
       * window covers the entire input). */
      self.input_len() - offset + 1
    }

    #[inline]
    pub fn initialize_window(&mut self, window_len: ComponentLen) {
      self.window_len = Some(window_len);
      self.offset = Some(self.window.initialize_window_at_border(
        self.input,
        self.direction,
        window_len,
      ));
    }
  }
  impl<'h> Iterator for HashWindowIt<'h> {
    type Item = Hash;

    fn next(&mut self) -> Option<Self::Item> {
      let offset = self.offset?;

      let cur_value = self.window.get_hash();

      if offset.as_size() == self.input.len() {
        self.offset = None;
      } else {
        debug_assert!(offset.as_size() >= (self.window_len() as usize));
        debug_assert!(offset.0 < self.input_len());
        let (next_char, drop_char) = match self.direction {
          WindowDirection::Left => (
            self.input[offset.as_size()],
            self.input[offset.as_size() - (self.window_len() as usize)],
          ),
          WindowDirection::Right => (
            self.input[self.input.len() - offset.as_size() - 1],
            self.input[self.input.len() - offset.as_size() + (self.window_len() as usize) - 1],
          ),
        };
        self.window.roll(drop_char, next_char);
        unsafe {
          self
            .offset
            .as_mut()
            .unwrap_unchecked()
            .unchecked_increment();
        }
      }

      return Some(cur_value);
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
      let remaining = self.remaining() as usize;
      (remaining, Some(remaining))
    }
  }
  impl<'h> ExactSizeIterator for HashWindowIt<'h> {}
  unsafe impl<'h> iter::TrustedLen for HashWindowIt<'h> {}

  #[cfg(test)]
  mod test {
    use core::mem;

    use super::*;

    #[test]
    fn long_window() {
      let s = b"asdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdfasdf";
      let s: &[u8] = s.as_ref();
      assert_eq!(100, s.len());

      let mut it = HashWindowIt::empty_window(s, WindowDirection::Left);
      it.initialize_window(92);
      assert!(92 > mem::size_of::<HashLen>() * 8);

      let hashes: Vec<_> = it.collect();
      assert_eq!(hashes, vec![
        Hash(9838263505978427426),
        Hash(1229782938247303333),
        Hash(2459565876494606781),
        Hash(4919131752989213662),
        Hash(9838263505978427426),
        Hash(1229782938247303333),
        Hash(2459565876494606781),
        Hash(4919131752989213662),
        Hash(9838263505978427426)
      ]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(92);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![
        Hash(15987178197214944631),
        Hash(13527612320720337748),
        Hash(8608480567731123980),
        Hash(17216961135462248075),
        Hash(15987178197214944631),
        Hash(13527612320720337748),
        Hash(8608480567731123980),
        Hash(17216961135462248075),
        Hash(15987178197214944631)
      ]);
    }

    #[test]
    fn hashes_iterator() {
      let s = b"asdf";
      let s: &[u8] = s.as_ref();

      let mut it = HashWindowIt::empty_window(s, WindowDirection::Left);
      it.initialize_window(2);

      let hashes: Vec<_> = it.collect();
      assert_eq!(hashes, vec![Hash(309), Hash(330), Hash(302)]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(2);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![Hash(304), Hash(315), Hash(327)]);

      let s_r = b"fdsa";
      let s_r: &[u8] = s_r.as_ref();

      let mut it_2r = HashWindowIt::empty_window(s_r, WindowDirection::Left);
      it_2r.initialize_window(2);

      let hashes: Vec<_> = it_2r.collect();
      assert_eq!(hashes, vec![Hash(304), Hash(315), Hash(327)]);

      let mut it_r2r = HashWindowIt::empty_window(s_r, WindowDirection::Right);
      it_r2r.initialize_window(2);

      let hashes: Vec<_> = it_r2r.collect();
      assert_eq!(hashes, vec![Hash(309), Hash(330), Hash(302)]);
    }

    #[test]
    fn single_hash_window() {
      let s = b"asdf";
      let s: &[u8] = s.as_ref();

      let mut it = HashWindowIt::empty_window(s, WindowDirection::Left);
      it.initialize_window(4);

      let hashes: Vec<_> = it.collect();
      assert_eq!(hashes, vec![Hash(1538)]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(4);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![Hash(1543)]);

      let s_r = b"fdsa";
      let s_r: &[u8] = s_r.as_ref();

      let mut it_2r = HashWindowIt::empty_window(s_r, WindowDirection::Left);
      it_2r.initialize_window(4);

      let hashes: Vec<_> = it_2r.collect();
      assert_eq!(hashes, vec![Hash(1543)]);

      let mut it_r2r = HashWindowIt::empty_window(s_r, WindowDirection::Right);
      it_r2r.initialize_window(4);

      let hashes: Vec<_> = it_r2r.collect();
      assert_eq!(hashes, vec![Hash(1538)]);
    }
  }
}

pub mod table {
  use super::hashing;
}
