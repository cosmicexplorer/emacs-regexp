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
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>. */

//! Rolling window hash iterators.

pub mod hashing {
  use core::{iter, mem::MaybeUninit};

  use crate::{ComponentLen, ComponentOffset};

  type HashToken = u8;
  type HashLen = u64;
  type WindowLen = u32;

  #[derive(Debug, Copy, Clone, PartialEq, Eq)]
  #[repr(transparent)]
  pub struct Hash(pub(crate) HashLen);

  /* TODO: if we make this 16 (= u64 / n = 4), the shift cancels out and we can
   * entirely avoid the "del" operation for size 4 windows!! This is a
   * "self-anihillating recursive method"! */
  const SHIFT_FACTOR: u32 = 19;

  impl Hash {
    #[inline(always)]
    pub(crate) const fn new() -> Self { Self(0) }

    #[inline(always)]
    pub(crate) const fn extend_byte(byte: HashToken) -> HashLen {
      u64::from_le_bytes([byte, !byte, byte, !byte, byte, !byte, byte, !byte])
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, byte: HashToken) {
      self.0 = self.0.wrapping_shl(SHIFT_FACTOR) ^ Self::extend_byte(byte);
    }

    #[inline(always)]
    pub(crate) fn del(&mut self, shift_len: WindowLen, byte: HashToken) {
      self.0 ^= Self::extend_byte(byte).wrapping_shl(shift_len);
    }

    #[inline(always)]
    pub(crate) fn roll(&mut self, shift_len: WindowLen, old: HashToken, new: HashToken) {
      self.del(shift_len, old);
      self.add(new);
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum WindowDirection {
    Left,
    Right,
  }

  #[derive(Debug, Clone)]
  struct HashWindow {
    hash: Hash,
    shift_len: WindowLen,
  }

  impl HashWindow {
    #[inline(always)]
    pub const fn new() -> Self {
      Self {
        hash: Hash::new(),
        shift_len: 0,
      }
    }

    #[inline(always)]
    pub fn add_next_to_window(&mut self, next: HashToken) {
      self.hash.add(next);
      self.shift_len += SHIFT_FACTOR;
    }

    #[inline(always)]
    pub fn roll(&mut self, old: HashToken, new: HashToken) {
      self.hash.roll(self.shift_len, old, new);
    }

    #[inline(always)]
    pub fn get_hash(&self) -> Hash { self.hash }

    #[inline]
    pub fn initialize_window_at_border(
      &mut self,
      entire_input: &[HashToken],
      direction: WindowDirection,
      window_len: WindowLen,
    ) -> ComponentOffset {
      assert!(
        (window_len as usize) <= entire_input.len(),
        "TODO: hash window must be no larger than input length!"
      );
      let mut offset = ComponentOffset::zero();
      assert_ne!(window_len, 0, "empty hash window not supported!");
      match direction {
        WindowDirection::Left => {
          for b in entire_input.iter().copied().take(window_len as usize) {
            self.add_next_to_window(b);
            unsafe {
              offset.unchecked_increment();
            }
          }
        },
        WindowDirection::Right => {
          for b in entire_input.iter().rev().copied().take(window_len as usize) {
            self.add_next_to_window(b);
            unsafe {
              offset.unchecked_increment();
            }
          }
        },
      };
      /* NB: This allows us to avoid a subtract operation in the Hash::del()
       * method. */
      self.shift_len -= SHIFT_FACTOR;
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
    window_len: Option<WindowLen>,
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
    pub fn window_len(&self) -> WindowLen { self.window_len.unwrap() }

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
    pub fn initialize_window(&mut self, window_len: WindowLen) {
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
    fn four_window() {
      let s = b"asdfasdfasdf";
      let s: &[u8] = s.as_ref();
      assert_eq!(12, s.len());

      let mut it = HashWindowIt::empty_window(s, WindowDirection::Left);
      it.initialize_window(4);

      let hashes: Vec<_> = it.collect();
      assert_eq!(hashes, vec![
        Hash(11286406054717856102),
        Hash(7670628888473607777),
        Hash(17210830329770380403),
        Hash(12438767043388152676),
        Hash(11286406054717856102),
        Hash(7670628888473607777),
        Hash(17210830329770380403),
        Hash(12438767043388152676),
        Hash(11286406054717856102)
      ]);

      let s2 = b"asdfgasdfasdf";
      let s2: &[u8] = s2.as_ref();
      assert_eq!(13, s2.len());

      let mut it2 = HashWindowIt::empty_window(s2, WindowDirection::Left);
      it2.initialize_window(4);

      let hashes: Vec<_> = it2.collect();
      assert_eq!(hashes, vec![
        Hash(11286406054717856102),
        Hash(7815304818856532071),
        Hash(14770404751692111457),
        Hash(12292969630548069491),
        Hash(12582882231464008548),
        Hash(11286406054717856102),
        Hash(7670628888473607777),
        Hash(17210830329770380403),
        Hash(12438767043388152676),
        Hash(11286406054717856102)
      ]);
    }

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
        Hash(11286406054717856102),
        Hash(10118016390498721377),
        Hash(1814617805841730675),
        Hash(12038385073892662116),
        Hash(8396252233597360486),
        Hash(12621013929200557665),
        Hash(9308607585786236019),
        Hash(12038385073892662116),
        Hash(8396252233597360486)
      ]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(92);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![
        Hash(16779045510005235297),
        Hash(2945601288652364134),
        Hash(3112776078462327652),
        Hash(2415191569027271795),
        Hash(12035020511624404577),
        Hash(15289668250356324710),
        Hash(12624378491468815204),
        Hash(2415191569027271795),
        Hash(12035020511624404577)
      ]);
    }

    #[test]
    fn hashes_iterator() {
      let s = b"asdf";
      let s: &[u8] = s.as_ref();
      let s2 = b"sdf";
      let s2: &[u8] = s2.as_ref();

      let mut it = HashWindowIt::empty_window(s, WindowDirection::Left);
      it.initialize_window(2);

      let hashes: Vec<_> = it.collect();
      assert_eq!(hashes, vec![
        Hash(9187201950435478643),
        Hash(17940362863843253092),
        Hash(4774451407313344870)
      ]);

      let mut it2 = HashWindowIt::empty_window(s2, WindowDirection::Left);
      it2.initialize_window(2);

      let hashes: Vec<_> = it2.collect();
      assert_eq!(hashes, vec![
        Hash(17940362863843253092),
        Hash(4774451407313344870)
      ]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(2);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![
        Hash(5787213827046415204),
        Hash(6293595036912422003),
        Hash(18302063728033111649)
      ]);

      let s_r = b"fdsa";
      let s_r: &[u8] = s_r.as_ref();

      let mut it_2r = HashWindowIt::empty_window(s_r, WindowDirection::Left);
      it_2r.initialize_window(2);

      let hashes: Vec<_> = it_2r.collect();
      assert_eq!(hashes, vec![
        Hash(5787213827046415204),
        Hash(6293595036912422003),
        Hash(18302063728033111649)
      ]);

      let mut it_r2r = HashWindowIt::empty_window(s_r, WindowDirection::Right);
      it_r2r.initialize_window(2);

      let hashes: Vec<_> = it_r2r.collect();
      assert_eq!(hashes, vec![
        Hash(9187201950435478643),
        Hash(17940362863843253092),
        Hash(4774451407313344870)
      ]);
    }

    #[test]
    fn single_hash_window() {
      let s = b"asdf";
      let s: &[u8] = s.as_ref();

      let mut it = HashWindowIt::empty_window(s, WindowDirection::Left);
      it.initialize_window(4);

      let hashes: Vec<_> = it.collect();
      assert_eq!(hashes, vec![Hash(11286406054717856102)]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(4);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![Hash(16779045510005235297)]);

      let s_r = b"fdsa";
      let s_r: &[u8] = s_r.as_ref();

      let mut it_2r = HashWindowIt::empty_window(s_r, WindowDirection::Left);
      it_2r.initialize_window(4);

      let hashes: Vec<_> = it_2r.collect();
      assert_eq!(hashes, vec![Hash(16779045510005235297)]);

      let mut it_r2r = HashWindowIt::empty_window(s_r, WindowDirection::Right);
      it_r2r.initialize_window(4);

      let hashes: Vec<_> = it_r2r.collect();
      assert_eq!(hashes, vec![Hash(11286406054717856102)]);
    }
  }
}

pub mod table {
  use super::hashing;
}
