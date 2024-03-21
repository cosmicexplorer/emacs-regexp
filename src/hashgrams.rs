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
  type WindowLen = u32;

  #[derive(Debug, Copy, Clone, PartialEq, Eq)]
  #[repr(transparent)]
  pub struct Hash(pub(crate) HashLen);

  const SHIFT_FACTOR: u32 = 4;

  impl Hash {
    #[inline(always)]
    pub(crate) const fn new() -> Self { Self(0) }

    #[inline(always)]
    pub(crate) fn extend_byte(byte: HashToken) -> HashLen {
      u64::from_le_bytes([byte, !byte, byte, !byte, byte, !byte, byte, !byte])
    }

    #[inline(always)]
    pub(crate) fn add(&mut self, byte: HashToken) {
      self.0 = self
        .0
        .wrapping_shl(SHIFT_FACTOR)
        .wrapping_add(Self::extend_byte(byte));
    }

    #[inline(always)]
    pub(crate) fn del(&mut self, len: WindowLen, byte: HashToken) {
      debug_assert!(len > 0);
      self.0 = self
        .0
        .wrapping_sub(Self::extend_byte(byte).wrapping_shl((len - 1).wrapping_mul(SHIFT_FACTOR)));
    }

    #[inline(always)]
    pub(crate) fn roll(&mut self, len: WindowLen, old: HashToken, new: HashToken) {
      self.del(len, old);
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
    window_len: WindowLen,
  }

  impl HashWindow {
    #[inline(always)]
    pub const fn new() -> Self {
      Self {
        hash: Hash::new(),
        window_len: 0,
      }
    }

    #[inline(always)]
    pub fn add_next_to_window(&mut self, next: HashToken) {
      self.hash.add(next);
      self.window_len += 1;
    }

    #[inline(always)]
    pub fn roll(&mut self, old: HashToken, new: HashToken) {
      self.hash.roll(self.window_len, old, new);
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
        Hash(15934541573398909606),
        Hash(15144992216158423233),
        Hash(2512202500310636675),
        Hash(3301751857551123348),
        Hash(15934541573398909606),
        Hash(15144992216158423233),
        Hash(2512202500310636675),
        Hash(3301751857551123348),
        Hash(15934541573398909606)
      ]);

      let s2 = b"asdfgasdfasdf";
      let s2: &[u8] = s2.as_ref();
      assert_eq!(13, s2.len());

      let mut it2 = HashWindowIt::empty_window(s2, WindowDirection::Left);
      it2.initialize_window(4);

      let hashes: Vec<_> = it2.collect();
      assert_eq!(hashes, vec![
        Hash(15934541573398909606),
        Hash(14714328930390885063),
        Hash(15360323859042192081),
        Hash(4880850572032096643),
        Hash(4450187286264558484),
        Hash(15934541573398909606),
        Hash(15144992216158423233),
        Hash(2512202500310636675),
        Hash(3301751857551123348),
        Hash(15934541573398909606)
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
        Hash(7642200561588687526),
        Hash(11594918685267904705),
        Hash(1051412655096469635),
        Hash(16822773337949610900),
        Hash(10910125041199403686),
        Hash(8541478137910708417),
        Hash(7536596118509983875),
        Hash(9905244310308529044),
        Hash(10910125041199403686)
      ]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(92);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![
        Hash(14192409407574059409),
        Hash(5717790302609683062),
        Hash(17697839403322819268),
        Hash(6464423775427344563),
        Hash(11197234180395968913),
        Hash(13135218888888889974),
        Hash(7249488267823268548),
        Hash(5311502270820497587),
        Hash(11197234180395968913)
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
        Hash(8254379643877814915),
        Hash(7105944215164379796),
        Hash(5742177143567175590)
      ]);

      let mut it2 = HashWindowIt::empty_window(s2, WindowDirection::Left);
      it2.initialize_window(2);

      let hashes: Vec<_> = it2.collect();
      assert_eq!(hashes, vec![
        Hash(7105944215164379796),
        Hash(5742177143567175590)
      ]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(2);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![
        Hash(3588860714729484740),
        Hash(4809073357737509555),
        Hash(7321275858048148881)
      ]);

      let s_r = b"fdsa";
      let s_r: &[u8] = s_r.as_ref();

      let mut it_2r = HashWindowIt::empty_window(s_r, WindowDirection::Left);
      it_2r.initialize_window(2);

      let hashes: Vec<_> = it_2r.collect();
      assert_eq!(hashes, vec![
        Hash(3588860714729484740),
        Hash(4809073357737509555),
        Hash(7321275858048148881)
      ]);

      let mut it_r2r = HashWindowIt::empty_window(s_r, WindowDirection::Right);
      it_r2r.initialize_window(2);

      let hashes: Vec<_> = it_r2r.collect();
      assert_eq!(hashes, vec![
        Hash(8254379643877814915),
        Hash(7105944215164379796),
        Hash(5742177143567175590)
      ]);
    }

    #[test]
    fn single_hash_window() {
      let s = b"asdf";
      let s: &[u8] = s.as_ref();

      let mut it = HashWindowIt::empty_window(s, WindowDirection::Left);
      it.initialize_window(4);

      let hashes: Vec<_> = it.collect();
      assert_eq!(hashes, vec![Hash(15934541573398909606)]);

      let mut it_r = HashWindowIt::empty_window(s, WindowDirection::Right);
      it_r.initialize_window(4);

      let hashes: Vec<_> = it_r.collect();
      assert_eq!(hashes, vec![Hash(3732415143318661521)]);

      let s_r = b"fdsa";
      let s_r: &[u8] = s_r.as_ref();

      let mut it_2r = HashWindowIt::empty_window(s_r, WindowDirection::Left);
      it_2r.initialize_window(4);

      let hashes: Vec<_> = it_2r.collect();
      assert_eq!(hashes, vec![Hash(3732415143318661521)]);

      let mut it_r2r = HashWindowIt::empty_window(s_r, WindowDirection::Right);
      it_r2r.initialize_window(4);

      let hashes: Vec<_> = it_r2r.collect();
      assert_eq!(hashes, vec![Hash(15934541573398909606)]);
    }
  }
}

pub mod table {
  use super::hashing;
}
