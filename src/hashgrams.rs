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
GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License
along with this program.  If not, see <https://www.gnu.org/licenses/>. */

use core::alloc::Allocator;

use hashbrown::HashTable;

use crate::{ComponentLen, ComponentOffset};

type HashToken = u8;
type HashLen = u64;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Hash(pub(crate) HashLen);

impl Hash {
  #[inline(always)]
  pub(crate) const fn new() -> Self { Self(0) }

  #[inline(always)]
  pub(crate) fn add(&mut self, byte: HashToken) {
    self.0 = self.0.wrapping_shl(1).wrapping_add(u64::from(byte));
  }

  #[inline(always)]
  pub(crate) fn del(&mut self, factor: HashLen, byte: HashToken) {
    self.0 = self.0.wrapping_sub(u64::from(byte).wrapping_mul(factor));
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
    self.hash_2pow = self.hash_2pow.wrapping_shl(1);
  }

  #[inline(always)]
  pub fn roll(&mut self, old: HashToken, new: HashToken) {
    self.hash.roll(self.hash_2pow, old, new);
  }

  #[inline(always)]
  pub fn get_hash(&self) -> Hash { self.hash }

  #[inline]
  pub fn initialize_window_at_border<const N: ComponentLen>(
    &mut self,
    entire_input: &[HashToken],
    direction: WindowDirection,
  ) -> ComponentOffset {
    assert!(
      N as usize <= entire_input.len(),
      "TODO: hash window must be no larger than input length!"
    );
    let mut offset = ComponentOffset(0);
    assert_ne!(N, 0, "empty hash window not supported!");
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
        for b in rest.iter().copied().take((N as usize) - 1) {
          self.add_next_to_window(b);
          unsafe {
            offset.unchecked_increment();
          }
        }
      },
      WindowDirection::Right => {
        for b in rest.iter().rev().copied().take((N as usize) - 1) {
          self.add_next_to_window(b);
          unsafe {
            offset.unchecked_increment();
          }
        }
      },
    };
    offset
  }
}

/* TODO: consider vectorized version! see e.g. https://github.com/ashvardanian/StringZilla/blob/bc1869a85293ff5aa6e5075475263002c43648eb/include/stringzilla/stringzilla.h#L3682-L3805 */
pub struct HashWindowIt<'h, const N: ComponentLen> {
  input: &'h [HashToken],
  offset: Option<ComponentOffset>,
  direction: WindowDirection,
  window: HashWindow,
}
impl<'h, const N: ComponentLen> HashWindowIt<'h, N> {
  #[inline(always)]
  pub const fn empty_window(input: &'h [HashToken], direction: WindowDirection) -> Self {
    Self {
      input,
      offset: None,
      direction,
      window: HashWindow::new(),
    }
  }

  #[inline]
  pub fn initialize_window(&mut self) {
    self.offset = Some(
      self
        .window
        .initialize_window_at_border::<N>(self.input, self.direction),
    );
  }
}
impl<'h, const N: ComponentLen> Iterator for HashWindowIt<'h, N> {
  type Item = Hash;

  fn next(&mut self) -> Option<Self::Item> {
    let offset = self.offset?;

    let cur_value = self.window.get_hash();

    if offset.as_size() == self.input.len() {
      self.offset = None;
    } else {
      debug_assert!(offset.as_size() >= N as usize);
      debug_assert!(offset.as_size() < self.input.len());
      let (next_char, drop_char) = match self.direction {
        WindowDirection::Left => (
          self.input[offset.as_size()],
          self.input[offset.as_size() - (N as usize)],
        ),
        WindowDirection::Right => (
          self.input[self.input.len() - offset.as_size() - 1],
          self.input[self.input.len() - offset.as_size() + (N as usize) - 1],
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
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn hashes_iterator() {
    let s = b"asdf";
    let s: &[u8] = s.as_ref();

    let mut it = HashWindowIt::<2>::empty_window(s, WindowDirection::Left);
    it.initialize_window();

    let hashes: Vec<_> = it.collect();
    assert_eq!(hashes, vec![Hash(309), Hash(330), Hash(302)]);

    let mut it_r = HashWindowIt::<2>::empty_window(s, WindowDirection::Right);
    it_r.initialize_window();

    let hashes: Vec<_> = it_r.collect();
    assert_eq!(hashes, vec![Hash(304), Hash(315), Hash(327)]);

    let s_r = b"fdsa";
    let s_r: &[u8] = s_r.as_ref();

    let mut it_2r = HashWindowIt::<2>::empty_window(s_r, WindowDirection::Left);
    it_2r.initialize_window();

    let hashes: Vec<_> = it_2r.collect();
    assert_eq!(hashes, vec![Hash(304), Hash(315), Hash(327)]);

    let mut it_r2r = HashWindowIt::<2>::empty_window(s_r, WindowDirection::Right);
    it_r2r.initialize_window();

    let hashes: Vec<_> = it_r2r.collect();
    assert_eq!(hashes, vec![Hash(309), Hash(330), Hash(302)]);
  }

  #[test]
  fn single_hash_window() {
    let s = b"asdf";
    let s: &[u8] = s.as_ref();

    let mut it = HashWindowIt::<4>::empty_window(s, WindowDirection::Left);
    it.initialize_window();

    let hashes: Vec<_> = it.collect();
    assert_eq!(hashes, vec![Hash(1538)]);

    let mut it_r = HashWindowIt::<4>::empty_window(s, WindowDirection::Right);
    it_r.initialize_window();

    let hashes: Vec<_> = it_r.collect();
    assert_eq!(hashes, vec![Hash(1543)]);

    let s_r = b"fdsa";
    let s_r: &[u8] = s_r.as_ref();

    let mut it_2r = HashWindowIt::<4>::empty_window(s_r, WindowDirection::Left);
    it_2r.initialize_window();

    let hashes: Vec<_> = it_2r.collect();
    assert_eq!(hashes, vec![Hash(1543)]);

    let mut it_r2r = HashWindowIt::<4>::empty_window(s_r, WindowDirection::Right);
    it_r2r.initialize_window();

    let hashes: Vec<_> = it_r2r.collect();
    assert_eq!(hashes, vec![Hash(1538)]);
  }
}
