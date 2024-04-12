/* Description: SIMD search for sets of literal byte strings.

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

//! SIMD search for sets of literal byte strings.

use core::{alloc::Allocator, simd::prelude::*};

use ::alloc::vec::Vec;

use crate::{continuation, ComponentOffset, IntraComponentInterval, UnanchoredMatchResult};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct SymbolIndex(pub usize);

pub struct Word<A>
where A: Allocator
{
  /// The actual sequence of tokens in the word, in order.
  pub word: Vec<SymbolIndex, A>,
  /// All the unique symbols contained in the word, deduplicated and in order of
  /// appearance from left to right.
  pub symbol_set: Vec<SymbolIndex, A>,
}

pub struct DerivedWord<'t, A>
where A: Allocator
{
  /// The remaining sequence of tokens in the word after left- or
  /// right-truncation.
  pub remaining_word: &'t [SymbolIndex],
  /// The possibly-reduced sequence of symbols remaining in the word.
  /* FIXME: use some sort of immutable set structure to avoid allocation for subsets! */
  pub remaining_symbols: Vec<SymbolIndex, A>,
}

#[inline(always)]
fn add_if_new_symbol<A>(symbol_set: &mut Vec<SymbolIndex, A>, i: SymbolIndex)
where A: Allocator {
  match symbol_set.iter().find(|s| **s == i) {
    Some(_) => (),
    None => {
      symbol_set.push(i);
    },
  }
}

impl<'t, A> DerivedWord<'t, A>
where A: Allocator
{
  pub fn left_truncate(word: &'t Word<A>, offset: ComponentOffset, alloc: A) -> Self {
    let ComponentOffset(offset) = offset;
    let remaining_word: &'t [SymbolIndex] = &word.word[offset..];

    Self::from_truncated(remaining_word, alloc)
  }

  pub fn right_truncate(word: &'t Word<A>, offset: ComponentOffset, alloc: A) -> Self {
    let ComponentOffset(offset) = offset;
    let remaining_word: &'t [SymbolIndex] = &word.word[..(word.word.len() - offset)];

    Self::from_truncated(remaining_word, alloc)
  }

  fn from_truncated(remaining_word: &'t [SymbolIndex], alloc: A) -> Self {
    let mut remaining_symbols: Vec<SymbolIndex, A> = Vec::new_in(alloc);

    for s in remaining_word.iter().copied() {
      add_if_new_symbol(&mut remaining_symbols, s);
    }
    Self {
      remaining_word,
      remaining_symbols,
    }
  }
}

pub struct LitBlock<A>
where A: Allocator
{
  alphabet: Vec<u8, A>,
  symbol_masks: Vec<Simd<u8, 32>, A>,
  words: Vec<Word<A>, A>,
  max_len: usize,
}

impl<A> LitBlock<A>
where A: Allocator
{
  pub fn from_literals(lits: impl IntoIterator<Item=impl IntoIterator<Item=u8>>, alloc: A) -> Self
  where A: Clone {
    let mut alphabet: Vec<u8, A> = Vec::new_in(alloc.clone());

    let mut translate_byte = |byte: u8| -> usize {
      match alphabet.iter().enumerate().find(|(_, b)| **b == byte) {
        Some((i, _)) => i,
        None => {
          alphabet.push(byte);
          alphabet.len() - 1
        },
      }
    };

    let mut words: Vec<Word<A>, A> = Vec::new_in(alloc.clone());
    let mut max_len: usize = 0;

    for lit in lits.into_iter() {
      let mut word: Vec<SymbolIndex, A> = Vec::new_in(alloc.clone());
      let mut symbol_set: Vec<SymbolIndex, A> = Vec::new_in(alloc.clone());

      for byte in lit.into_iter() {
        let index = SymbolIndex(translate_byte(byte));
        add_if_new_symbol(&mut symbol_set, index);
        word.push(index);
      }
      max_len = max_len.max(word.len());
      words.push(Word { word, symbol_set });
    }

    let symbol_masks = Self::alphabet_masks(&alphabet, alloc);
    Self {
      alphabet,
      symbol_masks,
      words,
      max_len,
    }
  }

  fn alphabet_masks(alphabet: &Vec<u8, A>, alloc: A) -> Vec<Simd<u8, 32>, A> {
    let mut ret: Vec<Simd<u8, 32>, A> = Vec::with_capacity_in(alphabet.len(), alloc);

    for byte in alphabet.iter().copied() {
      ret.push(Simd::splat(byte));
    }
    ret
  }

  pub fn match_inner(&self, haystack: &[u8], alloc: A) {
    /* FIXME: cover prefix/suffix! */
    let (_prefix, middle, _suffix): (&[u8], &[Simd<u8, 32>], &[u8]) = haystack.as_simd();

    let alpha_len = self.symbol_masks.len();
    /* FIXME: avoid allocating in match! */
    let mut alpha_matches: Vec<Simd<u8, 32>, A> = Vec::with_capacity_in(alpha_len, alloc);
    alpha_matches.resize(alpha_len, Simd::splat(0x0));

    for window in middle.iter() {
      /* Identify all tokens. */
      for i in 0..alpha_len {
        unsafe {
          *alpha_matches.get_unchecked_mut(i) = window & self.symbol_masks.get_unchecked(i);
        }
      }

      /* Iterate over each word and shift the masked input to match a
       * contiguous literal substring. */
      for Word { word, .. } in self.words.iter() {
        let mut string: Simd<u8, 32> = Simd::splat(u8::MAX);
        for (shift, SymbolIndex(sym)) in word.iter().copied().enumerate() {
          assert!(
            shift <= (u8::MAX as usize),
            "TODO: literals longer than u8::MAX are unsupported!"
          );
          let shift = shift as u8;
          let symbol_matches: &Simd<u8, 32> = unsafe { alpha_matches.get_unchecked(sym) };
          string &= symbol_matches >> shift;
        }
      }

      /* FIXME: cover literals across SIMD regions! */
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct WordIndex(pub usize);

pub struct LeftLitContinuation {
  word_index: WordIndex,
  offset: ComponentOffset,
}

impl LeftLitContinuation {}

struct LeftIndexedLiteral<'t, A>
where A: Allocator
{
  derived_word: DerivedWord<'t, A>,
}

impl<'t, A> LeftIndexedLiteral<'t, A> where A: Allocator {}
