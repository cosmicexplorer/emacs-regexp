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

use crate::{continuation, ComponentOffset};

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
  pub remaining_symbols: Vec<SymbolIndex, A>,
}

pub struct LitBlock<A>
where A: Allocator
{
  alphabet: Vec<u8, A>,
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

      let mut add_if_new_symbol = |i: SymbolIndex| match symbol_set.iter().find(|s| **s == i) {
        Some(_) => (),
        None => {
          symbol_set.push(i);
        },
      };

      for byte in lit.into_iter() {
        let index = SymbolIndex(translate_byte(byte));
        add_if_new_symbol(index);
        word.push(index);
      }
      max_len = max_len.max(word.len());
      words.push(Word { word, symbol_set });
    }

    Self {
      alphabet,
      words,
      max_len,
    }
  }

  /* pub fn match_keys */
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct WordIndex(pub usize);

pub enum LeftLitContinuation {
  All,
  Single(WordIndex, ComponentOffset),
}

struct LeftIndexedLiteral<'t, A>
where A: Allocator
{
  base: &'t LitBlock<A>,
  word_index: WordIndex,
  left_offset: ComponentOffset,
}

impl<'t, A> LeftIndexedLiteral<'t, A>
where A: Allocator
{
  fn f();
}
