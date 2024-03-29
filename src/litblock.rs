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

pub struct LitBlock<A>
where A: Allocator
{
  alphabet: Vec<u8, A>,
  words: Vec<Vec<usize, A>, A>,
}

impl<A> LitBlock<A>
where A: Allocator
{
  pub fn from_literals(lits: impl IntoIterator<Item=impl IntoIterator<Item=u8>>, alloc: A) -> Self
  where A: Clone {
    let mut alphabet: Vec<u8, A> = Vec::new_in(alloc.clone());

    let mut translate_byte = |byte: u8| -> usize {
      match alphabet.iter().enumerate().find(|(i, b)| **b == byte) {
        Some((i, _)) => i,
        None => {
          alphabet.push(byte);
          alphabet.len() - 1
        },
      }
    };

    let mut words: Vec<Vec<usize, A>, A> = Vec::new_in(alloc.clone());

    for lit in lits.into_iter() {
      let mut word: Vec<usize, A> = Vec::new_in(alloc.clone());
      for byte in lit.into_iter() {
        let index = translate_byte(byte);
        word.push(index);
      }
      words.push(word);
    }

    Self { alphabet, words }
  }
}
