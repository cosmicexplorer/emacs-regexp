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

use core::hash::{BuildHasher, BuildHasherDefault, Hash};

use indexmap::IndexMap;
use rustc_hash::FxHasher;

#[derive(Default)]
struct SortedMap<K, V, S>(IndexMap<K, V, S>);

impl<K, V, S> SortedMap<K, V, S>
where S: BuildHasher+Default
{
  pub fn sort_entries(entries: impl IntoIterator<Item=(K, V)>) -> Self
  where K: Ord+Eq+Hash+Copy {
    let mut entries: Vec<(K, V)> = entries.into_iter().collect();
    /* TODO: rayon? */
    /* TODO: don't require K to be Copy? */
    entries.sort_unstable_by_key(|v| v.0);
    Self(entries.into_iter().collect())
  }
}

#[derive(Default)]
struct Node<'t, K, ID> {
  end: Option<ID>,
  branches: SortedMap<K, Node<'t, K, ID>, BuildHasherDefault<FxHasher>>,
}

pub struct PrefixTrie<'t> {
  node: Node<'t, u8, &'t [u8]>,
}

impl<'t> PrefixTrie<'t> {
  pub fn traverse_literals(lits: impl IntoIterator<Item=&'t [u8]>) -> Self {
    Self {
      node: Self::recurse_literals(lits.into_iter().map(|l| (l, l))),
    }
  }

  fn recurse_literals(
    lits: impl IntoIterator<Item=(&'t [u8], &'t [u8])>,
  ) -> Node<'t, u8, &'t [u8]> {
    let ret: Node<'t, K, ID> = Default::default();
    let mut todo: Vec<(Node<'t, K, ID>, Vec<(&'t [u8], &'t [u8])>)> =
      vec![(ret, lits.into_iter().collect())];

    while let Some((cur, next)) = todo.pop() {
      assert!(!next.is_empty());

      let mut end: Vec<&'t [u8]> = Vec::new();
      let mut entries: IndexMap<u8, Vec<(&'t [u8], &'t [u8])>> = IndexMap::new();
      for (l, e) in lits.into_iter().map(|l| (l, l.split_first())) {
        match e {
          None => {
            end.push(l);
          },
          Some((key, rest)) => {
            entries.entry(*key).or_default().push((l, rest));
          },
        }
      }
      let entries: Vec<_> = entries.drain(..).collect();
      let mut sorted = SortedMap::sort_entries(entries.iter().map(|(k, _)| (k, Branch::empty())));
    }
  }
}

/* FIXME: for strings too! */
/* impl<'n> PrefixTrie<'n> { */
/* pub fn build(lits: impl IntoIterator<Item=&'n [u8]>) -> Self {} */
/* } */
