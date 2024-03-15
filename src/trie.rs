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

use core::{
  alloc::Allocator,
  cell::UnsafeCell,
  hash::{BuildHasher, BuildHasherDefault, Hash},
};

use hashbrown::HashMap;
use rustc_hash::FxHasher;

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct NodeIndex(pub usize);

pub struct PrefixTrie<'n, A>
where A: Allocator
{
  nodes: Vec<Node<u8, &'n [u8], A>, A>,
}

struct Node<K, Src, A>
where A: Allocator
{
  end: Option<Src>,
  branches: HashMap<K, NodeIndex, BuildHasherDefault<FxHasher>, A>,
}

impl<K, Src, A> Node<K, Src, A>
where A: Allocator
{
  pub fn new_in(alloc: A) -> Self {
    Self {
      end: None,
      branches: HashMap::with_hasher_in(BuildHasherDefault::<FxHasher>::default(), alloc),
    }
  }

  pub fn new() -> Self
  where A: Default {
    Self::new_in(A::default())
  }

  pub fn is_empty(&self) -> bool { self.end.is_none() && self.branches.is_empty() }

  pub fn challenge(&self, key: K) -> Option<NodeIndex>
  where K: Hash+Eq {
    self.branches.get(&key).cloned()
  }
}

impl<'n, A> PrefixTrie<'n, A>
where A: Allocator+Clone
{
  pub fn traverse_in(lits: impl IntoIterator<Item=&'n [u8]>, alloc: A) -> Self {
    let mut nodes: UnsafeCell<Vec<Node<u8, &'n [u8], A>, A>> =
      UnsafeCell::new(Vec::with_capacity_in(1, alloc.clone()));
    let ret = Node::new_in(alloc.clone());
    nodes.get_mut().push(ret);

    let mut lits_vec: Vec<(&'n [u8], &'n [u8]), A> = Vec::new_in(alloc.clone());
    for l in lits.into_iter() {
      lits_vec.push((l, l));
    }

    let mut todo: Vec<(NodeIndex, Vec<(&'n [u8], &'n [u8]), A>), A> =
      Vec::with_capacity_in(1, alloc.clone());
    todo.push((NodeIndex(unsafe { &*nodes.get() }.len() - 1), lits_vec));

    while let Some((NodeIndex(cur_node), lits)) = todo.pop() {
      let cur_node = unsafe { &mut *nodes.get() }.get_mut(cur_node).unwrap();
      assert!(cur_node.is_empty());

      let mut branches: HashMap<u8, Vec<(&'n [u8], &'n [u8]), A>, BuildHasherDefault<FxHasher>, A> =
        HashMap::with_hasher_in(BuildHasherDefault::<FxHasher>::default(), alloc.clone());

      for (src, rest) in lits.into_iter() {
        match rest.split_first() {
          None => {
            cur_node.end = Some(src);
          },
          Some((first, rest)) => {
            branches
              .entry(*first)
              .or_insert_with(|| Vec::new_in(alloc.clone()))
              .push((src, rest));
          },
        }
      }

      for (key, rest) in branches.into_iter() {
        let subnode = Node::new_in(alloc.clone());
        unsafe { &mut *nodes.get() }.push(subnode);
        let sub_node = NodeIndex(unsafe { &*nodes.get() }.len() - 1);

        todo.push((sub_node, rest));

        cur_node.branches.insert_unique_unchecked(key, sub_node);
      }
    }

    Self {
      nodes: nodes.into_inner(),
    }
  }

  pub fn traverse(lits: impl IntoIterator<Item=&'n [u8]>) -> Self
  where A: Default {
    Self::traverse_in(lits, A::default())
  }
}
