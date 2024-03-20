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

use core::{alloc::Allocator, hash::BuildHasherDefault, mem};

use hashbrown::HashTable;
use memchr::memmem;
use rustc_hash::FxHasher;
use xxhash_rust::xxh3::xxh3_64;

use crate::{
  continuation::{self, Resumable as _},
  state, trie, ComponentOffset, DoublyAnchoredMatcher, IntraComponentInterval,
  LeftAnchoredAutomaton, LeftAnchoredMatchResult, LeftAnchoredMatcher, RightAnchoredAutomaton,
  RightAnchoredMatchResult, RightAnchoredMatcher, UnanchoredMatchResult, UnanchoredMatcher,
};

pub mod doubly_anchored {
  use super::*;

  pub struct DoublyAnchoredSingleLiteral<'n> {
    lit: &'n [u8],
  }
  impl<'n> DoublyAnchoredSingleLiteral<'n> {
    pub fn new(lit: &'n [u8]) -> Self { Self { lit } }
  }
  impl<'n> DoublyAnchoredMatcher<'n> for DoublyAnchoredSingleLiteral<'n> {
    type I = [u8];
    type S = ();
    type X = ();
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=Self::S>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      let i = i.as_ref();
      if i == self.lit { Some(()) } else { None }.into_iter()
    }
  }

  type XXH3Output64 = u64;

  pub struct DoublyAnchoredMultipleLiteralsXXH3Vec<'n, A>
  where A: Allocator
  {
    lits_with_hashes: Vec<(XXH3Output64, &'n [u8]), A>,
  }
  impl<'n, A> DoublyAnchoredMultipleLiteralsXXH3Vec<'n, A>
  where A: Allocator
  {
    pub fn new_in(lits: impl IntoIterator<Item=&'n [u8]>, alloc: A) -> Self {
      let mut lits_with_hashes: Vec<(XXH3Output64, &'n [u8]), A> = Vec::new_in(alloc);
      for l in lits.into_iter() {
        let h = xxh3_64(l);
        lits_with_hashes.push((h, l));
      }
      Self { lits_with_hashes }
    }
    pub fn new(lits: impl IntoIterator<Item=&'n [u8]>) -> Self
    where A: Default {
      Self::new_in(lits, A::default())
    }
  }
  impl<'n, A> DoublyAnchoredMatcher<'n> for DoublyAnchoredMultipleLiteralsXXH3Vec<'n, A>
  where A: Allocator
  {
    type I = [u8];
    type S = &'n [u8];
    type X = ();
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=Self::S>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      let i = i.as_ref();
      let h = xxh3_64(i);
      self
        .lits_with_hashes
        .iter()
        .filter(move |(h2, _)| h == *h2)
        .map(|(_, l)| *l)
        .filter(move |l| *l == i)
    }
  }

  pub struct DoublyAnchoredMultipleLiteralsXXH3Set<'n, A>
  where A: Allocator
  {
    lits_with_hashes: HashTable<&'n [u8], A>,
  }
  impl<'n, A> DoublyAnchoredMultipleLiteralsXXH3Set<'n, A>
  where A: Allocator
  {
    pub fn new_in(lits: impl IntoIterator<Item=&'n [u8]>, alloc: A) -> Self {
      let mut lits_with_hashes: HashTable<&'n [u8], A> = HashTable::new_in(alloc);
      for l in lits.into_iter() {
        let h = xxh3_64(l);
        let _ = lits_with_hashes
          .entry(h, |l2| l == *l2, |l2| xxh3_64(l2))
          .or_insert(l);
      }
      Self { lits_with_hashes }
    }
    pub fn new(lits: impl IntoIterator<Item=&'n [u8]>) -> Self
    where A: Default {
      Self::new_in(lits, A::default())
    }
  }
  impl<'n, A> DoublyAnchoredMatcher<'n> for DoublyAnchoredMultipleLiteralsXXH3Set<'n, A>
  where A: Allocator
  {
    type I = [u8];
    type S = &'n [u8];
    type X = ();
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=Self::S>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      let i = i.as_ref();
      let h = xxh3_64(i);
      self
        .lits_with_hashes
        .find(h, |l| *l == i)
        .map(|l| *l)
        .into_iter()
    }
  }
}

enum PrefixNodeState<'t, 'n, C, A>
where A: Allocator
{
  NodeMinusEndState(&'t trie::Node<u8, &'n [u8], A>, C, ComponentOffset),
  Empty,
}

pub mod left_anchored {
  use super::*;

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct LeftSingleLiteralContinuation {
    pub offset: usize,
  }
  impl continuation::Continuation for LeftSingleLiteralContinuation {}

  #[derive(Debug, Copy, Clone)]
  pub struct LeftAnchoredSingleLiteralAutomaton<'n> {
    lit: &'n [u8],
  }
  impl<'n> LeftAnchoredSingleLiteralAutomaton<'n> {
    pub fn new(lit: &'n [u8]) -> Self { Self { lit } }
  }
  impl<'n> continuation::Resumable<'n, LeftAnchoredSingleLiteralMatcher<'n>>
    for LeftAnchoredSingleLiteralAutomaton<'n>
  {
    type C = LeftSingleLiteralContinuation;

    fn top(&self) -> Self::C { LeftSingleLiteralContinuation { offset: 0 } }

    fn index<'s>(&'s self, c: Self::C) -> impl Into<LeftAnchoredSingleLiteralMatcher<'n>>+'s
    where 's: 'n {
      LeftAnchoredSingleLiteralMatcher {
        base: *self,
        cont: c,
      }
    }
  }
  impl<'n> LeftAnchoredAutomaton<'n> for LeftAnchoredSingleLiteralAutomaton<'n> {
    type O = LeftAnchoredSingleLiteralMatcher<'n>;
  }

  #[derive(Debug, Copy, Clone)]
  pub struct LeftAnchoredSingleLiteralMatcher<'n> {
    base: LeftAnchoredSingleLiteralAutomaton<'n>,
    cont: LeftSingleLiteralContinuation,
  }
  impl<'n> LeftAnchoredMatcher<'n> for LeftAnchoredSingleLiteralMatcher<'n> {
    type I = [u8];
    type S = ();
    type X = ();
    type C = LeftSingleLiteralContinuation;
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=LeftAnchoredMatchResult<Self::S, Self::C>>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      let Self {
        base,
        cont: LeftSingleLiteralContinuation { offset },
      } = self;
      let lit = &base.lit[*offset..];
      if i.len() >= lit.len() {
        if i.starts_with(lit) {
          Some(LeftAnchoredMatchResult::CompleteMatch(
            (),
            ComponentOffset(lit.len().try_into().unwrap()),
          ))
        } else {
          None
        }
      } else {
        if lit.starts_with(i) {
          Some(LeftAnchoredMatchResult::PartialMatch(
            LeftSingleLiteralContinuation {
              offset: offset + i.len(),
            },
          ))
        } else {
          None
        }
      }
      .into_iter()
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct LeftPrefixContinuation {
    pub state: trie::NodeIndex,
  }
  impl continuation::Continuation for LeftPrefixContinuation {}


  #[derive(Debug, Clone)]
  pub struct LeftAnchoredMultipleLiteralsAutomaton<'n, A>
  where A: Allocator
  {
    trie: trie::PrefixTrie<'n, A>,
  }
  impl<'n, A> LeftAnchoredMultipleLiteralsAutomaton<'n, A>
  where A: Allocator+Clone
  {
    pub fn new_in(lits: impl IntoIterator<Item=&'n [u8]>, alloc: A) -> Self {
      Self {
        trie: trie::PrefixTrie::traverse_in(lits, trie::PrefixDirection::Left, alloc),
      }
    }

    pub fn new(lits: impl IntoIterator<Item=&'n [u8]>) -> Self
    where A: Default {
      Self::new_in(lits, A::default())
    }
  }
  impl<'t, 'n, A> continuation::Resumable<'t, LeftAnchoredMultipleLiteralsMatcher<'t, 'n, A>>
    for LeftAnchoredMultipleLiteralsAutomaton<'n, A>
  where
    A: Allocator,
    't: 'n,
    'n: 't,
  {
    type C = LeftPrefixContinuation;

    fn top(&self) -> Self::C {
      LeftPrefixContinuation {
        state: trie::PrefixTrie::<A>::get_top_node(),
      }
    }

    fn index<'s>(
      &'s self,
      c: Self::C,
    ) -> impl Into<LeftAnchoredMultipleLiteralsMatcher<'t, 'n, A>>+'s
    where
      's: 't,
    {
      let LeftPrefixContinuation { state } = c;
      let node = self.trie.get_node_by_index(state).unwrap();
      LeftAnchoredMultipleLiteralsMatcher {
        automaton: self,
        cont: c,
        node,
      }
    }
  }
  impl<'t, 'n, A> LeftAnchoredAutomaton<'t> for LeftAnchoredMultipleLiteralsAutomaton<'n, A>
  where
    A: Allocator+'t,
    't: 'n,
    'n: 't,
  {
    type O = LeftAnchoredMultipleLiteralsMatcher<'t, 'n, A>;
  }


  struct LeftPrefixIt<'t, 'n, 'h, A>
  where A: Allocator
  {
    automaton: &'t LeftAnchoredMultipleLiteralsAutomaton<'n, A>,
    input: &'h [u8],
    node_state: PrefixNodeState<'t, 'n, LeftPrefixContinuation, A>,
  }
  impl<'t, 'n, 'h, A> LeftPrefixIt<'t, 'n, 'h, A>
  where A: Allocator
  {
    pub fn from_automaton_and_input_and_start_node(
      automaton: &'t LeftAnchoredMultipleLiteralsAutomaton<'n, A>,
      input: &'h [u8],
      cont: LeftPrefixContinuation,
      start_node: &'t trie::Node<u8, &'n [u8], A>,
    ) -> Self {
      Self {
        automaton,
        input,
        /* Empty literals are not allowed, so we discount any possible end state from any start
         * state. This avoids double-counting end states. */
        node_state: PrefixNodeState::NodeMinusEndState(start_node, cont, ComponentOffset(0)),
      }
    }
  }
  impl<'t, 'n, 'h, A> Iterator for LeftPrefixIt<'t, 'n, 'h, A>
  where
    A: Allocator,
    't: 'n,
  {
    type Item = LeftAnchoredMatchResult<&'n [u8], LeftPrefixContinuation>;

    fn next(&mut self) -> Option<Self::Item> {
      let (mut cur_trie_node, mut cont, mut offset) =
      /* Replace the state with empty upon each iteration. */
      match mem::replace(&mut self.node_state, PrefixNodeState::Empty) {
        PrefixNodeState::Empty => return None,
        PrefixNodeState::NodeMinusEndState(node, cont, offset) => (node, cont, offset),
      };

      let remaining_input = &self.input[offset.as_size()..];
      for token in remaining_input.iter() {
        match cur_trie_node.challenge(*token) {
          /* Prefix match failed! We are TOTALLY done with iteration! */
          None => return None,
          /* Succeeded! Let's continue. */
          Some(next_index) => {
            offset.checked_increment();
            cont = LeftPrefixContinuation { state: next_index };

            let LeftAnchoredMultipleLiteralsMatcher {
              node: next_node, ..
            } = self.automaton.index(cont).into();

            if let Some(id) = next_node.end() {
              self.node_state = PrefixNodeState::NodeMinusEndState(next_node, cont, offset);
              return Some(LeftAnchoredMatchResult::CompleteMatch(id, offset));
            }

            cur_trie_node = next_node;
          },
        }
      }

      /* If we can't possibly consume any more input, then exit here without
       * producing any continuation. */
      if cur_trie_node.is_branchless() {
        return None;
      }

      Some(LeftAnchoredMatchResult::PartialMatch(cont))
    }
  }

  #[derive(Debug, Copy, Clone)]
  pub struct LeftAnchoredMultipleLiteralsMatcher<'t, 'n, A>
  where A: Allocator
  {
    automaton: &'t LeftAnchoredMultipleLiteralsAutomaton<'n, A>,
    cont: LeftPrefixContinuation,
    node: &'t trie::Node<u8, &'n [u8], A>,
  }
  impl<'t, 'n, A> LeftAnchoredMatcher<'n> for LeftAnchoredMultipleLiteralsMatcher<'t, 'n, A>
  where A: Allocator
  {
    type I = [u8];
    type S = &'n [u8];
    type X = ();
    type C = LeftPrefixContinuation;
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=LeftAnchoredMatchResult<Self::S, Self::C>>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      assert!(!i.is_empty());
      LeftPrefixIt::from_automaton_and_input_and_start_node(self.automaton, i, self.cont, self.node)
    }
  }
}

pub mod right_anchored {
  use super::*;

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct RightSingleLiteralContinuation {
    pub offset: usize,
  }
  impl continuation::Continuation for RightSingleLiteralContinuation {}

  #[derive(Debug, Copy, Clone)]
  pub struct RightAnchoredSingleLiteralAutomaton<'n> {
    lit: &'n [u8],
  }
  impl<'n> RightAnchoredSingleLiteralAutomaton<'n> {
    pub fn new(lit: &'n [u8]) -> Self { Self { lit } }
  }
  impl<'n> continuation::Resumable<'n, RightAnchoredSingleLiteralMatcher<'n>>
    for RightAnchoredSingleLiteralAutomaton<'n>
  {
    type C = RightSingleLiteralContinuation;

    fn top(&self) -> Self::C { RightSingleLiteralContinuation { offset: 0 } }

    fn index<'s>(&'s self, c: Self::C) -> impl Into<RightAnchoredSingleLiteralMatcher<'n>>+'s
    where 's: 'n {
      RightAnchoredSingleLiteralMatcher {
        base: *self,
        cont: c,
      }
    }
  }
  impl<'n> RightAnchoredAutomaton<'n> for RightAnchoredSingleLiteralAutomaton<'n> {
    type O = RightAnchoredSingleLiteralMatcher<'n>;
  }

  #[derive(Debug, Copy, Clone)]
  pub struct RightAnchoredSingleLiteralMatcher<'n> {
    base: RightAnchoredSingleLiteralAutomaton<'n>,
    cont: RightSingleLiteralContinuation,
  }
  impl<'n> RightAnchoredMatcher<'n> for RightAnchoredSingleLiteralMatcher<'n> {
    type I = [u8];
    type S = ();
    type X = ();
    type C = RightSingleLiteralContinuation;
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=RightAnchoredMatchResult<Self::S, Self::C>>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      let Self {
        base,
        cont: RightSingleLiteralContinuation { offset },
      } = self;
      let lit = &base.lit[..(base.lit.len() - offset)];
      if i.len() >= lit.len() {
        if i.ends_with(lit) {
          Some(RightAnchoredMatchResult::CompleteMatch(
            (),
            ComponentOffset(lit.len().try_into().unwrap()),
          ))
        } else {
          None
        }
      } else {
        if lit.ends_with(i) {
          Some(RightAnchoredMatchResult::PartialMatch(
            RightSingleLiteralContinuation {
              offset: offset + i.len(),
            },
          ))
        } else {
          None
        }
      }
      .into_iter()
    }
  }


  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct RightPrefixContinuation {
    pub state: trie::NodeIndex,
  }
  impl continuation::Continuation for RightPrefixContinuation {}


  #[derive(Debug, Clone)]
  pub struct RightAnchoredMultipleLiteralsAutomaton<'n, A>
  where A: Allocator
  {
    trie: trie::PrefixTrie<'n, A>,
  }
  impl<'n, A> RightAnchoredMultipleLiteralsAutomaton<'n, A>
  where A: Allocator+Clone
  {
    pub fn new_in(lits: impl IntoIterator<Item=&'n [u8]>, alloc: A) -> Self {
      Self {
        trie: trie::PrefixTrie::traverse_in(lits, trie::PrefixDirection::Right, alloc),
      }
    }

    pub fn new(lits: impl IntoIterator<Item=&'n [u8]>) -> Self
    where A: Default {
      Self::new_in(lits, A::default())
    }
  }
  impl<'t, 'n, A> continuation::Resumable<'t, RightAnchoredMultipleLiteralsMatcher<'t, 'n, A>>
    for RightAnchoredMultipleLiteralsAutomaton<'n, A>
  where
    A: Allocator,
    't: 'n,
    'n: 't,
  {
    type C = RightPrefixContinuation;

    fn top(&self) -> Self::C {
      RightPrefixContinuation {
        state: trie::PrefixTrie::<A>::get_top_node(),
      }
    }

    fn index<'s>(
      &'s self,
      c: Self::C,
    ) -> impl Into<RightAnchoredMultipleLiteralsMatcher<'t, 'n, A>>+'s
    where
      's: 't,
    {
      let RightPrefixContinuation { state } = c;
      let node = self.trie.get_node_by_index(state).unwrap();
      RightAnchoredMultipleLiteralsMatcher {
        automaton: self,
        cont: c,
        node,
      }
    }
  }
  impl<'t, 'n, A> RightAnchoredAutomaton<'t> for RightAnchoredMultipleLiteralsAutomaton<'n, A>
  where
    A: Allocator+'t,
    't: 'n,
    'n: 't,
  {
    type O = RightAnchoredMultipleLiteralsMatcher<'t, 'n, A>;
  }

  struct RightPrefixIt<'t, 'n, 'h, A>
  where A: Allocator
  {
    automaton: &'t RightAnchoredMultipleLiteralsAutomaton<'n, A>,
    input: &'h [u8],
    node_state: PrefixNodeState<'t, 'n, RightPrefixContinuation, A>,
  }
  impl<'t, 'n, 'h, A> RightPrefixIt<'t, 'n, 'h, A>
  where A: Allocator
  {
    pub fn from_automaton_and_input_and_start_node(
      automaton: &'t RightAnchoredMultipleLiteralsAutomaton<'n, A>,
      input: &'h [u8],
      cont: RightPrefixContinuation,
      start_node: &'t trie::Node<u8, &'n [u8], A>,
    ) -> Self {
      Self {
        automaton,
        input,
        /* Empty literals are not allowed, so we discount any possible end state from any start
         * state. This avoids double-counting end states. */
        node_state: PrefixNodeState::NodeMinusEndState(start_node, cont, ComponentOffset(0)),
      }
    }
  }
  impl<'t, 'n, 'h, A> Iterator for RightPrefixIt<'t, 'n, 'h, A>
  where
    A: Allocator,
    't: 'n,
  {
    type Item = RightAnchoredMatchResult<&'n [u8], RightPrefixContinuation>;

    fn next(&mut self) -> Option<Self::Item> {
      let (mut cur_trie_node, mut cont, mut offset) =
      /* Replace the state with empty upon each iteration. */
      match mem::replace(&mut self.node_state, PrefixNodeState::Empty) {
        PrefixNodeState::Empty => return None,
        PrefixNodeState::NodeMinusEndState(node, cont, offset) => (node, cont, offset),
      };

      let remaining_input = &self.input[..(self.input.len() - offset.as_size())];
      for token in remaining_input.iter().rev() {
        match cur_trie_node.challenge(*token) {
          /* Prefix match failed! We are TOTALLY done with iteration! */
          None => return None,
          /* Succeeded! Let's continue. */
          Some(next_index) => {
            offset.checked_increment();
            cont = RightPrefixContinuation { state: next_index };

            let RightAnchoredMultipleLiteralsMatcher {
              node: next_node, ..
            } = self.automaton.index(cont).into();

            if let Some(id) = next_node.end() {
              self.node_state = PrefixNodeState::NodeMinusEndState(next_node, cont, offset);
              return Some(RightAnchoredMatchResult::CompleteMatch(id, offset));
            }

            cur_trie_node = next_node;
          },
        }
      }

      /* If we can't possibly consume any more input, then exit here without
       * producing any continuation. */
      if cur_trie_node.is_branchless() {
        return None;
      }

      Some(RightAnchoredMatchResult::PartialMatch(cont))
    }
  }

  #[derive(Debug, Copy, Clone)]
  pub struct RightAnchoredMultipleLiteralsMatcher<'t, 'n, A>
  where A: Allocator
  {
    automaton: &'t RightAnchoredMultipleLiteralsAutomaton<'n, A>,
    cont: RightPrefixContinuation,
    node: &'t trie::Node<u8, &'n [u8], A>,
  }
  impl<'t, 'n, A> RightAnchoredMatcher<'n> for RightAnchoredMultipleLiteralsMatcher<'t, 'n, A>
  where A: Allocator
  {
    type I = [u8];
    type S = &'n [u8];
    type X = ();
    type C = RightPrefixContinuation;
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=RightAnchoredMatchResult<Self::S, Self::C>>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      assert!(!i.is_empty());
      RightPrefixIt::from_automaton_and_input_and_start_node(
        self.automaton,
        i,
        self.cont,
        self.node,
      )
    }
  }
}

pub mod unanchored {
  use super::{
    left_anchored::LeftSingleLiteralContinuation, right_anchored::RightSingleLiteralContinuation, *,
  };

  /* #[derive(Debug, Clone)] */
  /* pub struct UnanchoredSingleLiteralAutomaton<'n> {} */
}

#[cfg(test)]
mod test {
  use std::alloc::System;

  use super::{doubly_anchored::*, left_anchored::*, right_anchored::*, *};
  use crate::continuation::Resumable;

  #[test]
  fn doubly_anchored_match() {
    let s = b"asdf";
    let s: &[u8] = s.as_ref();
    let m = DoublyAnchoredSingleLiteral::new(s);
    assert_eq!(m.invoke(&mut (), &s).count(), 1);

    let s_wrong = b"f";
    let s_wrong: &[u8] = s_wrong.as_ref();
    assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0);
  }

  #[test]
  fn doubly_multiple_vec() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();
    let s2 = b"wow";
    let s2: &[u8] = s2.as_ref();
    let m = DoublyAnchoredMultipleLiteralsXXH3Vec::<System>::new([s1, s2]);
    assert_eq!(m.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![s1]);
    assert_eq!(m.invoke(&mut (), &s2).collect::<Vec<_>>(), vec![s2]);

    let s_wrong = b"f";
    let s_wrong: &[u8] = s_wrong.as_ref();
    assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0);
  }

  #[test]
  fn doubly_multiple_set() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();
    let s2 = b"wow";
    let s2: &[u8] = s2.as_ref();
    let m = DoublyAnchoredMultipleLiteralsXXH3Set::<System>::new([s1, s2]);
    assert_eq!(m.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![s1]);
    assert_eq!(m.invoke(&mut (), &s2).collect::<Vec<_>>(), vec![s2]);

    let s_wrong = b"f";
    let s_wrong: &[u8] = s_wrong.as_ref();
    assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0);
  }

  #[test]
  fn lr_match() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();

    let la = LeftAnchoredSingleLiteralAutomaton::new(s1);
    let ra = RightAnchoredSingleLiteralAutomaton::new(s1);

    let lt = la.top();
    assert_eq!(lt, LeftSingleLiteralContinuation { offset: 0 });
    let rt = ra.top();
    assert_eq!(rt, RightSingleLiteralContinuation { offset: 0 });

    let lm = la.index(lt).into();
    let rm = ra.index(rt).into();

    let sl = b"asdfeee";
    let sl: &[u8] = sl.as_ref();
    let sl2 = b"a";
    let sl2: &[u8] = sl2.as_ref();

    let sr = b"eeeasdf";
    let sr: &[u8] = sr.as_ref();
    let sr2 = b"f";
    let sr2: &[u8] = sr2.as_ref();

    let s_wrong = b"g";
    let s_wrong: &[u8] = s_wrong.as_ref();

    assert_eq!(lm.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![
      LeftAnchoredMatchResult::CompleteMatch((), ComponentOffset(4))
    ]);
    assert_eq!(lm.invoke(&mut (), &sl).collect::<Vec<_>>(), vec![
      LeftAnchoredMatchResult::CompleteMatch((), ComponentOffset(4))
    ]);
    assert_eq!(lm.invoke(&mut (), &sl2).collect::<Vec<_>>(), vec![
      LeftAnchoredMatchResult::PartialMatch(LeftSingleLiteralContinuation { offset: 1 })
    ]);
    let lm2 = la.index(LeftSingleLiteralContinuation { offset: 1 }).into();
    assert_eq!(lm2.invoke(&mut (), b"sdfee").collect::<Vec<_>>(), vec![
      LeftAnchoredMatchResult::CompleteMatch((), ComponentOffset(3))
    ]);
    assert_eq!(lm.invoke(&mut (), &sr).count(), 0);
    assert_eq!(lm.invoke(&mut (), &s_wrong).count(), 0);

    assert_eq!(rm.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::CompleteMatch((), ComponentOffset(4))
    ]);
    assert_eq!(rm.invoke(&mut (), &sl).count(), 0);
    assert_eq!(rm.invoke(&mut (), &sr).collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::CompleteMatch((), ComponentOffset(4))
    ]);
    assert_eq!(rm.invoke(&mut (), &sr2).collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::PartialMatch(RightSingleLiteralContinuation { offset: 1 })
    ]);
    let rm2 = ra
      .index(RightSingleLiteralContinuation { offset: 1 })
      .into();
    assert_eq!(rm2.invoke(&mut (), b"eeasd").collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::CompleteMatch((), ComponentOffset(3))
    ]);
    assert_eq!(rm.invoke(&mut (), &s_wrong).count(), 0);
  }

  #[test]
  fn lr_match_multiple() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();
    let s2 = b"ok3";
    let s2: &[u8] = s2.as_ref();
    let s3 = b"ok34";
    let s3: &[u8] = s3.as_ref();

    let la = LeftAnchoredMultipleLiteralsAutomaton::<System>::new([s1, s2, s3]);
    let ra = RightAnchoredMultipleLiteralsAutomaton::<System>::new([s1, s2, s3]);

    let lt = la.top();
    assert_eq!(lt, LeftPrefixContinuation {
      state: trie::NodeIndex(0)
    });
    let rt = ra.top();
    assert_eq!(rt, RightPrefixContinuation {
      state: trie::NodeIndex(0)
    });

    let lm = la.index(lt).into();
    let rm = ra.index(rt).into();

    let t1 = b"asdfee";
    let t1: &[u8] = t1.as_ref();
    let t1_r = b"eeasdf";
    let t1_r: &[u8] = t1_r.as_ref();

    let t2 = b"ok3";
    let t2: &[u8] = t2.as_ref();
    let t2_r = b"k34";
    let t2_r: &[u8] = t2_r.as_ref();

    let t3 = b"asd";
    let t3: &[u8] = t3.as_ref();
    let t3_r = b"sdf";
    let t3_r: &[u8] = t3_r.as_ref();

    let t_wrong = b"g";
    let t_wrong: &[u8] = t_wrong.as_ref();

    let t2_wrong = b"asdg";
    let t2_wrong: &[u8] = t2_wrong.as_ref();

    let mut x = ();

    let matches: Vec<_> = lm.invoke(&mut x, &t1).collect();
    assert_eq!(matches.len(), 1);
    match matches[0] {
      LeftAnchoredMatchResult::CompleteMatch(t, o) => {
        assert_eq!(s1.as_ptr(), t.as_ptr());
        assert_eq!(o, ComponentOffset(4));
      },
      _ => unreachable!(),
    }

    let matches: Vec<_> = rm.invoke(&mut x, &t1_r).collect();
    assert_eq!(matches.len(), 1);
    match matches[0] {
      RightAnchoredMatchResult::CompleteMatch(t, o) => {
        assert_eq!(s1.as_ptr(), t.as_ptr());
        assert_eq!(o, ComponentOffset(4));
      },
      _ => unreachable!(),
    }

    let matches: Vec<_> = lm.invoke(&mut x, &t2).collect();
    assert_eq!(matches.len(), 2);
    match matches[0] {
      LeftAnchoredMatchResult::CompleteMatch(t, o) => {
        assert_eq!(s2.as_ptr(), t.as_ptr());
        assert_eq!(o, ComponentOffset(3));
      },
      _ => unreachable!(),
    }
    assert_eq!(
      matches[1],
      LeftAnchoredMatchResult::PartialMatch(LeftPrefixContinuation {
        state: trie::NodeIndex(4)
      })
    );
    let lm2 = la
      .index(LeftPrefixContinuation {
        state: trie::NodeIndex(4),
      })
      .into();
    assert_eq!(lm2.invoke(&mut x, b"4").collect::<Vec<_>>(), vec![
      LeftAnchoredMatchResult::CompleteMatch(s3, ComponentOffset(1))
    ]);

    let matches: Vec<_> = rm.invoke(&mut x, &t2).collect();
    assert_eq!(matches.len(), 1);
    match matches[0] {
      RightAnchoredMatchResult::CompleteMatch(t, o) => {
        assert_eq!(s2.as_ptr(), t.as_ptr());
        assert_eq!(o, ComponentOffset(3));
      },
      _ => unreachable!(),
    }

    let matches: Vec<_> = rm.invoke(&mut x, &t2_r).collect();
    assert_eq!(matches.len(), 1);
    assert_eq!(
      matches[0],
      RightAnchoredMatchResult::PartialMatch(RightPrefixContinuation {
        state: trie::NodeIndex(10)
      })
    );
    let rm2 = ra
      .index(RightPrefixContinuation {
        state: trie::NodeIndex(10),
      })
      .into();
    assert_eq!(rm2.invoke(&mut x, b"o").collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::CompleteMatch(s3, ComponentOffset(1))
    ]);

    assert_eq!(lm.invoke(&mut x, &t3).collect::<Vec<_>>(), vec![
      LeftAnchoredMatchResult::PartialMatch(LeftPrefixContinuation {
        state: trie::NodeIndex(7)
      })
    ]);
    let lm3 = la
      .index(LeftPrefixContinuation {
        state: trie::NodeIndex(7),
      })
      .into();
    assert_eq!(lm3.invoke(&mut x, b"f").collect::<Vec<_>>(), vec![
      LeftAnchoredMatchResult::CompleteMatch(s1, ComponentOffset(1))
    ]);

    assert_eq!(rm.invoke(&mut x, &t3_r).collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::PartialMatch(RightPrefixContinuation {
        state: trie::NodeIndex(7)
      })
    ]);
    let rm3 = ra
      .index(RightPrefixContinuation {
        state: trie::NodeIndex(7),
      })
      .into();
    assert_eq!(rm3.invoke(&mut x, b"a").collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::CompleteMatch(s1, ComponentOffset(1))
    ]);

    assert_eq!(lm.invoke(&mut x, &t_wrong).count(), 0);
    assert_eq!(lm.invoke(&mut x, &t2_wrong).count(), 0);
    assert_eq!(rm.invoke(&mut x, &t_wrong).count(), 0);
    assert_eq!(rm.invoke(&mut x, &t2_wrong).count(), 0);
  }

  /* #[test] */
  /* fn unanchored_rabin_karp() { */
  /* let s1 = b"asdf"; */
  /* let s1: &[u8] = s1.as_ref(); */

  /* let sl = b"asdfeee"; */
  /* let sl: &[u8] = sl.as_ref(); */
  /* let sl2 = b"a"; */
  /* let sl2: &[u8] = sl2.as_ref(); */

  /* let sr = b"eeeasdf"; */
  /* let sr: &[u8] = sr.as_ref(); */
  /* let sr2 = b"f"; */
  /* let sr2: &[u8] = sr2.as_ref(); */

  /* let s_wrong = b"g"; */
  /* let s_wrong: &[u8] = s_wrong.as_ref(); */

  /* let m = UnanchoredSingleLiteralRabinKarp::new(s1); */

  /* assert_eq!(m.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![ */
  /* UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval { */
  /* left: ComponentOffset(0), */
  /* right: ComponentOffset(4), */
  /* }) */
  /* ]); */
  /* assert_eq!(m.invoke(&mut (), &sl).collect::<Vec<_>>(), vec![ */
  /* UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval { */
  /* left: ComponentOffset(0), */
  /* right: ComponentOffset(4), */
  /* }) */
  /* ]); */
  /* /\* FIXME: partial matches for unanchored! *\/ */
  /* assert_eq!(m.invoke(&mut (), &sl2).count(), 0); */
  /* assert_eq!(m.invoke(&mut (), &sr).collect::<Vec<_>>(), vec![ */
  /* UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval { */
  /* left: ComponentOffset(3), */
  /* right: ComponentOffset(7), */
  /* }) */
  /* ]); */
  /* /\* FIXME: partial matches for unanchored! *\/ */
  /* assert_eq!(m.invoke(&mut (), &sr2).count(), 0); */
  /* assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0); */
  /* } */

  /* #[test] */
  /* fn unanchored_memmem() { */
  /* let s1 = b"asdf"; */
  /* let s1: &[u8] = s1.as_ref(); */

  /* let sl = b"asdfeee"; */
  /* let sl: &[u8] = sl.as_ref(); */
  /* let sl2 = b"a"; */
  /* let sl2: &[u8] = sl2.as_ref(); */

  /* let sr = b"eeeasdf"; */
  /* let sr: &[u8] = sr.as_ref(); */
  /* let sr2 = b"f"; */
  /* let sr2: &[u8] = sr2.as_ref(); */

  /* let s_wrong = b"g"; */
  /* let s_wrong: &[u8] = s_wrong.as_ref(); */

  /* let m = UnanchoredSingleLiteralMemMem::new(s1); */
  /* let mut prestate = memmem::PrefilterState::new(); */

  /* assert_eq!(m.invoke(&mut prestate, &s1).collect::<Vec<_>>(), vec![ */
  /* UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval { */
  /* left: ComponentOffset(0), */
  /* right: ComponentOffset(4), */
  /* }) */
  /* ]); */
  /* assert_eq!(m.invoke(&mut prestate, &sl).collect::<Vec<_>>(), vec![ */
  /* UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval { */
  /* left: ComponentOffset(0), */
  /* right: ComponentOffset(4), */
  /* }) */
  /* ]); */
  /* /\* FIXME: partial matches for unanchored! *\/ */
  /* assert_eq!(m.invoke(&mut prestate, &sl2).count(), 0); */
  /* assert_eq!(m.invoke(&mut prestate, &sr).collect::<Vec<_>>(), vec![ */
  /* UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval { */
  /* left: ComponentOffset(3), */
  /* right: ComponentOffset(7), */
  /* }) */
  /* ]); */
  /* /\* FIXME: partial matches for unanchored! *\/ */
  /* assert_eq!(m.invoke(&mut prestate, &sr2).count(), 0); */
  /* assert_eq!(m.invoke(&mut prestate, &s_wrong).count(), 0); */
  /* } */
}
