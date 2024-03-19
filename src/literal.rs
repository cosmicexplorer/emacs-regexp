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

/* use aho_corasick::AhoCorasick; */
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
    i: &'h impl AsRef<Self::I>,
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
    i: &'h impl AsRef<Self::I>,
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
    i: &'h impl AsRef<Self::I>,
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
      trie: trie::PrefixTrie::traverse_in(lits, alloc),
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
  /* TODO: make these two an enum! */
  start_node: Option<&'t trie::Node<u8, &'n [u8], A>>,
  end_continuation: Option<LeftPrefixContinuation>,
}
impl<'t, 'n, 'h, A> LeftPrefixIt<'t, 'n, 'h, A>
where A: Allocator
{
  pub fn from_automaton_and_input_and_start_node(
    automaton: &'t LeftAnchoredMultipleLiteralsAutomaton<'n, A>,
    input: &'h [u8],
    start_node: &'t trie::Node<u8, &'n [u8], A>,
  ) -> Self {
    Self {
      automaton,
      input,
      start_node: Some(start_node),
      end_continuation: None,
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
    if let Some(end_continuation) = self.end_continuation.take() {
      return Some(LeftAnchoredMatchResult::PartialMatch(end_continuation));
    }

    let mut cur_trie_node = self.start_node?;

    assert!(!self.input.is_empty());

    for token in self.input.iter() {
      match cur_trie_node.challenge(*token) {
        /* Prefix match failed! */
        None => return None,
        /* Succeeded! Let's continue. */
        Some(next_index) => {
          let next_index = LeftPrefixContinuation { state: next_index };
          self.end_continuation = Some(next_index);
          let LeftAnchoredMultipleLiteralsMatcher {
            node: next_node, ..
          } = self.automaton.index(next_index).into();
          cur_trie_node = next_node;
        },
      }
    }

    return Some(if let Some(id) = cur_trie_node.end() {
      LeftAnchoredMatchResult::CompleteMatch(
        id,
        ComponentOffset::try_from_size(self.input.len())
          .expect("input component should fit within u32"),
      )
    } else {
      LeftAnchoredMatchResult::PartialMatch(self.end_continuation.take().expect(
        "self.end_continuation should have been set above since input was asserted nonempty",
      ))
    });
  }
}

#[derive(Debug, Copy, Clone)]
pub struct LeftAnchoredMultipleLiteralsMatcher<'t, 'n, A>
where A: Allocator
{
  automaton: &'t LeftAnchoredMultipleLiteralsAutomaton<'n, A>,
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
    LeftPrefixIt::from_automaton_and_input_and_start_node(self.automaton, i, self.node)
  }
}

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
          (),
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

/* TODO: backwards? */
pub struct UnanchoredSingleLiteralRabinKarp<'n> {
  finder: memmem::CompiledRabinKarpFinder<'n>,
}
impl<'n> UnanchoredSingleLiteralRabinKarp<'n> {
  pub fn new(lit: &'n [u8]) -> Self {
    Self {
      finder: memmem::CompiledRabinKarpFinder::for_needle(lit),
    }
  }
}

struct SingleLiteralRabinKarpInnerMatchIterator<'h, 'n> {
  finder: memmem::CompiledRabinKarpFinder<'n>,
  haystack: &'h [u8],
  pos: usize,
}
impl<'h, 'n> Iterator for SingleLiteralRabinKarpInnerMatchIterator<'h, 'n> {
  type Item = IntraComponentInterval;

  fn next(&mut self) -> Option<Self::Item> {
    let haystack = self.haystack.get(self.pos..)?;
    let idx = self.finder.find(haystack)?;
    /* Iterate to the beginning of the match. */
    let pos = self.pos + idx;
    /* NB: Now go exactly one past, so we can find overlapping matches! */
    self.pos = pos + 1;

    let int = IntraComponentInterval {
      left: ComponentOffset(pos.try_into().unwrap()),
      right: ComponentOffset((pos + self.finder.needle().len()).try_into().unwrap()),
    };
    Some(int)
  }

  fn size_hint(&self) -> (usize, Option<usize>) {
    let remaining_haystack_len = match self.haystack.len().checked_sub(self.pos) {
      None => return (0, Some(0)),
      Some(haystack_len) => haystack_len,
    };
    let needle_len = self.finder.needle().len();
    if needle_len == 0 {
      // Empty needles always succeed and match at every point
      // (including the very end)
      return (
        remaining_haystack_len.saturating_add(1),
        remaining_haystack_len.checked_add(1),
      );
    }
    /* Can match once if needle_len == haystack_len, then once further for
    each additional byte.
    This is many more than the quotient which is used in FindIter, since it
    does not check for
    overlapping matches. */
    (
      0,
      Some(remaining_haystack_len.saturating_sub(needle_len - 1)),
    )
  }
}

/* impl<'n> UnanchoredMatcher<'n> for UnanchoredSingleLiteralRabinKarp<'n> { */
/* type I = [u8]; */
/* type S = (); */
/* type X = (); */
/* type LC = LeftSingleLiteralContinuation<'n>; */
/* type RC = RightSingleLiteralContinuation<'n>; */
/* fn invoke<'s, 'x, 'h>( */
/* &'s self, */
/* _x: &'x mut Self::X, */
/* i: &'h Self::I, */
/* ) -> impl Iterator<Item=UnanchoredMatchResult<Self::S, Self::LC,
 * Self::RC>>+'s+'x+'h */
/* where */
/* 'x: 'n, */
/* 'n: 'x, */
/* 's: 'n, */
/* 'n: 'h, */
/* 'h: 'n, */
/* { */
/* let inner = SingleLiteralRabinKarpInnerMatchIterator { */
/* finder: self.finder.as_ref(), */
/* haystack: i, */
/* pos: 0, */
/* } */
/* .map(|int| UnanchoredMatchResult::CompleteMatch((), int)); */
/* /\* let left = *\/ */
/* inner */
/* } */
/* } */

/* /\* TODO: backwards? *\/ */
/* pub struct UnanchoredSingleLiteralMemMem<'n> { */
/* finder: memmem::Finder<'n>, */
/* } */
/* impl<'n> UnanchoredSingleLiteralMemMem<'n> { */
/* pub fn new(lit: &'n [u8]) -> Self { */
/* Self { */
/* finder: memmem::Finder::new(lit), */
/* } */
/* } */
/* } */

/* impl state::State for memmem::PrefilterState {} */

/* struct SingleLiteralMemMemInnerMatchIterator<'x, 'h, 'n> { */
/* finder: memmem::Finder<'n>, */
/* prestate: &'x mut memmem::PrefilterState, */
/* haystack: &'h [u8], */
/* pos: usize, */
/* } */
/* impl<'x, 'h, 'n> Iterator for SingleLiteralMemMemInnerMatchIterator<'x,
 * 'h, 'n> { */
/* type Item = IntraComponentInterval; */

/* fn next(&mut self) -> Option<Self::Item> { */
/* let haystack = self.haystack.get(self.pos..)?; */
/* let idx = self.finder.find_state(self.prestate, haystack)?; */
/* /\* Iterate to the beginning of the match. *\/ */
/* let pos = self.pos + idx; */
/* /\* NB: Now go exactly one past, so we can find overlapping matches! *\/ */
/* self.pos = pos + 1; */

/* let int = IntraComponentInterval { */
/* left: ComponentOffset(pos.try_into().unwrap()), */
/* right: ComponentOffset((pos +
 * self.finder.needle().len()).try_into().unwrap()), */
/* }; */
/* Some(int) */
/* } */

/* fn size_hint(&self) -> (usize, Option<usize>) { */
/* let remaining_haystack_len = match
 * self.haystack.len().checked_sub(self.pos) { */
/* None => return (0, Some(0)), */
/* Some(haystack_len) => haystack_len, */
/* }; */
/* let needle_len = self.finder.needle().len(); */
/* if needle_len == 0 { */
/* // Empty needles always succeed and match at every point */
/* // (including the very end) */
/* return ( */
/* remaining_haystack_len.saturating_add(1), */
/* remaining_haystack_len.checked_add(1), */
/* ); */
/* } */
/* /\* Can match once if needle_len == haystack_len, then once further for */
/* each additional byte. */
/* This is many more than the quotient which is used in FindIter, since it */
/* does not check for */
/* overlapping matches. *\/ */
/* ( */
/* 0, */
/* Some(remaining_haystack_len.saturating_sub(needle_len - 1)), */
/* ) */
/* } */
/* } */

/* impl<'n> UnanchoredMatcher<'n> for UnanchoredSingleLiteralMemMem<'n> { */
/* type I = [u8]; */
/* type S = (); */
/* type X = memmem::PrefilterState; */
/* type LC = LeftSingleLiteralContinuation<'n>; */
/* type RC = RightSingleLiteralContinuation<'n>; */
/* fn invoke<'s, 'x, 'h>( */
/* &'s self, */
/* x: &'x mut Self::X, */
/* i: &'h Self::I, */
/* ) -> impl Iterator<Item=UnanchoredMatchResult<Self::S, Self::LC,
 * Self::RC>>+'s+'x+'h */
/* where */
/* 'x: 'n, */
/* 'n: 'x, */
/* 's: 'n, */
/* 'n: 'h, */
/* 'h: 'n, */
/* { */
/* SingleLiteralMemMemInnerMatchIterator { */
/* finder: self.finder.as_ref(), */
/* prestate: x, */
/* haystack: i, */
/* pos: 0, */
/* } */
/* .map(|int| UnanchoredMatchResult::CompleteMatch((), int)) */
/* } */
/* } */

#[cfg(test)]
mod test {
  use std::alloc::System;

  use super::*;
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
      RightAnchoredMatchResult::PartialMatch((), RightSingleLiteralContinuation { offset: 1 })
    ]);
    let rm2 = ra
      .index(RightSingleLiteralContinuation { offset: 1 })
      .into();
    assert_eq!(rm2.invoke(&mut (), b"eeasd").collect::<Vec<_>>(), vec![
      RightAnchoredMatchResult::CompleteMatch((), ComponentOffset(3))
    ]);
    assert_eq!(rm.invoke(&mut (), &s_wrong).count(), 0);

    /* TODO: multiple matches! */
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
