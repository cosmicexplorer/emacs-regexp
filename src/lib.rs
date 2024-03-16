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

#![warn(rustdoc::missing_crate_level_docs)]
// #![warn(missing_docs)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]
#![feature(trait_alias)]
#![feature(allocator_api)]

pub mod literal;
pub mod trie;

pub mod input {
  pub trait Input {}

  impl Input for [u8] {}

  impl Input for str {}
}

pub enum Chunking {
  Contiguous,
  Streaming,
}

type ComponentLen = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ComponentOffset(pub ComponentLen);

type GlobalLen = u64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct GlobalOffset(pub GlobalLen);

pub mod continuation {
  pub trait Continuation {}

  pub trait Resumable<O> {
    type C: Continuation;

    fn top(&self) -> Self::C;

    fn index(&self, c: Self::C) -> O;
  }
}

pub mod alphabet {
  use core::hash::Hash;

  pub trait Symbol = Hash+Eq;
}

pub mod state {
  pub trait State {}

  impl State for () {}
}

pub trait DoublyAnchoredMatcher<'n> {
  type I: input::Input+?Sized;
  type S: alphabet::Symbol;
  type X: state::State;
  fn invoke<'s, 'x, 'h>(
    &'s self,
    x: &'x mut Self::X,
    i: &'h impl AsRef<Self::I>,
  ) -> impl Iterator<Item=Self::S>+'s+'x+'h
  where
    'x: 'n,
    'n: 'x,
    's: 'n,
    'n: 'h,
    'h: 'n;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LeftAnchoredMatchResult<S, C> {
  CompleteMatch(S, ComponentOffset),
  PartialMatch(S, C),
}

pub trait LeftAnchoredAutomaton<'n>: continuation::Resumable<Self::O> {
  type O: LeftAnchoredMatcher<'n, C=<Self as continuation::Resumable<Self::O>>::C>;
}

pub trait LeftAnchoredMatcher<'n> {
  type I: input::Input+?Sized;
  type S: alphabet::Symbol;
  type X: state::State;
  type C: continuation::Continuation;
  fn invoke<'s, 'x, 'h>(
    &'s self,
    x: &'x mut Self::X,
    i: &'h Self::I,
  ) -> impl Iterator<Item=LeftAnchoredMatchResult<Self::S, Self::C>>+'s+'x+'h
  where
    'x: 'n,
    'n: 'x,
    's: 'n,
    'n: 'h,
    'h: 'n;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RightAnchoredMatchResult<S, C> {
  CompleteMatch(S, ComponentOffset),
  PartialMatch(S, C),
}


pub trait RightAnchoredAutomaton<'n>: continuation::Resumable<Self::O> {
  type O: RightAnchoredMatcher<'n, C=<Self as continuation::Resumable<Self::O>>::C>;
}

pub trait RightAnchoredMatcher<'n> {
  type I: input::Input+?Sized;
  type S: alphabet::Symbol;
  type X: state::State;
  type C: continuation::Continuation;
  fn invoke<'s, 'x, 'h>(
    &'s self,
    x: &'x mut Self::X,
    i: &'h Self::I,
  ) -> impl Iterator<Item=RightAnchoredMatchResult<Self::S, Self::C>>+'s+'x+'h
  where
    'x: 'n,
    'n: 'x,
    's: 'n,
    'n: 'h,
    'h: 'n;
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IntraComponentInterval {
  pub left: ComponentOffset,
  pub right: ComponentOffset,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UnanchoredMatchResult<S, LC, RC> {
  CompleteMatch(S, IntraComponentInterval),
  PartialLeftOnly(S, LC, ComponentOffset),
  PartialRightOnly(S, RC, ComponentOffset),
  PartialBoth(S, LC, RC),
}

pub trait UnanchoredMatcher<'n> {
  type I: input::Input+?Sized;
  type S: alphabet::Symbol;
  type X: state::State;
  type LC: continuation::Continuation;
  type RC: continuation::Continuation;
  fn invoke<'s, 'x, 'h>(
    &'s self,
    x: &'x mut Self::X,
    i: &'h Self::I,
  ) -> impl Iterator<Item=UnanchoredMatchResult<Self::S, Self::LC, Self::RC>>+'s+'x+'h
  where
    'x: 'n,
    'n: 'x,
    's: 'n,
    'n: 'h,
    'h: 'n;
}
