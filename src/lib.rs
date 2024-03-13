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
#![deny(unsafe_code)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]

pub mod input {
  pub trait Input {}

  impl Input for &[u8] {}

  impl Input for &str {}
}

pub enum Chunking {
  Contiguous,
  Streaming,
}

type ComponentLen = u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ComponentOffset(ComponentLen);

type GlobalLen = u64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct GlobalOffset(GlobalLen);

pub enum Anchoring {
  DoublyAnchored,
  Left,
  Right,
  Unanchored,
}

pub enum Params {
  Single,
  MultipleParallel,
}

pub mod continuation {
  pub trait Continuation {}
}

pub mod alphabet {
  pub trait Symbol {}

  impl Symbol for () {}
}

pub trait DoublyAnchoredMatcher {
  type I: input::Input;
  type S: alphabet::Symbol;
  type It: Iterator<Item=Self::S>;
  fn invoke(&self, i: Self::I) -> Self::It;
}

/* type SymbolLen = u16; */

/* #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)] */
/* #[repr(transparent)] */
/* pub struct Symbol(SymbolLen); */

/* pub enum LeftAnchoredMatchResult<C> */
/* where C: continuation::Continuation */
/* { */
/* CompleteMatch(Symbol, ComponentOffset), */
/* PartialMatch(Symbol, C), */
/* } */

/* pub trait LeftAnchoredMatcher { */
/* type I: input::Input; */
/* type C: continuation::Continuation; */
/* type It: Iterator<Item=LeftAnchoredMatchResult<Self::C>>; */
/* fn invoke(&self, i: Self::I) -> Self::It; */
/* } */

/* pub enum RightAnchoredMatchResult<C> */
/* where C: continuation::Continuation */
/* { */
/* CompleteMatch(Symbol, ComponentOffset), */
/* PartialMatch(Symbol, C), */
/* } */

/* pub trait RightAnchoredMatcher { */
/* type I: input::Input; */
/* type C: continuation::Continuation; */
/* type It: Iterator<Item=RightAnchoredMatchResult<Self::C>>; */
/* fn invoke(&self, i: Self::I) -> Self::It; */
/* } */

/* pub struct IntraComponentInterval { */
/* pub left: ComponentOffset, */
/* pub right: ComponentOffset, */
/* } */

/* pub enum UnanchoredMatchResult<LC, RC> */
/* where */
/* LC: continuation::Continuation, */
/* RC: continuation::Continuation, */
/* { */
/* CompleteMatch(Symbol, IntraComponentInterval), */
/* PartialLeftOnly(Symbol, LC, ComponentOffset), */
/* PartialRightOnly(Symbol, RC, ComponentOffset), */
/* PartialBoth(Symbol, LC, RC), */
/* } */

/* pub trait UnanchoredMatcher { */
/* type I: input::Input; */
/* type LC: continuation::Continuation; */
/* type RC: continuation::Continuation; */
/* type It: Iterator<Item=UnanchoredMatchResult<Self::LC, Self::RC>>; */
/* fn invoke(&self, i: Self::I) -> Self::It; */
/* } */

pub mod literal {
  /* use indexmap::IndexSet; */

  use super::*;

  pub struct DoublyAnchoredSingleLiteral<'a>(pub &'a [u8]);
  impl<'a> DoublyAnchoredMatcher for DoublyAnchoredSingleLiteral<'a> {
    type I = &'a [u8];
    type S = ();
    type It = <Option<Self::S> as IntoIterator>::IntoIter;
    fn invoke(&self, i: Self::I) -> Self::It {
      if i == self.0 { Some(()) } else { None }.into_iter()
    }
  }
}
