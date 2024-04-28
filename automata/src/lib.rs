/* Description: Specialized string scanning and matching techniques.

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

//! Specialized string scanning and matching techniques.

#![warn(rustdoc::missing_crate_level_docs)]
// #![warn(missing_docs)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]
#![feature(trait_alias)]
#![feature(allocator_api)]
#![feature(unchecked_math)]
#![feature(trusted_len)]
#![feature(portable_simd)]
#![feature(slice_as_chunks)]
#![feature(maybe_uninit_uninit_array)]
#![feature(maybe_uninit_array_assume_init)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

#[cfg(not(test))]
extern crate alloc;

#[allow(unused_imports)]
mod alloc_types {
  /* no_std/no_main is enabled except for test environments, so we need to use
   * the special imports from the extern alloc crate. */
  cfg_if::cfg_if! {
    if #[cfg(test)] {
      pub use Box;
      pub use Vec;
    } else {
      pub use ::alloc::{boxed::Box, vec::Vec};
    }
  }
}

pub mod filters;
pub mod hashgrams;
pub mod litblock;
pub mod literal;
pub mod nfa;
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

type ComponentLen = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ComponentOffset(pub ComponentLen);

impl ComponentOffset {
  #[inline(always)]
  pub const fn zero() -> Self { Self(0) }

  #[inline(always)]
  pub const fn as_size(self) -> usize { self.0 }

  #[inline(always)]
  pub fn from_size(x: usize) -> Self { Self(x) }

  #[inline(always)]
  pub unsafe fn unchecked_increment(&mut self) { self.0 = self.0.unchecked_add(1); }

  #[inline(always)]
  pub fn checked_increment(&mut self) {
    self.0 = self
      .0
      .checked_add(1)
      .expect("incremented past component length!");
  }
}

type GlobalLen = u128;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct GlobalOffset(pub GlobalLen);

pub mod continuation {
  pub trait Continuation {}

  pub trait Resumable<'t, O> {
    type C: Continuation;

    fn top(&self) -> Self::C;

    fn index<'s>(&'s self, c: Self::C) -> impl Into<O>+'s
    where 's: 't;
  }

  pub trait Subsettable<'t> {
    type O;

    fn initial<'s>(&'s self) -> impl Into<Self::O>+'s
    where 's: 't;
  }

  pub trait SubsetResumable<'t>: Subsettable<'t> {
    type C: Continuation;

    fn index<'s>(&'s self, c: Self::C) -> impl Into<<Self as Subsettable<'t>>::O>+'s
    where 's: 't;
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
    i: &'h Self::I,
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
  PartialMatch(C),
}

pub trait LeftAnchoredAutomaton<'n>: continuation::Resumable<'n, Self::O> {
  type O: LeftAnchoredMatcher<'n, C=<Self as continuation::Resumable<'n, Self::O>>::C>+'n;
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
  PartialMatch(C),
}


pub trait RightAnchoredAutomaton<'n>: continuation::Resumable<'n, Self::O> {
  type O: RightAnchoredMatcher<'n, C=<Self as continuation::Resumable<'n, Self::O>>::C>+'n;
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

pub trait UnanchoredAutomaton<'n>:
  continuation::Resumable<'n, Self::LO>+continuation::Resumable<'n, Self::RO>
{
  type LO: LeftAnchoredMatcher<'n, C=<Self as continuation::Resumable<'n, Self::LO>>::C>+'n;
  type RO: RightAnchoredMatcher<'n, C=<Self as continuation::Resumable<'n, Self::RO>>::C>+'n;
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
