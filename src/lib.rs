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
#![feature(trait_alias)]

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
pub struct ComponentOffset(pub ComponentLen);

type GlobalLen = u64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct GlobalOffset(pub GlobalLen);

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
  use core::hash::Hash;

  pub trait Symbol = Hash+Eq;
}

pub trait DoublyAnchoredMatcher {
  type I: input::Input;
  type S: alphabet::Symbol;
  type It: Iterator<Item=Self::S>;
  fn invoke(&self, i: Self::I) -> Self::It;
}

pub enum LeftAnchoredMatchResult<S, C> {
  CompleteMatch(S, ComponentOffset),
  PartialMatch(S, C),
}

pub trait LeftAnchoredMatcher {
  type I: input::Input;
  type S: alphabet::Symbol;
  type C: continuation::Continuation;
  type It: Iterator<Item=LeftAnchoredMatchResult<Self::S, Self::C>>;
  fn invoke(&self, i: Self::I) -> Self::It;
}

pub enum RightAnchoredMatchResult<S, C> {
  CompleteMatch(S, ComponentOffset),
  PartialMatch(S, C),
}

pub trait RightAnchoredMatcher {
  type I: input::Input;
  type S: alphabet::Symbol;
  type C: continuation::Continuation;
  type It: Iterator<Item=RightAnchoredMatchResult<Self::S, Self::C>>;
  fn invoke(&self, i: Self::I) -> Self::It;
}

pub struct IntraComponentInterval {
  pub left: ComponentOffset,
  pub right: ComponentOffset,
}

pub enum UnanchoredMatchResult<S, LC, RC> {
  CompleteMatch(S, IntraComponentInterval),
  PartialLeftOnly(S, LC, ComponentOffset),
  PartialRightOnly(S, RC, ComponentOffset),
  PartialBoth(S, LC, RC),
}

pub trait UnanchoredMatcher {
  type I: input::Input;
  type S: alphabet::Symbol;
  type LC: continuation::Continuation;
  type RC: continuation::Continuation;
  type It: Iterator<Item=UnanchoredMatchResult<Self::S, Self::LC, Self::RC>>;
  fn invoke(&self, i: Self::I) -> Self::It;
}

pub mod literal {
  use indexmap::IndexSet;

  use super::*;

  pub struct DoublyAnchoredSingleLiteral<'a> {
    lit: &'a [u8],
  }
  impl<'a> DoublyAnchoredSingleLiteral<'a> {
    pub fn new(lit: &'a [u8]) -> Self { Self { lit } }
  }
  impl<'a> DoublyAnchoredMatcher for DoublyAnchoredSingleLiteral<'a> {
    type I = &'a [u8];
    type S = ();
    type It = <Option<Self::S> as IntoIterator>::IntoIter;
    fn invoke(&self, i: Self::I) -> Self::It {
      if i == self.lit { Some(()) } else { None }.into_iter()
    }
  }

  pub struct DoublyAnchoredMultipleLiterals<'a> {
    lits: IndexSet<&'a [u8]>,
  }
  impl<'a> DoublyAnchoredMultipleLiterals<'a> {
    pub fn new(lits: impl IntoIterator<Item=&'a [u8]>) -> Self {
      Self {
        lits: lits.into_iter().collect(),
      }
    }
  }
  impl<'a> DoublyAnchoredMatcher for DoublyAnchoredMultipleLiterals<'a> {
    type I = &'a [u8];
    type S = usize;
    type It = <Option<Self::S> as IntoIterator>::IntoIter;
    fn invoke(&self, i: Self::I) -> Self::It { self.lits.get_index_of(i).into_iter() }
  }

  pub struct LeftLiteralContinuation<'a> {
    pub rest: &'a [u8],
  }
  impl<'a> continuation::Continuation for LeftLiteralContinuation<'a> {}

  pub struct LeftAnchoredSingleLiteral<'a> {
    lit: &'a [u8],
  }
  impl<'a> LeftAnchoredSingleLiteral<'a> {
    pub fn new(lit: &'a [u8]) -> Self { Self { lit } }
  }
  impl<'a> LeftAnchoredMatcher for LeftAnchoredSingleLiteral<'a> {
    type I = &'a [u8];
    type S = ();
    type C = LeftLiteralContinuation<'a>;
    type It = <Option<LeftAnchoredMatchResult<Self::S, Self::C>> as IntoIterator>::IntoIter;
    fn invoke(&self, i: Self::I) -> Self::It {
      if i.len() >= self.lit.len() {
        if i.starts_with(self.lit) {
          Some(LeftAnchoredMatchResult::CompleteMatch(
            (),
            ComponentOffset(self.lit.len().try_into().unwrap()),
          ))
        } else {
          None
        }
      } else {
        if self.lit.starts_with(i) {
          Some(LeftAnchoredMatchResult::PartialMatch(
            (),
            LeftLiteralContinuation {
              rest: &self.lit[i.len()..],
            },
          ))
        } else {
          None
        }
      }
      .into_iter()
    }
  }
}
