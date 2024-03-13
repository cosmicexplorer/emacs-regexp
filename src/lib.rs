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

macro_rules! primitive_wrapper {
  ($name:ident, $inner:ty) => {
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct $name($inner);

    impl From<$inner> for $name {
      fn from(i: $inner) -> Self { Self(i) }
    }

    impl From<$name> for $inner {
      fn from(n: $name) -> Self { n.0 }
    }
  };
}

pub mod input {
  pub trait Input {}

  pub struct Bytes;
  impl Input for Bytes {}

  pub struct Unicode;
  impl Input for Unicode {}
}

pub mod chunk {
  pub trait Chunking {
    /* TODO: */
    /* type I: super::input::Input; */
  }

  pub struct Contiguous;
  impl Chunking for Contiguous {}

  pub struct Streaming;
  impl Chunking for Streaming {}
}

pub mod interval {
  pub type Index = u64;

  primitive_wrapper![Offset, Index];

  pub struct Interval {
    pub left: Offset,
    pub right: Offset,
  }
}

pub mod result {
  pub trait Result {}

  pub struct DidNotMatch;
  impl Result for DidNotMatch {}

  pub struct Matched<T>(pub T);
  impl<T> Result for Matched<T> {}
}

pub mod anchor {
  pub trait Anchoring {}

  pub trait AnchorInto<T> {}

  pub struct DoublyAnchored;
  impl Anchoring for DoublyAnchored {}

  pub struct Left;
  impl Anchoring for Left {}

  pub struct Right;
  impl Anchoring for Right {}

  pub struct Unanchored;
  impl Anchoring for Unanchored {}
}

pub mod params {
  pub trait Params {
    /* TODO: */
    /* type S: super::alphabet::Symbol; */
  }

  pub struct Single;
  impl Params for Single {}

  pub struct MultipleParallel;
  impl Params for MultipleParallel {}
}

pub mod alphabet {
  use core::hash::Hash;

  /* use indexmap::IndexSet; */

  pub trait Symbol: Hash+Eq {}

  /* pub struct Alphabet<S>(pub IndexSet<S>) */
  /* where S: Symbol; */
}

pub trait Automaton {
  type P: params::Params;
  type C: chunk::Chunking;
  type A: anchor::Anchoring;

  /* fn invoke(&self) -> A::Out; */
}

pub trait Builder {
  type I: input::Input;
  type S: alphabet::Symbol;
  type Out<P, C, A>: Automaton<P=P, C=C, A=A>
  where
    P: params::Params,
    C: chunk::Chunking,
    A: anchor::Anchoring;

  fn build<P, C, A>(p: P, c: C, a: A) -> Self::Out<P, C, A>
  where
    P: params::Params,
    C: chunk::Chunking,
    A: anchor::Anchoring;
}

/* pub struct Literal(pub String); */
