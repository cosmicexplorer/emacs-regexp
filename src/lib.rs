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

pub enum LeftAnchoredMatchResult<S, C> {
  CompleteMatch(S, ComponentOffset),
  PartialMatch(S, C),
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

pub enum RightAnchoredMatchResult<S, C> {
  CompleteMatch(S, ComponentOffset),
  PartialMatch(S, C),
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

pub mod literal {
  use indexmap::IndexSet;
  use memchr::memmem;

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

  pub struct DoublyAnchoredMultipleLiterals<'n> {
    lits: IndexSet<&'n [u8]>,
  }
  impl<'n> DoublyAnchoredMultipleLiterals<'n> {
    pub fn new(lits: impl IntoIterator<Item=&'n [u8]>) -> Self {
      Self {
        lits: lits.into_iter().collect(),
      }
    }
  }
  impl<'n> DoublyAnchoredMatcher<'n> for DoublyAnchoredMultipleLiterals<'n> {
    type I = [u8];
    type S = usize;
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
      self.lits.get_index_of(i).into_iter()
    }
  }

  pub struct LeftLiteralContinuation<'n> {
    pub rest: &'n [u8],
  }
  impl<'n> continuation::Continuation for LeftLiteralContinuation<'n> {}

  pub struct LeftAnchoredSingleLiteral<'n> {
    lit: &'n [u8],
  }
  impl<'n> LeftAnchoredSingleLiteral<'n> {
    pub fn new(lit: &'n [u8]) -> Self { Self { lit } }
  }
  impl<'n> LeftAnchoredMatcher<'n> for LeftAnchoredSingleLiteral<'n> {
    type I = [u8];
    type S = ();
    type X = ();
    type C = LeftLiteralContinuation<'n>;
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
      let ret: Option<LeftAnchoredMatchResult<Self::S, Self::C>> = if i.len() >= self.lit.len() {
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
      };
      ret.into_iter()
    }
  }

  pub struct RightLiteralContinuation<'n> {
    pub rest: &'n [u8],
  }
  impl<'n> continuation::Continuation for RightLiteralContinuation<'n> {}

  pub struct RightAnchoredSingleLiteral<'n> {
    lit: &'n [u8],
  }
  impl<'n> RightAnchoredSingleLiteral<'n> {
    pub fn new(lit: &'n [u8]) -> Self { Self { lit } }
  }
  impl<'n> RightAnchoredMatcher<'n> for RightAnchoredSingleLiteral<'n> {
    type I = [u8];
    type S = ();
    type X = ();
    type C = RightLiteralContinuation<'n>;
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
      if i.len() >= self.lit.len() {
        if i.ends_with(self.lit) {
          Some(RightAnchoredMatchResult::CompleteMatch(
            (),
            ComponentOffset(self.lit.len().try_into().unwrap()),
          ))
        } else {
          None
        }
      } else {
        if self.lit.ends_with(i) {
          Some(RightAnchoredMatchResult::PartialMatch(
            (),
            RightLiteralContinuation {
              rest: &self.lit[..(self.lit.len() - i.len())],
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

  struct SingleLiteralRabinKarpIterator<'h, 'n> {
    finder: memmem::CompiledRabinKarpFinder<'n>,
    haystack: &'h [u8],
    pos: usize,
  }
  impl<'h, 'n> Iterator for SingleLiteralRabinKarpIterator<'h, 'n> {
    type Item =
      UnanchoredMatchResult<(), LeftLiteralContinuation<'n>, RightLiteralContinuation<'n>>;

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
      Some(UnanchoredMatchResult::CompleteMatch((), int))
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

  impl<'n> UnanchoredMatcher<'n> for UnanchoredSingleLiteralRabinKarp<'n> {
    type I = [u8];
    type S = ();
    type X = ();
    type LC = LeftLiteralContinuation<'n>;
    type RC = RightLiteralContinuation<'n>;
    fn invoke<'s, 'x, 'h>(
      &'s self,
      _x: &'x mut Self::X,
      i: &'h Self::I,
    ) -> impl Iterator<Item=UnanchoredMatchResult<Self::S, Self::LC, Self::RC>>+'s+'x+'h
    where
      'x: 'n,
      'n: 'x,
      's: 'n,
      'n: 'h,
      'h: 'n,
    {
      SingleLiteralRabinKarpIterator {
        finder: self.finder.as_ref(),
        haystack: i,
        pos: 0,
      }
    }
  }

  /* TODO: backwards? */
  pub struct UnanchoredSingleLiteralMemMem<'n> {
    finder: memmem::Finder<'n>,
  }
  impl<'n> UnanchoredSingleLiteralMemMem<'n> {
    pub fn new(lit: &'n [u8]) -> Self {
      Self {
        finder: memmem::Finder::new(lit),
      }
    }
  }

  impl state::State for memmem::PrefilterState {}

  struct SingleLiteralMemMemIterator<'x, 'h, 'n> {
    finder: memmem::Finder<'n>,
    prestate: &'x mut memmem::PrefilterState,
    haystack: &'h [u8],
    pos: usize,
  }
  impl<'x, 'h, 'n> Iterator for SingleLiteralMemMemIterator<'x, 'h, 'n> {
    type Item =
      UnanchoredMatchResult<(), LeftLiteralContinuation<'n>, RightLiteralContinuation<'n>>;

    fn next(&mut self) -> Option<Self::Item> {
      let haystack = self.haystack.get(self.pos..)?;
      let idx = self.finder.find_state(self.prestate, haystack)?;
      /* Iterate to the beginning of the match. */
      let pos = self.pos + idx;
      /* NB: Now go exactly one past, so we can find overlapping matches! */
      self.pos = pos + 1;

      let int = IntraComponentInterval {
        left: ComponentOffset(pos.try_into().unwrap()),
        right: ComponentOffset((pos + self.finder.needle().len()).try_into().unwrap()),
      };
      Some(UnanchoredMatchResult::CompleteMatch((), int))
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

  impl<'n> UnanchoredMatcher<'n> for UnanchoredSingleLiteralMemMem<'n> {
    type I = [u8];
    type S = ();
    type X = memmem::PrefilterState;
    type LC = LeftLiteralContinuation<'n>;
    type RC = RightLiteralContinuation<'n>;
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
      'h: 'n,
    {
      SingleLiteralMemMemIterator {
        finder: self.finder.as_ref(),
        prestate: x,
        haystack: i,
        pos: 0,
      }
    }
  }


  #[cfg(test)]
  mod test {
    use super::*;

    #[test]
    fn doubly_anchored_match() {
      let s = b"asdf";
      let s: &[u8] = s.as_ref();
      let m = literal::DoublyAnchoredSingleLiteral::new(s);
      assert_eq!(m.invoke(&mut (), &s).count(), 1);

      let s_wrong = b"f";
      let s_wrong: &[u8] = s_wrong.as_ref();
      assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0);
    }

    #[test]
    fn doubly_multiple() {
      let s1 = b"asdf";
      let s1: &[u8] = s1.as_ref();
      let s2 = b"wow";
      let s2: &[u8] = s2.as_ref();
      let m = literal::DoublyAnchoredMultipleLiterals::new([s1, s2]);
      assert_eq!(m.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![0]);
      assert_eq!(m.invoke(&mut (), &s2).collect::<Vec<_>>(), vec![1]);

      let s_wrong = b"f";
      let s_wrong: &[u8] = s_wrong.as_ref();
      assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0);
    }
  }
}
