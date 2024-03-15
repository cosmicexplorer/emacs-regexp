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
use core::hash::BuildHasherDefault;

use indexmap::IndexSet;
use memchr::memmem;
use rustc_hash::FxHasher;

use crate::{
  continuation, state, ComponentOffset, DoublyAnchoredMatcher, IntraComponentInterval,
  LeftAnchoredMatchResult, LeftAnchoredMatcher, RightAnchoredMatchResult, RightAnchoredMatcher,
  UnanchoredMatchResult, UnanchoredMatcher,
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

pub struct DoublyAnchoredMultipleLiterals<'n> {
  lits: IndexSet<&'n [u8], BuildHasherDefault<FxHasher>>,
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    let inner = SingleLiteralRabinKarpInnerMatchIterator {
      finder: self.finder.as_ref(),
      haystack: i,
      pos: 0,
    }
    .map(|int| UnanchoredMatchResult::CompleteMatch((), int));
    /* let left = */
    inner
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

struct SingleLiteralMemMemInnerMatchIterator<'x, 'h, 'n> {
  finder: memmem::Finder<'n>,
  prestate: &'x mut memmem::PrefilterState,
  haystack: &'h [u8],
  pos: usize,
}
impl<'x, 'h, 'n> Iterator for SingleLiteralMemMemInnerMatchIterator<'x, 'h, 'n> {
  type Item = IntraComponentInterval;

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
    SingleLiteralMemMemInnerMatchIterator {
      finder: self.finder.as_ref(),
      prestate: x,
      haystack: i,
      pos: 0,
    }
    .map(|int| UnanchoredMatchResult::CompleteMatch((), int))
  }
}


#[cfg(test)]
mod test {
  use super::*;

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
  fn doubly_multiple() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();
    let s2 = b"wow";
    let s2: &[u8] = s2.as_ref();
    let m = DoublyAnchoredMultipleLiterals::new([s1, s2]);
    assert_eq!(m.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![0]);
    assert_eq!(m.invoke(&mut (), &s2).collect::<Vec<_>>(), vec![1]);

    let s_wrong = b"f";
    let s_wrong: &[u8] = s_wrong.as_ref();
    assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0);
  }

  #[test]
  fn lr_match() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();

    let lm = LeftAnchoredSingleLiteral::new(s1);
    let rm = RightAnchoredSingleLiteral::new(s1);

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
      LeftAnchoredMatchResult::PartialMatch((), LeftLiteralContinuation {
        rest: b"sdf".as_ref()
      })
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
      RightAnchoredMatchResult::PartialMatch((), RightLiteralContinuation {
        rest: b"asd".as_ref()
      })
    ]);
    assert_eq!(rm.invoke(&mut (), &s_wrong).count(), 0);

    /* TODO: multiple matches! */
  }

  #[test]
  fn unanchored_rabin_karp() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();

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

    let m = UnanchoredSingleLiteralRabinKarp::new(s1);

    assert_eq!(m.invoke(&mut (), &s1).collect::<Vec<_>>(), vec![
      UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval {
        left: ComponentOffset(0),
        right: ComponentOffset(4),
      })
    ]);
    assert_eq!(m.invoke(&mut (), &sl).collect::<Vec<_>>(), vec![
      UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval {
        left: ComponentOffset(0),
        right: ComponentOffset(4),
      })
    ]);
    /* FIXME: partial matches for unanchored! */
    assert_eq!(m.invoke(&mut (), &sl2).count(), 0);
    assert_eq!(m.invoke(&mut (), &sr).collect::<Vec<_>>(), vec![
      UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval {
        left: ComponentOffset(3),
        right: ComponentOffset(7),
      })
    ]);
    /* FIXME: partial matches for unanchored! */
    assert_eq!(m.invoke(&mut (), &sr2).count(), 0);
    assert_eq!(m.invoke(&mut (), &s_wrong).count(), 0);
  }

  #[test]
  fn unanchored_memmem() {
    let s1 = b"asdf";
    let s1: &[u8] = s1.as_ref();

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

    let m = UnanchoredSingleLiteralMemMem::new(s1);
    let mut prestate = memmem::PrefilterState::new();

    assert_eq!(m.invoke(&mut prestate, &s1).collect::<Vec<_>>(), vec![
      UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval {
        left: ComponentOffset(0),
        right: ComponentOffset(4),
      })
    ]);
    assert_eq!(m.invoke(&mut prestate, &sl).collect::<Vec<_>>(), vec![
      UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval {
        left: ComponentOffset(0),
        right: ComponentOffset(4),
      })
    ]);
    /* FIXME: partial matches for unanchored! */
    assert_eq!(m.invoke(&mut prestate, &sl2).count(), 0);
    assert_eq!(m.invoke(&mut prestate, &sr).collect::<Vec<_>>(), vec![
      UnanchoredMatchResult::CompleteMatch((), IntraComponentInterval {
        left: ComponentOffset(3),
        right: ComponentOffset(7),
      })
    ]);
    /* FIXME: partial matches for unanchored! */
    assert_eq!(m.invoke(&mut prestate, &sr2).count(), 0);
    assert_eq!(m.invoke(&mut prestate, &s_wrong).count(), 0);
  }
}
