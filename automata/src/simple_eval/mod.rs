/* Description: Left-to-right evaluation (parsing) methods.

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

//! Left-to-right evaluation (parsing) methods.

pub trait SearchState<Eval: ?Sized> {
  type Args;

  fn create(args: Self::Args) -> Self;
  fn reset(&mut self, eval: &Eval);
}

pub trait SimpleEvaluator<Cache: SearchState<Self>> {
  type Tok;
  type Success;
  type Err;

  fn create_cache(&self, args: Cache::Args) -> Cache {
    let mut cache = Cache::create(args);
    cache.reset(self);
    cache
  }

  fn evaluate(
    &self,
    cache: &mut Cache,
    tokens: impl Iterator<Item=Self::Tok>,
  ) -> Result<Self::Success, Self::Err>;
}


pub mod nfa {
  use core::{alloc::Allocator, hash::BuildHasherDefault};

  use emacs_regexp_syntax::encoding::LiteralEncoding;
  use indexmap::IndexSet;
  use rustc_hash::FxHasher;

  use super::{SearchState, SimpleEvaluator};
  use crate::{alloc_types::*, nfa};

  pub struct NFAEvaluator<L: LiteralEncoding, A: Allocator> {
    nfa: nfa::Universe<L::Single, A>,
  }

  impl<L, A> NFAEvaluator<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    pub const fn from_nfa(nfa: nfa::Universe<L::Single, A>) -> Self { Self { nfa } }
  }

  pub struct NFACache<A: Allocator> {
    current_states: IndexSet<nfa::State, BuildHasherDefault<FxHasher>, A>,
  }

  impl<A> NFACache<A>
  where A: Allocator
  {
    pub fn new(alloc: A) -> Self
    where A: Clone {
      Self {
        current_states: IndexSet::with_hasher_in(Default::default(), alloc),
      }
    }

    pub fn drain(&mut self) -> impl Iterator<Item=nfa::State>+'_ { self.current_states.drain(..) }
  }

  impl<L, ANFA, ACache> SearchState<NFAEvaluator<L, ANFA>> for NFACache<ACache>
  where
    L: LiteralEncoding,
    ANFA: Allocator,
    ACache: Allocator+Clone,
  {
    type Args = ACache;

    fn create(args: Self::Args) -> Self { Self::new(args) }

    fn reset(&mut self, eval: &NFAEvaluator<L, ANFA>) {
      self.current_states.clear();
      let initial_state = nfa::State::zero();
      assert!(eval.nfa.lookup_state(initial_state).is_some());
      assert!(self.current_states.insert(initial_state));
    }
  }

  impl<L, ANFA, ACache> SimpleEvaluator<NFACache<ACache>> for NFAEvaluator<L, ANFA>
  where
    L: LiteralEncoding,
    ANFA: Allocator,
    ACache: Allocator+Clone,
  {
    type Tok = L::Single;
    type Success = usize;
    type Err = ();

    fn evaluate(
      &self,
      _cache: &mut NFACache<ACache>,
      mut tokens: impl Iterator<Item=Self::Tok>,
    ) -> Result<Self::Success, Self::Err> {
      if tokens.next().is_some() {
        Ok(0)
      } else {
        Err(())
      }
    }
  }

  #[cfg(test)]
  mod test {
    use std::alloc::Global;

    use emacs_regexp_syntax::{encoding::UnicodeEncoding, parser::parse};

    use super::*;

    #[test]
    fn eval_simple() {
      let expr = parse::<UnicodeEncoding, _>(".", Global).unwrap();
      let universe =
        nfa::Universe::<char, Global>::recursively_construct_from_regexp(expr).unwrap();

      let eval: NFAEvaluator<UnicodeEncoding, _> = NFAEvaluator::from_nfa(universe);
      let mut cache = eval.create_cache(Global);

      assert_eq!(
        eval.evaluate(&mut cache, UnicodeEncoding::iter("asdf")),
        Ok(0)
      );
      assert_eq!(
        eval.evaluate(&mut cache, UnicodeEncoding::iter("")),
        Err(())
      );
    }
  }
}
