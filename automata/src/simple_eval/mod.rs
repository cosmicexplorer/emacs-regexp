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

pub trait SimpleEvaluator {
  type Tok;
  type Success;
  type Err;

  fn evaluate(&self, tokens: impl Iterator<Item=Self::Tok>) -> Result<Self::Success, Self::Err>;
}


pub mod nfa {
  use core::alloc::Allocator;

  use emacs_regexp_syntax::encoding::LiteralEncoding;

  use super::SimpleEvaluator;
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

  impl<L, A> SimpleEvaluator for NFAEvaluator<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    type Tok = L::Single;
    type Success = usize;
    type Err = ();

    fn evaluate(
      &self,
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
      assert_eq!(eval.evaluate(UnicodeEncoding::iter("asdf")), Ok(0));
      assert_eq!(eval.evaluate(UnicodeEncoding::iter("")), Err(()));
    }
  }
}
