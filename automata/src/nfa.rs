/* Description: Non-deterministic finite automation structure.

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

//! Non-deterministic finite automation structure.

use core::{alloc::Allocator, hash::BuildHasherDefault};

use displaydoc::Display;
use emacs_regexp_syntax::{
  ast::{
    expr::Expr,
    literals::single::{escapes::Escaped, SingleLiteral},
  },
  encoding::LiteralEncoding,
};
use indexmap::IndexMap;
use rustc_hash::FxHasher;
use thiserror::Error;

use crate::alloc_types::*;

#[derive(Debug, Display, Error)]
pub enum NFAConstructionError {
  /// backref provided in AST
  Backref,
}


#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct State(usize);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct StateShift(usize);

impl StateShift {
  #[inline(always)]
  pub const fn zero() -> Self { Self(0) }

  #[inline(always)]
  pub fn increase_shift(&mut self, by: usize) {
    let Self(ref mut shift) = self;
    *shift = shift.checked_add(by).expect("shifted past usize!");
  }
}

/// NB: We avoid coalescing epsilon transitions at all!
#[derive(Copy, Clone, Debug)]
pub enum Transitions<Sym> {
  SingleEpsilon(State),
  DoubleEpsilon(State, State),
  Symbol(Sym, State),
  Final,
}

#[derive(Copy, Clone, Debug)]
pub struct Node<Sym> {
  trans: Transitions<Sym>,
}

#[derive(Clone)]
pub struct Universe<Sym, A: Allocator> {
  states: Vec<Node<Sym>, A>,
}

impl<Sym, A> Universe<Sym, A>
where A: Allocator
{
  pub const fn new_in(alloc: A) -> Self {
    Self {
      states: Vec::new_in(alloc),
    }
  }

  pub const fn new() -> Self
  where A: Default {
    Self::new_in(A::default())
  }

  #[inline(always)]
  pub fn first_mut(&mut self) -> Option<&mut Node<Sym>> { self.states.first_mut() }

  #[inline(always)]
  pub fn len(&self) -> usize { self.states.len() }

  #[inline(always)]
  pub fn lookup_state(&self, state: State) -> Option<&Node<Sym>> {
    let State(state) = state;
    self.states.get(state)
  }

  #[inline]
  pub fn insert_new_state(&mut self, node: Node<Sym>) -> State {
    let new_state = State(self.states.len());
    self.states.push(node);
    new_state
  }

  #[inline]
  pub fn shift_states(&mut self, shift: StateShift) {
    let StateShift(shift) = shift;
    if shift == 0 {
      return;
    }
    let Self { ref mut states } = self;
    states
      .iter_mut()
      .for_each(|Node { ref mut trans }| match trans {
        Transitions::SingleEpsilon(State(ref mut state)) => {
          *state += shift;
        },
        Transitions::DoubleEpsilon(State(ref mut state_a), State(ref mut state_b)) => {
          *state_a += shift;
          *state_b += shift;
        },
        Transitions::Symbol(_, State(ref mut state)) => {
          *state += shift;
        },
        Transitions::Final => (),
      });
  }
}

impl<Sym, A> Universe<Sym, A>
where
  /* FIXME: make this iterative instead to avoid cloning! */ A: Allocator+Clone
{
  pub fn recursively_construct_from_regexp_in<L>(
    expr: Expr<L, A>,
    alloc: A,
  ) -> Result<Self, NFAConstructionError>
  where
    L: LiteralEncoding,
    Sym: From<L::Single>,
  {
    match expr {
      Expr::SingleLiteral(SingleLiteral(sl)) => {
        let mut ret = Self::new_in(alloc);
        let final_state = ret.insert_new_state(Node {
          trans: Transitions::Final,
        });
        ret.insert_new_state(Node {
          trans: Transitions::Symbol(sl.into(), final_state),
        });
        Ok(ret)
      },
      Expr::EscapedLiteral(Escaped(SingleLiteral(el))) => {
        let mut ret = Self::new_in(alloc);
        let final_state = ret.insert_new_state(Node {
          trans: Transitions::Final,
        });
        ret.insert_new_state(Node {
          trans: Transitions::Symbol(el.into(), final_state),
        });
        Ok(ret)
      },
      Expr::Backref(_) => Err(NFAConstructionError::Backref),
      Expr::Concatenation { components } => {
        /* Recursively construct sub-universes. */
        let mut sub_universes: Vec<Self, A> =
          Vec::with_capacity_in(components.len(), alloc.clone());
        for (i, ref mut o) in components
          .into_iter()
          .zip(sub_universes.spare_capacity_mut().iter_mut())
        {
          o.write(Self::recursively_construct_from_regexp_in(
            *i,
            alloc.clone(),
          )?);
        }
        unsafe {
          sub_universes.set_len(sub_universes.capacity());
        }

        let mut cur_shift = StateShift::zero();
        for ref mut u in sub_universes.iter_mut() {
          /* Shift states of each component according to the accumulated length
           * of prior components. */
          u.shift_states(cur_shift);

          cur_shift.increase_shift(u.len());
        }

        let mut cur_shift = StateShift::zero();
        for i in 0..(sub_universes.len() - 1) {
          let next_len: usize = sub_universes.get(i + 1).unwrap().len();
          let cur: &mut Self = sub_universes.get_mut(i).unwrap();
          cur_shift.increase_shift(cur.len());
          let next_start = State(cur_shift.0 + next_len - 1);
          /* Replace intermediate Final states with an epsilon transition to
           * the next initial state! */
          let Node { ref mut trans } = cur.first_mut().unwrap();
          if let Transitions::Final = trans {
            *trans = Transitions::SingleEpsilon(next_start);
          } else {
            unreachable!()
          }
        }

        let mut ret = Self::new_in(alloc);
        for Self { states } in sub_universes.into_iter() {
          ret.states.extend(states);
        }
        Ok(ret)
      },
      _ => unreachable!(),
    }
  }

  pub fn recursively_construct_from_regexp<L>(
    expr: Expr<L, A>,
  ) -> Result<Self, NFAConstructionError>
  where
    L: LiteralEncoding,
    Sym: From<L::Single>,
    A: Default,
  {
    Self::recursively_construct_from_regexp_in(expr, A::default())
  }
}

struct M<A>
where A: Allocator
{
  m: IndexMap<usize, usize, BuildHasherDefault<FxHasher>, A>,
}
