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
#[derive(Clone, Debug)]
pub enum Transitions<Sym, A: Allocator> {
  SingleEpsilon(State),
  MultiEpsilon(Vec<State, A>),
  Symbol(Sym, State),
  Final,
}

#[derive(Clone, Debug)]
pub struct Node<Sym, A: Allocator> {
  trans: Transitions<Sym, A>,
}

#[derive(Clone)]
pub struct Universe<Sym, A: Allocator> {
  states: Vec<Node<Sym, A>, A>,
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
  pub fn first_mut(&mut self) -> Option<&mut Node<Sym, A>> { self.states.first_mut() }

  #[inline(always)]
  pub fn last_mut(&mut self) -> Option<&mut Node<Sym, A>> { self.states.last_mut() }

  #[inline(always)]
  pub fn len(&self) -> usize { self.states.len() }

  #[inline(always)]
  pub fn lookup_state(&self, state: State) -> Option<&Node<Sym, A>> {
    let State(state) = state;
    self.states.get(state)
  }

  #[inline]
  pub fn insert_new_state(&mut self, node: Node<Sym, A>) -> State {
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
        Transitions::MultiEpsilon(ref mut to_states) => {
          to_states.iter_mut().for_each(|State(ref mut to)| {
            *to += shift;
          })
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
      Expr::Alternation { cases } => {
        let mut ret = Self::new_in(alloc.clone());
        let final_state = ret.insert_new_state(Node {
          trans: Transitions::Final,
        });
        let new_final = State(0);

        /* Recursively construct sub-universes. */
        let mut sub_universes: Vec<Self, A> = Vec::with_capacity_in(cases.len(), alloc.clone());
        for (i, ref mut o) in cases
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
        /* We have added a new final state. */
        cur_shift.increase_shift(1);
        let mut cur_start_index: usize = 0;
        let mut start_states: Vec<State, A> =
          Vec::with_capacity_in(sub_universes.len(), alloc.clone());
        for (ref mut u, ref mut s) in sub_universes
          .iter_mut()
          .zip(start_states.spare_capacity_mut().iter_mut())
        {
          /* Shift states of each component according to the accumulated length
           * of prior components. */
          u.shift_states(cur_shift);

          /* Replace intermediate Final states with an epsilon transition to the new
           * final state. */
          let Node { ref mut trans } = u.first_mut().unwrap();
          if let Transitions::Final = trans {
            *trans = Transitions::SingleEpsilon(new_final);
          } else {
            unreachable!()
          }

          cur_shift.increase_shift(u.len());
          /* The start index of the current universe after shifting will be 1 less than
           * the resulting shift. */
          cur_start_index += u.len();
          debug_assert_eq!(cur_start_index, cur_shift.0 - 1);
          /* Record the shifted start state of this sub-universe. */
          s.write(State(cur_start_index));
        }
        unsafe {
          start_states.set_len(start_states.capacity());
        }
        for Self { states } in sub_universes.into_iter() {
          ret.states.extend(states);
        }

        ret.insert_new_state(Node {
          trans: Transitions::MultiEpsilon(start_states),
        });
        Ok(ret)
      },
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
          /* Initial states are at the end of each universe. Calculate the initial
           * state for the next universe, which is at the far end. */
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
      _ => todo!("unsupported expr case"),
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
