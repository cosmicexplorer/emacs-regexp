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

use core::{alloc::Allocator, fmt, hash::BuildHasherDefault};

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


mod builder {
  use core::{alloc::Allocator, cell::RefCell};

  use emacs_regexp_syntax::{
    ast::{
      expr::Expr,
      literals::single::{escapes::Escaped, SingleLiteral},
    },
    encoding::LiteralEncoding,
  };

  use super::NFAConstructionError;
  use crate::alloc_types::*;

  struct StateRef<Sym, A: Allocator>(rc::Weak<RefCell<Node<Sym, A>>, A>);

  enum Transition<Sym, A: Allocator> {
    SingleEpsilon(StateRef<Sym, A>),
    MultiEpsilon(Vec<StateRef<Sym, A>, A>),
    Symbol(Sym, StateRef<Sym, A>),
    Final,
  }

  struct Node<Sym, A: Allocator>(Transition<Sym, A>);

  struct Universe<Sym, A: Allocator>(Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A>);

  impl<Sym, A> Universe<Sym, A>
  where A: Allocator+Clone
  {
    pub fn for_single_literal<L>(lit: SingleLiteral<L>, alloc: A) -> Self
    where
      L: LiteralEncoding,
      Sym: From<L::Single>,
    {
      let mut states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let fin: rc::Rc<RefCell<Node<Sym, A>>, A> =
        rc::Rc::new_in(RefCell::new(Node(Transition::Final)), alloc.clone());
      let fin_ref = StateRef(rc::Rc::downgrade(&fin));
      states.push(fin);

      let SingleLiteral(lit) = lit;
      let start = rc::Rc::new_in(
        RefCell::new(Node(Transition::Symbol(lit.into(), fin_ref))),
        alloc,
      );
      states.push(start);

      Self(states)
    }

    pub fn for_escaped_literal<L>(lit: Escaped<L>, alloc: A) -> Self
    where
      L: LiteralEncoding,
      Sym: From<L::Single>,
    {
      let mut states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let fin: rc::Rc<RefCell<Node<Sym, A>>, A> =
        rc::Rc::new_in(RefCell::new(Node(Transition::Final)), alloc.clone());
      let fin_ref = StateRef(rc::Rc::downgrade(&fin));
      states.push(fin);

      let Escaped(SingleLiteral(lit)) = lit;
      let start = rc::Rc::new_in(
        RefCell::new(Node(Transition::Symbol(lit.into(), fin_ref))),
        alloc,
      );
      states.push(start);

      Self(states)
    }
  }
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

#[derive(Clone)]
pub enum Transition<Sym, A: Allocator> {
  SingleEpsilon(State),
  MultiEpsilon(Vec<State, A>),
  Symbol(Sym, State),
  Final,
}

impl<Sym, A> PartialEq for Transition<Sym, A>
where
  Sym: PartialEq,
  A: Allocator,
{
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::SingleEpsilon(s1), Self::SingleEpsilon(s2)) => s1.eq(s2),
      (Self::MultiEpsilon(m1), Self::MultiEpsilon(m2)) => m1.eq(m2),
      (Self::Symbol(y1, s1), Self::Symbol(y2, s2)) => y1.eq(y2) && s1.eq(s2),
      (Self::Final, Self::Final) => true,
      _ => false,
    }
  }
}

impl<Sym, A> Eq for Transition<Sym, A>
where
  Sym: PartialEq+Eq,
  A: Allocator,
{
}

impl<Sym, A> fmt::Debug for Transition<Sym, A>
where
  Sym: fmt::Debug,
  A: Allocator,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::SingleEpsilon(s) => write!(f, "Transition::SingleEpsilon({s:?})"),
      Self::MultiEpsilon(m) => write!(f, "Transition::MultiEpsilon({m:?})"),
      Self::Symbol(y, s) => write!(f, "Transition::Symbol({y:?}, {s:?})"),
      Self::Final => write!(f, "Transition::Final"),
    }
  }
}

#[derive(Clone)]
pub struct Node<Sym, A: Allocator> {
  trans: Transition<Sym, A>,
}

impl<Sym, A> PartialEq for Node<Sym, A>
where
  Sym: PartialEq,
  A: Allocator,
{
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self { trans: t1 }, Self { trans: t2 }) => t1.eq(t2),
    }
  }
}

impl<Sym, A> Eq for Node<Sym, A>
where
  Sym: PartialEq+Eq,
  A: Allocator,
{
}

impl<Sym, A> fmt::Debug for Node<Sym, A>
where
  Sym: fmt::Debug,
  A: Allocator,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Node {{ trans: {:?} }}", &self.trans)
  }
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
        Transition::SingleEpsilon(State(ref mut state)) => {
          *state += shift;
        },
        Transition::MultiEpsilon(ref mut to_states) => {
          to_states.iter_mut().for_each(|State(ref mut to)| {
            *to += shift;
          })
        },
        Transition::Symbol(_, State(ref mut state)) => {
          *state += shift;
        },
        Transition::Final => (),
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
          trans: Transition::Final,
        });
        ret.insert_new_state(Node {
          trans: Transition::Symbol(sl.into(), final_state),
        });
        Ok(ret)
      },
      Expr::EscapedLiteral(Escaped(SingleLiteral(el))) => {
        let mut ret = Self::new_in(alloc);
        let final_state = ret.insert_new_state(Node {
          trans: Transition::Final,
        });
        ret.insert_new_state(Node {
          trans: Transition::Symbol(el.into(), final_state),
        });
        Ok(ret)
      },
      Expr::Backref(_) => Err(NFAConstructionError::Backref),
      Expr::Alternation { cases } => {
        let mut ret = Self::new_in(alloc.clone());
        let final_state = ret.insert_new_state(Node {
          trans: Transition::Final,
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
          if let Transition::Final = trans {
            *trans = Transition::SingleEpsilon(new_final);
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
          trans: Transition::MultiEpsilon(start_states),
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
          if let Transition::Final = trans {
            *trans = Transition::SingleEpsilon(next_start);
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

impl<Sym, A> PartialEq for Universe<Sym, A>
where
  Sym: PartialEq,
  A: Allocator,
{
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Self { states: s1 }, Self { states: s2 }) => s1.eq(s2),
    }
  }
}

impl<Sym, A> Eq for Universe<Sym, A>
where
  Sym: PartialEq+Eq,
  A: Allocator,
{
}

impl<Sym, A> fmt::Debug for Universe<Sym, A>
where
  Sym: fmt::Debug,
  A: Allocator,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    write!(f, "Universe {{ states: {:?} }}", &self.states)
  }
}

#[cfg(test)]
mod test {
  use std::alloc::Global;

  use emacs_regexp_syntax::{encoding::UnicodeEncoding, parser::parse};

  use super::*;

  #[test]
  fn compile_single_lit() {
    let expr = parse::<UnicodeEncoding, _>("a", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr).unwrap();
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Final
        },
        Node {
          trans: Transition::Symbol('a', State(0))
        },
      ]
    });
  }

  #[test]
  fn compile_concat() {
    let expr = parse::<UnicodeEncoding, _>("ab", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr).unwrap();
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Final
        },
        Node {
          trans: Transition::Symbol('b', State(0))
        },
        Node {
          trans: Transition::Symbol('a', State(1))
        },
      ]
    });
  }
}

/* TODO: NFA parser! */
/* struct M<A> */
/* where A: Allocator */
/* { */
/* m: IndexMap<usize, usize, BuildHasherDefault<FxHasher>, A>, */
/* } */
