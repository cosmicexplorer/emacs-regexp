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

use core::{alloc::Allocator, fmt, hash::BuildHasherDefault, mem, num::NonZeroUsize};

use emacs_regexp_syntax::{ast::expr::Expr, encoding::LiteralEncoding};
use indexmap::IndexMap;
use rustc_hash::FxHasher;
use smallvec::SmallVec;

use crate::alloc_types::*;

cfg_if::cfg_if! {
  if #[cfg(test)] {
    trait MaybeDebug<T> = From<T> + fmt::Debug;
  } else {
    trait MaybeDebug<T> = From<T>;
  }
}

mod builder {
  use core::{alloc::Allocator, cell::RefCell, fmt, mem, num::NonZeroUsize, ops};

  use emacs_regexp_syntax::{
    ast::{
      expr::Expr,
      groups::{Backref, BackrefIndex, ExplicitGroupIndex, GroupKind},
      literals::single::{escapes::Escaped, SingleLiteral},
      postfix_operators::{GreedyBehavior, MaybeGreedyOperator, PostfixOp, SimpleOperator},
    },
    encoding::LiteralEncoding,
  };

  use super::MaybeDebug;
  use crate::alloc_types::*;

  pub struct StateRef<Sym, A: Allocator>(pub rc::Weak<RefCell<Node<Sym, A>>, A>);

  impl<Sym, A> fmt::Debug for StateRef<Sym, A>
  where A: Allocator
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { self.0.fmt(f) }
  }

  impl<Sym, A> Clone for StateRef<Sym, A>
  where A: Allocator+Clone
  {
    fn clone(&self) -> Self { Self(self.0.clone()) }
  }

  pub enum Transition<Sym, A: Allocator> {
    SingleEpsilon(StateRef<Sym, A>),
    MultiEpsilon(Vec<StateRef<Sym, A>, A>),
    Symbol(RefCell<Option<Sym>>, StateRef<Sym, A>),
    StartGroup(Option<NonZeroUsize>, StateRef<Sym, A>),
    EndGroup(StateRef<Sym, A>),
    Backref(NonZeroUsize, StateRef<Sym, A>),
    Final,
  }

  impl<Sym, A> fmt::Debug for Transition<Sym, A>
  where
    Sym: fmt::Debug,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::SingleEpsilon(sr) => write!(f, "Transition::SingleEpsilon({sr:?})"),
        Self::MultiEpsilon(m) => write!(f, "Transition::MultiEpsilon({m:?})"),
        Self::Symbol(sym, sr) => write!(f, "Transition::Symbol({sym:?}, {sr:?})"),
        Self::StartGroup(i, s) => write!(f, "Transition::StartGroup({i:?}, {s:?})"),
        Self::EndGroup(s) => write!(f, "Transition::EndGroup({s:?})"),
        Self::Backref(i, s) => write!(f, "Transition::Backref({i:?}, {s:?})"),
        Self::Final => write!(f, "Transition::Final"),
      }
    }
  }

  pub struct Node<Sym, A: Allocator>(pub Transition<Sym, A>);

  impl<Sym, A> fmt::Debug for Node<Sym, A>
  where
    Sym: fmt::Debug,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Node({:?})", &self.0) }
  }

  pub struct Universe<Sym, A: Allocator>(pub Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A>);

  impl<Sym, A> fmt::Debug for Universe<Sym, A>
  where
    Sym: fmt::Debug,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Universe({:?})", &self.0) }
  }

  impl<Sym, A> Universe<Sym, A>
  where
    Sym: MaybeDebug<Sym>,
    A: Allocator+Clone,
  {
    fn for_single_literal<L>(lit: SingleLiteral<L>, alloc: A) -> Self
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
        RefCell::new(Node(Transition::Symbol(
          RefCell::new(Some(lit.into())),
          fin_ref,
        ))),
        alloc,
      );
      states.push(start);

      Self(states)
    }

    fn for_escaped_literal<L>(lit: Escaped<L>, alloc: A) -> Self
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
        RefCell::new(Node(Transition::Symbol(
          RefCell::new(Some(lit.into())),
          fin_ref,
        ))),
        alloc,
      );
      states.push(start);

      Self(states)
    }

    fn for_backref(backref: Backref, alloc: A) -> Self {
      let mut states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let fin: rc::Rc<RefCell<Node<Sym, A>>, A> =
        rc::Rc::new_in(RefCell::new(Node(Transition::Final)), alloc.clone());
      let fin_ref = StateRef(rc::Rc::downgrade(&fin));
      states.push(fin);

      let Backref(BackrefIndex(backref_index)) = backref;
      let backref_index: usize = backref_index.into();
      let backref_index = NonZeroUsize::new(backref_index).unwrap();
      let start = rc::Rc::new_in(
        RefCell::new(Node(Transition::Backref(backref_index, fin_ref))),
        alloc,
      );
      states.push(start);

      Self(states)
    }

    fn assert_final_state(node: impl ops::Deref<Target=Node<Sym, A>>) {
      match *node {
        Node(Transition::Final) => (),
        _ => unreachable!("expected final state was not final"),
      }
    }

    fn for_postfix(inner: Self, op: PostfixOp, alloc: A) -> Self {
      match op {
        PostfixOp::Simple(MaybeGreedyOperator { op, greediness }) => {
          Self::for_simple_postfix(inner, op, greediness, alloc)
        },
        PostfixOp::Repeat(_) => todo!("repeat not yet implemented"),
      }
    }

    fn for_simple_postfix(
      inner: Self,
      op: SimpleOperator,
      greediness: GreedyBehavior,
      alloc: A,
    ) -> Self {
      match op {
        /* For the kleene star, compose it as ((<x>)+)?. */
        SimpleOperator::Star => {
          let as_plus = Self::for_plus(inner, greediness, alloc.clone());
          Self::for_question(as_plus, greediness, alloc)
        },
        SimpleOperator::Plus => Self::for_plus(inner, greediness, alloc),
        SimpleOperator::Question => Self::for_question(inner, greediness, alloc),
      }
    }

    fn for_plus(inner: Self, greediness: GreedyBehavior, alloc: A) -> Self {
      let mut all_states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let fin: rc::Rc<RefCell<Node<Sym, A>>, A> =
        rc::Rc::new_in(RefCell::new(Node(Transition::Final)), alloc.clone());
      let fin_ref = StateRef(rc::Rc::downgrade(&fin));
      all_states.push(fin);

      let Self(inner) = inner;
      /* Get a reference to the inner start state. */
      let inner_start = StateRef(rc::Rc::downgrade(inner.last().unwrap()));
      /* Make the inner end choose to point to either the new final, or the inner
       * start. */
      {
        let mut alternates: Vec<StateRef<Sym, A>, A> = Vec::with_capacity_in(2, alloc.clone());
        match greediness {
          /* If greedy, prefer the longer route. */
          GreedyBehavior::Greedy => {
            alternates.push(inner_start);
            alternates.push(fin_ref);
          },
          /* If non-greedy, prefer the shorter route. */
          GreedyBehavior::NonGreedy => {
            alternates.push(fin_ref);
            alternates.push(inner_start);
          },
        }

        let inner_end = inner.first().unwrap();
        Self::assert_final_state(inner_end.borrow());
        let mut inner_end = inner_end.borrow_mut();
        *inner_end = Node(Transition::MultiEpsilon(alternates));
      }

      /* Add all inner states to the universe. */
      all_states.extend(inner);

      Self(all_states)
    }

    fn for_question(inner: Self, greediness: GreedyBehavior, alloc: A) -> Self {
      let mut all_states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let Self(inner) = inner;
      /* Get references to the inner start and final states. */
      let inner_end = {
        let inner_end = inner.first().unwrap();
        Self::assert_final_state(inner_end.borrow());
        StateRef(rc::Rc::downgrade(inner_end))
      };
      let inner_start = StateRef(rc::Rc::downgrade(inner.last().unwrap()));
      /* Add all inner states to the universe. */
      all_states.extend(inner);

      /* Add a start state that goes either directly to the final state or through
       * the inner start state. */
      let alternates: Vec<StateRef<Sym, A>, A> = {
        let mut alternates: Vec<StateRef<Sym, A>, A> = Vec::with_capacity_in(2, alloc.clone());
        match greediness {
          /* If greedy, prefer the longer route. */
          GreedyBehavior::Greedy => {
            alternates.push(inner_start);
            alternates.push(inner_end);
          },
          /* If non-greedy, prefer the shorter route. */
          GreedyBehavior::NonGreedy => {
            alternates.push(inner_end);
            alternates.push(inner_start);
          },
        }
        alternates
      };
      let st: rc::Rc<RefCell<Node<Sym, A>>, A> = rc::Rc::new_in(
        RefCell::new(Node(Transition::MultiEpsilon(alternates))),
        alloc,
      );
      all_states.push(st);

      Self(all_states)
    }

    fn for_group(inner: Self, kind: GroupKind, alloc: A) -> Self {
      let maybe_index: Option<NonZeroUsize> = match kind {
        GroupKind::Basic => None,
        /* For non-capturing groups, do not generate any additional bytecode. */
        GroupKind::Shy => return inner,
        GroupKind::ExplicitlyNumbered(ExplicitGroupIndex(index)) => Some(index),
      };

      let mut all_states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let fin: rc::Rc<RefCell<Node<Sym, A>>, A> =
        rc::Rc::new_in(RefCell::new(Node(Transition::Final)), alloc.clone());
      let fin_ref = StateRef(rc::Rc::downgrade(&fin));
      all_states.push(fin);

      let Self(inner) = inner;
      /* Make the end point to our newly allocated final state, closing the group
       * as we do so. */
      {
        let inner_end = inner.first().unwrap();
        Self::assert_final_state(inner_end.borrow());
        let mut inner_end = inner_end.borrow_mut();
        *inner_end = Node(Transition::EndGroup(fin_ref));
      }

      /* Make a new start which points to the internal start node, opening the
       * group as we do so. */
      let inner_start = StateRef(rc::Rc::downgrade(inner.last().unwrap()));

      /* Add the inner nodes to the current universe. */
      all_states.extend(inner);

      let st: rc::Rc<RefCell<Node<Sym, A>>, A> = rc::Rc::new_in(
        RefCell::new(Node(Transition::StartGroup(maybe_index, inner_start))),
        alloc,
      );
      all_states.push(st);

      Self(all_states)
    }

    fn for_alternations(cases: Vec<Self, A>, alloc: A) -> Self {
      let mut all_states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let fin: rc::Rc<RefCell<Node<Sym, A>>, A> =
        rc::Rc::new_in(RefCell::new(Node(Transition::Final)), alloc.clone());
      let fin_ref = StateRef(rc::Rc::downgrade(&fin));
      all_states.push(fin);

      /* Get references to all start and end states of each case, and add internal
       * states to the universe. */
      let mut start_states: Vec<StateRef<Sym, A>, A> =
        Vec::with_capacity_in(cases.len(), alloc.clone());
      let mut end_states: Vec<rc::Weak<RefCell<Node<Sym, A>>, A>, A> =
        Vec::with_capacity_in(cases.len(), alloc.clone());
      for Self(cur_states) in cases.into_iter().rev() {
        let cur_st = rc::Rc::downgrade(cur_states.last().unwrap());
        let cur_fin = rc::Rc::downgrade(cur_states.first().unwrap());
        start_states.push(StateRef(cur_st));
        end_states.push(cur_fin);
        all_states.extend(cur_states);
      }

      /* Mutate all end states to point to the new final state. */
      for cur_end in end_states.into_iter() {
        let cur_end = cur_end.upgrade().unwrap();
        Self::assert_final_state(cur_end.borrow());
        let mut cur_end = cur_end.borrow_mut();
        *cur_end = Node(Transition::SingleEpsilon(fin_ref.clone()));
      }
      /* Reverse the start states so the cases come out in the original order after
       * being reversed again in from_builder(). */
      start_states.reverse();
      /* Create a new start state with edges to the start of each case. */
      let st: rc::Rc<RefCell<Node<Sym, A>>, A> = rc::Rc::new_in(
        RefCell::new(Node(Transition::MultiEpsilon(start_states))),
        alloc,
      );
      all_states.push(st);

      Self(all_states)
    }

    fn for_concatenations(components: Vec<Self, A>, alloc: A) -> Self {
      let mut all_states: Vec<rc::Rc<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());

      let fin: rc::Rc<RefCell<Node<Sym, A>>, A> =
        rc::Rc::new_in(RefCell::new(Node(Transition::Final)), alloc.clone());
      let fin_ref = StateRef(rc::Rc::downgrade(&fin));
      all_states.push(fin);

      if components.is_empty() {
        return Self(all_states);
      }

      /* Get references to all start and end states of each case, and add internal
       * states to the universe. */
      let mut start_states: Vec<rc::Weak<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());
      let mut end_states: Vec<rc::Weak<RefCell<Node<Sym, A>>, A>, A> = Vec::new_in(alloc.clone());
      /* NB: We iterate in *REVERSE* so that *later* components are closer to the
       * *front*! */
      for Self(cur_states) in components.into_iter().rev() {
        let cur_st = rc::Rc::downgrade(cur_states.last().unwrap());
        let cur_fin = rc::Rc::downgrade(cur_states.first().unwrap());
        start_states.push(cur_st);
        end_states.push(cur_fin);
        all_states.extend(cur_states);
      }

      debug_assert_eq!(start_states.len(), end_states.len());
      /* Mutate all end states to point to the start state one *after* them. */
      for (i, cur_end) in end_states.into_iter().enumerate() {
        let cur_end = cur_end.upgrade().unwrap();
        Self::assert_final_state(cur_end.borrow());
        let mut cur_end = cur_end.borrow_mut();

        if i == 0 {
          /* The last end state (reversed) should point to the newly created final
           * state. */
          *cur_end = Node(Transition::SingleEpsilon(fin_ref.clone()));
        } else {
          debug_assert!(i > 0);
          let next_start = &start_states[i - 1];
          *cur_end = Node(Transition::SingleEpsilon(StateRef(next_start.clone())));
        }
      }
      /* Make a new start state, and point it to the first start state (at the
       * end). */
      let first_start = start_states.last().unwrap().clone();
      mem::drop(start_states);
      let st: rc::Rc<RefCell<Node<Sym, A>>, A> = rc::Rc::new_in(
        RefCell::new(Node(Transition::SingleEpsilon(StateRef(first_start)))),
        alloc,
      );
      all_states.push(st);

      Self(all_states)
    }

    pub fn recursively_construct_from_regexp<L>(expr: Expr<L, A>, alloc: A) -> Self
    where
      L: LiteralEncoding,
      Sym: From<L::Single>,
    {
      match expr {
        Expr::SingleLiteral(sl) => Self::for_single_literal(sl, alloc),
        Expr::EscapedLiteral(el) => Self::for_escaped_literal(el, alloc),
        Expr::Backref(br) => Self::for_backref(br, alloc),
        Expr::Postfix { inner, op } => {
          let inner = Self::recursively_construct_from_regexp(*inner, alloc.clone());
          Self::for_postfix(inner, op, alloc)
        },
        Expr::Group { kind, inner } => {
          let inner = Self::recursively_construct_from_regexp(*inner, alloc.clone());
          Self::for_group(inner, kind, alloc)
        },
        Expr::Alternation { cases } => {
          let mut sub_universes: Vec<Self, A> = Vec::new_in(alloc.clone());
          for c in cases.into_iter() {
            sub_universes.push(Self::recursively_construct_from_regexp(*c, alloc.clone()));
          }
          Self::for_alternations(sub_universes, alloc)
        },
        Expr::Concatenation { components } => {
          let mut sub_universes: Vec<Self, A> = Vec::new_in(alloc.clone());
          for c in components.into_iter() {
            sub_universes.push(Self::recursively_construct_from_regexp(*c, alloc.clone()));
          }
          Self::for_concatenations(sub_universes, alloc)
        },
        _ => todo!("expr type not yet implemented"),
      }
    }
  }
}


#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct State(usize);

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct GroupIndex(pub NonZeroUsize);

#[derive(Clone)]
pub enum Transition<Sym, A: Allocator> {
  SingleEpsilon(State),
  MultiEpsilon(SmallVec<State, A, 2>),
  Symbol(Sym, State),
  StartGroup(Option<GroupIndex>, State),
  EndGroup(State),
  Backref(GroupIndex, State),
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
      (Self::StartGroup(i1, s1), Self::StartGroup(i2, s2)) => i1.eq(i2) && s1.eq(s2),
      (Self::EndGroup(s1), Self::EndGroup(s2)) => s1.eq(s2),
      (Self::Backref(i1, s1), Self::Backref(i2, s2)) => i1.eq(i2) && s1.eq(s2),
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
      Self::StartGroup(i, s) => write!(f, "Transition::StartGroup({i:?}, {s:?})"),
      Self::EndGroup(s) => write!(f, "Transition::EndGroup({s:?})"),
      Self::Backref(i, s) => write!(f, "Transition::Backref({i:?}, {s:?})"),
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
  states: Box<[Node<Sym, A>], A>,
}

impl<Sym, A> Universe<Sym, A>
where A: Allocator
{
  #[inline(always)]
  pub fn lookup_state(&self, state: State) -> Option<&Node<Sym, A>> {
    let State(state) = state;
    self.states.get(state)
  }
}

#[allow(private_bounds)]
impl<Sym, A> Universe<Sym, A>
where
  Sym: MaybeDebug<Sym>,
  A: Allocator+Clone,
{
  fn from_builder(mut builder: builder::Universe<Sym, A>, alloc: A) -> Self {
    /* First, reverse all the states so they go from left to right. The builder
     * constructs them backwards. */
    builder.0.reverse();

    let mut all_states: Vec<Node<Sym, A>, A> =
      Vec::with_capacity_in(builder.0.len(), alloc.clone());
    let mut state_map: IndexMap<
      *const builder::Node<Sym, A>,
      State,
      BuildHasherDefault<FxHasher>,
      A,
    > = IndexMap::with_hasher_in(BuildHasherDefault::<FxHasher>::default(), alloc.clone());

    /* Associate each node location to an index in the resulting universe. */
    for (i, node) in builder.0.iter().enumerate() {
      let p: *const builder::Node<Sym, A> = node.as_ptr().cast_const();
      assert!(state_map.insert(p, State(i)).is_none());
    }

    /* Transform each reference-based node to an index-based node. */
    for node in builder.0.iter() {
      let src_p: *const builder::Node<Sym, A> = node.as_ptr().cast_const();

      let builder::Node(ref trans) = *node.borrow();
      let trans: Transition<Sym, A> = match trans {
        builder::Transition::SingleEpsilon(builder::StateRef(weak)) => {
          let p: *const builder::Node<Sym, A> = weak.upgrade().unwrap().as_ptr().cast_const();
          let state = state_map.get(&p).unwrap();
          Transition::SingleEpsilon(*state)
        },
        builder::Transition::MultiEpsilon(state_refs) => {
          let states: SmallVec<State, A, 2> = {
            let mut states: SmallVec<State, A, 2> =
              SmallVec::with_capacity_in(state_refs.len(), alloc.clone());
            for builder::StateRef(weak) in state_refs.iter() {
              let p: *const builder::Node<Sym, A> = weak.upgrade().unwrap().as_ptr().cast_const();
              let state = state_map.get(&p).unwrap();
              states.push(*state);
            }
            states
          };
          Transition::MultiEpsilon(states)
        },
        builder::Transition::Symbol(sym, builder::StateRef(weak)) => {
          let p: *const builder::Node<Sym, A> = weak.upgrade().unwrap().as_ptr().cast_const();
          let state = state_map.get(&p).unwrap();
          let sym: Sym = sym.borrow_mut().take().unwrap();
          Transition::Symbol(sym, *state)
        },
        builder::Transition::StartGroup(maybe_index, builder::StateRef(weak)) => {
          let maybe_index = maybe_index.map(GroupIndex);
          let p: *const builder::Node<Sym, A> = weak.upgrade().unwrap().as_ptr().cast_const();
          let state = state_map.get(&p).unwrap();
          Transition::StartGroup(maybe_index, *state)
        },
        builder::Transition::EndGroup(builder::StateRef(weak)) => {
          let p: *const builder::Node<Sym, A> = weak.upgrade().unwrap().as_ptr().cast_const();
          let state = state_map.get(&p).unwrap();
          Transition::EndGroup(*state)
        },
        builder::Transition::Backref(backref_index, builder::StateRef(weak)) => {
          let p: *const builder::Node<Sym, A> = weak.upgrade().unwrap().as_ptr().cast_const();
          let state = state_map.get(&p).unwrap();
          Transition::Backref(GroupIndex(*backref_index), *state)
        },
        builder::Transition::Final => Transition::Final,
      };

      /* Ensure the resulting state index is what we expect it to be. */
      let State(src_state_index) = state_map.get(&src_p).unwrap();
      assert_eq!(*src_state_index, all_states.len());
      /* Push the new node into the universe. */
      all_states.push(Node { trans });
    }
    mem::drop(builder);

    Self {
      states: all_states.into_boxed_slice(),
    }
  }

  pub fn recursively_construct_from_regexp_in<L>(expr: Expr<L, A>, alloc: A) -> Self
  where
    L: LiteralEncoding,
    Sym: From<L::Single>,
  {
    let builder = builder::Universe::recursively_construct_from_regexp(expr, alloc.clone());
    Self::from_builder(builder, alloc)
  }

  pub fn recursively_construct_from_regexp<L>(expr: Expr<L, A>) -> Self
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
  use smallvec::smallvec;

  use super::*;

  #[test]
  fn compile_empty() {
    let expr = parse::<UnicodeEncoding, _>("", Global).unwrap();
    let universe = Universe::<char, _>::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![Node {
        trans: Transition::Final
      },]
      .into_boxed_slice()
    });
  }

  #[test]
  fn compile_single_lit() {
    let expr = parse::<UnicodeEncoding, _>("a", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Symbol('a', State(1))
        },
        Node {
          trans: Transition::Final
        },
      ]
      .into_boxed_slice()
    });
  }

  #[test]
  fn compile_escaped_lit() {
    let expr = parse::<UnicodeEncoding, _>("\\+", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Symbol('+', State(1))
        },
        Node {
          trans: Transition::Final
        },
      ]
      .into_boxed_slice()
    });
  }

  #[test]
  fn compile_alt() {
    let expr = parse::<UnicodeEncoding, _>("a\\|b", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(1), State(3)])
        },
        Node {
          trans: Transition::Symbol('a', State(2))
        },
        Node {
          trans: Transition::SingleEpsilon(State(5))
        },
        Node {
          trans: Transition::Symbol('b', State(4))
        },
        Node {
          trans: Transition::SingleEpsilon(State(5))
        },
        Node {
          trans: Transition::Final
        },
      ]
      .into_boxed_slice()
    });
  }

  #[test]
  fn compile_concat() {
    let expr = parse::<UnicodeEncoding, _>("ab", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::SingleEpsilon(State(1))
        },
        Node {
          trans: Transition::Symbol('a', State(2))
        },
        Node {
          trans: Transition::SingleEpsilon(State(3))
        },
        Node {
          trans: Transition::Symbol('b', State(4))
        },
        Node {
          trans: Transition::SingleEpsilon(State(5))
        },
        Node {
          trans: Transition::Final
        },
      ]
      .into_boxed_slice()
    });
  }

  #[test]
  fn compile_group() {
    let expr = parse::<UnicodeEncoding, _>("\\(?:b\\)", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Symbol('b', State(1)),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });

    let expr = parse::<UnicodeEncoding, _>("\\(b\\)", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::StartGroup(None, State(1)),
        },
        Node {
          trans: Transition::Symbol('b', State(2)),
        },
        Node {
          trans: Transition::EndGroup(State(3)),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });

    let expr = parse::<UnicodeEncoding, _>("\\(?2:b\\)", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::StartGroup(NonZeroUsize::new(2).map(GroupIndex), State(1)),
        },
        Node {
          trans: Transition::Symbol('b', State(2)),
        },
        Node {
          trans: Transition::EndGroup(State(3)),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });
  }

  #[test]
  fn test_postfix() {
    let expr = parse::<UnicodeEncoding, _>("a?", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(1), State(2)]),
        },
        Node {
          trans: Transition::Symbol('a', State(2)),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });

    let expr = parse::<UnicodeEncoding, _>("a??", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(2), State(1)]),
        },
        Node {
          trans: Transition::Symbol('a', State(2)),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });

    let expr = parse::<UnicodeEncoding, _>("a+", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Symbol('a', State(1)),
        },
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(0), State(2)]),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });

    let expr = parse::<UnicodeEncoding, _>("a+?", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Symbol('a', State(1)),
        },
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(2), State(0)]),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });

    let expr = parse::<UnicodeEncoding, _>("a*", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(1), State(3)]),
        },
        Node {
          trans: Transition::Symbol('a', State(2)),
        },
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(1), State(3)]),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });

    let expr = parse::<UnicodeEncoding, _>("a*?", Global).unwrap();
    let universe = Universe::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(3), State(1)]),
        },
        Node {
          trans: Transition::Symbol('a', State(2)),
        },
        Node {
          trans: Transition::MultiEpsilon(smallvec![State(3), State(1)]),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });
  }

  #[test]
  fn test_backref() {
    let expr = parse::<UnicodeEncoding, _>("\\1", Global).unwrap();
    let universe = Universe::<char, _>::recursively_construct_from_regexp(expr);
    assert_eq!(universe, Universe {
      states: vec![
        Node {
          trans: Transition::Backref(GroupIndex(NonZeroUsize::new(1).unwrap()), State(1)),
        },
        Node {
          trans: Transition::Final,
        }
      ]
      .into_boxed_slice()
    });
  }
}

/* TODO: NFA parser! */
/* struct M<A> */
/* where A: Allocator */
/* { */
/* m: IndexMap<usize, usize, BuildHasherDefault<FxHasher>, A>, */
/* } */
