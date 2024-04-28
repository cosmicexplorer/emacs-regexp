/* Description: Implementation of emacs regex matching!

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

//! Implementation of emacs regex matching!

#![warn(rustdoc::missing_crate_level_docs)]
// #![warn(missing_docs)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]
#![feature(allocator_api)]
#![feature(layout_for_ptr)]
#![feature(error_in_core)]
#![feature(slice_ptr_get)]
#![feature(fmt_internals)]
#![feature(new_uninit)]
#![feature(maybe_uninit_write_slice)]
#![allow(internal_features)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

extern crate alloc;

use core::{alloc::Allocator, fmt, mem};

use displaydoc::Display;
pub use emacs_regexp_syntax as syntax;
use emacs_regexp_syntax::{
  ast::expr::Expr,
  encoding::LiteralEncoding,
  parser::{parse, ParseError},
};
use thiserror::Error;

pub mod nfa;

#[allow(unused_imports)]
mod alloc_types {
  /* no_std/no_main is enabled except for test environments, so we need to use
   * the special imports from the extern alloc crate. */
  cfg_if::cfg_if! {
    if #[cfg(test)] {
      pub use Box;
      pub use Vec;
    } else {
      pub use ::alloc::{boxed::Box, vec::Vec};
    }
  }
}

#[derive(Debug, Clone, Display, Error)]
pub enum RegexpError {
  /// parse error
  ParseError(#[from] ParseError),
  /// compile error
  CompileError,
  /// match error
  MatchError,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pattern<'n, L: LiteralEncoding> {
  data: L::Str<'n>,
}

impl<'n, L: LiteralEncoding> Pattern<'n, L> {
  #[inline(always)]
  pub const fn new(data: L::Str<'n>) -> Self { Self { data } }
}

#[derive(Clone)]
pub struct Matcher<L, AData, AExpr>
where
  L: LiteralEncoding,
  AData: Allocator,
  AExpr: Allocator,
{
  pub data: L::String<AData>,
  pub expr: Expr<L, AExpr>,
}

impl<L, AData, AExpr> fmt::Debug for Matcher<L, AData, AExpr>
where
  L: LiteralEncoding,
  L::Single: fmt::Debug,
  AData: Allocator+Clone,
  L::String<AData>: fmt::Debug,
  AExpr: Allocator,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let Self { data, expr } = self;
    let expr_display = crate::util::Writer::display_in(expr, L::str_allocator(data).clone())?;
    write!(
      f,
      "Matcher {{ data: {:?}, expr({:?}): {:?} }}",
      data, expr_display, expr
    )
  }
}

impl<L, AData, AExpr> Matcher<L, AData, AExpr>
where
  L: LiteralEncoding,
  L::Single: fmt::Debug,
  AData: Allocator,
  AExpr: Allocator,
{
  pub fn compile(
    pattern: Pattern<'_, L>,
    alloc_data: AData,
    alloc_expr: AExpr,
  ) -> Result<Self, RegexpError>
  where
    AExpr: Clone,
  {
    let Pattern { data } = pattern;

    /* Copy the string data into our own allocator.
     * (FIXME: THIS IS FOR TESTING!!) */
    let new_data = L::owned_str(data, alloc_data);

    /* Parse the pattern string into an AST! */
    let expr: Expr<L, AExpr> = parse::<L, _>(data, alloc_expr)?;

    Ok(Self {
      data: new_data,
      expr,
    })
  }

  pub fn execute<'i>(&self, input: Input<'i, L>) -> Result<(), RegexpError> {
    let Input { data: input_data } = input;
    let Self { data, .. } = self;

    /* (FIXME: THIS IS FOR TESTING!!) */
    let data: L::Str<'_> = L::str_ref(data);
    /* FIXME: fix covariance of L::str_ref()!!! */
    let data: L::Str<'i> = unsafe { mem::transmute(data) };
    if data == input_data {
      Ok(())
    } else {
      Err(RegexpError::MatchError)
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Input<'h, L: LiteralEncoding> {
  data: L::Str<'h>,
}

impl<'h, L: LiteralEncoding> Input<'h, L> {
  #[inline(always)]
  pub const fn new(data: L::Str<'h>) -> Self { Self { data } }
}

pub mod util {
  use core::{alloc::Allocator, fmt, str};

  pub use emacs_regexp_syntax::util::boxing;

  use crate::alloc_types::*;

  /// Mutable writable object that impls [`fmt::Write`].
  pub struct Writer<A: Allocator> {
    data: Vec<u8, A>,
  }

  impl<A: Allocator> Writer<A> {
    pub fn with_initial_capacity_in(len: usize, alloc: A) -> Self {
      Self {
        data: Vec::with_capacity_in(len, alloc),
      }
    }

    pub fn with_initial_capacity(len: usize) -> Self
    where A: Default {
      Self::with_initial_capacity_in(len, A::default())
    }

    pub fn data(&self) -> &[u8] { &self.data }

    pub fn into_boxed(self) -> Box<[u8], A> {
      let Self { data } = self;
      data.into_boxed_slice()
    }

    pub fn into_string(self) -> Box<str, A> {
      let b = self.into_boxed();
      unsafe { boxing::box_into_string(b) }
    }

    pub fn debug_in(x: impl fmt::Debug, alloc: A) -> Result<Box<str, A>, fmt::Error> {
      let mut w = Self::with_initial_capacity_in(50, alloc);
      {
        let mut f = fmt::Formatter::new(&mut w);
        x.fmt(&mut f)?;
      }
      Ok(w.into_string())
    }

    pub fn debug(x: impl fmt::Debug) -> Result<Box<str, A>, fmt::Error>
    where A: Default {
      Self::debug_in(x, A::default())
    }

    pub fn display_in(x: impl fmt::Display, alloc: A) -> Result<Box<str, A>, fmt::Error> {
      let mut w = Self::with_initial_capacity_in(50, alloc);
      {
        let mut f = fmt::Formatter::new(&mut w);
        x.fmt(&mut f)?;
      }
      Ok(w.into_string())
    }

    pub fn display(x: impl fmt::Display) -> Result<Box<str, A>, fmt::Error>
    where A: Default {
      Self::display_in(x, A::default())
    }
  }

  impl<A: Allocator> fmt::Write for Writer<A> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
      self.data.extend_from_slice(s.as_bytes());
      Ok(())
    }
  }
}

#[cfg(test)]
mod test {
  use std::alloc::Global;

  use emacs_regexp_syntax::encoding::UnicodeEncoding;

  use super::*;

  #[test]
  fn basic_workflow() {
    let s = "asdf";
    let p = Pattern { data: s };

    let m = Matcher::<UnicodeEncoding, _, _>::compile(p, Global, Global).unwrap();
    let ast = format!("{:?}", m.expr);
    assert_eq!(ast, "Expr::Concatenation { components: [Expr::SingleLiteral(SingleLiteral('a')), Expr::SingleLiteral(SingleLiteral('s')), Expr::SingleLiteral(SingleLiteral('d')), Expr::SingleLiteral(SingleLiteral('f'))] }");

    let i = Input { data: s };
    m.execute(i).unwrap();

    let s2 = "bsdf";
    let i2 = Input { data: s2 };
    match m.execute(i2) {
      Err(RegexpError::MatchError) => (),
      _ => unreachable!(),
    }
  }

  #[test]
  fn parse_error() {
    /* This fails because it has a close group without any open group. */
    let s = "as\\)";
    let p = Pattern { data: s };

    assert!(matches!(
      Matcher::<UnicodeEncoding, _, _>::compile(p, Global, Global),
      Err(RegexpError::ParseError(_))
    ));
  }
}
