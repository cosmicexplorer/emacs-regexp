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

use core::{alloc::Allocator, fmt, mem::MaybeUninit, str};

use displaydoc::Display;
pub use emacs_regexp_syntax as syntax;
use emacs_regexp_syntax::{
  ast::expr::Expr,
  encoding::ByteEncoding,
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
use alloc_types::*;

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
pub struct Pattern<'n> {
  data: &'n [u8],
}

impl<'n> Pattern<'n> {
  #[inline(always)]
  pub const fn new(data: &'n [u8]) -> Self { Self { data } }
}

#[derive(Clone)]
pub struct Matcher<AData, AExpr>
where
  AData: Allocator,
  AExpr: Allocator,
{
  pub data: Box<[u8], AData>,
  pub expr: Expr<ByteEncoding, AExpr>,
}

impl<AData, AExpr> fmt::Debug for Matcher<AData, AExpr>
where
  AData: Allocator+Clone,
  AExpr: Allocator,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    let Self { data, expr } = self;
    let expr_display = crate::util::Writer::display_in(expr, Box::allocator(data).clone())?;
    let data = str::from_utf8(&data).expect("TODO: non-utf8 patterns!");
    write!(
      f,
      "Matcher {{ data: {:?}, expr({:?}): {:?} }}",
      data, expr_display, expr
    )
  }
}

impl<AData, AExpr> Matcher<AData, AExpr>
where
  AData: Allocator,
  AExpr: Allocator,
{
  pub fn compile(
    pattern: Pattern,
    alloc_data: AData,
    alloc_expr: AExpr,
  ) -> Result<Self, RegexpError>
  where
    AExpr: Clone,
  {
    let Pattern { data } = pattern;

    /* Copy the string data into our own allocator.
     * (FIXME: THIS IS FOR TESTING!!) */
    let new_data: Box<[u8], AData> = {
      let mut new_data: Box<[MaybeUninit<u8>], AData> =
        Box::new_uninit_slice_in(data.len(), alloc_data);
      MaybeUninit::copy_from_slice(new_data.as_mut(), data);
      unsafe { new_data.assume_init() }
    };

    /* Parse the pattern string into an AST! */
    let expr: Expr<ByteEncoding, AExpr> = parse::<ByteEncoding, _>(data, alloc_expr)?;

    Ok(Self {
      data: new_data,
      expr,
    })
  }

  pub fn execute(&self, input: Input) -> Result<(), RegexpError> {
    let Input { data: input_data } = input;
    let Self { data, .. } = self;

    /* (FIXME: THIS IS FOR TESTING!!) */
    if **data == *input_data {
      Ok(())
    } else {
      Err(RegexpError::MatchError)
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Input<'h> {
  data: &'h [u8],
}

impl<'h> Input<'h> {
  #[inline(always)]
  pub const fn new(data: &'h [u8]) -> Self { Self { data } }
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

  use super::*;

  #[test]
  fn basic_workflow() {
    let s = b"asdf";
    let p = Pattern { data: s };

    let m = Matcher::compile(p, Global, Global).unwrap();
    let ast = format!("{:?}", m.expr);
    assert_eq!(ast, "Expr::Concatenation { components: [Expr::SingleLiteral(SingleLiteral(97)), Expr::SingleLiteral(SingleLiteral(115)), Expr::SingleLiteral(SingleLiteral(100)), Expr::SingleLiteral(SingleLiteral(102))] }");

    let i = Input { data: s };
    m.execute(i).unwrap();

    let s2 = b"bsdf";
    let i2 = Input { data: s2 };
    match m.execute(i2) {
      Err(RegexpError::MatchError) => (),
      _ => unreachable!(),
    }
  }

  #[test]
  fn parse_error() {
    /* This fails because it has a close group without any open group. */
    let s = b"as\\)";
    let p = Pattern { data: s };

    assert!(matches!(
      Matcher::compile(p, Global, Global),
      Err(RegexpError::ParseError(_))
    ));
  }
}
