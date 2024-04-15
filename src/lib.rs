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
#![feature(error_in_core)]
#![feature(new_uninit)]
#![feature(maybe_uninit_write_slice)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

extern crate alloc;

use core::{alloc::Allocator, mem::MaybeUninit};

#[cfg(not(test))]
use ::alloc::boxed::Box;
use displaydoc::Display;
pub use emacs_regexp_syntax as syntax;
use emacs_regexp_syntax::{
  ast::expr::Expr,
  encoding::ByteEncoding,
  parser::{parse_bytes, ParseError},
};
use thiserror::Error;

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

pub struct Matcher<AData, AExpr>
where
  AData: Allocator,
  AExpr: Allocator,
{
  pub data: Box<[u8], AData>,
  pub expr: Expr<ByteEncoding, AExpr>,
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
    let expr: Expr<ByteEncoding, AExpr> = parse_bytes(data, alloc_expr)?;

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
