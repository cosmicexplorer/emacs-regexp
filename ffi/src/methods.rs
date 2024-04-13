/* Description: FFI methods exposed over the C ABI.

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

//! FFI methods exposed over the C ABI.

use core::mem::MaybeUninit;

use emacs_regexp::syntax::parser::parse_bytes;

use crate::objects::{
  CallbackAllocator, Input, Matcher, OwnedExpr, OwnedSlice, Pattern, RegexpError,
};

#[no_mangle]
pub extern "C" fn always_panic() {
  todo!("this always panics!");
}

/// asdf
#[must_use]
#[no_mangle]
pub extern "C" fn compile(
  pattern: &Pattern,
  alloc: &CallbackAllocator,
  out: &mut MaybeUninit<Matcher>,
) -> RegexpError {
  let (out_d, out_e) = Matcher::destructure_output_fields(out);
  let alloc = *alloc;
  /* Dereference the byte string data, and hope it's valid! */
  let p = unsafe { pattern.data.data() };

  RegexpError::wrap(move || {
    /* Copy the string data into our own allocator.
     * (FIXME: THIS IS FOR TESTING!!) */
    let d = OwnedSlice::from_data(p, alloc);
    out_d.write(d);

    /* Parse the pattern string into an AST! */
    let e = {
      let expr = parse_bytes(p, alloc).map_err(|_| RegexpError::ParseError)?;
      OwnedExpr::from_expr(expr, alloc)
    };
    out_e.write(e);

    Ok(())
  })
}

#[must_use]
#[no_mangle]
pub extern "C" fn execute(
  matcher: &Matcher,
  _alloc: &CallbackAllocator,
  input: &Input,
) -> RegexpError {
  /* Get the matcher slice to compare against.
   * (FIXME: THIS IS FOR TESTING!!) */
  let d = matcher.data.data();
  /* Dereference the byte string data, and hope it's valid! */
  let i = unsafe { input.data.data() };

  RegexpError::wrap(|| {
    if i == d {
      Ok(())
    } else {
      Err(RegexpError::MatchError)
    }
  })
}


#[cfg(test)]
mod test {
  use super::*;
  use crate::objects::ForeignSlice;

  #[test]
  fn basic_workflow() {
    let s = ForeignSlice::from_data(b"asdf");
    let p = Pattern { data: s };
    let c = CallbackAllocator::LIBC_ALLOC;

    let mut m: MaybeUninit<Matcher> = MaybeUninit::uninit();
    assert_eq!(compile(&p, &c, &mut m), RegexpError::None);
    let m = unsafe { m.assume_init() };
    let ast = format!("{:?}", m.expr.expr());
    assert_eq!(ast, "Expr::Concatenation { components: [Expr::SingleLiteral(SingleLiteral(97)), Expr::SingleLiteral(SingleLiteral(115)), Expr::SingleLiteral(SingleLiteral(100)), Expr::SingleLiteral(SingleLiteral(102))] }");

    let i = Input { data: s };
    assert_eq!(execute(&m, &c, &i), RegexpError::None);

    let s2 = ForeignSlice::from_data(b"bsdf");
    let i2 = Input { data: s2 };
    assert_eq!(execute(&m, &c, &i2), RegexpError::MatchError);
  }

  #[test]
  fn parse_error() {
    /* This fails because it has a close group without any open group. */
    let s = ForeignSlice::from_data(b"as\\)");
    let p = Pattern { data: s };
    let c = CallbackAllocator::LIBC_ALLOC;

    let mut m: MaybeUninit<Matcher> = MaybeUninit::uninit();
    assert_eq!(compile(&p, &c, &mut m), RegexpError::ParseError);
  }
}
