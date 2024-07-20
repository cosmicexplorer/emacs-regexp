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

/* We require #[must_use] on the extern methods to generate
 * __attribute__((warn_unused_result)), and we employ #[must_use] on
 * RegexpError to get a rust-level assurance that the result is used. We
 * would like to generate a must_use annotation for the generated C bindings
 * as well, but this appears not to be possible for C: https://github.com/mozilla/cbindgen/blob/316298182ebf508240c95ddf9943556b2fb546e1/src/bindgen/ir/enumeration.rs#L705/. */
#![allow(clippy::double_must_use)]

//! FFI methods exposed over the C ABI.

use core::{ffi::c_char, mem::MaybeUninit, ptr::NonNull};

use emacs_regexp_syntax::encoding::MultibyteEncoding;

use crate::{
  alloc_types::*,
  objects::{CallbackAllocator, Input, Matcher, Pattern, SharedAllocator},
};

#[cfg(feature = "panic-testing")]
#[no_mangle]
pub extern "C" fn always_panic() -> ! { todo!("this always panics!") }

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq)]
#[must_use]
#[repr(u8)]
pub enum RegexpError {
  #[default]
  None = 0,
  DecodeError = 1,
  ParseError = 2,
  CompileError = 3,
  MatchError = 4,
}

impl RegexpError {
  #[inline(always)]
  pub fn wrap(f: impl FnOnce() -> Result<(), Self>) -> Self {
    match f() {
      Ok(()) => Self::None,
      Err(e) => {
        assert_ne!(
          e,
          Self::None,
          "regexp error of none was provided: this is a logic error"
        );
        e
      },
    }
  }
}

#[repr(C)]
pub union CompileResult {
  matcher: Matcher,
  error: Option<NonNull<c_char>>,
}

/// asdf
#[must_use]
#[no_mangle]
pub extern "C" fn rex_compile(
  pattern: &Pattern,
  alloc: &CallbackAllocator,
  out: &mut MaybeUninit<CompileResult>,
) -> RegexpError {
  let alloc = *alloc;
  let p = match unsafe { pattern.try_as_pattern() } {
    Ok(p) => p,
    Err(_) => return RegexpError::DecodeError,
  };

  let (shared_alloc, boxed_alloc, alloc) = SharedAllocator::from_alloc(alloc);

  let m: emacs_regexp::Matcher<MultibyteEncoding, CallbackAllocator, SharedAllocator> =
    match emacs_regexp::Matcher::compile(p, alloc, shared_alloc) {
      Ok(m) => m,
      Err(e) => match e {
        emacs_regexp::RegexpError::ParseError(e) => {
          let e: Box<str, CallbackAllocator> = crate::util::Writer::debug_in(e, alloc).unwrap();
          let e: Box<[u8], CallbackAllocator> =
            crate::util::boxing::reallocate_with_trailing_null(e);
          let (p, _alloc) = crate::util::boxing::box_c_char(e);
          unsafe {
            (*out.as_mut_ptr()).error = Some(p);
          }
          return RegexpError::ParseError;
        },
        emacs_regexp::RegexpError::CompileError => {
          unsafe {
            (*out.as_mut_ptr()).error = None;
          }
          return RegexpError::CompileError;
        },
        emacs_regexp::RegexpError::MatchError => unreachable!(),
      },
    };

  let m = Matcher::from_matcher(m, alloc, boxed_alloc);
  unsafe {
    (*out.as_mut_ptr()).matcher = m;
  }

  RegexpError::None
}

#[must_use]
#[no_mangle]
pub extern "C" fn rex_display_expr(
  matcher: &Matcher,
  alloc: &CallbackAllocator,
) -> NonNull<c_char> {
  let m: Box<str, CallbackAllocator> =
    crate::util::Writer::debug_in(matcher.as_matcher(), *alloc).unwrap();
  let m: Box<[u8], CallbackAllocator> = crate::util::boxing::reallocate_with_trailing_null(m);
  let (p, _alloc) = crate::util::boxing::box_c_char(m);
  p
}

#[must_use]
#[no_mangle]
pub extern "C" fn rex_execute(
  matcher: &Matcher,
  _alloc: &CallbackAllocator,
  input: &Input,
) -> RegexpError {
  let matcher = matcher.as_matcher();
  let input = match unsafe { input.try_as_input() } {
    Ok(i) => i,
    Err(_) => return RegexpError::DecodeError,
  };
  RegexpError::wrap(|| {
    matcher.execute(input).map_err(|e| match e {
      emacs_regexp::RegexpError::MatchError => RegexpError::MatchError,
      _ => unreachable!(),
    })
  })
}


#[cfg(test)]
mod test {
  use core::mem;

  use super::*;
  use crate::objects::ForeignSlice;

  #[test]
  fn basic_workflow() {
    let s = ForeignSlice::from_data(b"asdf");
    let p = Pattern { data: s };
    let c = CallbackAllocator::LIBC_ALLOC;

    let mut m: MaybeUninit<CompileResult> = MaybeUninit::uninit();
    assert_eq!(rex_compile(&p, &c, &mut m), RegexpError::None);
    let m = unsafe { m.assume_init().matcher };
    let ast = format!("{:?}", m.as_matcher().expr);
    let expected = "Expr::Concatenation { components: [Expr::SingleLiteral(SingleLiteral('a')), Expr::SingleLiteral(SingleLiteral('s')), Expr::SingleLiteral(SingleLiteral('d')), Expr::SingleLiteral(SingleLiteral('f'))] }";
    assert_eq!(ast, expected);
    let e = rex_display_expr(&m, &c);
    let s_e: &str = unsafe { core::ffi::CStr::from_ptr(mem::transmute(e)) }
      .to_str()
      .unwrap();
    assert_eq!(s_e, "Matcher { data: \"asdf\", expr(\"asdf\"): Expr::Concatenation { components: [Expr::SingleLiteral(SingleLiteral('a')), Expr::SingleLiteral(SingleLiteral('s')), Expr::SingleLiteral(SingleLiteral('d')), Expr::SingleLiteral(SingleLiteral('f'))] } }");

    let i = Input { data: s };
    assert_eq!(rex_execute(&m, &c, &i), RegexpError::None);

    let s2 = ForeignSlice::from_data(b"bsdf");
    let i2 = Input { data: s2 };
    assert_eq!(rex_execute(&m, &c, &i2), RegexpError::MatchError);
  }

  #[test]
  fn parse_error() {
    /* This fails because it has a close group without any open group. */
    let s = ForeignSlice::from_data(b"as\\)");
    let p = Pattern { data: s };
    let c = CallbackAllocator::LIBC_ALLOC;

    let mut m: MaybeUninit<CompileResult> = MaybeUninit::uninit();
    assert_eq!(rex_compile(&p, &c, &mut m), RegexpError::ParseError);
    let e: NonNull<c_char> = unsafe { m.assume_init().error }.unwrap();
    let s: &str = unsafe { core::ffi::CStr::from_ptr(mem::transmute(e)) }
      .to_str()
      .unwrap();
    assert_eq!(s, "ParseError { kind: UnmatchedCloseParen, at: 3 }");

    use core::alloc::Allocator;
    unsafe {
      c.deallocate(
        e.cast(),
        core::alloc::Layout::from_size_align_unchecked(0, 0),
      );
    }
  }
}
