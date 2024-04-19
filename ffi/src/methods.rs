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

use core::{
  ffi::c_char,
  fmt,
  mem::{self, MaybeUninit},
  ptr::NonNull,
};

#[cfg(not(test))]
use ::alloc::boxed::Box;
use cfg_if::cfg_if;

use crate::objects::{CallbackAllocator, Input, Matcher, Pattern};

#[cfg(feature = "panic-testing")]
#[no_mangle]
pub extern "C" fn always_panic() -> ! { todo!("this always panics!") }

cfg_if! {
  if #[cfg(feature = "libc")] {
    pub type BoxAllocator = crate::libc_backend::LibcAllocator;
    static_assertions::const_assert_eq!(0, mem::size_of::<BoxAllocator>());

    #[inline(always)]
    fn box_allocator(_alloc: CallbackAllocator) -> BoxAllocator {
      crate::libc_backend::LibcAllocator
    }

    pub type ErrorAllocator = crate::libc_backend::LibcAllocator;
    static_assertions::const_assert_eq!(0, mem::size_of::<ErrorAllocator>());

    #[inline(always)]
    fn error_allocator(_alloc: CallbackAllocator) -> ErrorAllocator {
      crate::libc_backend::LibcAllocator
    }
  } else {
    pub type BoxAllocator = CallbackAllocator;
    static_assertions::const_assert_eq!(24, mem::size_of::<BoxAllocator>());

    #[inline(always)]
    fn box_allocator(alloc: CallbackAllocator) -> BoxAllocator {
      alloc
    }

    pub type ErrorAllocator = CallbackAllocator;
    static_assertions::const_assert_eq!(24, mem::size_of::<ErrorAllocator>());

    #[inline(always)]
    fn error_allocator(alloc: CallbackAllocator) -> ErrorAllocator {
      alloc
    }
  }
}

#[derive(Default, Debug, Copy, Clone, PartialEq, Eq)]
#[must_use]
#[repr(u8)]
pub enum RegexpError {
  #[default]
  None = 0,
  ParseError = 1,
  CompileError = 2,
  MatchError = 3,
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
  let p = unsafe { pattern.as_pattern() };

  let m: emacs_regexp::Matcher<CallbackAllocator, BoxAllocator> =
    match emacs_regexp::Matcher::compile(p, alloc, box_allocator(alloc)) {
      Ok(m) => m,
      Err(e) => match e {
        emacs_regexp::RegexpError::ParseError(e) => {
          let ea = error_allocator(alloc);
          let mut w = crate::util::Writer::with_initial_capacity_in(200, ea);
          {
            let mut f = fmt::Formatter::new(&mut w);
            let _ = fmt::Debug::fmt(&e, &mut f);
          }
          let _ = w.write_null_byte();
          let (p, _ea) = Box::into_raw_with_allocator(w.into_boxed());
          let p: NonNull<[u8]> = unsafe { NonNull::new_unchecked(p) };
          let p: NonNull<u8> = unsafe { NonNull::new_unchecked(p.as_mut_ptr()) };
          unsafe {
            (*out.as_mut_ptr()).error = Some(p.cast());
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

  let m = Matcher::from_matcher(m, alloc);
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
) -> Option<NonNull<c_char>> {
  let ea = error_allocator(*alloc);
  let mut w = crate::util::Writer::with_initial_capacity_in(400, ea);
  {
    let mut f = fmt::Formatter::new(&mut w);
    let _ = fmt::Debug::fmt(matcher.as_matcher(), &mut f);
  }
  let _ = w.write_null_byte();
  let (p, _ea) = Box::into_raw_with_allocator(w.into_boxed());
  let p: NonNull<[u8]> = unsafe { NonNull::new_unchecked(p) };
  let p: NonNull<u8> = unsafe { NonNull::new_unchecked(p.as_mut_ptr()) };
  Some(p.cast())
}

#[must_use]
#[no_mangle]
pub extern "C" fn rex_execute(
  matcher: &Matcher,
  _alloc: &CallbackAllocator,
  input: &Input,
) -> RegexpError {
  let matcher = matcher.as_matcher();
  let input = unsafe { input.as_input() };
  RegexpError::wrap(|| {
    matcher.execute(input).map_err(|e| match e {
      emacs_regexp::RegexpError::MatchError => RegexpError::MatchError,
      _ => unreachable!(),
    })
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

    let mut m: MaybeUninit<CompileResult> = MaybeUninit::uninit();
    assert_eq!(rex_compile(&p, &c, &mut m), RegexpError::None);
    let m = unsafe { m.assume_init().matcher };
    let ast = format!("{:?}", m.as_matcher().expr);
    let expected = "Expr::Concatenation { components: [Expr::SingleLiteral(SingleLiteral(97)), Expr::SingleLiteral(SingleLiteral(115)), Expr::SingleLiteral(SingleLiteral(100)), Expr::SingleLiteral(SingleLiteral(102))] }";
    assert_eq!(ast, expected);
    let e = rex_display_expr(&m, &c).unwrap();
    let s_e: &str = unsafe { core::ffi::CStr::from_ptr(mem::transmute(e)) }
      .to_str()
      .unwrap();
    assert_eq!(s_e, "Matcher { data: [97, 115, 100, 102], expr: Expr::Concatenation { components: [Expr::SingleLiteral(SingleLiteral(97)), Expr::SingleLiteral(SingleLiteral(115)), Expr::SingleLiteral(SingleLiteral(100)), Expr::SingleLiteral(SingleLiteral(102))] } }");

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
