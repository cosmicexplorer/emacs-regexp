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
  ffi::c_void,
  mem::{self, MaybeUninit},
  ptr::NonNull,
};

#[cfg(not(test))]
use ::alloc::boxed::Box;
use cfg_if::cfg_if;

use crate::objects::{CallbackAllocator, Input, Matcher, Pattern, RegexpError};

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
  } else {
    pub type BoxAllocator = CallbackAllocator;
    static_assertions::const_assert_eq!(24, mem::size_of::<BoxAllocator>());

    #[inline(always)]
    fn box_allocator(alloc: CallbackAllocator) -> BoxAllocator {
      alloc
    }
  }
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
  let p = unsafe { pattern.as_pattern() };

  RegexpError::wrap(move || {
    let m: emacs_regexp::Matcher<CallbackAllocator, BoxAllocator> =
      emacs_regexp::Matcher::compile(p, alloc, box_allocator(alloc)).map_err(|e| match e {
        emacs_regexp::RegexpError::ParseError(_) => RegexpError::ParseError,
        emacs_regexp::RegexpError::CompileError => RegexpError::CompileError,
        emacs_regexp::RegexpError::MatchError => unreachable!(),
      })?;

    let m: Box<emacs_regexp::Matcher<CallbackAllocator, BoxAllocator>, CallbackAllocator> =
      Box::new_in(m, alloc);

    let (m, m_alloc) = Box::into_raw_with_allocator(m);
    out_e.write(m_alloc);

    let m: NonNull<c_void> = unsafe { NonNull::new_unchecked(m) }.cast();
    out_d.write(m);

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

    let mut m: MaybeUninit<Matcher> = MaybeUninit::uninit();
    assert_eq!(compile(&p, &c, &mut m), RegexpError::None);
    let m = unsafe { m.assume_init() };
    let ast = format!("{:?}", m.as_matcher().expr);
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
