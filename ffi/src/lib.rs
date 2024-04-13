/* Description: C ABI interface to expose to C code such as emacs.

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

#![warn(rustdoc::missing_crate_level_docs)]
// #![warn(missing_docs)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]
#![feature(allocator_api)]
#![feature(slice_ptr_get)]
#![feature(new_uninit)]
#![feature(ptr_as_uninit)]
#![feature(core_intrinsics)]
#![feature(lang_items)]
#![allow(internal_features)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! C ABI interface to expose to C code such as emacs.

extern crate alloc;

/// Necessary rust-specific hooks to override when generating an output library.
#[cfg(not(test))]
pub mod lang_items {
  use core::{
    alloc::{GlobalAlloc, Layout},
    intrinsics::abort,
    panic::PanicInfo,
  };

  use ::alloc::alloc::handle_alloc_error;

  /// Even when compiled with `panic="abort"`, we need to define this method
  /// anyway for some reason to successfully compile this `no_std` crate. If
  /// this is ever called, it should have the same behavior as `panic="abort"`.
  #[panic_handler]
  pub fn panic(_info: &PanicInfo) -> ! { abort() }

  /// This method is called to perform stack unwinding, especially across
  /// language runtimes, and must be defined for our `librex.so` to link
  /// correctly. While we might like to be able to make use of rust's structured
  /// panic control flow features in this library, it would require a lot of
  /// work to make that portable, so instead we simply ignore/avoid any stack
  /// unwinding (and this entire crate workspace is compiled with
  /// `panic="abort"`).
  #[lang = "eh_personality"]
  pub fn rust_eh_personality() {}

  /// Empty struct to do nothing and immediately error. See [`ALLOCATOR`].
  pub struct ImmediatelyErrorAllocator;

  unsafe impl GlobalAlloc for ImmediatelyErrorAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 { handle_alloc_error(layout) }
    unsafe fn dealloc(&self, _ptr: *mut u8, layout: Layout) { handle_alloc_error(layout) }
  }

  /// We need to provide a `#[global_allocator]` in order to produce a `no_std`
  /// binary, but we don't actually want to ever allocate dynamically in this
  /// crate without using an explicitly provided implementation of
  /// [`core::alloc::Allocator`]. So we provide this implementation which
  /// immediately panics at runtime if we ever attempt to use the global
  /// allocator.
  #[global_allocator]
  pub static ALLOCATOR: ImmediatelyErrorAllocator = ImmediatelyErrorAllocator;
}

pub mod objects {
  use core::{
    alloc::{AllocError, Allocator, Layout},
    ffi::c_void,
    mem::{self, MaybeUninit},
    ptr::{self, NonNull},
    slice,
  };

  #[cfg(not(test))]
  use ::alloc::boxed::Box;
  use emacs_regexp::syntax::{ast::expr::Expr, encoding::ByteEncoding};

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

  #[derive(Debug, Copy, Clone, PartialEq, Eq)]
  #[repr(C)]
  pub struct ForeignSlice {
    len: usize,
    data: *const c_void,
  }

  impl ForeignSlice {
    #[inline(always)]
    pub unsafe fn data(&self) -> &[u8] {
      let source: *const u8 = mem::transmute(self.data);
      slice::from_raw_parts(source, self.len)
    }

    #[cfg(test)]
    #[inline]
    pub fn from_data(data: &[u8]) -> Self {
      let source: *const c_void = unsafe { mem::transmute(data.as_ptr()) };
      Self {
        len: data.len(),
        data: source,
      }
    }
  }

  #[derive(Debug, Clone, PartialEq, Eq)]
  #[repr(C)]
  pub struct Pattern {
    pub data: ForeignSlice,
  }

  #[derive(Debug)]
  #[repr(C)]
  pub struct OwnedSlice {
    len: usize,
    data: NonNull<c_void>,
    alloc: CallbackAllocator,
  }

  impl OwnedSlice {
    #[inline(always)]
    pub fn data(&self) -> &[u8] {
      let source: *const u8 = unsafe { mem::transmute(self.data) };
      unsafe { slice::from_raw_parts(source, self.len) }
    }

    #[inline]
    pub fn from_data(data: &[u8], alloc: CallbackAllocator) -> Self {
      /* Allocate exactly enough space with the custom allocator. */
      let mut new_data: Box<[MaybeUninit<u8>], CallbackAllocator> =
        Box::new_uninit_slice_in(data.len(), alloc);

      /* Initialize the allocation from the source data. */
      let new_data: Box<[u8], CallbackAllocator> = unsafe {
        /* Perform transmute type gymnastics to get a pointer to the start of the
         * new allocation. */
        let base: *mut u8 = {
          let nd: &mut [MaybeUninit<u8>] = new_data.as_mut();
          mem::transmute(nd.as_mut_ptr())
        };
        /* Write the source data into the newly allocated region, initializing the
         * memory. */
        ptr::copy_nonoverlapping(data.as_ptr(), base, data.len());
        /* Get an initialized box for the newly initialized memory! */
        new_data.assume_init()
      };

      /* Convert the box into a raw pointer so it can be FFIed. */
      let (new_data, alloc): (*mut [u8], CallbackAllocator) =
        Box::into_raw_with_allocator(new_data);

      /* Perform transmute type gymnastics to extract a c_void. */
      let new_data: NonNull<c_void> = unsafe {
        /* NB: .as_mut_ptr() here requires #![feature(slice_ptr_get)], because we are
         * extracting a `*mut u8` from a `*mut [u8]`! This is safe and
         * correct, but note the subtle type conversion! */
        let new_data: *mut c_void = mem::transmute(new_data.as_mut_ptr());
        NonNull::new_unchecked(new_data)
      };
      Self {
        len: data.len(),
        data: new_data,
        alloc,
      }
    }

    #[inline]
    pub fn into_box(self) -> Box<[u8], CallbackAllocator> {
      let Self { len, data, alloc } = self;
      let p: NonNull<u8> = unsafe { mem::transmute(data) };
      let p: NonNull<[u8]> = NonNull::slice_from_raw_parts(p, len);
      unsafe { Box::from_raw_in(mem::transmute(p), alloc) }
    }
  }

  #[derive(Debug)]
  #[repr(C)]
  pub struct OwnedExpr {
    data: NonNull<c_void>,
    alloc: CallbackAllocator,
  }

  impl OwnedExpr {
    #[inline(always)]
    pub fn expr(&self) -> &Expr<ByteEncoding, CallbackAllocator> {
      let p: *mut Expr<ByteEncoding, CallbackAllocator> = unsafe { mem::transmute(self.data) };
      unsafe { &*p }
    }

    #[inline]
    pub fn from_expr(
      data: Expr<ByteEncoding, CallbackAllocator>,
      alloc: CallbackAllocator,
    ) -> Self {
      /* Box the expr onto the heap. */
      let boxed = Box::new_in(data, alloc);
      /* Convert the box into a raw pointer so it can be FFIed. */
      let (box_data, alloc): (
        *mut Expr<ByteEncoding, CallbackAllocator>,
        CallbackAllocator,
      ) = Box::into_raw_with_allocator(boxed);
      /* Perform transmute type gymnastics to extract a c_void. */
      let box_data: NonNull<c_void> = unsafe {
        let box_data: *mut c_void = mem::transmute(box_data);
        NonNull::new_unchecked(box_data)
      };
      Self {
        data: box_data,
        alloc,
      }
    }

    #[inline]
    pub fn into_box(self) -> Box<Expr<ByteEncoding, CallbackAllocator>, CallbackAllocator> {
      let Self { data, alloc } = self;
      let p: *mut Expr<ByteEncoding, CallbackAllocator> = unsafe { mem::transmute(data) };
      unsafe { Box::from_raw_in(p, alloc) }
    }
  }

  #[derive(Debug, Copy, Clone)]
  #[repr(C)]
  pub struct CallbackAllocator {
    ctx: Option<NonNull<c_void>>,
    alloc: Option<unsafe extern "C" fn(Option<NonNull<c_void>>, usize) -> Option<NonNull<c_void>>>,
    free: Option<unsafe extern "C" fn(Option<NonNull<c_void>>, NonNull<c_void>) -> ()>,
  }

  #[cfg(test)]
  impl CallbackAllocator {
    #[inline]
    pub fn new(
      ctx: Option<NonNull<c_void>>,
      alloc: Option<
        unsafe extern "C" fn(Option<NonNull<c_void>>, usize) -> Option<NonNull<c_void>>,
      >,
      free: Option<unsafe extern "C" fn(Option<NonNull<c_void>>, NonNull<c_void>) -> ()>,
    ) -> Self {
      Self { ctx, alloc, free }
    }
  }

  unsafe impl Allocator for CallbackAllocator {
    #[inline(always)]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
      let n = layout.pad_to_align().size();
      match unsafe { self.alloc.unwrap()(self.ctx, n) } {
        None => Err(AllocError),
        Some(p) => Ok(NonNull::slice_from_raw_parts(
          unsafe { mem::transmute(p) },
          n,
        )),
      }
    }

    #[inline(always)]
    unsafe fn deallocate(&self, ptr: NonNull<u8>, _layout: Layout) {
      let p: NonNull<c_void> = mem::transmute(ptr);
      self.free.unwrap()(self.ctx, p);
    }
  }

  #[derive(Debug)]
  #[repr(C)]
  pub struct Matcher {
    pub data: OwnedSlice,
    pub expr: OwnedExpr,
  }

  impl Matcher {
    /// Get the offsets for each field within the allocated output space.
    #[inline]
    pub fn destructure_output_fields(
      out: &mut MaybeUninit<Self>,
    ) -> (&mut MaybeUninit<OwnedSlice>, &mut MaybeUninit<OwnedExpr>) {
      let o = out.as_mut_ptr();
      unsafe {
        let d: *mut OwnedSlice = ptr::addr_of_mut!((*o).data);
        let e: *mut OwnedExpr = ptr::addr_of_mut!((*o).expr);
        (
          d.as_uninit_mut().unwrap_unchecked(),
          e.as_uninit_mut().unwrap_unchecked(),
        )
      }
    }
  }

  #[derive(Debug, Clone, PartialEq, Eq)]
  #[repr(C)]
  pub struct Input {
    pub data: ForeignSlice,
  }
}

pub mod methods {
  use core::mem::MaybeUninit;

  use emacs_regexp::syntax::parser::parse_bytes;

  use super::objects::{
    CallbackAllocator, Input, Matcher, OwnedExpr, OwnedSlice, Pattern, RegexpError,
  };

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
}

#[cfg(test)]
mod test {
  use core::{
    ffi::c_void,
    mem::{self, MaybeUninit},
    ptr::NonNull,
  };

  use super::{methods::*, objects::*};

  unsafe extern "C" fn rex_alloc(
    ctx: Option<NonNull<c_void>>,
    len: usize,
  ) -> Option<NonNull<c_void>> {
    assert!(ctx.is_none());
    assert!(len > 0);
    NonNull::new(libc::malloc(len))
  }
  unsafe extern "C" fn rex_free(ctx: Option<NonNull<c_void>>, p: NonNull<c_void>) {
    assert!(ctx.is_none());
    libc::free(mem::transmute(p));
  }

  #[test]
  fn basic_workflow() {
    let s = ForeignSlice::from_data(b"asdf");
    let p = Pattern { data: s };
    let c = CallbackAllocator::new(None, Some(rex_alloc), Some(rex_free));

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
    let c = CallbackAllocator::new(None, Some(rex_alloc), Some(rex_free));

    let mut m: MaybeUninit<Matcher> = MaybeUninit::uninit();
    assert_eq!(compile(&p, &c, &mut m), RegexpError::ParseError);
  }
}
