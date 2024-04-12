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
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! C ABI interface to expose to C code such as emacs.

use core::{mem::MaybeUninit, panic::PanicInfo};

use num_enum::{IntoPrimitive, TryFromPrimitive};

#[panic_handler]
fn panic(info: &PanicInfo) -> ! { loop {} }

#[derive(Default, Copy, Clone, IntoPrimitive, TryFromPrimitive, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum RegexpError {
  #[default]
  None = 0,
  CompileError = 1,
  MatchError = 2,
}

#[repr(C)]
pub struct Pattern;

#[repr(C)]
pub struct Matcher;

#[repr(C)]
pub struct Input;

/// asdf
#[no_mangle]
pub extern "C" fn compile(pattern: &Pattern, out: &mut MaybeUninit<Matcher>) -> RegexpError {
  RegexpError::None
}

#[no_mangle]
pub extern "C" fn execute(matcher: &Matcher, input: &Input) -> RegexpError { RegexpError::None }
