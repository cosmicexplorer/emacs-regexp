/* Description: AST generation from emacs regexp pattern strings.

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
#![feature(error_in_core)]
#![feature(trait_alias)]
#![feature(ascii_char)]
#![feature(new_uninit)]
#![feature(maybe_uninit_write_slice)]
#![feature(slice_ptr_get)]
#![feature(layout_for_ptr)]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(not(test), no_main)]

//! AST generation from emacs regexp pattern strings.

extern crate alloc;

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

pub mod ast;
pub mod parser;

pub mod encoding {
  use core::{alloc::Allocator, ascii, fmt, hash::Hash, mem::MaybeUninit, str};

  use emacs_multibyte::{OwnedString, PackedString, SingleChar};

  use crate::alloc_types::*;

  pub trait LiteralRequirements = Eq+Ord+Hash;

  pub trait LiteralEncoding {
    type Single: LiteralRequirements+Copy+Clone;
    type Str<'a>: LiteralRequirements+Copy+Clone;

    fn fmt(s: &Self::Single, f: &mut fmt::Formatter) -> fmt::Result;

    fn iter<'a>(s: Self::Str<'a>) -> impl Iterator<Item=Self::Single>+'a;

    type String<A: Allocator>: LiteralRequirements;

    fn str_ref<'s, 'a, A: Allocator>(s: &'s Self::String<A>) -> Self::Str<'a>
    where 's: 'a;

    fn owned_str<'s, A: Allocator>(data: Self::Str<'s>, alloc: A) -> Self::String<A>;

    fn str_allocator<'s, A: Allocator>(s: &'s Self::String<A>) -> &'s A;

    fn coalesce<A: Allocator>(s: Vec<Self::Single, A>, alloc: A) -> Self::String<A>;

    fn parse_ascii(c: Self::Single) -> Option<ascii::Char>;

    /// `\`
    const BACKSLASH: Self::Single;
    /// `|`
    const PIPE: Self::Single;

    /// `:`
    const COLON: Self::Single;
    /// `?`
    const QUESTION: Self::Single;
    /// `+`
    const PLUS: Self::Single;
    /// `*`
    const STAR: Self::Single;
    /// `^`
    const CARAT: Self::Single;
    /// `$`
    const DOLLAR: Self::Single;
    /// `-`
    const DASH: Self::Single;
    /// `,`
    const COMMA: Self::Single;
    /// `.`
    const DOT: Self::Single;
    /// `_`
    const UNDERSCORE: Self::Single;
    /// `=`
    const EQUALS: Self::Single;

    /// `\``
    const BACKTICK: Self::Single;
    /// `'`
    const SINGLE_QUOTE: Self::Single;

    /// `b`
    const SMALL_B: Self::Single;
    /// `B`
    const BIG_B: Self::Single;
    /// `w`
    const SMALL_W: Self::Single;
    /// `W`
    const BIG_W: Self::Single;
    /// `s`
    const SMALL_S: Self::Single;
    /// `S`
    const BIG_S: Self::Single;
    /// `c`
    const SMALL_C: Self::Single;
    /// `C`
    const BIG_C: Self::Single;

    /// `<`
    const OPEN_ANGLE_BRACE: Self::Single;
    /// `>`
    const CLOSE_ANGLE_BRACE: Self::Single;

    /// `{`
    const OPEN_CURLY_BRACE: Self::Single;
    /// `}`
    const CLOSE_CURLY_BRACE: Self::Single;

    /// `(`
    const OPEN_CIRCLE_BRACE: Self::Single;
    /// `)`
    const CLOSE_CIRCLE_BRACE: Self::Single;

    /// `[`
    const OPEN_SQUARE_BRACE: Self::Single;
    /// `]`
    const CLOSE_SQUARE_BRACE: Self::Single;

    /// `:ascii:`
    const CLASS_ASCII: Self::Str<'static>;
    /// `:nonascii:`
    const CLASS_NONASCII: Self::Str<'static>;
    /// `:alnum:`
    const CLASS_ALNUM: Self::Str<'static>;
    /// `:alpha:`
    const CLASS_ALPHA: Self::Str<'static>;
    /// `:blank:`
    const CLASS_BLANK: Self::Str<'static>;
    /// `:space:`
    const CLASS_SPACE: Self::Str<'static>;
    /// `:cntrl:`
    const CLASS_CNTRL: Self::Str<'static>;
    /// `:digit:`
    const CLASS_DIGIT: Self::Str<'static>;
    /// `:xdigit:`
    const CLASS_XDIGIT: Self::Str<'static>;
    /// `:print:`
    const CLASS_PRINT: Self::Str<'static>;
    /// `:graph:`
    const CLASS_GRAPH: Self::Str<'static>;
    /// `:lower:`
    const CLASS_LOWER: Self::Str<'static>;
    /// `:upper:`
    const CLASS_UPPER: Self::Str<'static>;
    /// `:unibyte:`
    const CLASS_UNIBYTE: Self::Str<'static>;
    /// `:multibyte:`
    const CLASS_MULTIBYTE: Self::Str<'static>;
    /// `:word:`
    const CLASS_WORD: Self::Str<'static>;
    /// `:punct:`
    const CLASS_PUNCT: Self::Str<'static>;

    fn parse_nonnegative_integer<A: Allocator>(s: Vec<Self::Single, A>, alloc: A) -> Option<usize>;

    /// 0
    const ZERO: Self::Single;
    /// 1
    const ONE: Self::Single;
    /// 2
    const TWO: Self::Single;
    /// 3
    const THREE: Self::Single;
    /// 4
    const FOUR: Self::Single;
    /// 5
    const FIVE: Self::Single;
    /// 6
    const SIX: Self::Single;
    /// 7
    const SEVEN: Self::Single;
    /// 8
    const EIGHT: Self::Single;
    ///9
    const NINE: Self::Single;
  }

  pub struct ByteEncoding;
  impl LiteralEncoding for ByteEncoding {
    type Single = u8;
    type Str<'a> = &'a [u8];

    #[inline(always)]
    fn fmt(s: &u8, f: &mut fmt::Formatter) -> fmt::Result {
      if !(s.is_ascii_alphanumeric() || s.is_ascii_punctuation() || s.is_ascii_whitespace()) {
        todo!("figure out how to print non-printable chars: {}", s);
      }
      let s = char::from_u32(*s as u32).unwrap();
      write!(f, "{}", s)
    }

    fn iter<'a>(s: Self::Str<'a>) -> impl Iterator<Item=u8>+'a { s.iter().copied() }

    type String<A: Allocator> = Box<[u8], A>;

    #[inline(always)]
    fn str_ref<'s, 'a, A: Allocator>(s: &'s Box<[u8], A>) -> &'a [u8]
    where 's: 'a {
      s.as_ref()
    }

    #[inline(always)]
    fn owned_str<'s, A: Allocator>(data: &'s [u8], alloc: A) -> Box<[u8], A> {
      let mut new_data: Box<[MaybeUninit<u8>], A> = Box::new_uninit_slice_in(data.len(), alloc);
      MaybeUninit::copy_from_slice(new_data.as_mut(), data);
      unsafe { new_data.assume_init() }
    }

    #[inline(always)]
    fn str_allocator<'s, A: Allocator>(s: &'s Self::String<A>) -> &'s A { Box::allocator(s) }

    #[inline(always)]
    fn coalesce<A: Allocator>(s: Vec<u8, A>, _alloc: A) -> Self::String<A> { s.into_boxed_slice() }

    #[inline(always)]
    fn parse_ascii(c: u8) -> Option<ascii::Char> {
      let c = char::from_u32(c as u32).unwrap();
      c.as_ascii()
    }

    const BACKSLASH: u8 = b'\\';
    const PIPE: u8 = b'|';

    const COLON: u8 = b':';
    const QUESTION: u8 = b'?';
    const PLUS: u8 = b'+';
    const STAR: u8 = b'*';
    const CARAT: u8 = b'^';
    const DOLLAR: u8 = b'$';
    const DASH: u8 = b'-';
    const COMMA: u8 = b',';
    const DOT: u8 = b'.';
    const UNDERSCORE: u8 = b'_';
    const EQUALS: u8 = b'=';

    const BACKTICK: u8 = b'`';
    const SINGLE_QUOTE: u8 = b'\'';

    const SMALL_B: u8 = b'b';
    const BIG_B: u8 = b'B';
    const SMALL_W: u8 = b'w';
    const BIG_W: u8 = b'W';
    const SMALL_S: u8 = b's';
    const BIG_S: u8 = b'S';
    const SMALL_C: u8 = b'c';
    const BIG_C: u8 = b'C';

    const OPEN_ANGLE_BRACE: u8 = b'<';
    const CLOSE_ANGLE_BRACE: u8 = b'>';

    const OPEN_CURLY_BRACE: u8 = b'{';
    const CLOSE_CURLY_BRACE: u8 = b'}';

    const OPEN_CIRCLE_BRACE: u8 = b'(';
    const CLOSE_CIRCLE_BRACE: u8 = b')';

    const OPEN_SQUARE_BRACE: u8 = b'[';
    const CLOSE_SQUARE_BRACE: u8 = b']';

    const CLASS_ASCII: &'static [u8] = b":ascii:";
    const CLASS_NONASCII: &'static [u8] = b":nonascii:";
    const CLASS_ALNUM: &'static [u8] = b":alnum:";
    const CLASS_ALPHA: &'static [u8] = b":alpha:";
    const CLASS_BLANK: &'static [u8] = b":blank:";
    const CLASS_SPACE: &'static [u8] = b":space:";
    const CLASS_CNTRL: &'static [u8] = b":cntrl:";
    const CLASS_DIGIT: &'static [u8] = b":digit:";
    const CLASS_XDIGIT: &'static [u8] = b":xdigit:";
    const CLASS_PRINT: &'static [u8] = b":print:";
    const CLASS_GRAPH: &'static [u8] = b":graph:";
    const CLASS_LOWER: &'static [u8] = b":lower:";
    const CLASS_UPPER: &'static [u8] = b":upper:";
    const CLASS_UNIBYTE: &'static [u8] = b":unibyte:";
    const CLASS_MULTIBYTE: &'static [u8] = b":multibyte:";
    const CLASS_WORD: &'static [u8] = b":word:";
    const CLASS_PUNCT: &'static [u8] = b":punct:";

    fn parse_nonnegative_integer<A: Allocator>(s: Vec<u8, A>, _alloc: A) -> Option<usize> {
      let s: &str = str::from_utf8(&s[..]).ok()?;
      let n: usize = s.parse().ok()?;
      Some(n)
    }

    const ZERO: u8 = b'0';
    const ONE: u8 = b'1';
    const TWO: u8 = b'2';
    const THREE: u8 = b'3';
    const FOUR: u8 = b'4';
    const FIVE: u8 = b'5';
    const SIX: u8 = b'6';
    const SEVEN: u8 = b'7';
    const EIGHT: u8 = b'8';
    const NINE: u8 = b'9';
  }

  pub struct UnicodeEncoding;
  impl LiteralEncoding for UnicodeEncoding {
    type Single = char;
    type Str<'a> = &'a str;

    fn fmt(s: &char, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", s) }

    fn iter<'a>(s: Self::Str<'a>) -> impl Iterator<Item=char>+'a { s.chars() }

    /* FIXME: use smallvec! */
    type String<A: Allocator> = Box<str, A>;

    #[inline(always)]
    fn str_ref<'s, 'a, A: Allocator>(s: &'s Box<str, A>) -> &'a str
    where 's: 'a {
      s.as_ref()
    }

    #[inline(always)]
    fn owned_str<'s, A: Allocator>(data: &'s str, alloc: A) -> Box<str, A> {
      let mut new_data: Box<[MaybeUninit<u8>], A> =
        Box::new_uninit_slice_in(data.as_bytes().len(), alloc);
      MaybeUninit::copy_from_slice(new_data.as_mut(), data.as_bytes());
      unsafe { crate::util::boxing::box_into_string(new_data.assume_init()) }
    }

    #[inline(always)]
    fn str_allocator<'s, A: Allocator>(s: &'s Self::String<A>) -> &'s A { Box::allocator(s) }

    #[inline(always)]
    fn coalesce<A: Allocator>(s: Vec<char, A>, alloc: A) -> Self::String<A> {
      crate::util::string::coalesce_utf8_chars(s.into_iter(), alloc)
    }

    #[inline(always)]
    fn parse_ascii(c: char) -> Option<ascii::Char> { c.as_ascii() }

    const BACKSLASH: char = '\\';
    const PIPE: char = '|';

    const COLON: char = ':';
    const QUESTION: char = '?';
    const PLUS: char = '+';
    const STAR: char = '*';
    const CARAT: char = '^';
    const DOLLAR: char = '$';
    const DASH: char = '-';
    const COMMA: char = ',';
    const DOT: char = '.';
    const UNDERSCORE: char = '_';
    const EQUALS: char = '=';

    const BACKTICK: char = '`';
    const SINGLE_QUOTE: char = '\'';

    const SMALL_B: char = 'b';
    const BIG_B: char = 'B';
    const SMALL_W: char = 'w';
    const BIG_W: char = 'W';
    const SMALL_S: char = 's';
    const BIG_S: char = 'S';
    const SMALL_C: char = 'c';
    const BIG_C: char = 'C';

    const OPEN_ANGLE_BRACE: char = '<';
    const CLOSE_ANGLE_BRACE: char = '>';

    const OPEN_CURLY_BRACE: char = '{';
    const CLOSE_CURLY_BRACE: char = '}';

    const OPEN_CIRCLE_BRACE: char = '(';
    const CLOSE_CIRCLE_BRACE: char = ')';

    const OPEN_SQUARE_BRACE: char = '[';
    const CLOSE_SQUARE_BRACE: char = ']';

    const CLASS_ASCII: &'static str = ":ascii:";
    const CLASS_NONASCII: &'static str = ":nonascii:";
    const CLASS_ALNUM: &'static str = ":alnum:";
    const CLASS_ALPHA: &'static str = ":alpha:";
    const CLASS_BLANK: &'static str = ":blank:";
    const CLASS_SPACE: &'static str = ":space:";
    const CLASS_CNTRL: &'static str = ":cntrl:";
    const CLASS_DIGIT: &'static str = ":digit:";
    const CLASS_XDIGIT: &'static str = ":xdigit:";
    const CLASS_PRINT: &'static str = ":print:";
    const CLASS_GRAPH: &'static str = ":graph:";
    const CLASS_LOWER: &'static str = ":lower:";
    const CLASS_UPPER: &'static str = ":upper:";
    const CLASS_UNIBYTE: &'static str = ":unibyte:";
    const CLASS_MULTIBYTE: &'static str = ":multibyte:";
    const CLASS_WORD: &'static str = ":word:";
    const CLASS_PUNCT: &'static str = ":punct:";

    #[inline(always)]
    fn parse_nonnegative_integer<A: Allocator>(s: Vec<char, A>, alloc: A) -> Option<usize> {
      let s: Box<str, A> = Self::coalesce(s, alloc);
      let n: usize = s.parse().ok()?;
      Some(n)
    }

    const ZERO: char = '0';
    const ONE: char = '1';
    const TWO: char = '2';
    const THREE: char = '3';
    const FOUR: char = '4';
    const FIVE: char = '5';
    const SIX: char = '6';
    const SEVEN: char = '7';
    const EIGHT: char = '8';
    const NINE: char = '9';
  }

  pub struct MultibyteEncoding;
  impl LiteralEncoding for MultibyteEncoding {
    /// emacs uses a 22 bit char encoding!
    type Single = SingleChar;
    /// However, this is stored in a compressed representation, which may use a
    /// varying number of bits.
    type Str<'a> = PackedString<'a>;

    #[inline(always)]
    fn fmt(s: &SingleChar, f: &mut fmt::Formatter) -> fmt::Result {
      match s.try_as_unicode() {
        Some(c) => write!(f, "{}", c),
        None => todo!("formatting multibyte chars is not yet supported: {:?}", s),
      }
    }

    #[inline(always)]
    fn iter<'a>(s: Self::Str<'a>) -> impl Iterator<Item=SingleChar>+'a { s.iter_uniform_chars() }

    type String<A: Allocator> = OwnedString<A>;

    #[inline(always)]
    fn str_ref<'s, 'a, A: Allocator>(s: &'s OwnedString<A>) -> PackedString<'a>
    where 's: 'a {
      s.as_packed_str()
    }

    #[inline(always)]
    fn owned_str<'s, A: Allocator>(data: PackedString<'s>, alloc: A) -> OwnedString<A> {
      let mut new_data: Box<[MaybeUninit<u8>], A> =
        Box::new_uninit_slice_in(data.as_bytes().len(), alloc);
      MaybeUninit::copy_from_slice(new_data.as_mut(), data.as_bytes());
      unsafe { OwnedString::from_bytes(new_data.assume_init()) }
    }

    #[inline(always)]
    fn str_allocator<'s, A: Allocator>(s: &'s Self::String<A>) -> &'s A { s.allocator() }

    #[inline(always)]
    fn coalesce<A: Allocator>(s: Vec<SingleChar, A>, alloc: A) -> Self::String<A> {
      OwnedString::coalesce_chars(s.into_iter(), alloc)
    }

    #[inline(always)]
    fn parse_ascii(c: SingleChar) -> Option<ascii::Char> { c.try_as_ascii() }

    const BACKSLASH: SingleChar = SingleChar::from_byte(b'\\');
    const PIPE: SingleChar = SingleChar::from_byte(b'|');

    const COLON: SingleChar = SingleChar::from_byte(b':');
    const QUESTION: SingleChar = SingleChar::from_byte(b'?');
    const PLUS: SingleChar = SingleChar::from_byte(b'+');
    const STAR: SingleChar = SingleChar::from_byte(b'*');
    const CARAT: SingleChar = SingleChar::from_byte(b'^');
    const DOLLAR: SingleChar = SingleChar::from_byte(b'$');
    const DASH: SingleChar = SingleChar::from_byte(b'-');
    const COMMA: SingleChar = SingleChar::from_byte(b',');
    const DOT: SingleChar = SingleChar::from_byte(b'.');
    const UNDERSCORE: SingleChar = SingleChar::from_byte(b'_');
    const EQUALS: SingleChar = SingleChar::from_byte(b'=');

    const BACKTICK: SingleChar = SingleChar::from_byte(b'`');
    const SINGLE_QUOTE: SingleChar = SingleChar::from_byte(b'\'');

    const SMALL_B: SingleChar = SingleChar::from_byte(b'b');
    const BIG_B: SingleChar = SingleChar::from_byte(b'B');
    const SMALL_W: SingleChar = SingleChar::from_byte(b'w');
    const BIG_W: SingleChar = SingleChar::from_byte(b'W');
    const SMALL_S: SingleChar = SingleChar::from_byte(b's');
    const BIG_S: SingleChar = SingleChar::from_byte(b'S');
    const SMALL_C: SingleChar = SingleChar::from_byte(b'c');
    const BIG_C: SingleChar = SingleChar::from_byte(b'C');

    const OPEN_ANGLE_BRACE: SingleChar = SingleChar::from_byte(b'<');
    const CLOSE_ANGLE_BRACE: SingleChar = SingleChar::from_byte(b'>');

    const OPEN_CURLY_BRACE: SingleChar = SingleChar::from_byte(b'{');
    const CLOSE_CURLY_BRACE: SingleChar = SingleChar::from_byte(b'}');

    const OPEN_CIRCLE_BRACE: SingleChar = SingleChar::from_byte(b'(');
    const CLOSE_CIRCLE_BRACE: SingleChar = SingleChar::from_byte(b')');

    const OPEN_SQUARE_BRACE: SingleChar = SingleChar::from_byte(b'[');
    const CLOSE_SQUARE_BRACE: SingleChar = SingleChar::from_byte(b']');

    const CLASS_ASCII: PackedString<'static> = unsafe { PackedString::from_bytes(b":ascii:") };
    const CLASS_NONASCII: PackedString<'static> =
      unsafe { PackedString::from_bytes(b":nonascii:") };
    const CLASS_ALNUM: PackedString<'static> = unsafe { PackedString::from_bytes(b":alnum:") };
    const CLASS_ALPHA: PackedString<'static> = unsafe { PackedString::from_bytes(b":alpha:") };
    const CLASS_BLANK: PackedString<'static> = unsafe { PackedString::from_bytes(b":blank:") };
    const CLASS_SPACE: PackedString<'static> = unsafe { PackedString::from_bytes(b":space:") };
    const CLASS_CNTRL: PackedString<'static> = unsafe { PackedString::from_bytes(b":cntrl:") };
    const CLASS_DIGIT: PackedString<'static> = unsafe { PackedString::from_bytes(b":digit:") };
    const CLASS_XDIGIT: PackedString<'static> = unsafe { PackedString::from_bytes(b":xdigit:") };
    const CLASS_PRINT: PackedString<'static> = unsafe { PackedString::from_bytes(b":print:") };
    const CLASS_GRAPH: PackedString<'static> = unsafe { PackedString::from_bytes(b":graph:") };
    const CLASS_LOWER: PackedString<'static> = unsafe { PackedString::from_bytes(b":lower:") };
    const CLASS_UPPER: PackedString<'static> = unsafe { PackedString::from_bytes(b":upper:") };
    const CLASS_UNIBYTE: PackedString<'static> = unsafe { PackedString::from_bytes(b":unibyte:") };
    const CLASS_MULTIBYTE: PackedString<'static> =
      unsafe { PackedString::from_bytes(b":multibyte:") };
    const CLASS_WORD: PackedString<'static> = unsafe { PackedString::from_bytes(b":word:") };
    const CLASS_PUNCT: PackedString<'static> = unsafe { PackedString::from_bytes(b":punct:") };

    #[inline(always)]
    fn parse_nonnegative_integer<A: Allocator>(s: Vec<SingleChar, A>, alloc: A) -> Option<usize> {
      let s: OwnedString<A> = Self::coalesce(s, alloc);
      let s = s.as_packed_str();
      let s = str::from_utf8(s.as_bytes()).ok()?;
      let n: usize = s.parse().ok()?;
      Some(n)
    }

    const ZERO: SingleChar = SingleChar::from_byte(b'0');
    const ONE: SingleChar = SingleChar::from_byte(b'1');
    const TWO: SingleChar = SingleChar::from_byte(b'2');
    const THREE: SingleChar = SingleChar::from_byte(b'3');
    const FOUR: SingleChar = SingleChar::from_byte(b'4');
    const FIVE: SingleChar = SingleChar::from_byte(b'5');
    const SIX: SingleChar = SingleChar::from_byte(b'6');
    const SEVEN: SingleChar = SingleChar::from_byte(b'7');
    const EIGHT: SingleChar = SingleChar::from_byte(b'8');
    const NINE: SingleChar = SingleChar::from_byte(b'9');
  }
}

pub use emacs_multibyte::util;
