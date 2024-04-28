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
  use core::{alloc::Allocator, ascii, fmt, hash::Hash, str};

  use crate::alloc_types::*;

  pub trait LiteralRequirements = Eq+Ord+Hash;

  pub trait LiteralEncoding {
    type Single: LiteralRequirements+Copy+Clone;
    type Str: LiteralRequirements+?Sized+'static;

    fn fmt(s: &Self::Single, f: &mut fmt::Formatter) -> fmt::Result;

    fn iter(s: &Self::Str) -> impl Iterator<Item=Self::Single>;

    type String<A: Allocator>: LiteralRequirements+AsRef<Self::Str>;

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
    const CLASS_ASCII: &'static Self::Str;
    /// `:nonascii:`
    const CLASS_NONASCII: &'static Self::Str;
    /// `:alnum:`
    const CLASS_ALNUM: &'static Self::Str;
    /// `:alpha:`
    const CLASS_ALPHA: &'static Self::Str;
    /// `:blank:`
    const CLASS_BLANK: &'static Self::Str;
    /// `:space:`
    const CLASS_SPACE: &'static Self::Str;
    /// `:cntrl:`
    const CLASS_CNTRL: &'static Self::Str;
    /// `:digit:`
    const CLASS_DIGIT: &'static Self::Str;
    /// `:xdigit:`
    const CLASS_XDIGIT: &'static Self::Str;
    /// `:print:`
    const CLASS_PRINT: &'static Self::Str;
    /// `:graph:`
    const CLASS_GRAPH: &'static Self::Str;
    /// `:lower:`
    const CLASS_LOWER: &'static Self::Str;
    /// `:upper:`
    const CLASS_UPPER: &'static Self::Str;
    /// `:unibyte:`
    const CLASS_UNIBYTE: &'static Self::Str;
    /// `:multibyte:`
    const CLASS_MULTIBYTE: &'static Self::Str;
    /// `:word:`
    const CLASS_WORD: &'static Self::Str;
    /// `:punct:`
    const CLASS_PUNCT: &'static Self::Str;

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
    type Str = [u8];

    #[inline(always)]
    fn fmt(s: &u8, f: &mut fmt::Formatter) -> fmt::Result {
      if !(s.is_ascii_alphanumeric() || s.is_ascii_punctuation() || s.is_ascii_whitespace()) {
        todo!("figure out how to print non-printable chars: {}", s);
      }
      let s = char::from_u32(*s as u32).unwrap();
      write!(f, "{}", s)
    }

    fn iter(s: &Self::Str) -> impl Iterator<Item=u8> { s.iter().copied() }

    type String<A: Allocator> = Box<[u8], A>;

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

    const CLASS_ASCII: &'static [u8] = ":ascii:".as_bytes();
    const CLASS_NONASCII: &'static [u8] = ":nonascii:".as_bytes();
    const CLASS_ALNUM: &'static [u8] = ":alnum:".as_bytes();
    const CLASS_ALPHA: &'static [u8] = ":alpha:".as_bytes();
    const CLASS_BLANK: &'static [u8] = ":blank:".as_bytes();
    const CLASS_SPACE: &'static [u8] = ":space:".as_bytes();
    const CLASS_CNTRL: &'static [u8] = ":cntrl:".as_bytes();
    const CLASS_DIGIT: &'static [u8] = ":digit:".as_bytes();
    const CLASS_XDIGIT: &'static [u8] = ":xdigit:".as_bytes();
    const CLASS_PRINT: &'static [u8] = ":print:".as_bytes();
    const CLASS_GRAPH: &'static [u8] = ":graph:".as_bytes();
    const CLASS_LOWER: &'static [u8] = ":lower:".as_bytes();
    const CLASS_UPPER: &'static [u8] = ":upper:".as_bytes();
    const CLASS_UNIBYTE: &'static [u8] = ":unibyte:".as_bytes();
    const CLASS_MULTIBYTE: &'static [u8] = ":multibyte:".as_bytes();
    const CLASS_WORD: &'static [u8] = ":word:".as_bytes();
    const CLASS_PUNCT: &'static [u8] = ":punct:".as_bytes();

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
    type Str = str;

    fn fmt(s: &char, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", s) }

    fn iter(s: &Self::Str) -> impl Iterator<Item=char> { s.chars() }

    /* FIXME: use smallvec! */
    type String<A: Allocator> = Box<str, A>;

    #[inline]
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

    #[inline]
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
    type Single = u32;
    /// However, this is stored in a compressed representation, which may use a
    /// varying number of bits.
    type Str = [u8];

    fn fmt(s: &u32, _f: &mut fmt::Formatter) -> fmt::Result {
      todo!("multibyte not yet supported: {}", s)
    }

    fn iter(s: &Self::Str) -> impl Iterator<Item=u32> {
      todo!("multibyte not yet supported: {:?}", s);
      #[allow(unreachable_code)]
      [].iter().copied()
    }

    type String<A: Allocator> = Box<[u8], A>;

    fn coalesce<A: Allocator>(s: Vec<u32, A>, _alloc: A) -> Self::String<A> {
      todo!("multibyte not yet supported: {:?}", s)
    }

    fn parse_ascii(c: u32) -> Option<ascii::Char> { todo!("multibyte not yet supported: {:?}", c) }

    /* FIXME: not supported yet! */
    const BACKSLASH: u32 = 0;
    const PIPE: u32 = 0;

    const COLON: u32 = 0;
    const QUESTION: u32 = 0;
    const PLUS: u32 = 0;
    const STAR: u32 = 0;
    const CARAT: u32 = 0;
    const DOLLAR: u32 = 0;
    const DASH: u32 = 0;
    const COMMA: u32 = 0;
    const DOT: u32 = 0;
    const UNDERSCORE: u32 = 0;
    const EQUALS: u32 = 0;

    const BACKTICK: u32 = 0;
    const SINGLE_QUOTE: u32 = 0;

    const SMALL_B: u32 = 0;
    const BIG_B: u32 = 0;
    const SMALL_W: u32 = 0;
    const BIG_W: u32 = 0;
    const SMALL_S: u32 = 0;
    const BIG_S: u32 = 0;
    const SMALL_C: u32 = 0;
    const BIG_C: u32 = 0;

    const OPEN_ANGLE_BRACE: u32 = 0;
    const CLOSE_ANGLE_BRACE: u32 = 0;

    const OPEN_CURLY_BRACE: u32 = 0;
    const CLOSE_CURLY_BRACE: u32 = 0;

    const OPEN_CIRCLE_BRACE: u32 = 0;
    const CLOSE_CIRCLE_BRACE: u32 = 0;

    const OPEN_SQUARE_BRACE: u32 = 0;
    const CLOSE_SQUARE_BRACE: u32 = 0;

    const CLASS_ASCII: &'static [u8] = ":ascii:".as_bytes();
    const CLASS_NONASCII: &'static [u8] = ":nonascii:".as_bytes();
    const CLASS_ALNUM: &'static [u8] = ":alnum:".as_bytes();
    const CLASS_ALPHA: &'static [u8] = ":alpha:".as_bytes();
    const CLASS_BLANK: &'static [u8] = ":blank:".as_bytes();
    const CLASS_SPACE: &'static [u8] = ":space:".as_bytes();
    const CLASS_CNTRL: &'static [u8] = ":cntrl:".as_bytes();
    const CLASS_DIGIT: &'static [u8] = ":digit:".as_bytes();
    const CLASS_XDIGIT: &'static [u8] = ":xdigit:".as_bytes();
    const CLASS_PRINT: &'static [u8] = ":print:".as_bytes();
    const CLASS_GRAPH: &'static [u8] = ":graph:".as_bytes();
    const CLASS_LOWER: &'static [u8] = ":lower:".as_bytes();
    const CLASS_UPPER: &'static [u8] = ":upper:".as_bytes();
    const CLASS_UNIBYTE: &'static [u8] = ":unibyte:".as_bytes();
    const CLASS_MULTIBYTE: &'static [u8] = ":multibyte:".as_bytes();
    const CLASS_WORD: &'static [u8] = ":word:".as_bytes();
    const CLASS_PUNCT: &'static [u8] = ":punct:".as_bytes();

    fn parse_nonnegative_integer<A: Allocator>(s: Vec<u32, A>, _alloc: A) -> Option<usize> {
      todo!("multibyte not yet supported: {:?}", s)
    }

    const ZERO: u32 = 0;
    const ONE: u32 = 0;
    const TWO: u32 = 0;
    const THREE: u32 = 0;
    const FOUR: u32 = 0;
    const FIVE: u32 = 0;
    const SIX: u32 = 0;
    const SEVEN: u32 = 0;
    const EIGHT: u32 = 0;
    const NINE: u32 = 0;
  }
}

/// stuff to do with the input string provided as the "pattern"
pub mod pattern {
  /* TODO: ??? */
}

pub use emacs_multibyte::util;
