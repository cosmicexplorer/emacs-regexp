/* Description: ???

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
#![deny(unsafe_code)]
/* Ensure any doctest warnings fails the doctest! */
#![doc(test(attr(deny(warnings))))]

//! ???

pub mod offsets {
  use core::{cmp, fmt};

  /// A single position in a regular expression.
  ///
  /// A position encodes one half of a span, and include the byte offset, line
  /// number and column number.
  #[derive(Clone, Copy, Eq, PartialEq)]
  pub struct Position {
    /// The absolute offset of this position, starting at `0` from the
    /// beginning of the regular expression pattern string.
    pub offset: usize,
    /// The line number, starting at `1`.
    pub line: usize,
    /// The approximate column number, starting at `1`.
    pub column: usize,
  }

  impl fmt::Debug for Position {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      write!(
        f,
        "Position(o: {:?}, l: {:?}, c: {:?})",
        self.offset, self.line, self.column
      )
    }
  }

  impl cmp::Ord for Position {
    fn cmp(&self, other: &Position) -> cmp::Ordering { self.offset.cmp(&other.offset) }
  }

  impl cmp::PartialOrd for Position {
    fn partial_cmp(&self, other: &Position) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
  }

  /// Span represents the position information of a single AST item.
  ///
  /// All span positions are absolute byte offsets that can be used on the
  /// original regular expression that was parsed.
  #[derive(Clone, Copy, Eq, PartialEq)]
  pub struct Span {
    /// The start byte offset.
    pub start: Position,
    /// The end byte offset.
    pub end: Position,
  }

  impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
      write!(f, "Span({:?}, {:?})", self.start, self.end)
    }
  }

  impl cmp::Ord for Span {
    fn cmp(&self, other: &Span) -> cmp::Ordering {
      (&self.start, &self.end).cmp(&(&other.start, &other.end))
    }
  }

  impl cmp::PartialOrd for Span {
    fn partial_cmp(&self, other: &Span) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
  }
}
