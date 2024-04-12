/* Description: AST for regexp pattern strings.

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

/// AST for regexp pattern strings.

#[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Negation {
  #[default]
  Standard,
  Negated,
}

/// https://www.gnu.org/software/emacs/manual/html_node/elisp/Non_002dASCII-Characters.html
pub mod literals {
  pub mod single {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct SingleLiteral<LSi>(pub LSi);

    pub mod escapes {
      use super::SingleLiteral;

      #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
      pub struct Escaped<LSi>(pub SingleLiteral<LSi>);
    }
  }
}

pub mod character_alternatives {
  use core::alloc::Allocator;

  use ::alloc::vec::Vec;

  use super::literals::single::SingleLiteral;

  /// https://www.gnu.org/software/emacs/manual/html_node/elisp/Char-Classes.html#Char-Classes
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum CharacterClass {
    /// [:ascii:]
    ASCII,
    /// [:nonascii:]
    NonASCII,
    /// [:alnum:]
    AlNum,
    /// [:alpha:]
    Alpha,
    /// [:blank:]
    Blank, /* horizontal whitespace */
    /// [:space:]
    Whitespace, /* syntax table! */
    /// [:cntrl:]
    Control,
    /// [:digit:]
    Digit,
    /// [:xdigit:]
    HexDigit,
    /// [:print:]
    Printing,
    /// [:graph:]
    Graphic,
    /// [:lower:]
    LowerCase,
    /// [:upper:]
    UpperCase,
    /// [:unibyte:]
    Unibyte,
    /// [:multibyte:]
    Multibyte,
    /// [:word:]
    Word, /* syntax table! */
    /// [:punct:]
    Punctuation, /* syntax table! */
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum CharAltComponent<LSi> {
    /// a
    SingleLiteral(SingleLiteral<LSi>),
    /// a-z
    LiteralRange {
      left: SingleLiteral<LSi>,
      right: SingleLiteral<LSi>,
    },
    /// [:ascii:]
    Class(CharacterClass),
  }

  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum ComplementBehavior {
    #[default]
    Uncomplemented,
    /// as if beginning with `^`
    Complemented,
  }

  /// [a-z0-9] or [^a-z]
  #[derive(Debug, Clone)]
  pub struct CharacterAlternative<LSi, A>
  where A: Allocator
  {
    pub complemented: ComplementBehavior,
    pub elements: Vec<CharAltComponent<LSi>, A>,
  }

  impl<LSi, A> PartialEq for CharacterAlternative<LSi, A>
  where
    LSi: PartialEq,
    A: Allocator,
  {
    fn eq(&self, other: &Self) -> bool {
      self.complemented == other.complemented
        && self
          .elements
          .iter()
          .zip(other.elements.iter())
          .all(|(a, b)| a == b)
    }
  }

  impl<LSi, A> Eq for CharacterAlternative<LSi, A>
  where
    LSi: Eq,
    A: Allocator,
  {
  }
}

pub mod postfix_operators {
  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum GreedyBehavior {
    #[default]
    Greedy,
    NonGreedy,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum SimpleOperator {
    Star,
    Plus,
    Question,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct MaybeGreedyOperator {
    pub op: SimpleOperator,
    pub greediness: GreedyBehavior,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct RepeatNumeral(pub usize);

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct ExactRepeatOperator {
    pub times: RepeatNumeral,
  }

  /// {0,1} or {,1} => ?
  /// {0,} or {,}   => *
  /// {1,}          => +
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct GeneralRepeatOperator {
    pub left: Option<RepeatNumeral>,
    pub right: Option<RepeatNumeral>,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum RepeatOperator {
    Exact(ExactRepeatOperator),
    General(GeneralRepeatOperator),
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum PostfixOp {
    Simple(MaybeGreedyOperator),
    Repeat(RepeatOperator),
  }
}

pub mod anchors {
  use super::Negation;

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum StartAnchor {
    /// ^
    Carat,
    /// \`
    Backtick,
    /// \<
    Word,
    /// \_<
    Symbol,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum EndAnchor {
    /// $
    Dollar,
    /// \'
    SingleQuote,
    /// \>
    Word,
    /// \_>
    Symbol,
  }

  /// \=
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct PointAnchor;

  /// \b or \B (negated)
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct WordAnchor {
    pub negation: Negation,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum Anchor {
    Start(StartAnchor),
    End(EndAnchor),
    Point(PointAnchor),
    Word(WordAnchor),
  }
}

pub mod groups {
  use core::num::NonZeroUsize;

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct ExplicitGroupIndex(pub NonZeroUsize);

  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum GroupKind {
    /// \(...\)
    Basic,
    /// \(?:...\)
    #[default]
    Shy,
    /// \(?<num>:...\)
    ExplicitlyNumbered(ExplicitGroupIndex),
  }

  /// 1..=9
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct BackrefIndex(pub u8);

  /// \1 -> \9
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct Backref(pub BackrefIndex);
}

pub mod char_properties {
  use super::Negation;

  /// \w or \W (negated)
  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct WordChar {
    pub negation: Negation,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct SyntaxCode(pub u8);

  /// \s<code> or \S<code> (negated)
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct SyntaxChar {
    pub code: SyntaxCode,
    pub negation: Negation,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct CategoryCode(pub u8);

  /// \c<code> or \C<code> (negated)
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct CategoryChar {
    pub code: CategoryCode,
    pub negation: Negation,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum CharPropertiesSelector {
    Word(WordChar),
    Syntax(SyntaxChar),
    Category(CategoryChar),
  }
}

/// https://www.gnu.org/software/emacs/manual/html_node/emacs/Regexps.html
pub mod expr {
  use core::alloc::Allocator;

  use ::alloc::{boxed::Box, vec::Vec};

  use super::{
    anchors::Anchor,
    char_properties::CharPropertiesSelector,
    character_alternatives::CharacterAlternative,
    groups::{Backref, GroupKind},
    literals::single::{escapes::Escaped, SingleLiteral},
    postfix_operators::PostfixOp,
  };
  use crate::encoding::LiteralEncoding;

  #[derive(Debug, Clone)]
  pub enum SingleCharSelector<LSi, A>
  where A: Allocator
  {
    Prop(CharPropertiesSelector),
    Alt(CharacterAlternative<LSi, A>),
    Esc(Escaped<LSi>),
    /// .
    Dot, /* any char except newline */
  }

  impl<LSi, A> PartialEq for SingleCharSelector<LSi, A>
  where
    LSi: PartialEq,
    A: Allocator,
  {
    fn eq(&self, other: &Self) -> bool {
      match (self, other) {
        (Self::Prop(a), Self::Prop(b)) => a == b,
        (Self::Alt(a), Self::Alt(b)) => a == b,
        (Self::Esc(a), Self::Esc(b)) => a == b,
        (Self::Dot, Self::Dot) => true,
        _ => false,
      }
    }
  }

  impl<LSi, A> Eq for SingleCharSelector<LSi, A>
  where
    LSi: Eq,
    A: Allocator,
  {
  }

  #[derive(Debug, Clone)]
  pub enum Expr<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    /// a
    SingleLiteral(L::Single),
    /// \\ or \+
    EscapedLiteral(Escaped<L::Single>),
    /// \\1-9
    Backref(Backref),
    /// ^ or $
    Anchor(Anchor),
    /// [a-z] or \w or \s-
    CharSelector(SingleCharSelector<L::Single, A>),
    /// <expr><op>
    Postfix {
      inner: Box<Expr<L, A>, A>,
      op: PostfixOp,
    },
    /// (<expr>)
    Group {
      kind: GroupKind,
      inner: Box<Expr<L, A>, A>,
    },
    /// <expr>\|<expr>
    Alternation { cases: Vec<Box<Expr<L, A>, A>, A> },
    /// <expr><expr>
    Concatenation {
      components: Vec<Box<Expr<L, A>, A>, A>,
    },
  }

  impl<L, A> PartialEq for Expr<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    fn eq(&self, other: &Self) -> bool {
      match (self, other) {
        (Self::SingleLiteral(a), Self::SingleLiteral(b)) => a == b,
        (Self::EscapedLiteral(a), Self::EscapedLiteral(b)) => a == b,
        (Self::Backref(a), Self::Backref(b)) => a == b,
        (Self::Anchor(a), Self::Anchor(b)) => a == b,
        (Self::CharSelector(a), Self::CharSelector(b)) => a == b,
        (
          Self::Postfix {
            inner: inner_a,
            op: op_a,
          },
          Self::Postfix {
            inner: inner_b,
            op: op_b,
          },
        ) => op_a == op_b && inner_a.eq(inner_b),
        (
          Self::Group {
            kind: kind_a,
            inner: inner_a,
          },
          Self::Group {
            kind: kind_b,
            inner: inner_b,
          },
        ) => kind_a == kind_b && inner_a.eq(inner_b),
        (Self::Alternation { cases: cases_a }, Self::Alternation { cases: cases_b }) => {
          cases_a.iter().zip(cases_b.iter()).all(|(a, b)| a.eq(b))
        },
        (
          Self::Concatenation {
            components: components_a,
          },
          Self::Concatenation {
            components: components_b,
          },
        ) => components_a
          .iter()
          .zip(components_b.iter())
          .all(|(a, b)| a.eq(b)),
        _ => false,
      }
    }
  }

  impl<L, A> Eq for Expr<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
  }
}
