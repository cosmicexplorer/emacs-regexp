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
    pub struct ByteSingleLiteral(pub u8);

    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    pub struct UnicodeSingleLiteral(pub char);

    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    #[repr(transparent)]
    /* emacs uses a 22 bit char encoding! */
    pub struct MultibyteSingleLiteral(pub u32);

    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum SingleLiteral {
      Byte(ByteSingleLiteral),
      Unicode(UnicodeSingleLiteral),
      Multibyte(MultibyteSingleLiteral),
    }

    pub mod escapes {
      use super::SingleLiteral;

      #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
      pub struct Escaped(pub SingleLiteral);
    }
  }

  pub mod string {
    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct ByteStringLiteral<'n>(pub &'n [u8]);

    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct UnicodeStringLiteral<'n>(pub &'n str);

    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub struct MultibyteStringLiteral<'n>(pub &'n [u8]);

    #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
    pub enum StringLiteral<'n> {
      Byte(ByteStringLiteral<'n>),
      Unicode(UnicodeStringLiteral<'n>),
      Multibyte(MultibyteStringLiteral<'n>),
    }
  }
}

pub mod character_alternatives {
  use core::alloc::Allocator;

  use super::literals::single::SingleLiteral;

  /// https://www.gnu.org/software/emacs/manual/html_node/elisp/Char-Classes.html#Char-Classes
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum CharacterClass {
    /// .
    Dot, /* any char except newline */
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
  pub enum CharAltComponent {
    /// a
    SingleLiteral(SingleLiteral),
    /// a-z
    LiteralRange {
      left: SingleLiteral,
      right: SingleLiteral,
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
  #[derive(Debug, Clone, PartialEq, Eq)]
  pub struct CharacterAlternative<A>
  where A: Allocator
  {
    pub complemented: ComplementBehavior,
    pub components: Vec<CharAltComponent, A>,
  }
}

pub mod postfix_operators {
  use core::num::NonZeroUsize;

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
  pub struct RepeatNumeral(pub NonZeroUsize);

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

  use super::{
    char_properties::CharPropertiesSelector,
    character_alternatives::CharacterAlternative,
    groups::GroupKind,
    literals::{single::escapes::Escaped, string::StringLiteral},
    postfix_operators::PostfixOp,
  };

  #[derive(Debug, Clone, PartialEq, Eq)]
  pub enum SingleCharSelector<A>
  where A: Allocator
  {
    Prop(CharPropertiesSelector),
    Alt(CharacterAlternative<A>),
    Esc(Escaped),
  }

  #[derive(Debug, Clone, PartialEq, Eq)]
  pub enum Expr<'n, A>
  where A: Allocator
  {
    /// asdf
    Literal(StringLiteral<'n>),
    /// [a-z] or \w or \s-
    CharSelector(SingleCharSelector<A>),
    /// <expr><op>
    Postfix {
      inner: Box<Expr<'n, A>, A>,
      op: PostfixOp,
    },
    /// (<expr>)
    Group {
      kind: GroupKind,
      inner: Box<Expr<'n, A>, A>,
    },
    /// <expr>\|<expr>
    Alternation {
      left: Box<Expr<'n, A>, A>,
      right: Box<Expr<'n, A>, A>,
    },
  }
}
