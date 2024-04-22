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

/// See <https://www.gnu.org/software/emacs/manual/html_node/elisp/Non_002dASCII-Characters.html>.
pub mod literals {
  pub mod single {
    use core::{cmp, fmt, hash};

    #[cfg(test)]
    use proptest::{prelude::*, strategy::Map};

    use crate::encoding::LiteralEncoding;

    #[derive(Copy)]
    #[repr(transparent)]
    pub struct SingleLiteral<L>(pub L::Single)
    where L: LiteralEncoding;

    #[cfg(test)]
    impl<L> Arbitrary for SingleLiteral<L>
    where
      L: LiteralEncoding,
      L::Single: Arbitrary,
    {
      type Parameters = <L::Single as Arbitrary>::Parameters;
      type Strategy = Map<<L::Single as Arbitrary>::Strategy, fn(L::Single) -> Self>;

      fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
        <L::Single as Arbitrary>::arbitrary_with(args).prop_map(|c| Self(c))
      }
    }

    impl<L> Clone for SingleLiteral<L>
    where L: LiteralEncoding
    {
      fn clone(&self) -> Self { Self(self.0.clone()) }
    }

    impl<L> PartialEq for SingleLiteral<L>
    where L: LiteralEncoding
    {
      fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
    }

    impl<L> Eq for SingleLiteral<L> where L: LiteralEncoding {}

    impl<L> cmp::PartialOrd for SingleLiteral<L>
    where L: LiteralEncoding
    {
      fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { self.0.partial_cmp(&other.0) }
    }

    impl<L> cmp::Ord for SingleLiteral<L>
    where L: LiteralEncoding
    {
      fn cmp(&self, other: &Self) -> cmp::Ordering { self.0.cmp(&other.0) }
    }

    impl<L> hash::Hash for SingleLiteral<L>
    where L: LiteralEncoding
    {
      fn hash<H: hash::Hasher>(&self, state: &mut H) { self.0.hash(state); }
    }

    impl<L> fmt::Debug for SingleLiteral<L>
    where
      L: LiteralEncoding,
      L::Single: fmt::Debug,
    {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "SingleLiteral({:?})", self.0)
      }
    }

    impl<L> fmt::Display for SingleLiteral<L>
    where L: LiteralEncoding
    {
      fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { L::fmt(&self.0, f) }
    }

    pub mod escapes {
      use core::{cmp, fmt, hash};

      #[cfg(test)]
      use proptest::{prelude::*, strategy::Map};

      use super::{LiteralEncoding, SingleLiteral};

      #[derive(Copy)]
      pub struct Escaped<L>(pub SingleLiteral<L>)
      where L: LiteralEncoding;

      #[cfg(test)]
      impl<L> Arbitrary for Escaped<L>
      where
        L: LiteralEncoding,
        L::Single: Arbitrary,
      {
        type Parameters = <SingleLiteral<L> as Arbitrary>::Parameters;
        type Strategy =
          Map<<SingleLiteral<L> as Arbitrary>::Strategy, fn(SingleLiteral<L>) -> Self>;

        fn arbitrary_with(args: Self::Parameters) -> Self::Strategy {
          <SingleLiteral<L> as Arbitrary>::arbitrary_with(args).prop_map(|c| Self(c))
        }
      }

      impl<L> Clone for Escaped<L>
      where L: LiteralEncoding
      {
        fn clone(&self) -> Self { Self(self.0.clone()) }
      }

      impl<L> PartialEq for Escaped<L>
      where L: LiteralEncoding
      {
        fn eq(&self, other: &Self) -> bool { self.0.eq(&other.0) }
      }

      impl<L> Eq for Escaped<L> where L: LiteralEncoding {}

      impl<L> cmp::PartialOrd for Escaped<L>
      where L: LiteralEncoding
      {
        fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
          self.0.partial_cmp(&other.0)
        }
      }

      impl<L> cmp::Ord for Escaped<L>
      where L: LiteralEncoding
      {
        fn cmp(&self, other: &Self) -> cmp::Ordering { self.0.cmp(&other.0) }
      }

      impl<L> hash::Hash for Escaped<L>
      where L: LiteralEncoding
      {
        fn hash<H: hash::Hasher>(&self, state: &mut H) { self.0.hash(state); }
      }


      impl<L> fmt::Debug for Escaped<L>
      where
        L: LiteralEncoding,
        L::Single: fmt::Debug,
      {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Escaped({:?})", self.0) }
      }

      impl<L> fmt::Display for Escaped<L>
      where L: LiteralEncoding
      {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "\\{}", self.0) }
      }
    }
  }
}

pub mod character_alternatives {
  use core::{alloc::Allocator, fmt, hash};

  #[cfg(test)]
  use {proptest::prelude::*, proptest_derive::Arbitrary};

  use super::literals::single::SingleLiteral;
  use crate::{alloc_types::*, encoding::LiteralEncoding};

  /// See <https://www.gnu.org/software/emacs/manual/html_node/elisp/Char-Classes.html#Char-Classes>.
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[cfg_attr(test, derive(Arbitrary))]
  pub enum CharacterClass {
    /// `[:ascii:]`
    ASCII,
    /// `[:nonascii:]`
    NonASCII,
    /// `[:alnum:]`
    AlNum,
    /// `[:alpha:]`
    Alpha,
    /// `[:blank:]`
    Blank, /* horizontal whitespace */
    /// `[:space:]`
    Whitespace, /* syntax table! */
    /// `[:cntrl:]`
    Control,
    /// `[:digit:]`
    Digit,
    /// `[:xdigit:]`
    HexDigit,
    /// `[:print:]`
    Printing,
    /// `[:graph:]`
    Graphic,
    /// `[:lower:]`
    LowerCase,
    /// `[:upper:]`
    UpperCase,
    /// `[:unibyte:]`
    Unibyte,
    /// `[:multibyte:]`
    Multibyte,
    /// `[:word:]`
    Word, /* syntax table! */
    /// `[:punct:]`
    Punctuation, /* syntax table! */
  }

  impl fmt::Display for CharacterClass {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::ASCII => write!(f, "[:ascii:]"),
        Self::NonASCII => write!(f, "[:nonascii:]"),
        Self::AlNum => write!(f, "[:alnum:]"),
        Self::Alpha => write!(f, "[:alpha:]"),
        Self::Blank => write!(f, "[:blank:]"),
        Self::Whitespace => write!(f, "[:space:]"),
        Self::Control => write!(f, "[:cntrl:]"),
        Self::Digit => write!(f, "[:digit:]"),
        Self::HexDigit => write!(f, "[:xdigit:]"),
        Self::Printing => write!(f, "[:print:]"),
        Self::Graphic => write!(f, "[:graph:]"),
        Self::LowerCase => write!(f, "[:lower:]"),
        Self::UpperCase => write!(f, "[:upper:]"),
        Self::Unibyte => write!(f, "[:unibyte:]"),
        Self::Multibyte => write!(f, "[:multibyte:]"),
        Self::Word => write!(f, "[:word:]"),
        Self::Punctuation => write!(f, "[:punct:]"),
      }
    }
  }

  #[derive(Copy)]
  pub enum CharAltComponent<L>
  where L: LiteralEncoding
  {
    /// `a`
    SingleLiteral(SingleLiteral<L>),
    /// `a-z`
    LiteralRange {
      left: SingleLiteral<L>,
      right: SingleLiteral<L>,
    },
    /// `[:ascii:]`
    Class(CharacterClass),
  }

  impl<L> Clone for CharAltComponent<L>
  where L: LiteralEncoding
  {
    fn clone(&self) -> Self {
      match self {
        Self::SingleLiteral(sl) => Self::SingleLiteral(sl.clone()),
        Self::LiteralRange { left, right } => Self::LiteralRange {
          left: left.clone(),
          right: right.clone(),
        },
        Self::Class(cc) => Self::Class(cc.clone()),
      }
    }
  }

  impl<L> PartialEq for CharAltComponent<L>
  where L: LiteralEncoding
  {
    fn eq(&self, other: &Self) -> bool {
      match (self, other) {
        (Self::SingleLiteral(sl1), Self::SingleLiteral(sl2)) => sl1.eq(sl2),
        (
          Self::LiteralRange {
            left: l1,
            right: r1,
          },
          Self::LiteralRange {
            left: l2,
            right: r2,
          },
        ) => l1.eq(l2) && r1.eq(r2),
        (Self::Class(c1), Self::Class(c2)) => c1.eq(c2),
        _ => false,
      }
    }
  }

  impl<L> Eq for CharAltComponent<L> where L: LiteralEncoding {}

  impl<L> hash::Hash for CharAltComponent<L>
  where L: LiteralEncoding
  {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
      match self {
        Self::SingleLiteral(sl) => sl.hash(state),
        Self::LiteralRange { left, right } => {
          left.hash(state);
          right.hash(state);
        },
        Self::Class(cc) => cc.hash(state),
      }
    }
  }

  impl<L> fmt::Debug for CharAltComponent<L>
  where
    L: LiteralEncoding,
    L::Single: fmt::Debug,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::SingleLiteral(sl) => write!(f, "CharAltComponent::SingleLiteral({:?})", sl),
        Self::LiteralRange { left, right } => {
          write!(
            f,
            "CharAltComponent::LiteralRange {{ left: {:?}, right: {:?} }}",
            left, right
          )
        },
        Self::Class(cc) => write!(f, "CharAltComponent::Class({:?})", cc),
      }
    }
  }

  impl<L> fmt::Display for CharAltComponent<L>
  where L: LiteralEncoding
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::SingleLiteral(sl) => write!(f, "{}", sl),
        Self::LiteralRange { left, right } => write!(f, "{}-{}", left, right),
        Self::Class(cc) => write!(f, "{}", cc),
      }
    }
  }

  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum ComplementBehavior {
    #[default]
    Uncomplemented,
    /// as if beginning with `^`
    Complemented,
  }

  /// `[a-z0-9]` or `[^a-z]`
  pub struct CharacterAlternative<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    pub complemented: ComplementBehavior,
    pub elements: Vec<CharAltComponent<L>, A>,
  }

  impl<L, A> Clone for CharacterAlternative<L, A>
  where
    L: LiteralEncoding,
    A: Allocator+Clone,
  {
    fn clone(&self) -> Self {
      let Self {
        complemented,
        elements,
      } = self;
      Self {
        complemented: complemented.clone(),
        elements: elements.clone(),
      }
    }
  }

  impl<L, A> fmt::Debug for CharacterAlternative<L, A>
  where
    L: LiteralEncoding,
    L::Single: fmt::Debug,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      let elements: &[CharAltComponent<L>] = self.elements.as_ref();
      write!(
        f,
        "CharacterAlternative {{ complemented: {:?}, elements: {:?} }}",
        self.complemented, elements
      )
    }
  }

  impl<L, A> fmt::Display for CharacterAlternative<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      write!(f, "[")?;
      match self.complemented {
        ComplementBehavior::Complemented => write!(f, "^")?,
        _ => (),
      }
      for el in self.elements.iter() {
        write!(f, "{}", el)?;
      }
      write!(f, "]")
    }
  }

  impl<L, A> PartialEq for CharacterAlternative<L, A>
  where
    L: LiteralEncoding,
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

  impl<L, A> Eq for CharacterAlternative<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
  }
}

pub mod postfix_operators {
  use core::fmt;

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

  impl fmt::Display for SimpleOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Star => write!(f, "*"),
        Self::Plus => write!(f, "+"),
        Self::Question => write!(f, "?"),
      }
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct MaybeGreedyOperator {
    pub op: SimpleOperator,
    pub greediness: GreedyBehavior,
  }

  impl fmt::Display for MaybeGreedyOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      write!(f, "{}", &self.op)?;
      match self.greediness {
        GreedyBehavior::NonGreedy => write!(f, "?")?,
        _ => (),
      }
      Ok(())
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct RepeatNumeral(pub usize);

  impl fmt::Display for RepeatNumeral {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.0) }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct ExactRepeatOperator {
    pub times: RepeatNumeral,
  }

  impl fmt::Display for ExactRepeatOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "\\{{{}\\}}", self.times) }
  }

  /// {0,1} or {,1} => ?
  /// {0,} or {,}   => *
  /// {1,}          => +
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct GeneralRepeatOperator {
    pub left: Option<RepeatNumeral>,
    pub right: Option<RepeatNumeral>,
  }

  impl fmt::Display for GeneralRepeatOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      let Self { left, right } = self;
      match (left, right) {
        (None, None) => write!(f, "\\{{,\\}}"),
        (Some(_), None) => unreachable!(),
        (None, Some(right)) => write!(f, "\\{{,{}\\}}", right),
        (Some(left), Some(right)) => write!(f, "\\{{{},{}\\}}", left, right),
      }
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum RepeatOperator {
    Exact(ExactRepeatOperator),
    General(GeneralRepeatOperator),
  }

  impl fmt::Display for RepeatOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Exact(ero) => write!(f, "{}", ero),
        Self::General(gro) => write!(f, "{}", gro),
      }
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum PostfixOp {
    Simple(MaybeGreedyOperator),
    Repeat(RepeatOperator),
  }

  impl fmt::Display for PostfixOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Simple(mgo) => write!(f, "{}", mgo),
        Self::Repeat(ro) => write!(f, "{}", ro),
      }
    }
  }
}

pub mod anchors {
  use core::fmt;

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

  impl fmt::Display for StartAnchor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Carat => write!(f, "^"),
        Self::Backtick => write!(f, "\\`"),
        Self::Word => write!(f, "\\<"),
        Self::Symbol => write!(f, "\\_<"),
      }
    }
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

  impl fmt::Display for EndAnchor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Dollar => write!(f, "$"),
        Self::SingleQuote => write!(f, "\\'"),
        Self::Word => write!(f, "\\>"),
        Self::Symbol => write!(f, "\\_>"),
      }
    }
  }

  /// \=
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct PointAnchor;

  impl fmt::Display for PointAnchor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "\\=") }
  }

  /// \b or \B (negated)
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct WordAnchor {
    pub negation: Negation,
  }

  impl fmt::Display for WordAnchor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self.negation {
        Negation::Standard => write!(f, "\\b"),
        Negation::Negated => write!(f, "\\B"),
      }
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum Anchor {
    Start(StartAnchor),
    End(EndAnchor),
    Point(PointAnchor),
    Word(WordAnchor),
  }

  impl fmt::Display for Anchor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Start(sa) => write!(f, "{}", sa),
        Self::End(ea) => write!(f, "{}", ea),
        Self::Point(pa) => write!(f, "{}", pa),
        Self::Word(wa) => write!(f, "{}", wa),
      }
    }
  }
}

pub mod groups {
  use core::{fmt, num::NonZeroUsize};

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct ExplicitGroupIndex(pub NonZeroUsize);

  impl fmt::Display for ExplicitGroupIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.0) }
  }

  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum GroupKind {
    /// `\(...\)`
    Basic,
    /// `\(?:...\)`
    #[default]
    Shy,
    /// `\(?<num>:...\)`
    ExplicitlyNumbered(ExplicitGroupIndex),
  }

  /// `1..=9`
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct BackrefIndex(pub u8);

  impl fmt::Display for BackrefIndex {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.0) }
  }

  /// `\1 -> \9`
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct Backref(pub BackrefIndex);

  impl fmt::Display for Backref {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "\\{}", self.0) }
  }
}

pub mod char_properties {
  use core::{ascii, fmt};

  use super::Negation;

  /// `\w` or `\W` *(negated)*
  #[derive(Debug, Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct WordChar {
    pub negation: Negation,
  }

  impl fmt::Display for WordChar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self.negation {
        Negation::Standard => write!(f, "\\w"),
        Negation::Negated => write!(f, "\\W"),
      }
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct SyntaxCode(pub ascii::Char);

  impl fmt::Display for SyntaxCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.0) }
  }

  /// `\s<code>` or `\S<code>` *(negated)*
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct SyntaxChar {
    pub code: SyntaxCode,
    pub negation: Negation,
  }

  impl fmt::Display for SyntaxChar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self.negation {
        Negation::Standard => write!(f, "\\s{}", self.code),
        Negation::Negated => write!(f, "\\S{}", self.code),
      }
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct CategoryCode(pub ascii::Char);

  impl fmt::Display for CategoryCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.0) }
  }

  /// `\c<code>` or `\C<code>` *(negated)*
  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct CategoryChar {
    pub code: CategoryCode,
    pub negation: Negation,
  }

  impl fmt::Display for CategoryChar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self.negation {
        Negation::Standard => write!(f, "\\c{}", self.code),
        Negation::Negated => write!(f, "\\C{}", self.code),
      }
    }
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum CharPropertiesSelector {
    Word(WordChar),
    Syntax(SyntaxChar),
    Category(CategoryChar),
  }


  impl fmt::Display for CharPropertiesSelector {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Word(wc) => write!(f, "{}", wc),
        Self::Syntax(sc) => write!(f, "{}", sc),
        Self::Category(cc) => write!(f, "{}", cc),
      }
    }
  }
}

/// See <https://www.gnu.org/software/emacs/manual/html_node/emacs/Regexps.html>.
pub mod expr {
  use core::{alloc::Allocator, fmt};

  use super::{
    anchors::Anchor,
    char_properties::CharPropertiesSelector,
    character_alternatives::CharacterAlternative,
    groups::{Backref, GroupKind},
    literals::single::{escapes::Escaped, SingleLiteral},
    postfix_operators::PostfixOp,
  };
  use crate::{alloc_types::*, encoding::LiteralEncoding};

  pub enum SingleCharSelector<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    Prop(CharPropertiesSelector),
    Alt(CharacterAlternative<L, A>),
    Esc(Escaped<L>),
    /// `.`
    ///
    /// Any char except newline.
    Dot,
  }

  impl<L, A> Clone for SingleCharSelector<L, A>
  where
    L: LiteralEncoding,
    A: Allocator+Clone,
  {
    fn clone(&self) -> Self {
      match self {
        Self::Prop(cps) => Self::Prop(cps.clone()),
        Self::Alt(ca) => Self::Alt(ca.clone()),
        Self::Esc(esc) => Self::Esc(esc.clone()),
        Self::Dot => Self::Dot,
      }
    }
  }

  impl<L, A> fmt::Debug for SingleCharSelector<L, A>
  where
    L: LiteralEncoding,
    L::Single: fmt::Debug,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Prop(cps) => write!(f, "SingleCharSelector::Prop({:?})", cps),
        Self::Alt(ca) => write!(f, "SingleCharSelector::Alt({:?})", ca),
        Self::Esc(esc) => write!(f, "SingleCharSelector::Esc({:?})", esc),
        Self::Dot => write!(f, "SingleCharSelector::Dot"),
      }
    }
  }

  impl<L, A> fmt::Display for SingleCharSelector<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::Prop(cps) => write!(f, "{}", cps),
        Self::Alt(ca) => write!(f, "{}", ca),
        Self::Esc(esc) => write!(f, "{}", esc),
        Self::Dot => write!(f, "."),
      }
    }
  }

  impl<L, A> PartialEq for SingleCharSelector<L, A>
  where
    L: LiteralEncoding,
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

  impl<L, A> Eq for SingleCharSelector<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
  }

  pub enum Expr<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    /// `a`
    SingleLiteral(SingleLiteral<L>),
    /// `\\` or `\+`
    EscapedLiteral(Escaped<L>),
    /// `\<1-9>`
    Backref(Backref),
    /// `^` or `$`
    Anchor(Anchor),
    /// `[a-z]` or `\w` or `\s-`
    CharSelector(SingleCharSelector<L, A>),
    /// `<expr><op>`
    Postfix {
      inner: Box<Expr<L, A>, A>,
      op: PostfixOp,
    },
    /// `(<expr>)`
    Group {
      kind: GroupKind,
      inner: Box<Expr<L, A>, A>,
    },
    /// `<expr>\|<expr>`
    Alternation { cases: Vec<Box<Expr<L, A>, A>, A> },
    /// `<expr><expr>`
    Concatenation {
      components: Vec<Box<Expr<L, A>, A>, A>,
    },
  }

  impl<L, A> Clone for Expr<L, A>
  where
    L: LiteralEncoding,
    A: Allocator+Clone,
  {
    fn clone(&self) -> Self {
      match self {
        Self::SingleLiteral(sl) => Self::SingleLiteral(sl.clone()),
        Self::EscapedLiteral(el) => Self::EscapedLiteral(el.clone()),
        Self::Backref(br) => Self::Backref(br.clone()),
        Self::Anchor(a) => Self::Anchor(a.clone()),
        Self::CharSelector(scs) => Self::CharSelector(scs.clone()),
        Self::Postfix { inner, op } => Self::Postfix {
          inner: inner.clone(),
          op: op.clone(),
        },
        Self::Group { kind, inner } => Self::Group {
          kind: kind.clone(),
          inner: inner.clone(),
        },
        Self::Alternation { cases } => Self::Alternation {
          cases: cases.clone(),
        },
        Self::Concatenation { components } => Self::Concatenation {
          components: components.clone(),
        },
      }
    }
  }

  impl<L, A> fmt::Debug for Expr<L, A>
  where
    L: LiteralEncoding,
    L::Single: fmt::Debug,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::SingleLiteral(sl) => write!(f, "Expr::SingleLiteral({:?})", sl),
        Self::EscapedLiteral(el) => write!(f, "Expr::EscapedLiteral({:?})", el),
        Self::Backref(br) => write!(f, "Expr::Backref({:?})", br),
        Self::Anchor(a) => write!(f, "Expr::Anchor({:?})", a),
        Self::CharSelector(scs) => write!(f, "Expr::CharSelector({:?})", scs),
        Self::Postfix { inner, op } => {
          write!(f, "Expr::Postfix {{ inner: {:?}, op: {:?} }}", inner, op)
        },
        Self::Group { kind, inner } => {
          write!(f, "Expr::Group {{ kind: {:?}, inner: {:?} }}", kind, inner)
        },
        Self::Alternation { cases } => {
          write!(f, "Expr::Alternation {{ cases: {:?} }}", cases)
        },
        Self::Concatenation { components } => {
          write!(f, "Expr::Concatenation {{ components: {:?} }}", components)
        },
      }
    }
  }

  impl<L, A> fmt::Display for Expr<L, A>
  where
    L: LiteralEncoding,
    A: Allocator,
  {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      match self {
        Self::SingleLiteral(sl) => write!(f, "{}", sl),
        Self::EscapedLiteral(el) => write!(f, "{}", el),
        Self::Backref(br) => write!(f, "{}", br),
        Self::Anchor(a) => write!(f, "{}", a),
        Self::CharSelector(scs) => write!(f, "{}", scs),
        Self::Postfix { inner, op } => write!(f, "{}{}", inner.as_ref(), op),
        Self::Group { kind, inner } => {
          match kind {
            GroupKind::Basic => write!(f, "\\(")?,
            GroupKind::Shy => write!(f, "\\(?:")?,
            GroupKind::ExplicitlyNumbered(egi) => write!(f, "\\(?{}:", egi)?,
          }
          write!(f, "{}", inner.as_ref())?;
          write!(f, "\\)")
        },
        Self::Alternation { cases } => {
          let (first, rest) = cases.split_first().expect("should have >0 cases!");
          write!(f, "{}", first)?;
          for c in rest.iter() {
            write!(f, "\\|{}", c)?;
          }
          Ok(())
        },
        Self::Concatenation { components } => {
          for c in components.iter() {
            write!(f, "{}", c)?;
          }
          Ok(())
        },
      }
    }
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
          (cases_a.len() == cases_b.len())
            && cases_a.iter().zip(cases_b.iter()).all(|(a, b)| a.eq(b))
        },
        (
          Self::Concatenation {
            components: components_a,
          },
          Self::Concatenation {
            components: components_b,
          },
        ) => {
          (components_a.len() == components_b.len())
            && components_a
              .iter()
              .zip(components_b.iter())
              .all(|(a, b)| a.eq(b))
        },
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

#[cfg(test)]
mod test {
  use super::{expr::*, groups::*, literals::single::*, postfix_operators::*};
  use crate::encoding::ByteEncoding;

  #[test]
  fn expr_display() {
    let e = Expr::Concatenation {
      components: vec![
        Box::new(Expr::<ByteEncoding, _>::SingleLiteral(SingleLiteral(b'a'))),
        Box::new(Expr::Postfix {
          inner: Box::new(Expr::Group {
            kind: GroupKind::Basic,
            inner: Box::new(Expr::Alternation {
              cases: vec![
                Box::new(Expr::Concatenation {
                  components: vec![
                    Box::new(Expr::SingleLiteral(SingleLiteral(b's'))),
                    Box::new(Expr::SingleLiteral(SingleLiteral(b'd'))),
                  ],
                }),
                Box::new(Expr::Concatenation {
                  components: vec![
                    Box::new(Expr::Postfix {
                      inner: Box::new(Expr::CharSelector(SingleCharSelector::Dot)),
                      op: PostfixOp::Simple(MaybeGreedyOperator {
                        op: SimpleOperator::Question,
                        greediness: GreedyBehavior::Greedy,
                      }),
                    }),
                    Box::new(Expr::SingleLiteral(SingleLiteral(b'e'))),
                  ],
                }),
              ],
            }),
          }),
          op: PostfixOp::Simple(MaybeGreedyOperator {
            op: SimpleOperator::Plus,
            greediness: GreedyBehavior::NonGreedy,
          }),
        }),
        Box::new(Expr::SingleLiteral(SingleLiteral(b'f'))),
      ],
    };
    assert_eq!(&format!("{}", e), "a\\(sd\\|.?e\\)+?f");

    let e = Expr::<ByteEncoding, _>::Concatenation {
      components: vec![
        Box::new(Expr::SingleLiteral(SingleLiteral(b'a'))),
        Box::new(Expr::SingleLiteral(SingleLiteral(b's'))),
        Box::new(Expr::SingleLiteral(SingleLiteral(b'd'))),
        Box::new(Expr::Postfix {
          inner: Box::new(Expr::SingleLiteral(SingleLiteral(b'f'))),
          op: PostfixOp::Simple(MaybeGreedyOperator {
            greediness: GreedyBehavior::Greedy,
            op: SimpleOperator::Plus,
          }),
        }),
        Box::new(Expr::SingleLiteral(SingleLiteral(b'a'))),
        Box::new(Expr::SingleLiteral(SingleLiteral(b'a'))),
      ],
    };
    assert_eq!(&format!("{}", e), "asdf+aa");
  }
}

#[cfg(test)]
mod proptest_strategies {
  use proptest::prelude::*;

  use super::{expr::*, groups::*, literals::single::*, postfix_operators::*};
}
