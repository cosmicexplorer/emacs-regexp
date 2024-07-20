/* Description: Parsers for regexp patterns.

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

//! Parsers for regexp patterns.

use core::{alloc::Allocator, fmt, mem, num::NonZeroUsize};

use displaydoc::Display;
use thiserror::Error;

use crate::{
  alloc_types::*,
  ast::{
    anchors::{Anchor, EndAnchor, PointAnchor, StartAnchor, WordAnchor},
    char_properties::{
      CategoryChar, CategoryCode, CharPropertiesSelector, SyntaxChar, SyntaxCode, WordChar,
    },
    character_alternatives::{
      CharAltComponent, CharacterAlternative, CharacterClass, ComplementBehavior,
    },
    expr::{Expr, SingleCharSelector},
    groups::{Backref, BackrefIndex, ExplicitGroupIndex, GroupKind},
    literals::single::{escapes::Escaped, SingleLiteral},
    postfix_operators::{
      ExactRepeatOperator, GeneralRepeatOperator, GreedyBehavior, MaybeGreedyOperator, PostfixOp,
      RepeatNumeral, RepeatOperator, SimpleOperator,
    },
    Negation,
  },
  encoding::LiteralEncoding,
};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ContextKind {
  TopLevel,
  Group(GroupKind),
}

enum ContextComponent<L, A>
where
  L: LiteralEncoding,
  A: Allocator,
{
  SingleLiteral(SingleLiteral<L>),
  EscapedLiteral(Escaped<L>),
  Backref(Backref),
  Anchor(Anchor),
  CharSelector(SingleCharSelector<L, A>),
  Postfix { expr: Expr<L, A>, op: PostfixOp },
  Group { expr: Expr<L, A>, kind: GroupKind },
  Alternator,
}

impl<L, A> fmt::Debug for ContextComponent<L, A>
where
  L: LiteralEncoding,
  L::Single: fmt::Debug,
  A: Allocator,
{
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
    match self {
      Self::SingleLiteral(sl) => write!(f, "ContextComponent::SingleLiteral({:?})", sl),
      Self::EscapedLiteral(el) => write!(f, "ContextComponent::EscapedLiteral({:?})", el),
      Self::Backref(br) => write!(f, "ContextComponent::Backref({:?})", br),
      Self::Anchor(a) => write!(f, "ContextComponent::Anchor({:?})", a),
      Self::CharSelector(scs) => write!(f, "ContextComponent::CharSelector({:?})", scs),
      Self::Postfix { expr, op } => write!(
        f,
        "ContextComponent::Postfix {{ expr: {:?}, op: {:?} }}",
        expr, op
      ),
      Self::Group { expr, kind } => write!(
        f,
        "ContextComponent::Group {{ expr: {:?}, kind: {:?} }}",
        expr, kind
      ),
      Self::Alternator => write!(f, "ContextComponent::Alternator"),
    }
  }
}

fn apply_postfix<L, A>(
  component: ContextComponent<L, A>,
  op: PostfixOp,
  alloc: A,
) -> Option<ContextComponent<L, A>>
where
  L: LiteralEncoding,
  A: Allocator,
{
  let expr = match component {
    ContextComponent::SingleLiteral(c) => Expr::SingleLiteral(c),
    ContextComponent::EscapedLiteral(c) => Expr::EscapedLiteral(c),
    ContextComponent::Backref(b) => Expr::Backref(b),
    ContextComponent::Anchor(a) => Expr::Anchor(a),
    ContextComponent::CharSelector(scs) => Expr::CharSelector(scs),
    ContextComponent::Postfix { expr, op } => Expr::Postfix {
      inner: Box::new_in(expr, alloc),
      op,
    },
    ContextComponent::Group { expr, kind } => Expr::Group {
      inner: Box::new_in(expr, alloc),
      kind,
    },
    ContextComponent::Alternator => return None,
  };

  Some(ContextComponent::Postfix { expr, op })
}

fn coalesce_components<L, A>(
  components: impl IntoIterator<Item=ContextComponent<L, A>>,
  alloc: A,
) -> Expr<L, A>
where
  L: LiteralEncoding,
  A: Allocator+Clone,
{
  let mut cur_sequence: Vec<Box<Expr<L, A>, A>, A> = Vec::new_in(alloc.clone());
  let mut prev_alt_cases: Vec<Box<Expr<L, A>, A>, A> = Vec::new_in(alloc.clone());

  for el in components.into_iter() {
    let expr = match el {
      ContextComponent::Alternator => {
        let mut these_components = mem::replace(&mut cur_sequence, Vec::new_in(alloc.clone()));
        let new_case = if these_components.len() == 1 {
          these_components.pop().unwrap()
        } else {
          Box::new_in(
            Expr::Concatenation {
              components: these_components,
            },
            alloc.clone(),
          )
        };
        prev_alt_cases.push(new_case);
        continue;
      },
      ContextComponent::SingleLiteral(c) => Expr::SingleLiteral(c),
      ContextComponent::EscapedLiteral(c) => Expr::EscapedLiteral(c),
      ContextComponent::Backref(b) => Expr::Backref(b),
      ContextComponent::Anchor(a) => Expr::Anchor(a),
      ContextComponent::CharSelector(scs) => Expr::CharSelector(scs),
      ContextComponent::Postfix { expr, op } => Expr::Postfix {
        inner: Box::new_in(expr, alloc.clone()),
        op,
      },
      ContextComponent::Group { expr, kind } => Expr::Group {
        kind,
        inner: Box::new_in(expr, alloc.clone()),
      },
    };
    cur_sequence.push(Box::new_in(expr, alloc.clone()));
  }

  let final_case = if cur_sequence.len() == 1 {
    cur_sequence.pop().unwrap()
  } else {
    Box::new_in(
      Expr::Concatenation {
        components: cur_sequence,
      },
      alloc,
    )
  };

  if prev_alt_cases.is_empty() {
    *final_case
  } else {
    prev_alt_cases.push(final_case);
    Expr::Alternation {
      cases: prev_alt_cases,
    }
  }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display)]
pub enum ParseErrorKind {
  /// unmatched close paren
  UnmatchedCloseParen,
  /// invalid escape underscore
  InvalidEscapeUnderscore,
  /// invalid char range dash
  InvalidCharRangeDash,
  /// invalid char class
  InvalidCharClass,
  /// unknown char class
  UnknownCharClass,
  /// invalid postfix position
  InvalidPostfixPosition,
  /// postfix after alternator
  PostfixAfterAlternator,
  /// unmatched close repeat
  UnmatchedCloseRepeat,
  /// invalid repeat numeral
  InvalidRepeatNumeral,
  /// invalid close repeat
  InvalidCloseRepeat,
  /// invalid explicit group number
  InvalidExplicitGroupNumber,
  /// unmatched open paren
  UnmatchedOpenParen,
  /// invalid state at end of pattern
  InvalidEndState,
  /// invalid syntax code
  InvalidSyntaxCode,
  /// invalid category code
  InvalidCategoryCode,
}

/// parse error kind = {kind}, at = {at}
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display, Error)]
pub struct ParseError {
  pub kind: ParseErrorKind,
  pub at: usize,
}

pub fn parse<L, A>(pattern: L::Str<'_>, alloc: A) -> Result<Expr<L, A>, ParseError>
where
  L: LiteralEncoding,
  L::Single: fmt::Debug,
  A: Allocator+Clone,
{
  #[allow(clippy::type_complexity)]
  let mut group_context: Vec<(ContextKind, Vec<ContextComponent<L, A>, A>), A> =
    Vec::new_in(alloc.clone());
  group_context.push((ContextKind::TopLevel, Vec::new_in(alloc.clone())));

  let mut previous_was_backslash: bool = false;
  let mut previous_two_were_backslash_underscore: bool = false;

  let mut previous_was_syntax_code: bool = false;
  let mut previous_was_category_code: bool = false;
  let mut previous_code_negation: Option<Negation> = None;

  let mut previous_was_open_square_brace: bool = false;
  let mut currently_within_char_alternative: Option<CharacterAlternative<L, A>> = None;
  let mut previous_was_range_hyphen: bool = false;
  let mut currently_within_char_class: Option<Vec<L::Single, A>> = None;
  let mut previous_was_final_class_colon: bool = false;

  let mut currently_first_repeat_arg: Option<Vec<L::Single, A>> = None;
  let mut currently_second_repeat_arg: Option<Vec<L::Single, A>> = None;
  let mut previous_was_closing_backslash_of_repeat: bool = false;

  let mut previous_was_star: bool = false;
  let mut previous_was_plus: bool = false;
  let mut previous_was_question: bool = false;
  let mut previously_had_postfix: Option<PostfixOp> = None;

  let mut previous_was_open_group: bool = false;
  let mut previous_was_special_group: bool = false;
  let mut currently_within_group_number: Option<Vec<L::Single, A>> = None;

  let mut out_i: usize = 0;
  for (i, character) in L::iter(pattern).enumerate() {
    out_i = i;
    let (mut ctx_kind, mut components) = group_context.pop().unwrap();

    if previous_was_special_group {
      previous_was_special_group = false;
      if character == L::COLON {
        let new_components = Vec::new_in(alloc.clone());
        group_context.push((ctx_kind, components));
        group_context.push((ContextKind::Group(GroupKind::Shy), new_components));
        continue;
      }
      currently_within_group_number = Some(Vec::new_in(alloc.clone()));
    }
    if let Some(mut group_num_chars) = currently_within_group_number.take() {
      if character == L::COLON {
        let x: NonZeroUsize = match L::parse_nonnegative_integer(group_num_chars, alloc.clone())
          .and_then(NonZeroUsize::new)
        {
          None => {
            return Err(ParseError {
              kind: ParseErrorKind::InvalidExplicitGroupNumber,
              at: i,
            })
          },
          Some(x) => x,
        };
        let index = ExplicitGroupIndex(x);
        let new_components = Vec::new_in(alloc.clone());
        group_context.push((ctx_kind, components));
        group_context.push((
          ContextKind::Group(GroupKind::ExplicitlyNumbered(index)),
          new_components,
        ));
        continue;
      }
      if character == L::ZERO
        || character == L::ONE
        || character == L::TWO
        || character == L::THREE
        || character == L::FOUR
        || character == L::FIVE
        || character == L::SIX
        || character == L::SEVEN
        || character == L::EIGHT
        || character == L::NINE
      {
        group_num_chars.push(character);
        currently_within_group_number = Some(group_num_chars);
        group_context.push((ctx_kind, components));
        continue;
      }
      return Err(ParseError {
        kind: ParseErrorKind::InvalidExplicitGroupNumber,
        at: i,
      });
    }
    if previous_was_open_group {
      previous_was_open_group = false;
      if character == L::QUESTION {
        previous_was_special_group = true;
        group_context.push((ctx_kind, components));
        continue;
      }
      let new_components = Vec::new_in(alloc.clone());
      group_context.push((
        mem::replace(&mut ctx_kind, ContextKind::Group(GroupKind::Basic)),
        mem::replace(&mut components, new_components),
      ));
    }

    if previous_was_open_square_brace {
      previous_was_open_square_brace = false;
      debug_assert!(currently_within_char_alternative.is_none());
      if character == L::CARAT {
        currently_within_char_alternative = Some(CharacterAlternative {
          complemented: ComplementBehavior::Complemented,
          elements: Vec::new_in(alloc.clone()),
        });
        group_context.push((ctx_kind, components));
        continue;
      }
      currently_within_char_alternative = Some(CharacterAlternative {
        complemented: ComplementBehavior::Uncomplemented,
        elements: Vec::new_in(alloc.clone()),
      });
    }

    if let Some(CharacterAlternative {
      complemented,
      mut elements,
    }) = currently_within_char_alternative.take()
    {
      if let Some(mut class_chars) = currently_within_char_class.take() {
        if class_chars.is_empty() {
          if character == L::COLON {
            class_chars.push(character);
            currently_within_char_class = Some(class_chars);
            currently_within_char_alternative = Some(CharacterAlternative {
              complemented,
              elements,
            });
            group_context.push((ctx_kind, components));
            continue;
          }
          #[cfg(test)]
          dbg!(class_chars);
          return Err(ParseError {
            kind: ParseErrorKind::InvalidCharClass,
            at: i,
          });
        }
        debug_assert!(!class_chars.is_empty());

        if previous_was_final_class_colon {
          debug_assert_eq!(class_chars[0], L::COLON);
          debug_assert_eq!(class_chars[class_chars.len() - 1], L::COLON);
          let new_class = if character == L::CLOSE_SQUARE_BRACE {
            let class_str: L::String<A> = L::coalesce(
              mem::replace(&mut class_chars, Vec::new_in(alloc.clone())),
              alloc.clone(),
            );
            let class_str_ref: L::Str<'_> = L::str_ref(&class_str);
            /* FIXME: It's valid to compare an L::Str<'_> (or an L::Str<'a>) to an
             * L::Str<'static>, but the lifetime variance here is wrong and requires a
             * transmute. */
            let class_str_ref: L::Str<'static> = unsafe { mem::transmute(class_str_ref) };
            if class_str_ref == L::CLASS_ASCII {
              CharacterClass::ASCII
            } else if class_str_ref == L::CLASS_NONASCII {
              CharacterClass::NonASCII
            } else if class_str_ref == L::CLASS_ALNUM {
              CharacterClass::AlNum
            } else if class_str_ref == L::CLASS_ALPHA {
              CharacterClass::Alpha
            } else if class_str_ref == L::CLASS_BLANK {
              CharacterClass::Blank
            } else if class_str_ref == L::CLASS_SPACE {
              CharacterClass::Whitespace
            } else if class_str_ref == L::CLASS_CNTRL {
              CharacterClass::Control
            } else if class_str_ref == L::CLASS_DIGIT {
              CharacterClass::Digit
            } else if class_str_ref == L::CLASS_XDIGIT {
              CharacterClass::HexDigit
            } else if class_str_ref == L::CLASS_PRINT {
              CharacterClass::Printing
            } else if class_str_ref == L::CLASS_GRAPH {
              CharacterClass::Graphic
            } else if class_str_ref == L::CLASS_LOWER {
              CharacterClass::LowerCase
            } else if class_str_ref == L::CLASS_UPPER {
              CharacterClass::UpperCase
            } else if class_str_ref == L::CLASS_UNIBYTE {
              CharacterClass::Unibyte
            } else if class_str_ref == L::CLASS_MULTIBYTE {
              CharacterClass::Multibyte
            } else if class_str_ref == L::CLASS_WORD {
              CharacterClass::Word
            } else if class_str_ref == L::CLASS_PUNCT {
              CharacterClass::Punctuation
            } else {
              return Err(ParseError {
                kind: ParseErrorKind::InvalidCharClass,
                at: i,
              });
            }
          } else {
            return Err(ParseError {
              kind: ParseErrorKind::InvalidCharClass,
              at: i,
            });
          };
          previous_was_final_class_colon = false;
          elements.push(CharAltComponent::Class(new_class));
          currently_within_char_alternative = Some(CharacterAlternative {
            complemented,
            elements,
          });
          group_context.push((ctx_kind, components));
          continue;
        }

        if character == L::COLON {
          previous_was_final_class_colon = true;
          class_chars.push(character);
          currently_within_char_class = Some(class_chars);
          currently_within_char_alternative = Some(CharacterAlternative {
            complemented,
            elements,
          });
          group_context.push((ctx_kind, components));
          continue;
        }
        class_chars.push(character);
        currently_within_char_class = Some(class_chars);
        currently_within_char_alternative = Some(CharacterAlternative {
          complemented,
          elements,
        });
        group_context.push((ctx_kind, components));
        continue;
      }

      if previous_was_range_hyphen {
        debug_assert!(i > 0);
        match elements.pop() {
          Some(CharAltComponent::SingleLiteral(left)) => {
            let new_char_alt_component = CharAltComponent::LiteralRange {
              left,
              right: SingleLiteral(character),
            };
            elements.push(new_char_alt_component);
            previous_was_range_hyphen = false;
            currently_within_char_alternative = Some(CharacterAlternative {
              complemented,
              elements,
            });
            group_context.push((ctx_kind, components));
            continue;
          },
          _ => {
            return Err(ParseError {
              kind: ParseErrorKind::InvalidCharRangeDash,
              at: i - 1,
            })
          },
        }
      }

      if character == L::OPEN_SQUARE_BRACE {
        currently_within_char_class = Some(Vec::new_in(alloc.clone()));
        currently_within_char_alternative = Some(CharacterAlternative {
          complemented,
          elements,
        });
        group_context.push((ctx_kind, components));
        continue;
      }
      if character == L::DASH {
        previous_was_range_hyphen = true;
        currently_within_char_alternative = Some(CharacterAlternative {
          complemented,
          elements,
        });
        group_context.push((ctx_kind, components));
        continue;
      }
      if character == L::CLOSE_SQUARE_BRACE {
        let new_component =
          ContextComponent::CharSelector(SingleCharSelector::Alt(CharacterAlternative {
            complemented,
            elements,
          }));
        components.push(new_component);
        group_context.push((ctx_kind, components));
        continue;
      }
      let new_component = CharAltComponent::SingleLiteral(SingleLiteral(character));
      elements.push(new_component);
      currently_within_char_alternative = Some(CharacterAlternative {
        complemented,
        elements,
      });
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_two_were_backslash_underscore {
      components.push(ContextComponent::Anchor(
        if character == L::OPEN_ANGLE_BRACE {
          Anchor::Start(StartAnchor::Symbol)
        } else if character == L::CLOSE_ANGLE_BRACE {
          Anchor::End(EndAnchor::Symbol)
        } else {
          return Err(ParseError {
            kind: ParseErrorKind::InvalidEscapeUnderscore,
            at: i,
          });
        },
      ));
      previous_two_were_backslash_underscore = false;
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_was_syntax_code {
      let negation = previous_code_negation.take().unwrap();
      let ascii_char = L::parse_ascii(character).ok_or(ParseError {
        kind: ParseErrorKind::InvalidSyntaxCode,
        at: i,
      })?;
      components.push(ContextComponent::CharSelector(SingleCharSelector::Prop(
        CharPropertiesSelector::Syntax(SyntaxChar {
          code: SyntaxCode(ascii_char),
          negation,
        }),
      )));
      previous_was_syntax_code = false;
      group_context.push((ctx_kind, components));
      continue;
    }
    if previous_was_category_code {
      let negation = previous_code_negation.take().unwrap();
      let ascii_char = L::parse_ascii(character).ok_or(ParseError {
        kind: ParseErrorKind::InvalidCategoryCode,
        at: i,
      })?;
      components.push(ContextComponent::CharSelector(SingleCharSelector::Prop(
        CharPropertiesSelector::Category(CategoryChar {
          code: CategoryCode(ascii_char),
          negation,
        }),
      )));
      previous_was_category_code = false;
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_was_closing_backslash_of_repeat {
      if character == L::CLOSE_CURLY_BRACE {
        previous_was_closing_backslash_of_repeat = false;
      } else {
        return Err(ParseError {
          kind: ParseErrorKind::InvalidCloseRepeat,
          at: i,
        });
      }
      match (
        currently_first_repeat_arg.take(),
        currently_second_repeat_arg.take(),
      ) {
        (None, None) => unreachable!(),
        (None, Some(_)) => unreachable!(),
        (Some(left), None) => {
          let x: usize = L::parse_nonnegative_integer(left, alloc.clone()).ok_or(ParseError {
            kind: ParseErrorKind::InvalidRepeatNumeral,
            at: i,
          })?;
          previously_had_postfix = Some(PostfixOp::Repeat(RepeatOperator::Exact(
            ExactRepeatOperator {
              times: RepeatNumeral(x),
            },
          )));
        },
        (Some(left), Some(right)) => {
          let left: Option<RepeatNumeral> = if left.is_empty() {
            None
          } else {
            let x: usize = L::parse_nonnegative_integer(left, alloc.clone()).ok_or(ParseError {
              kind: ParseErrorKind::InvalidRepeatNumeral,
              at: i,
            })?;
            Some(RepeatNumeral(x))
          };
          let right: Option<RepeatNumeral> = if right.is_empty() {
            None
          } else {
            let x: usize =
              L::parse_nonnegative_integer(right, alloc.clone()).ok_or(ParseError {
                kind: ParseErrorKind::InvalidRepeatNumeral,
                at: i,
              })?;
            Some(RepeatNumeral(x))
          };
          previously_had_postfix = Some(PostfixOp::Repeat(RepeatOperator::General(
            GeneralRepeatOperator { left, right },
          )));
        },
      }
      group_context.push((ctx_kind, components));
      continue;
    }
    if let Some(mut second_repeat_arg) = currently_second_repeat_arg.take() {
      if character == L::BACKSLASH {
        previous_was_closing_backslash_of_repeat = true;
        currently_second_repeat_arg = Some(second_repeat_arg);
      } else if character == L::ZERO
        || character == L::ONE
        || character == L::TWO
        || character == L::THREE
        || character == L::FOUR
        || character == L::FIVE
        || character == L::SIX
        || character == L::SEVEN
        || character == L::EIGHT
        || character == L::NINE
      {
        second_repeat_arg.push(character);
        currently_second_repeat_arg = Some(second_repeat_arg);
      } else {
        return Err(ParseError {
          kind: ParseErrorKind::InvalidRepeatNumeral,
          at: i,
        });
      }
      group_context.push((ctx_kind, components));
      continue;
    }
    if let Some(mut first_repeat_arg) = currently_first_repeat_arg.take() {
      if character == L::BACKSLASH {
        previous_was_closing_backslash_of_repeat = true;
        currently_first_repeat_arg = Some(first_repeat_arg);
      } else if character == L::COMMA {
        currently_first_repeat_arg = Some(first_repeat_arg);
        currently_second_repeat_arg = Some(Vec::new_in(alloc.clone()));
      } else if character == L::ZERO
        || character == L::ONE
        || character == L::TWO
        || character == L::THREE
        || character == L::FOUR
        || character == L::FIVE
        || character == L::SIX
        || character == L::SEVEN
        || character == L::EIGHT
        || character == L::NINE
      {
        first_repeat_arg.push(character);
        currently_first_repeat_arg = Some(first_repeat_arg);
      } else {
        return Err(ParseError {
          kind: ParseErrorKind::InvalidRepeatNumeral,
          at: i,
        });
      }
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_was_backslash {
      previous_was_backslash = false;
      if character == L::UNDERSCORE {
        previous_two_were_backslash_underscore = true;
        group_context.push((ctx_kind, components));
        continue;
      };
      if character == L::OPEN_CIRCLE_BRACE {
        previous_was_open_group = true;
        group_context.push((ctx_kind, components));
        continue;
      }
      if character == L::CLOSE_CIRCLE_BRACE {
        match ctx_kind {
          ContextKind::TopLevel => {
            return Err(ParseError {
              kind: ParseErrorKind::UnmatchedCloseParen,
              at: i,
            });
          },
          ContextKind::Group(kind) => {
            let inner = coalesce_components(components, alloc.clone());
            let new_group = ContextComponent::Group { kind, expr: inner };
            let (ctx_kind, mut components) = group_context.pop().unwrap();
            components.push(new_group);
            group_context.push((ctx_kind, components));
            continue;
          },
        }
      }
      if character == L::OPEN_CURLY_BRACE {
        currently_first_repeat_arg = Some(Vec::new_in(alloc.clone()));
        group_context.push((ctx_kind, components));
        continue;
      }
      if character == L::CLOSE_CURLY_BRACE {
        return Err(ParseError {
          kind: ParseErrorKind::UnmatchedCloseRepeat,
          at: i,
        });
      }
      if character == L::SMALL_S {
        previous_was_syntax_code = true;
        previous_code_negation = Some(Negation::Standard);
        group_context.push((ctx_kind, components));
        continue;
      }
      if character == L::BIG_S {
        previous_was_syntax_code = true;
        previous_code_negation = Some(Negation::Negated);
        group_context.push((ctx_kind, components));
        continue;
      }
      if character == L::SMALL_C {
        previous_was_category_code = true;
        previous_code_negation = Some(Negation::Standard);
        group_context.push((ctx_kind, components));
        continue;
      }
      if character == L::BIG_C {
        previous_was_category_code = true;
        previous_code_negation = Some(Negation::Negated);
        group_context.push((ctx_kind, components));
        continue;
      }
      let new_component = if character == L::PIPE {
        ContextComponent::Alternator
      } else if character == L::ONE {
        ContextComponent::Backref(Backref(BackrefIndex(1)))
      } else if character == L::TWO {
        ContextComponent::Backref(Backref(BackrefIndex(2)))
      } else if character == L::THREE {
        ContextComponent::Backref(Backref(BackrefIndex(3)))
      } else if character == L::FOUR {
        ContextComponent::Backref(Backref(BackrefIndex(4)))
      } else if character == L::FIVE {
        ContextComponent::Backref(Backref(BackrefIndex(5)))
      } else if character == L::SIX {
        ContextComponent::Backref(Backref(BackrefIndex(6)))
      } else if character == L::SEVEN {
        ContextComponent::Backref(Backref(BackrefIndex(7)))
      } else if character == L::EIGHT {
        ContextComponent::Backref(Backref(BackrefIndex(8)))
      } else if character == L::NINE {
        ContextComponent::Backref(Backref(BackrefIndex(9)))
      } else if character == L::EQUALS {
        ContextComponent::Anchor(Anchor::Point(PointAnchor))
      } else if character == L::SMALL_B {
        ContextComponent::Anchor(Anchor::Word(WordAnchor {
          negation: Negation::Standard,
        }))
      } else if character == L::BIG_B {
        ContextComponent::Anchor(Anchor::Word(WordAnchor {
          negation: Negation::Negated,
        }))
      } else if character == L::BACKTICK {
        ContextComponent::Anchor(Anchor::Start(StartAnchor::Backtick))
      } else if character == L::OPEN_ANGLE_BRACE {
        ContextComponent::Anchor(Anchor::Start(StartAnchor::Word))
      } else if character == L::SINGLE_QUOTE {
        ContextComponent::Anchor(Anchor::End(EndAnchor::SingleQuote))
      } else if character == L::CLOSE_ANGLE_BRACE {
        ContextComponent::Anchor(Anchor::End(EndAnchor::Word))
      } else if character == L::SMALL_W {
        ContextComponent::CharSelector(SingleCharSelector::Prop(CharPropertiesSelector::Word(
          WordChar {
            negation: Negation::Standard,
          },
        )))
      } else if character == L::BIG_W {
        ContextComponent::CharSelector(SingleCharSelector::Prop(CharPropertiesSelector::Word(
          WordChar {
            negation: Negation::Negated,
          },
        )))
      } else {
        ContextComponent::EscapedLiteral(Escaped(SingleLiteral(character)))
      };
      components.push(new_component);
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_was_star {
      previous_was_star = false;
      if character == L::QUESTION {
        previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
          op: SimpleOperator::Star,
          greediness: GreedyBehavior::NonGreedy,
        }));
        group_context.push((ctx_kind, components));
        continue;
      }
      previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
        op: SimpleOperator::Star,
        greediness: GreedyBehavior::Greedy,
      }));
    }
    if previous_was_plus {
      previous_was_plus = false;
      if character == L::QUESTION {
        previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
          op: SimpleOperator::Plus,
          greediness: GreedyBehavior::NonGreedy,
        }));
        group_context.push((ctx_kind, components));
        continue;
      }
      previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
        op: SimpleOperator::Plus,
        greediness: GreedyBehavior::Greedy,
      }));
    }
    if previous_was_question {
      previous_was_question = false;
      if character == L::QUESTION {
        previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
          op: SimpleOperator::Question,
          greediness: GreedyBehavior::NonGreedy,
        }));
        group_context.push((ctx_kind, components));
        continue;
      }
      previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
        op: SimpleOperator::Question,
        greediness: GreedyBehavior::Greedy,
      }));
    }

    if let Some(op) = previously_had_postfix.take() {
      let postfixed_expr = match components.pop() {
        None => {
          return Err(ParseError {
            kind: ParseErrorKind::InvalidPostfixPosition,
            at: i,
          })
        },
        Some(c) => match apply_postfix(c, op, alloc.clone()) {
          None => {
            return Err(ParseError {
              kind: ParseErrorKind::PostfixAfterAlternator,
              at: i,
            })
          },
          Some(expr) => expr,
        },
      };
      components.push(postfixed_expr);
    }

    if character == L::BACKSLASH {
      previous_was_backslash = true;
      group_context.push((ctx_kind, components));
      continue;
    }
    if character == L::OPEN_SQUARE_BRACE {
      previous_was_open_square_brace = true;
      group_context.push((ctx_kind, components));
      continue;
    }
    if character == L::STAR {
      previous_was_star = true;
      group_context.push((ctx_kind, components));
      continue;
    }
    if character == L::PLUS {
      previous_was_plus = true;
      group_context.push((ctx_kind, components));
      continue;
    }
    if character == L::QUESTION {
      previous_was_question = true;
      group_context.push((ctx_kind, components));
      continue;
    }
    let new_component = if character == L::CARAT {
      ContextComponent::<L, A>::Anchor(Anchor::Start(StartAnchor::Carat))
    } else if character == L::DOLLAR {
      ContextComponent::Anchor(Anchor::End(EndAnchor::Dollar))
    } else if character == L::DOT {
      ContextComponent::CharSelector(SingleCharSelector::Dot)
    } else {
      ContextComponent::SingleLiteral(SingleLiteral(character))
    };
    components.push(new_component);
    group_context.push((ctx_kind, components));
  }
  /* END LOOP! */

  let mut top_level_components = match group_context.pop().unwrap() {
    (ContextKind::Group(_), _) => {
      return Err(ParseError {
        kind: ParseErrorKind::UnmatchedOpenParen,
        at: out_i,
      })
    },
    (ContextKind::TopLevel, top_level_components) => {
      assert!(group_context.is_empty());
      top_level_components
    },
  };

  /* Address any state remaining at the end! */
  if previous_was_special_group {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  if currently_within_group_number.is_some() {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  #[cfg(test)]
  dbg!(&top_level_components);

  if previous_was_open_group {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  if previous_was_open_square_brace {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  #[cfg(test)]
  dbg!(&top_level_components);

  if currently_within_char_alternative.is_some() {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  #[cfg(test)]
  dbg!(&top_level_components);

  if previous_was_final_class_colon {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  if previous_was_range_hyphen {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }

  if previous_two_were_backslash_underscore {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }

  if previous_was_syntax_code {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  if previous_was_category_code {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }

  if previous_was_closing_backslash_of_repeat {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  if currently_second_repeat_arg.is_some() {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  if currently_first_repeat_arg.is_some() {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }
  if previous_was_backslash {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: out_i,
    });
  }

  if previous_was_star {
    previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
      op: SimpleOperator::Star,
      greediness: GreedyBehavior::Greedy,
    }));
  }
  if previous_was_plus {
    previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
      op: SimpleOperator::Plus,
      greediness: GreedyBehavior::Greedy,
    }));
  }
  if previous_was_question {
    previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
      op: SimpleOperator::Question,
      greediness: GreedyBehavior::Greedy,
    }));
  }
  if let Some(op) = previously_had_postfix {
    let postfixed_expr = match top_level_components.pop() {
      None => {
        return Err(ParseError {
          kind: ParseErrorKind::InvalidPostfixPosition,
          at: out_i,
        })
      },
      Some(c) => match apply_postfix(c, op, alloc.clone()) {
        None => {
          return Err(ParseError {
            kind: ParseErrorKind::PostfixAfterAlternator,
            at: out_i,
          })
        },
        Some(expr) => expr,
      },
    };
    top_level_components.push(postfixed_expr);
  }


  let top_level_expr = coalesce_components(top_level_components, alloc);

  Ok(top_level_expr)
}

#[cfg(test)]
mod test {
  use std::alloc::Global;

  use proptest::prelude::*;

  use super::*;
  use crate::encoding::{ByteEncoding, MultibyteEncoding, UnicodeEncoding};

  #[test]
  fn parse_empty() {
    let parsed = parse::<ByteEncoding, _>(b"", Global).unwrap();
    assert_eq!(parsed, Expr::<ByteEncoding, Global>::Concatenation {
      components: vec![]
    });

    let parsed = parse::<UnicodeEncoding, _>("", Global).unwrap();
    assert_eq!(parsed, Expr::<UnicodeEncoding, Global>::Concatenation {
      components: vec![]
    });

    /* FIXME: multibyte! */
  }

  #[test]
  fn parse_single_lit() {
    let parsed = parse::<ByteEncoding, _>(b"a", Global).unwrap();
    assert_eq!(
      parsed,
      Expr::<ByteEncoding, Global>::SingleLiteral(SingleLiteral(b'a'))
    );

    let parsed = parse::<UnicodeEncoding, _>("a", Global).unwrap();
    assert_eq!(
      parsed,
      Expr::<UnicodeEncoding, Global>::SingleLiteral(SingleLiteral('a'))
    );

    let parsed = parse::<ByteEncoding, _>(b"\\a", Global).unwrap();
    assert_eq!(
      parsed,
      Expr::<ByteEncoding, Global>::EscapedLiteral(Escaped(SingleLiteral(b'a')))
    );

    let parsed = parse::<UnicodeEncoding, _>("\\a", Global).unwrap();
    assert_eq!(
      parsed,
      Expr::<UnicodeEncoding, Global>::EscapedLiteral(Escaped(SingleLiteral('a')))
    );
  }

  #[test]
  fn parse_plus_postfix() {
    let parsed = parse::<ByteEncoding, _>(b"asdf\\(.\\)+a", Global).unwrap();
    assert_eq!(parsed, Expr::<ByteEncoding, Global>::Concatenation {
      components: vec![
        Box::new(Expr::SingleLiteral(SingleLiteral(b'a'))),
        Box::new(Expr::SingleLiteral(SingleLiteral(b's'))),
        Box::new(Expr::SingleLiteral(SingleLiteral(b'd'))),
        Box::new(Expr::SingleLiteral(SingleLiteral(b'f'))),
        Box::new(Expr::Postfix {
          inner: Box::new(Expr::Group {
            kind: GroupKind::Basic,
            inner: Box::new(Expr::CharSelector(SingleCharSelector::Dot)),
          }),
          op: PostfixOp::Simple(MaybeGreedyOperator {
            greediness: GreedyBehavior::Greedy,
            op: SimpleOperator::Plus,
          }),
        }),
        Box::new(Expr::SingleLiteral(SingleLiteral(b'a'))),
      ]
    });

    let parsed = parse::<ByteEncoding, _>(b"asdf+", Global).unwrap();
    assert_eq!(parsed, Expr::<ByteEncoding, Global>::Concatenation {
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
      ]
    });

    let parsed = parse::<ByteEncoding, _>(b"asdf+aa", Global).unwrap();
    assert_eq!(parsed, Expr::<ByteEncoding, Global>::Concatenation {
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
      ]
    });
    assert_eq!(&format!("{}", parsed), "asdf+aa");
  }

  #[test]
  fn parse_repeat() {
    let parsed = parse::<ByteEncoding, _>(b"a\\{2\\}", Global).unwrap();
    assert_eq!(parsed, Expr::Postfix {
      inner: Box::new(Expr::SingleLiteral(SingleLiteral(b'a'))),
      op: PostfixOp::Repeat(RepeatOperator::Exact(ExactRepeatOperator {
        times: RepeatNumeral(2)
      })),
    });
    assert_eq!(&format!("{}", parsed), "a\\{2\\}");
  }

  #[test]
  fn parse_char_alt() {
    let parsed = parse::<UnicodeEncoding, _>("a[a]", Global).unwrap();
    assert_eq!(parsed, Expr::Concatenation {
      components: vec![
        Box::new(Expr::SingleLiteral(SingleLiteral('a'))),
        Box::new(Expr::CharSelector(SingleCharSelector::Alt(
          CharacterAlternative {
            complemented: ComplementBehavior::Uncomplemented,
            elements: vec![CharAltComponent::SingleLiteral(SingleLiteral('a'))]
          }
        )))
      ]
    });
    assert_eq!(&format!("{}", parsed), "a[a]");

    let parsed = parse::<UnicodeEncoding, _>("a[a]a", Global).unwrap();
    assert_eq!(parsed, Expr::Concatenation {
      components: vec![
        Box::new(Expr::SingleLiteral(SingleLiteral('a'))),
        Box::new(Expr::CharSelector(SingleCharSelector::Alt(
          CharacterAlternative {
            complemented: ComplementBehavior::Uncomplemented,
            elements: vec![CharAltComponent::SingleLiteral(SingleLiteral('a'))]
          }
        ))),
        Box::new(Expr::SingleLiteral(SingleLiteral('a'))),
      ]
    });
    assert_eq!(&format!("{}", parsed), "a[a]a");
  }

  prop_compose! {
    fn gen_expr_byte()
      (
        e in prop::arbitrary::arbitrary_with::<
          Expr<ByteEncoding, Global>,
          _,
          _
        >((((), 5, Global), 5, 5, 5, 5, 5))
      ) -> Expr<ByteEncoding, Global> {
        e
      }
  }

  prop_compose! {
    fn gen_expr_utf8()
      (
        e in prop::arbitrary::arbitrary_with::<
          Expr<UnicodeEncoding, Global>,
          _,
          _
        >((((), 5, Global), 5, 5, 5, 5, 5))
      ) -> Expr<UnicodeEncoding, Global> {
        e
      }
  }

  prop_compose! {
    fn gen_expr_multibyte()
      (
        e in prop::arbitrary::arbitrary_with::<
          Expr<MultibyteEncoding, Global>,
          _,
          _
        >((((), 5, Global), 5, 5, 5, 5, 5))
      ) -> Expr<MultibyteEncoding, Global> {
        e
      }
  }

  /* FIXME: how to handle non-ascii chars? */
  /* proptest! { */
  /* #[test] */
  /* fn parse_byte_roundtrip(e in gen_expr_byte()) { */
  /* let formatted = format!("{}", e); */
  /* let parsed = parse::<ByteEncoding, Global>(formatted.as_bytes(), Global); */
  /* prop_assert!(parsed.is_ok()); */
  /* let parsed = parsed.unwrap(); */
  /* prop_assert_eq!(e, parsed); */
  /* } */
  /* } */

  proptest! {
    #[test]
    fn parse_utf8_roundtrip(e in gen_expr_utf8()) {
      let formatted = format!("{}", e);
      let parsed = parse::<UnicodeEncoding, Global>(&formatted, Global);
      prop_assert!(parsed.is_ok());
      let parsed = parsed.unwrap();
      prop_assert_eq!(e, parsed);
    }
  }

  /* FIXME: how to handle non-unicode chars? */
  proptest! {
    #[test]
    fn parse_multibyte_roundtrip(e in gen_expr_multibyte()) {
      let formatted = format!("{}", e);
      let parsed = parse::<MultibyteEncoding, Global>(
        emacs_multibyte::PackedString::from_str(&formatted),
        Global);
      prop_assert!(parsed.is_ok());
      let parsed = parsed.unwrap();
      prop_assert_eq!(e, parsed);
    }
  }
}
