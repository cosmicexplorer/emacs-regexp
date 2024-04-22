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

use core::{alloc::Allocator, mem, num::NonZeroUsize, str};

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
  encoding::ByteEncoding,
};


/* pub fn parse<'n, L, A>(pattern: L::String<'n>) -> Expr<'n, L, A> */
/* where */
/* L: LiteralEncoding, */
/* A: Allocator, */
/* { */
/* todo!() */
/* } */

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ContextKind {
  TopLevel,
  Group(GroupKind),
}

enum ContextComponent<A>
where A: Allocator
{
  SingleLiteral(SingleLiteral<ByteEncoding>),
  EscapedLiteral(Escaped<ByteEncoding>),
  Backref(Backref),
  Anchor(Anchor),
  CharSelector(SingleCharSelector<ByteEncoding, A>),
  Postfix {
    expr: Expr<ByteEncoding, A>,
    op: PostfixOp,
  },
  Group {
    expr: Expr<ByteEncoding, A>,
    kind: GroupKind,
  },
  Alternator,
}

fn apply_postfix<A>(
  component: ContextComponent<A>,
  op: PostfixOp,
  alloc: A,
) -> Option<ContextComponent<A>>
where
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

fn coalesce_components<A>(
  components: impl IntoIterator<Item=ContextComponent<A>>,
  alloc: A,
) -> Expr<ByteEncoding, A>
where
  A: Allocator+Clone,
{
  let mut cur_sequence: Vec<Box<Expr<ByteEncoding, A>, A>, A> = Vec::new_in(alloc.clone());
  let mut prev_alt_cases: Vec<Box<Expr<ByteEncoding, A>, A>, A> = Vec::new_in(alloc.clone());

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
  /// internal logic error
  InternalLogicError,
  /// invalid state at end of pattern
  InvalidEndState,
}

/// parse error kind = {kind}, at = {at}
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Display, Error)]
pub struct ParseError {
  pub kind: ParseErrorKind,
  pub at: usize,
}

pub fn parse_bytes<A>(pattern: &[u8], alloc: A) -> Result<Expr<ByteEncoding, A>, ParseError>
where A: Allocator+Clone {
  let mut group_context: Vec<(ContextKind, Vec<ContextComponent<A>, A>), A> =
    Vec::new_in(alloc.clone());
  group_context.push((ContextKind::TopLevel, Vec::new_in(alloc.clone())));

  let mut previous_was_backslash: bool = false;
  let mut previous_two_were_backslash_underscore: bool = false;

  let mut previous_was_syntax_code: bool = false;
  let mut previous_was_category_code: bool = false;
  let mut previous_code_negation: Option<Negation> = None;

  let mut previous_was_open_square_brace: bool = false;
  let mut currently_within_char_alternative: Option<CharacterAlternative<ByteEncoding, A>> = None;
  let mut previous_was_range_hyphen: bool = false;
  let mut currently_within_char_class: Option<Vec<u8, A>> = None;
  let mut previous_was_final_class_colon: bool = false;

  let mut currently_first_repeat_arg: Option<Vec<u8, A>> = None;
  let mut currently_second_repeat_arg: Option<Vec<u8, A>> = None;
  let mut previous_was_closing_backslash_of_repeat: bool = false;

  let mut previous_was_star: bool = false;
  let mut previous_was_plus: bool = false;
  let mut previous_was_question: bool = false;
  let mut previously_had_postfix: Option<PostfixOp> = None;

  let mut previous_was_open_group: bool = false;
  let mut previous_was_special_group: bool = false;
  let mut currently_within_group_number: Option<Vec<u8, A>> = None;

  for (i, byte) in pattern.iter().enumerate() {
    let (mut ctx_kind, mut components) = group_context.pop().ok_or(ParseError {
      kind: ParseErrorKind::InternalLogicError,
      at: i,
    })?;

    if previous_was_special_group {
      previous_was_special_group = false;
      match byte {
        b':' => {
          let new_components = Vec::new_in(alloc.clone());
          group_context.push((ctx_kind, components));
          group_context.push((ContextKind::Group(GroupKind::Shy), new_components));
          continue;
        },
        _ => {
          currently_within_group_number = Some(Vec::new_in(alloc.clone()));
        },
      }
    }
    if let Some(mut group_num_chars) = currently_within_group_number.take() {
      match byte {
        b':' => {
          let s = str::from_utf8(&group_num_chars[..]).unwrap();
          if s.is_empty() {
            return Err(ParseError {
              kind: ParseErrorKind::InvalidExplicitGroupNumber,
              at: i,
            });
          }
          let x: usize = s.parse().unwrap();
          match NonZeroUsize::new(x) {
            None => {
              return Err(ParseError {
                kind: ParseErrorKind::InvalidExplicitGroupNumber,
                at: i,
              })
            },
            Some(x) => {
              let index = ExplicitGroupIndex(x);
              let new_components = Vec::new_in(alloc.clone());
              group_context.push((ctx_kind, components));
              group_context.push((
                ContextKind::Group(GroupKind::ExplicitlyNumbered(index)),
                new_components,
              ));
              continue;
            },
          }
        },
        x @ (b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' | b'8' | b'9') => {
          group_num_chars.push(*x);
          currently_within_group_number = Some(group_num_chars);
          group_context.push((ctx_kind, components));
          continue;
        },
        _ => {
          return Err(ParseError {
            kind: ParseErrorKind::InvalidExplicitGroupNumber,
            at: i,
          });
        },
      }
    }
    if previous_was_open_group {
      previous_was_open_group = false;
      match byte {
        b'?' => {
          previous_was_special_group = true;
          group_context.push((ctx_kind, components));
          continue;
        },
        _ => {
          let new_components = Vec::new_in(alloc.clone());
          group_context.push((
            mem::replace(&mut ctx_kind, ContextKind::Group(GroupKind::Basic)),
            mem::replace(&mut components, new_components),
          ));
        },
      }
    }

    if previous_was_open_square_brace {
      previous_was_open_square_brace = false;
      debug_assert!(currently_within_char_alternative.is_none());
      match byte {
        b'^' => {
          currently_within_char_alternative = Some(CharacterAlternative {
            complemented: ComplementBehavior::Complemented,
            elements: Vec::new_in(alloc.clone()),
          });
          group_context.push((ctx_kind, components));
          continue;
        },
        _ => {
          currently_within_char_alternative = Some(CharacterAlternative {
            complemented: ComplementBehavior::Uncomplemented,
            elements: Vec::new_in(alloc.clone()),
          });
        },
      }
    }

    if let Some(CharacterAlternative {
      complemented,
      mut elements,
    }) = currently_within_char_alternative.take()
    {
      if let Some(mut class_chars) = currently_within_char_class.take() {
        if class_chars.is_empty() {
          match byte {
            b':' => {
              class_chars.push(b':');
              currently_within_char_class = Some(class_chars);
              currently_within_char_alternative = Some(CharacterAlternative {
                complemented,
                elements,
              });
              group_context.push((ctx_kind, components));
              continue;
            },
            _ => {
              return Err(ParseError {
                kind: ParseErrorKind::InvalidCharClass,
                at: i,
              });
            },
          }
        }
        debug_assert!(!class_chars.is_empty());

        if previous_was_final_class_colon {
          debug_assert_eq!(class_chars[0], b':');
          debug_assert_eq!(class_chars[class_chars.len() - 1], b':');
          let new_class = match byte {
            b']' => match &class_chars[..] {
              b":ascii:" => CharacterClass::ASCII,
              b":nonascii:" => CharacterClass::NonASCII,
              b":alnum:" => CharacterClass::AlNum,
              b":alpha:" => CharacterClass::Alpha,
              b":blank:" => CharacterClass::Blank,
              b":space:" => CharacterClass::Whitespace,
              b":cntrl:" => CharacterClass::Control,
              b":digit:" => CharacterClass::Digit,
              b":xdigit:" => CharacterClass::HexDigit,
              b":print:" => CharacterClass::Printing,
              b":graph:" => CharacterClass::Graphic,
              b":lower:" => CharacterClass::LowerCase,
              b":upper:" => CharacterClass::UpperCase,
              b":unibyte:" => CharacterClass::Unibyte,
              b":multibyte:" => CharacterClass::Multibyte,
              b":word:" => CharacterClass::Word,
              b":punct:" => CharacterClass::Punctuation,
              _ => {
                return Err(ParseError {
                  kind: ParseErrorKind::UnknownCharClass,
                  at: i,
                });
              },
            },
            _ => {
              return Err(ParseError {
                kind: ParseErrorKind::InvalidCharClass,
                at: i,
              });
            },
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

        match byte {
          b':' => {
            previous_was_final_class_colon = true;
            class_chars.push(b':');
            currently_within_char_class = Some(class_chars);
            currently_within_char_alternative = Some(CharacterAlternative {
              complemented,
              elements,
            });
            group_context.push((ctx_kind, components));
            continue;
          },
          x if *x >= b'a' && *x <= b'z' => {
            class_chars.push(*x);
            currently_within_char_class = Some(class_chars);
            currently_within_char_alternative = Some(CharacterAlternative {
              complemented,
              elements,
            });
            group_context.push((ctx_kind, components));
            continue;
          },
          _ => {
            return Err(ParseError {
              kind: ParseErrorKind::InvalidCharClass,
              at: i,
            });
          },
        }
      }

      if previous_was_range_hyphen {
        debug_assert!(i > 0);
        match elements.pop() {
          Some(CharAltComponent::SingleLiteral(left)) => {
            let new_char_alt_component = CharAltComponent::LiteralRange {
              left,
              right: SingleLiteral(*byte),
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

      match byte {
        b'-' => {
          previous_was_range_hyphen = true;
          currently_within_char_alternative = Some(CharacterAlternative {
            complemented,
            elements,
          });
          group_context.push((ctx_kind, components));
          continue;
        },
        b'[' => {
          currently_within_char_class = Some(Vec::new_in(alloc.clone()));
          currently_within_char_alternative = Some(CharacterAlternative {
            complemented,
            elements,
          });
          group_context.push((ctx_kind, components));
          continue;
        },
        b']' => {
          let new_char_alternative = CharacterAlternative {
            complemented,
            elements,
          };
          components.push(ContextComponent::CharSelector(SingleCharSelector::Alt(
            new_char_alternative,
          )));
          group_context.push((ctx_kind, components));
          continue;
        },
        x => {
          let new_component = CharAltComponent::SingleLiteral(SingleLiteral(*x));
          elements.push(new_component);
          currently_within_char_alternative = Some(CharacterAlternative {
            complemented,
            elements,
          });
          group_context.push((ctx_kind, components));
          continue;
        },
      }
    }

    if previous_two_were_backslash_underscore {
      components.push(ContextComponent::Anchor(match byte {
        b'<' => Anchor::Start(StartAnchor::Symbol),
        b'>' => Anchor::End(EndAnchor::Symbol),
        _ => {
          return Err(ParseError {
            kind: ParseErrorKind::InvalidEscapeUnderscore,
            at: i,
          })
        },
      }));
      previous_two_were_backslash_underscore = false;
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_was_syntax_code {
      let negation = previous_code_negation.take().unwrap();
      components.push(ContextComponent::CharSelector(SingleCharSelector::Prop(
        CharPropertiesSelector::Syntax(SyntaxChar {
          code: SyntaxCode(*byte),
          negation,
        }),
      )));
      previous_was_syntax_code = false;
      group_context.push((ctx_kind, components));
      continue;
    }
    if previous_was_category_code {
      let negation = previous_code_negation.take().unwrap();
      components.push(ContextComponent::CharSelector(SingleCharSelector::Prop(
        CharPropertiesSelector::Category(CategoryChar {
          code: CategoryCode(*byte),
          negation,
        }),
      )));
      previous_was_category_code = false;
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_was_closing_backslash_of_repeat {
      match byte {
        b'}' => {
          previous_was_closing_backslash_of_repeat = false;
        },
        _ => {
          return Err(ParseError {
            kind: ParseErrorKind::InvalidCloseRepeat,
            at: i,
          });
        },
      }
      match (
        currently_first_repeat_arg.take(),
        currently_second_repeat_arg.take(),
      ) {
        (None, None) => unreachable!(),
        (None, Some(_)) => unreachable!(),
        (Some(left), None) => {
          if left.is_empty() {
            return Err(ParseError {
              kind: ParseErrorKind::InvalidRepeatNumeral,
              at: i,
            });
          } else {
            let s = str::from_utf8(&left).unwrap();
            let x: usize = s.parse().unwrap();
            previously_had_postfix = Some(PostfixOp::Repeat(RepeatOperator::Exact(
              ExactRepeatOperator {
                times: RepeatNumeral(x),
              },
            )));
          }
        },
        (Some(left), Some(right)) => {
          let left = if left.is_empty() {
            None
          } else {
            let s = str::from_utf8(&left).unwrap();
            let x: usize = s.parse().unwrap();
            Some(RepeatNumeral(x))
          };
          let right = if right.is_empty() {
            None
          } else {
            let s = str::from_utf8(&right).unwrap();
            let x: usize = s.parse().unwrap();
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
      match byte {
        b'\\' => {
          previous_was_closing_backslash_of_repeat = true;
          currently_second_repeat_arg = Some(second_repeat_arg);
          continue;
        },
        x @ (b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' | b'8' | b'9') => {
          second_repeat_arg.push(*x);
          currently_second_repeat_arg = Some(second_repeat_arg);
          continue;
        },
        _ => {
          return Err(ParseError {
            kind: ParseErrorKind::InvalidRepeatNumeral,
            at: i,
          })
        },
      }
    }
    if let Some(mut first_repeat_arg) = currently_first_repeat_arg.take() {
      match byte {
        b'\\' => {
          previous_was_closing_backslash_of_repeat = true;
          currently_first_repeat_arg = Some(first_repeat_arg);
          continue;
        },
        b',' => {
          currently_first_repeat_arg = Some(first_repeat_arg);
          currently_second_repeat_arg = Some(Vec::new_in(alloc.clone()));
        },
        x @ (b'0' | b'1' | b'2' | b'3' | b'4' | b'5' | b'6' | b'7' | b'8' | b'9') => {
          first_repeat_arg.push(*x);
          currently_first_repeat_arg = Some(first_repeat_arg);
          continue;
        },
        _ => {
          return Err(ParseError {
            kind: ParseErrorKind::InvalidRepeatNumeral,
            at: i,
          })
        },
      }
    }

    if previous_was_backslash {
      previous_was_backslash = false;
      let new_component = match byte {
        b'_' => {
          previous_two_were_backslash_underscore = true;
          group_context.push((ctx_kind, components));
          continue;
        },
        b'|' => ContextComponent::Alternator,
        b'(' => {
          previous_was_open_group = true;
          group_context.push((ctx_kind, components));
          continue;
        },
        b')' => match ctx_kind {
          ContextKind::TopLevel => {
            return Err(ParseError {
              kind: ParseErrorKind::UnmatchedCloseParen,
              at: i,
            })
          },
          ContextKind::Group(kind) => {
            let inner = coalesce_components(components, alloc.clone());
            let new_group = ContextComponent::Group { kind, expr: inner };
            let (ctx_kind, mut components) = group_context.pop().unwrap();
            components.push(new_group);
            group_context.push((ctx_kind, components));
            continue;
          },
        },
        b'{' => {
          currently_first_repeat_arg = Some(Vec::new_in(alloc.clone()));
          group_context.push((ctx_kind, components));
          continue;
        },
        b'}' => {
          return Err(ParseError {
            kind: ParseErrorKind::UnmatchedCloseRepeat,
            at: i,
          })
        },
        b'1' => ContextComponent::Backref(Backref(BackrefIndex(1))),
        b'2' => ContextComponent::Backref(Backref(BackrefIndex(2))),
        b'3' => ContextComponent::Backref(Backref(BackrefIndex(3))),
        b'4' => ContextComponent::Backref(Backref(BackrefIndex(4))),
        b'5' => ContextComponent::Backref(Backref(BackrefIndex(5))),
        b'6' => ContextComponent::Backref(Backref(BackrefIndex(6))),
        b'7' => ContextComponent::Backref(Backref(BackrefIndex(7))),
        b'8' => ContextComponent::Backref(Backref(BackrefIndex(8))),
        b'9' => ContextComponent::Backref(Backref(BackrefIndex(9))),
        b'=' => ContextComponent::Anchor(Anchor::Point(PointAnchor)),
        b'b' => ContextComponent::Anchor(Anchor::Word(WordAnchor {
          negation: Negation::Standard,
        })),
        b'B' => ContextComponent::Anchor(Anchor::Word(WordAnchor {
          negation: Negation::Negated,
        })),
        b'`' => ContextComponent::Anchor(Anchor::Start(StartAnchor::Backtick)),
        b'<' => ContextComponent::Anchor(Anchor::Start(StartAnchor::Word)),
        b'\'' => ContextComponent::Anchor(Anchor::End(EndAnchor::SingleQuote)),
        b'>' => ContextComponent::Anchor(Anchor::End(EndAnchor::Word)),
        b'w' => ContextComponent::CharSelector(SingleCharSelector::Prop(
          CharPropertiesSelector::Word(WordChar {
            negation: Negation::Standard,
          }),
        )),
        b'W' => ContextComponent::CharSelector(SingleCharSelector::Prop(
          CharPropertiesSelector::Word(WordChar {
            negation: Negation::Negated,
          }),
        )),
        b's' => {
          previous_was_syntax_code = true;
          previous_code_negation = Some(Negation::Standard);
          group_context.push((ctx_kind, components));
          continue;
        },
        b'S' => {
          previous_was_syntax_code = true;
          previous_code_negation = Some(Negation::Negated);
          group_context.push((ctx_kind, components));
          continue;
        },
        b'c' => {
          previous_was_category_code = true;
          previous_code_negation = Some(Negation::Standard);
          group_context.push((ctx_kind, components));
          continue;
        },
        b'C' => {
          previous_was_category_code = true;
          previous_code_negation = Some(Negation::Negated);
          group_context.push((ctx_kind, components));
          continue;
        },
        x => ContextComponent::EscapedLiteral(Escaped(SingleLiteral(*x))),
      };
      components.push(new_component);
      group_context.push((ctx_kind, components));
      continue;
    }

    if previous_was_star {
      previous_was_star = false;
      match byte {
        b'?' => {
          previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
            op: SimpleOperator::Star,
            greediness: GreedyBehavior::NonGreedy,
          }));
          group_context.push((ctx_kind, components));
          continue;
        },
        _ => {
          previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
            op: SimpleOperator::Star,
            greediness: GreedyBehavior::Greedy,
          }));
        },
      }
    }
    if previous_was_plus {
      previous_was_plus = false;
      match byte {
        b'?' => {
          previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
            op: SimpleOperator::Plus,
            greediness: GreedyBehavior::NonGreedy,
          }));
          group_context.push((ctx_kind, components));
          continue;
        },
        _ => {
          previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
            op: SimpleOperator::Plus,
            greediness: GreedyBehavior::Greedy,
          }));
        },
      }
    }
    if previous_was_question {
      previous_was_question = false;
      match byte {
        b'?' => {
          previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
            op: SimpleOperator::Question,
            greediness: GreedyBehavior::NonGreedy,
          }));
          group_context.push((ctx_kind, components));
          continue;
        },
        _ => {
          previously_had_postfix = Some(PostfixOp::Simple(MaybeGreedyOperator {
            op: SimpleOperator::Question,
            greediness: GreedyBehavior::Greedy,
          }));
        },
      }
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

    let new_component = match byte {
      b'\\' => {
        previous_was_backslash = true;
        group_context.push((ctx_kind, components));
        continue;
      },
      b'[' => {
        previous_was_open_square_brace = true;
        group_context.push((ctx_kind, components));
        continue;
      },
      b'*' => {
        previous_was_star = true;
        group_context.push((ctx_kind, components));
        continue;
      },
      b'+' => {
        previous_was_plus = true;
        group_context.push((ctx_kind, components));
        continue;
      },
      b'?' => {
        previous_was_question = true;
        group_context.push((ctx_kind, components));
        continue;
      },
      b'^' => ContextComponent::<A>::Anchor(Anchor::Start(StartAnchor::Carat)),
      b'$' => ContextComponent::Anchor(Anchor::End(EndAnchor::Dollar)),
      b'.' => ContextComponent::CharSelector(SingleCharSelector::Dot),
      x => ContextComponent::SingleLiteral(SingleLiteral(*x)),
    };
    components.push(new_component);
    group_context.push((ctx_kind, components));
  }
  /* END LOOP! */

  let mut top_level_components = match group_context.pop().unwrap() {
    (ContextKind::Group(_), _) => {
      return Err(ParseError {
        kind: ParseErrorKind::UnmatchedOpenParen,
        at: pattern.len(),
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
      at: pattern.len(),
    });
  }
  if let Some(_) = currently_within_group_number {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }

  if previous_was_open_group {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }
  if previous_was_open_square_brace {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }

  if let Some(_) = currently_within_char_alternative {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }

  if previous_was_final_class_colon {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }
  if previous_was_range_hyphen {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }

  if previous_two_were_backslash_underscore {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }

  if previous_was_syntax_code {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }
  if previous_was_category_code {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }

  if previous_was_closing_backslash_of_repeat {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }
  if let Some(_) = currently_second_repeat_arg {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }
  if let Some(_) = currently_first_repeat_arg {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
    });
  }
  if previous_was_backslash {
    return Err(ParseError {
      kind: ParseErrorKind::InvalidEndState,
      at: pattern.len(),
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
          at: pattern.len(),
        })
      },
      Some(c) => match apply_postfix(c, op, alloc.clone()) {
        None => {
          return Err(ParseError {
            kind: ParseErrorKind::PostfixAfterAlternator,
            at: pattern.len(),
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

  use super::*;

  #[test]
  fn parse_single_lit() {
    let parsed = parse_bytes(b"a", Global).unwrap();
    assert_eq!(
      parsed,
      Expr::<ByteEncoding, Global>::SingleLiteral(SingleLiteral(b'a'))
    );

    let parsed = parse_bytes(b"\\a", Global).unwrap();
    assert_eq!(
      parsed,
      Expr::<ByteEncoding, Global>::EscapedLiteral(Escaped(SingleLiteral(b'a')))
    );
  }

  #[test]
  fn parse_plus_postfix() {
    let parsed = parse_bytes(b"asdf\\(.\\)+a", Global).unwrap();
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

    let parsed = parse_bytes(b"asdf+", Global).unwrap();
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

    let parsed = parse_bytes(b"asdf+aa", Global).unwrap();
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
    let _parsed = parse_bytes(b"asdf+a.a\\{2\\}", Global).unwrap();
    ()
  }
}
