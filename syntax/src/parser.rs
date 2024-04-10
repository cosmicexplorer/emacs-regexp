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

use core::alloc::Allocator;

use crate::{
  ast::{
    expr::{Expr, SingleCharSelector},
    groups::GroupKind,
    literals::string::StringLiteral,
    postfix_operators::PostfixOp,
  },
  encoding::{ByteEncoding, LiteralEncoding},
};


pub fn parse<'n, L, A>(pattern: L::String<'n>) -> Expr<'n, L, A>
where
  L: LiteralEncoding,
  A: Allocator,
{
  todo!()
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ContextKind {
  TopLevel,
  Group(GroupKind),
}

enum ContextComponent<'n, A>
where A: Allocator
{
  Literal(StringLiteral<&'n [u8]>),
  CharSelector(SingleCharSelector<u8, A>),
  Postfix {
    expr: Box<Expr<'n, ByteEncoding, A>, A>,
    op: PostfixOp,
  },
  Group {
    expr: Box<Expr<'n, ByteEncoding, A>, A>,
    kind: GroupKind,
  },
  Alternator,
}

pub fn parse_bytes<'n, A>(pattern: &'n [u8], alloc: A) -> Expr<'n, ByteEncoding, A>
where A: Allocator+Clone {
  let mut group_context: Vec<(ContextKind, ContextComponent<'n, A>), A> =
    Vec::new_in(alloc.clone());
  todo!()
}
