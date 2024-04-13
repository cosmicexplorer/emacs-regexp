/* Description: librex C header generated from emacs-regexp-ffi Rust code.

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

#ifndef rex_h
#define rex_h

/* Generated with cbindgen:0.26.0 */

/* This file is autogenerated from Rust code by cbindgen. */

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

enum RegexpError {
  None = 0,
  ParseError = 1,
  CompileError = 2,
  MatchError = 3,
};
typedef uint8_t RegexpError;

typedef struct ForeignSlice {
  size_t len;
  const void *data;
} ForeignSlice;

typedef struct Pattern {
  struct ForeignSlice data;
} Pattern;

typedef struct CallbackAllocator {
  void *ctx;
  void *(*alloc)(void*, size_t);
  void (*free)(void*, void*);
} CallbackAllocator;

typedef struct OwnedSlice {
  size_t len;
  void *data;
  struct CallbackAllocator alloc;
} OwnedSlice;

typedef struct OwnedExpr {
  void *data;
  struct CallbackAllocator alloc;
} OwnedExpr;

typedef struct Matcher {
  struct OwnedSlice data;
  struct OwnedExpr expr;
} Matcher;

typedef struct Input {
  struct ForeignSlice data;
} Input;

void always_panic(void) __attribute__((noreturn));

/**
 * asdf
 */
__attribute__((warn_unused_result))
RegexpError compile(const struct Pattern *pattern,
                    const struct CallbackAllocator *alloc,
                    struct Matcher *out);

__attribute__((warn_unused_result))
RegexpError execute(const struct Matcher *matcher,
                    const struct CallbackAllocator *_alloc,
                    const struct Input *input);

#endif /* rex_h */