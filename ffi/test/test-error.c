#include <assert.h>
#include <stdlib.h>

#include "rex.h"

void *rex_alloc(void *_ctx, size_t n) { return malloc(n); }
void rex_free(void *_ctx, void *p) { free(p); }

int main() {
  REX_ForeignSlice s;
  s.len = 5;
  s.data = "asd\\)";

  REX_Pattern p;
  p.data = s;

  REX_CallbackAllocator c;
  c.ctx = NULL;
  c.alloc = rex_alloc;
  c.free = rex_free;

  REX_Matcher m;
  assert(compile(&p, &c, &m) == ParseError);
}
