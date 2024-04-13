#include <assert.h>
#include <stdlib.h>

#include "rex.h"

void *rex_alloc(void *_ctx, size_t n) { return malloc(n); }
void rex_free(void *_ctx, void *p) { free(p); }

int main() {
  ForeignSlice s;
  s.len = 5;
  s.data = "asd\\)";

  Pattern p;
  p.data = s;

  CallbackAllocator c;
  c.ctx = NULL;
  c.alloc = rex_alloc;
  c.free = rex_free;

  Matcher m;
  assert(compile(&p, &c, &m) == ParseError);
}
