#include <assert.h>
#include <stdlib.h>

#include "rex.h"

void *rex_alloc(void *_ctx, size_t n) { return malloc(n); }
void rex_free(void *_ctx, void *p) { free(p); }

int main() {
  REX_ForeignSlice s;
  s.len = 4;
  s.data = "asdf";

  REX_Pattern p;
  p.data = s;

  REX_CallbackAllocator c;
  c.ctx = NULL;
  c.alloc = rex_alloc;
  c.free = rex_free;

  REX_Matcher m;
  assert(compile(&p, &c, &m) == None);

  REX_Input i;
  i.data = s;

  assert(execute(&m, &c, &i) == None);

  REX_ForeignSlice s2;
  s2.len = 4;
  s2.data = "bsdf";
  REX_Input i2;
  i2.data = s2;

  assert(execute(&m, &c, &i2) == MatchError);
}
