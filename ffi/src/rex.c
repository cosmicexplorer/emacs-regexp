#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

#include "rex.h"

void *rex_alloc(void *_ctx, size_t n) { return malloc(n); }
void rex_free(void *_ctx, void *p) { free(p); }

int main() {
  ForeignSlice s;
  s.len = 4;
  s.data = "asdf";

  Pattern p;
  p.data = s;

  CallbackAllocator c;
  c.ctx = NULL;
  c.alloc = rex_alloc;
  c.free = rex_free;

  printf("%s\n", "1!");

  Matcher m;
  assert(compile(&p, &c, &m) == None);
  printf("%s\n", "2!");

  Input i;
  i.data = s;

  assert(execute(&m, &c, &i) == None);
  printf("%s\n", "3!");

  ForeignSlice s2;
  s2.len = 4;
  s2.data = "bsdf";
  Input i2;
  i2.data = s2;

  assert(execute(&m, &c, &i2) == MatchError);

  printf("%s\n", "wow!");
}
