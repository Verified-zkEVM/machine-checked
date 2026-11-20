/* memcmp, as a byte loop: clang compiles it to the twelve instructions rustc's
   compiler_builtins has for it in an SP1 guest, with two of the increments in another order. */

typedef unsigned long size_t;

int memcmp(const void *a, const void *b, size_t n) {
  const unsigned char *p = a, *q = b;
  while (n) {
    unsigned char x = *p, y = *q;
    if (x != y) return (int)x - (int)y;
    p++; q++; n--;
  }
  return 0;
}

void _start(void) { for (;;) {} }
