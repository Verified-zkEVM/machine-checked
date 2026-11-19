/* The first examples: straight-line code, a branch and a loop. */
typedef unsigned long long u64;

u64 add3(u64 a, u64 b, u64 c) { return a + b + c; }

u64 max_u64(u64 a, u64 b) { return a > b ? a : b; }

u64 sum_to(u64 n) {
  u64 s = 0;
  while (n != 0) {
    s += n;
    n -= 1;
  }
  return s;
}
