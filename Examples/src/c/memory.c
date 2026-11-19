/* Memory, a loop over an array, and a call with a stack frame. */
typedef unsigned long long u64;

void swap(u64 *a, u64 *b) {
  u64 t = *a;
  *a = *b;
  *b = t;
}

u64 sum_array(const u64 *p, u64 n) {
  u64 s = 0;
  for (u64 i = 0; i < n; i++) s += p[i];
  return s;
}

__attribute__((noinline)) u64 max2(u64 a, u64 b) { return a > b ? a : b; }

u64 max3(u64 a, u64 b, u64 c) { return max2(max2(a, b), c); }
