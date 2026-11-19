/* Bytes: a string, a fill, and a loop over the bits of a word. */
typedef unsigned long long u64;
typedef unsigned char u8;

u64 str_len(const u8 *s) {
  u64 n = 0;
  while (s[n] != 0) n++;
  return n;
}

void fill(u8 *p, u64 n, u8 v) {
  for (u64 i = 0; i < n; i++) p[i] = v;
}

u64 count_ones(u64 x) {
  u64 c = 0;
  while (x != 0) {
    c += x & 1;
    x >>= 1;
  }
  return c;
}
