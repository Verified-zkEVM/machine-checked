/* Copying and comparing bytes: the first rung of the ladder. */

typedef unsigned long u64;
typedef unsigned char u8;

/* Copy n bytes from src to dst. The regions do not overlap. */
void copy_bytes(u8 *dst, const u8 *src, u64 n) {
  for (u64 i = 0; i < n; i++) dst[i] = src[i];
}

/* 1 if the n bytes at a and at b are the same, and 0 otherwise. */
u64 equal_bytes(const u8 *a, const u8 *b, u64 n) {
  for (u64 i = 0; i < n; i++)
    if (a[i] != b[i]) return 0;
  return 1;
}
