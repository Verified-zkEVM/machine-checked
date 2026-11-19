/* Multi-limb addition: the second rung of the ladder. */

typedef unsigned long u64;

/* r = a + b, on numbers of n 64-bit limbs, least significant first. Returns the carry out. */
u64 add_limbs(u64 *r, const u64 *a, const u64 *b, u64 n) {
  u64 carry = 0;
  for (u64 i = 0; i < n; i++) {
    u64 s = a[i] + carry;
    u64 c1 = s < carry;
    u64 t = s + b[i];
    u64 c2 = t < s;
    r[i] = t;
    carry = c1 | c2;
  }
  return carry;
}
