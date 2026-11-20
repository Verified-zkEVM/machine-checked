/* Long straight-line code: 32 unrolled rounds of mixing. */
unsigned long mix(unsigned long x, unsigned long y) {
#define R(k) x ^= y + 0x9e3779b97f4a7c15UL * (k); x = (x << 7) | (x >> 57); y += x ^ (k);
  R(1) R(2) R(3) R(4) R(5) R(6) R(7) R(8) R(9) R(10) R(11) R(12) R(13) R(14) R(15) R(16)
  R(17) R(18) R(19) R(20) R(21) R(22) R(23) R(24) R(25) R(26) R(27) R(28) R(29) R(30) R(31) R(32)
  return x ^ y;
}
void _start(void) { for (;;); }
