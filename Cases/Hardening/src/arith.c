/* Division and remainder at their edges, the high half of products, 32-bit words, shifts. */
long sdiv(long a, long b) { return b == 0 ? 0 : a / b; }
long srem(long a, long b) { return b == 0 ? a : a % b; }
unsigned long udiv(unsigned long a, unsigned long b) { return b == 0 ? 0 : a / b; }
unsigned long mulhi(unsigned long a, unsigned long b) { return (unsigned long)(((unsigned __int128)a * b) >> 64); }
long smulhi(long a, long b) { return (long)(((__int128)a * b) >> 64); }
int add32(int a, int b) { return a + b; }
unsigned shl32(unsigned a, unsigned s) { return a << (s & 31); }
int sra32(int a, unsigned s) { return a >> (s & 31); }
unsigned long rotl(unsigned long x, unsigned s) { s &= 63; return (x << s) | (x >> ((64 - s) & 63)); }
unsigned long popcount(unsigned long x) { unsigned long c = 0; while (x) { x &= x - 1; c++; } return c; }
long abs_branchless(long x) { long m = x >> 63; return (x ^ m) - m; }
int div32(int a, int b) { return b == 0 ? 0 : a / b; }
void _start(void) { for (;;); }
