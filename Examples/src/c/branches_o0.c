/* Branches, a loop, straight-line arithmetic. */
long add3(long a, long b, long c) { return a + b + c; }
long max2(long a, long b) { return a > b ? a : b; }
unsigned long umax2(unsigned long a, unsigned long b) { return a > b ? a : b; }
long clamp(long x, long lo, long hi) { return x < lo ? lo : (x > hi ? hi : x); }
long sum(const long *p, unsigned long n) { long s = 0; for (unsigned long i = 0; i < n; i++) s += p[i]; return s; }
unsigned long count_down(unsigned long n) { unsigned long k = 0; while (n) { n >>= 1; k++; } return k; }
void _start(void) { for (;;); }
