/* Calls: direct, recursive, through pointers, tail, many values live across a call, no return. */
__attribute__((noinline)) long inc(long x) { return x + 1; }
long twice_inc(long x) { return inc(inc(x)); }
unsigned long fact(unsigned long n) { return n == 0 ? 1 : n * fact(n - 1); }
__attribute__((noinline)) long apply(long (*f)(long), long x) { return f(x); }
long apply_inc(long x) { return apply(inc, x); }
__attribute__((noinline)) long sum4(long a, long b, long c, long d) { return a + b + c + d; }
long keep(long a, long b, long c, long d) { long s = sum4(a, b, c, d); return s + a * b + c * d; }
long tail_inc(long x) { return inc(x + 1); }
__attribute__((noreturn, noinline)) void stop(void) { for (;;); }
long checked_div(long a, long b) { if (b == 0) stop(); return a / b; }
void _start(void) { for (;;); }
