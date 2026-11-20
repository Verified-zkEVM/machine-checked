/* Recursion that a compiler cannot turn into a loop: two calls of itself. */
unsigned long fib(unsigned long n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); }
void _start(void) { for (;;); }
