/* A switch dense enough for a jump table. */
long classify(unsigned long k) {
  switch (k) { case 0: return 10; case 1: return 21; case 2: return 32; case 3: return 43;
               case 4: return 54; case 5: return 65; case 6: return 76; case 7: return 87; default: return -1; }
}
void _start(void) { for (;;); }
