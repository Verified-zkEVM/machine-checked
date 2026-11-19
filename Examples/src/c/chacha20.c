/* ChaCha20 (RFC 8439): the fourth rung of the ladder. */

typedef unsigned int u32;

#define ROTL(x, n) (((x) << (n)) | ((x) >> (32 - (n))))
#define QR(a, b, c, d)                                                         \
  a += b; d ^= a; d = ROTL(d, 16);                                             \
  c += d; b ^= c; b = ROTL(b, 12);                                             \
  a += b; d ^= a; d = ROTL(d, 8);                                              \
  c += d; b ^= c; b = ROTL(b, 7)

/* The quarter round on the words at s[0], s[1], s[2], s[3]. */
void quarter_round(u32 *s) {
  u32 a = s[0], b = s[1], c = s[2], d = s[3];
  QR(a, b, c, d);
  s[0] = a; s[1] = b; s[2] = c; s[3] = d;
}

/* The block function: out = the state after twenty rounds, plus the state. */
void chacha20_block(u32 *out, const u32 *in) {
  u32 x[16];
  for (int i = 0; i < 16; i++) x[i] = in[i];
  for (int i = 0; i < 10; i++) {
    QR(x[0], x[4], x[8], x[12]);
    QR(x[1], x[5], x[9], x[13]);
    QR(x[2], x[6], x[10], x[14]);
    QR(x[3], x[7], x[11], x[15]);
    QR(x[0], x[5], x[10], x[15]);
    QR(x[1], x[6], x[11], x[12]);
    QR(x[2], x[7], x[8], x[13]);
    QR(x[3], x[4], x[9], x[14]);
  }
  for (int i = 0; i < 16; i++) out[i] = x[i] + in[i];
}
