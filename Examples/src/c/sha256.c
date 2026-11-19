/* SHA-256 (FIPS 180-4): the top rung of the ladder. */

typedef unsigned int u32;
typedef unsigned long u64;

#define ROTR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
#define CH(x, y, z) (((x) & (y)) ^ (~(x) & (z)))
#define MAJ(x, y, z) (((x) & (y)) ^ ((x) & (z)) ^ ((y) & (z)))
#define BSIG0(x) (ROTR(x, 2) ^ ROTR(x, 13) ^ ROTR(x, 22))
#define BSIG1(x) (ROTR(x, 6) ^ ROTR(x, 11) ^ ROTR(x, 25))
#define SSIG0(x) (ROTR(x, 7) ^ ROTR(x, 18) ^ ((x) >> 3))
#define SSIG1(x) (ROTR(x, 17) ^ ROTR(x, 19) ^ ((x) >> 10))

static const u32 K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2};

/* One round: the working variables v[0..7] are a..h; k and w are the round's constant and
   word of the schedule. */
void sha256_round(u32 *v, u32 k, u32 w) {
  u32 a = v[0], b = v[1], c = v[2], d = v[3], e = v[4], f = v[5], g = v[6], h = v[7];
  u32 t1 = h + BSIG1(e) + CH(e, f, g) + k + w;
  u32 t2 = BSIG0(a) + MAJ(a, b, c);
  v[7] = g; v[6] = f; v[5] = e; v[4] = d + t1;
  v[3] = c; v[2] = b; v[1] = a; v[0] = t1 + t2;
}

/* The message schedule: w[0..15] hold the block; fill w[16..63]. */
void sha256_schedule(u32 *w) {
  for (u64 t = 16; t < 64; t++)
    w[t] = SSIG1(w[t - 2]) + w[t - 7] + SSIG0(w[t - 15]) + w[t - 16];
}

/* The compression function: update the hash value h[0..7] with the block m[0..15] (words). */
void sha256_compress(u32 *h, const u32 *m) {
  u32 w[64];
  u32 v[8];
  for (u64 t = 0; t < 16; t++) w[t] = m[t];
  sha256_schedule(w);
  for (u64 i = 0; i < 8; i++) v[i] = h[i];
  for (u64 t = 0; t < 64; t++) sha256_round(v, K[t], w[t]);
  for (u64 i = 0; i < 8; i++) h[i] += v[i];
}
