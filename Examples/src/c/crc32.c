/* CRC-32 with a lookup table in read-only data: the third rung of the ladder.
   The table is that of the reflected polynomial 0xEDB88320, for four
   bits at a time, so that it is short enough to read. */

typedef unsigned int u32;
typedef unsigned long u64;
typedef unsigned char u8;

static const u32 TABLE[16] = {
    0x00000000, 0x1db71064, 0x3b6e20c8, 0x26d930ac, 0x76dc4190, 0x6b6b51f4, 0x4db26158, 0x5005713c,
    0xedb88320, 0xf00f9344, 0xd6d6a3e8, 0xcb61b38c, 0x9b64c2b0, 0x86d3d2d4, 0xa00ae278, 0xbdbdf21c};

/* The CRC-32 of n bytes, continuing from crc (which starts as 0). */
u32 crc32(u32 crc, const u8 *p, u64 n) {
  crc = ~crc;
  for (u64 i = 0; i < n; i++) {
    crc ^= p[i];
    crc = (crc >> 4) ^ TABLE[crc & 15];
    crc = (crc >> 4) ^ TABLE[crc & 15];
  }
  return ~crc;
}
