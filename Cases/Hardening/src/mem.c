/* Every load and store width, signed and not; byte loops; unaligned reads. */
void set_bytes(unsigned char *p, unsigned char v, unsigned long n) { for (unsigned long i = 0; i < n; i++) p[i] = v; }
void copy_bytes(unsigned char *d, const unsigned char *s, unsigned long n) { for (unsigned long i = 0; i < n; i++) d[i] = s[i]; }
unsigned long str_len(const char *s) { unsigned long n = 0; while (s[n]) n++; return n; }
long load_s8(const signed char *p) { return *p; }
unsigned long load_u8(const unsigned char *p) { return *p; }
long load_s16(const short *p) { return *p; }
unsigned long load_u16(const unsigned short *p) { return *p; }
long load_s32(const int *p) { return *p; }
unsigned long load_u32(const unsigned *p) { return *p; }
void store_widths(unsigned char *p, unsigned long v) { p[0] = v; *(unsigned short *)(p + 2) = v; *(unsigned *)(p + 4) = v; *(unsigned long *)(p + 8) = v; }
unsigned read_le32(const unsigned char *p) { return p[0] | p[1] << 8 | p[2] << 16 | (unsigned)p[3] << 24; }
void swap(long *a, long *b) { long t = *a; *a = *b; *b = t; }
void _start(void) { for (;;); }
