#define TLX_I32(v) ((v) >= -2147483648LL && (v) <= 2147483647LL)
static inline int tlx_add(int64_t a, int64_t b, int64_t *r) { *r = a + b; return TLX_I32(*r); }
static inline int tlx_sub(int64_t a, int64_t b, int64_t *r) { *r = a - b; return TLX_I32(*r); }
static inline int tlx_mul(int64_t a, int64_t b, int64_t *r) { *r = a * b; return TLX_I32(*r); }
static inline int tlx_divf(int64_t a, int64_t b, int64_t *r) {
  if (b == 0) return 0;
  int64_t q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; *r = q; return TLX_I32(q);
}
static inline int tlx_divn(int64_t a, int64_t b, int64_t *r) {
  if (b == 0) return 0;
  int64_t q = a / b; if (q < 0 && q * b != a) q--; *r = q; return 1;
}
static inline int tlx_pow(int64_t a, int64_t b, int64_t *r) {
  if (b < 0 || (a == 0 && b == 0)) return 0;
  if (b == 0) { *r = 1; return 1; }
  if (a == 0 || a == 1) { *r = a; return 1; }
  if (a == -1) { *r = (b % 2 == 0) ? 1 : -1; return 1; }
  int64_t x = 1; /* |a| >= 2: overflows within 32 steps */
  for (int64_t i = 0; i < b; i++) { x *= a; if (x < INT32_MIN || x > INT32_MAX) return 0; }
  *r = x; return 1;
}
static inline int tlx_gcd(int64_t a, int64_t b, int64_t *r) {
  uint64_t x = a < 0 ? -(uint64_t)a : (uint64_t)a, y = b < 0 ? -(uint64_t)b : (uint64_t)b;
  while (y != 0) { uint64_t t = x % y; x = y; y = t; }
  if (x > INT32_MAX) return 0;
  *r = (int64_t)x; return 1;
}
static inline int tlx_mod(int64_t a, int64_t b, int64_t *r) {
  if (b <= 0) return 0;
  int64_t m = a % b; if (m < 0) m += b; *r = m; return 1;
}
static inline int64_t tlx_bit(const uint64_t *s, int64_t n, int64_t r) {
  return r >= 0 && r < n * 64 && ((s[r >> 6] >> (r & 63)) & 1);
}
static inline uint64_t tlx_bget(const uint64_t *p, uint32_t word, uint32_t shift, uint32_t bits) {
  return (p[word] >> shift) & ((1ULL << bits) - 1ULL);
}
static inline void tlx_bset(uint64_t *p, uint32_t word, uint32_t shift, uint32_t bits, uint64_t val) {
  uint64_t m = (1ULL << bits) - 1ULL;
  p[word] = (p[word] & ~(m << shift)) | ((val & m) << shift);
}
static inline uint64_t tlx_sget(const uint64_t *p, uint32_t bits, uint64_t idx) {
  uint32_t per = 64u / bits;
  uint64_t w = idx / per;
  uint32_t sh = 64u - ((uint32_t)(idx % per) + 1u) * bits;
  return (p[w] >> sh) & ((1ULL << bits) - 1ULL);
}
static inline void tlx_sset(uint64_t *p, uint32_t bits, uint64_t idx, uint64_t val) {
  uint32_t per = 64u / bits;
  uint64_t w = idx / per;
  uint32_t sh = 64u - ((uint32_t)(idx % per) + 1u) * bits;
  uint64_t m = (1ULL << bits) - 1ULL;
  p[w] = (p[w] & ~(m << sh)) | ((val & m) << sh);
}
static inline int tlx_cmpw(const uint64_t *a, const uint64_t *b, uint32_t n) {
  for (uint32_t i = 0; i < n; i++) { if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1; }
  return 0;
}
static inline int64_t tlx_sorted_member(const uint64_t *s, const uint64_t *x, uint32_t n) {
  int64_t lo = 0, hi = (int64_t)s[0] - 1;
  while (lo <= hi) { int64_t mid = (lo + hi) >> 1; int c = tlx_cmpw(s + 1 + mid * n, x, n);
    if (c == 0) return 1; if (c < 0) lo = mid + 1; else hi = mid - 1; }
  return 0;
}
static inline int tlx_sorted_insert(uint64_t *out, uint32_t words, const uint64_t *s, const uint64_t *x, uint32_t n, uint64_t max_card) {
  uint64_t len = s[0]; uint64_t pos = 0;
  while (pos < len) { int c = tlx_cmpw(s + 1 + pos * n, x, n); if (c == 0) { memcpy(out, s, words * 8); return 1; } if (c > 0) break; pos++; }
  if (len + 1 > max_card) return 0;
  memset(out, 0, words * 8); out[0] = len + 1;
  memcpy(out + 1, s + 1, pos * n * 8); memcpy(out + 1 + pos * n, x, n * 8);
  memcpy(out + 1 + (pos + 1) * n, s + 1 + pos * n, (len - pos) * n * 8);
  return 1;
}
/* Insert x (n words) into the sorted-array set s in place. */
static inline int tlx_sorted_add(uint64_t *s, const uint64_t *x, uint32_t n, uint64_t max_card) {
  uint64_t len = s[0]; uint64_t pos = 0;
  while (pos < len) { int c = tlx_cmpw(s + 1 + pos * n, x, n); if (c == 0) return 1; if (c > 0) break; pos++; }
  if (len + 1 > max_card) return 0;
  memmove(s + 1 + (pos + 1) * n, s + 1 + pos * n, (len - pos) * n * 8);
  memcpy(s + 1 + pos * n, x, n * 8); s[0] = len + 1;
  return 1;
}
/* Union (op 0), intersection (1) or difference (2) of sorted-array sets a
   and b into out (0 if more than max_card elements). */
static inline int tlx_sorted_op(int op, uint64_t *out, uint32_t words, const uint64_t *a, const uint64_t *b, uint32_t n, uint64_t max_card) {
  uint64_t la = a[0], lb = b[0], i = 0, j = 0, len = 0;
  memset(out, 0, words * 8);
  while (i < la || j < lb) {
    const uint64_t *x; int fa = 0, fb = 0;
    if (i < la && j < lb) {
      int c = tlx_cmpw(a + 1 + i * n, b + 1 + j * n, n);
      if (c == 0) { x = a + 1 + i * n; fa = fb = 1; }
      else if (c < 0) { x = a + 1 + i * n; fa = 1; }
      else { x = b + 1 + j * n; fb = 1; }
    } else if (i < la) { x = a + 1 + i * n; fa = 1; }
    else { x = b + 1 + j * n; fb = 1; }
    int keep = op == 0 || (op == 1 && fa && fb) || (op == 2 && fa && !fb);
    if (keep) {
      if (len == max_card) return 0;
      memcpy(out + 1 + len * n, x, n * 8); len++;
    }
    i += fa; j += fb;
  }
  out[0] = len;
  return 1;
}
static inline int64_t tlx_card(const uint64_t *s, int64_t n) {
  int64_t c = 0; for (int64_t i = 0; i < n; i++) c += __builtin_popcountll(s[i]); return c;
}

/* Prefix ordering ABI: declarations checked against encoded_order::schema by
   tests/encoded_order.rs. The JIT calls Rust; C retains its inline loops. */
enum {
  TLXC_ORDER_WORDS = 0, TLXC_ORDER_SET = 1, TLXC_ORDER_PRODUCT = 2, TLXC_ORDER_UNION = 3,
  TLXC_ORDER_OPCODE = 0, TLXC_ORDER_WIDTH = 1, TLXC_ORDER_SPAN = 2,
  TLXC_ORDER_CHILDREN = 3, TLXC_ORDER_HEADER = 4
};
static int tlx_order_compare(const uint64_t *p, const uint64_t *a, const uint64_t *b) {
  if (p[TLXC_ORDER_OPCODE] == TLXC_ORDER_WORDS) {
    for (uint64_t i = 0; i < p[TLXC_ORDER_WIDTH]; i++) if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
    return 0;
  }
  if (p[TLXC_ORDER_OPCODE] == TLXC_ORDER_SET) {
    int ca = __builtin_popcountll(a[0]), cb = __builtin_popcountll(b[0]);
    if (ca != cb) return ca < cb ? -1 : 1;
    if (a[0] == b[0]) return 0;
    return (a[0] & (1ULL << __builtin_ctzll(a[0] ^ b[0]))) ? -1 : 1;
  }
  if (p[TLXC_ORDER_OPCODE] == TLXC_ORDER_PRODUCT) {
    const uint64_t *c = p + TLXC_ORDER_HEADER;
    for (uint64_t i = 0, off = 0; i < p[TLXC_ORDER_CHILDREN]; i++) {
      int cmp = tlx_order_compare(c, a + off, b + off);
      if (cmp) return cmp;
      off += c[TLXC_ORDER_WIDTH]; c += c[TLXC_ORDER_SPAN];
    }
    return 0;
  }
  if (a[0] != b[0]) return a[0] < b[0] ? -1 : 1;
  const uint64_t *c = p + TLXC_ORDER_HEADER;
  for (uint64_t i = 0; i < a[0]; i++) c += c[TLXC_ORDER_SPAN];
  return tlx_order_compare(c, a + 1, b + 1);
}
static void tlx_order_indices(const uint64_t *p, const uint64_t *s, uint64_t *out) {
  uint64_t k = p[TLXC_ORDER_WIDTH];
  for (uint64_t i = 0; i < s[0]; i++) {
    uint64_t j = i;
    while (j && tlx_order_compare(p, s + 1 + i * k, s + 1 + out[j-1] * k) < 0) {
      out[j] = out[j-1]; j--;
    }
    out[j] = i;
  }
}

static uint64_t tlx_order_bit_indices(const uint64_t *keys, const uint64_t *s, uint64_t nw, uint64_t *out) {
  uint64_t n = 0;
  for (uint64_t i = 0; i < nw; i++) {
    uint64_t b = s[i];
    while (b) {
      uint64_t r = i * 64 + __builtin_ctzll(b), j = n;
      b &= b - 1;
      while (j && keys[r] < keys[out[j-1]]) { out[j] = out[j-1]; j--; }
      out[j] = r; n++;
    }
  }
  return n;
}
