// Faster/leaner checker: decides L(T^a .^b F^a) <= 0 with move ordering + compact hash.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int n;
static inline int cell(u64 s, int i) { return (s >> (2 * i)) & 3; }
static inline u64 setc(u64 s, int i, int v) { return (s & ~(3ULL << (2 * i))) | ((u64)v << (2 * i)); }
static int nl, nr;
// Generate moves into array; returns count.
static inline int leftMoves(u64 s, u64 *out) {
  int k = 0;
  for (int i = 0; i < n; i++) if (cell(s, i) == 1) {
    if (i + 1 < n && cell(s, i + 1) == 0) out[k++] = setc(setc(s, i, 0), i + 1, 1);
    else if (i + 2 < n && cell(s, i + 1) == 2 && cell(s, i + 2) == 0) out[k++] = setc(setc(s, i, 0), i + 2, 1);
  }
  return k;
}
static inline int rightMoves(u64 s, u64 *out) {
  int k = 0;
  for (int i = n - 1; i >= 0; i--) if (cell(s, i) == 2) {
    if (i - 1 >= 0 && cell(s, i - 1) == 0) out[k++] = setc(setc(s, i, 0), i - 1, 2);
    else if (i - 2 >= 0 && cell(s, i - 1) == 1 && cell(s, i - 2) == 0) out[k++] = setc(setc(s, i, 0), i - 2, 2);
  }
  return k;
}
u64 mirror(u64 s) { u64 t = 0; for (int i = 0; i < n; i++) { int c = cell(s, i); t = setc(t, n - 1 - i, c == 1 ? 2 : c == 2 ? 1 : 0); } return t; }

// compact hash
static u64 *keys; static uint8_t *vals; static u64 cap, mask, used;
static inline u64 hsh(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
static inline uint8_t *slot(u64 s) {
  u64 k = s + 1;  // avoid 0 key
  u64 h = hsh(k) & mask;
  while (true) {
    if (keys[h] == k) return &vals[h];
    if (keys[h] == 0) {
      keys[h] = k; vals[h] = 0; used++;
      if (used * 10 > cap * 9) { fprintf(stderr, "hash full\n"); exit(2); }
      return &vals[h];
    }
    h = (h + 1) & mask;
  }
}
static inline uint8_t peek(u64 s) {
  u64 k = s + 1; u64 h = hsh(k) & mask;
  while (true) { if (keys[h] == k) return vals[h]; if (keys[h] == 0) return 0; h = (h + 1) & mask; }
}
bool LF(u64 s); bool RF(u64 s); bool Np(u64 s); bool Mp(u64 s);
bool LF(u64 s) {
  uint8_t v = peek(s); if (v & 1) return v & 2;
  u64 mv[64]; int k = leftMoves(s, mv); bool r = false;
  for (int j = 0; j < k && !r; j++) if (!RF(mv[j])) r = true;
  *slot(s) |= 1 | (r ? 2 : 0); return r;
}
bool RF(u64 s) {
  uint8_t v = peek(s); if (v & 4) return v & 8;
  u64 mv[64]; int k = rightMoves(s, mv); bool r = false;
  for (int j = 0; j < k && !r; j++) if (!LF(mv[j])) r = true;
  *slot(s) |= 4 | (r ? 8 : 0); return r;
}
bool Mp(u64 s) {
  uint8_t v = peek(s); if (v & 64) return v & 128;
  u64 mv[64]; int k = rightMoves(s, mv); bool r = false;
  // symmetric replies first
  for (int j = 0; j < k && !r; j++) if (mirror(mv[j]) == mv[j] && Np(mv[j])) r = true;
  if (!r && !LF(s)) r = true;
  for (int j = 0; j < k && !r; j++) if (mirror(mv[j]) != mv[j] && Np(mv[j])) r = true;
  *slot(s) |= 64 | (r ? 128 : 0); return r;
}
bool Np(u64 s) {
  uint8_t v = peek(s); if (v & 16) return v & 32;
  bool r;
  if (mirror(s) == s) r = true;  // M'(P) automatic for symmetric P
  else r = Mp(s);
  if (r) { u64 mv[64]; int k = leftMoves(s, mv); for (int j = 0; j < k && r; j++) if (!Mp(mv[j])) r = false; }
  *slot(s) |= 16 | (r ? 32 : 0); return r;
}
u64 encode(const string &str) { u64 s = 0; for (int i = 0; i < (int)str.size(); i++) s = setc(s, i, str[i] == 'T' ? 1 : str[i] == 'F' ? 2 : 0); return s; }
int main(int argc, char **argv) {
  int a = atoi(argv[1]), b = atoi(argv[2]); int lg = argc > 3 ? atoi(argv[3]) : 28;
  cap = 1ULL << lg; mask = cap - 1;
  keys = (u64 *)calloc(cap, sizeof(u64)); vals = (uint8_t *)calloc(cap, 1);
  n = 2 * a + b;
  u64 s = encode(string(a, 'T') + string(b, '.') + string(a, 'F'));
  auto t0 = chrono::steady_clock::now();
  bool ok = Np(s);
  double dt = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
  printf("a=%d b=%d  L<=0:%d  states=%llu  %.1fs\n", a, b, (int)ok, (unsigned long long)used, dt);
}
