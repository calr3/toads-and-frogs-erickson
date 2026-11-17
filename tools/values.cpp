// Exact values 0 and * of the starting positions T^a .^b F^a.
//
// T^a .^b F^a is its own mirror image (reverse the board, swap toads and frogs), so its value G
// satisfies G = -G. Hence G <= 0 implies G = 0, and G + * <= 0 implies G = * (as * = -*).
// The program decides both by exhaustive search with memoisation:
//   le0(s)  : s <= 0      every Left move q has a Right reply r with le0(r);
//   le0s(s) : s + * <= 0  Left's move in * (leaving s) has a Right reply r with le0(r), and every
//                         Left move q in s has a reply: Right's move in * (le0(q)) or a Right move
//                         r in q with le0s(r).
// A position that is neither 0 nor * is reported as "other" (for the starts: +-1/8 at (3, 2), and
// longer infinitesimals; infinitesimality itself is decided by tools/stops.cpp).
//
// Boards of at most 32 cells: a position is a pair of 32-bit masks (toads, frogs).
// Usage: values A B [A B ...]   prints "a b value states seconds" per pair.
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
typedef unsigned int u32;
int n;
static inline u64 key(u32 t, u32 f) { return ((u64)t << 32) | f; }
// open-addressing table: key -> flags (bit 0/1: le0 known/value, bit 2/3: le0s known/value)
struct Memo {
  vector<u64> k; vector<unsigned char> v; size_t cnt = 0, mask;
  Memo() { k.assign(1 << 20, ~0ULL); v.assign(1 << 20, 0); mask = (1 << 20) - 1; }
  static size_t h(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
  unsigned char get(u64 x) const { size_t i = h(x) & mask; while (k[i] != ~0ULL) { if (k[i] == x) return v[i]; i = (i + 1) & mask; } return 0; }
  void put(u64 x, unsigned char bits) {
    if (2 * (cnt + 1) > k.size()) grow();
    size_t i = h(x) & mask; while (k[i] != ~0ULL && k[i] != x) i = (i + 1) & mask;
    if (k[i] == ~0ULL) { k[i] = x; cnt++; }
    v[i] |= bits;
  }
  void grow() {
    vector<u64> ok; vector<unsigned char> ov; ok.swap(k); ov.swap(v);
    k.assign(ok.size() * 2, ~0ULL); v.assign(ok.size() * 2, 0); mask = k.size() - 1; cnt = 0;
    for (size_t i = 0; i < ok.size(); i++) if (ok[i] != ~0ULL) { size_t j = h(ok[i]) & mask; while (k[j] != ~0ULL) j = (j + 1) & mask; k[j] = ok[i]; v[j] = ov[i]; cnt++; }
  }
  void clear() { k.assign(1 << 20, ~0ULL); v.assign(1 << 20, 0); mask = (1 << 20) - 1; cnt = 0; }
} memo;
// Left moves: a toad slides right into an empty cell, or jumps a single frog into an empty cell.
int lmoves(u32 t, u32 f, u64 *out) {
  u32 occ = t | f, full = (n == 32) ? ~0u : ((1u << n) - 1); int k = 0;
  for (u32 x = t; x; x &= x - 1) {
    int i = __builtin_ctz(x);
    if (i + 1 < n && !(occ >> (i + 1) & 1)) out[k++] = key(t ^ (1u << i) ^ (1u << (i + 1)), f);
    else if (i + 2 < n && (f >> (i + 1) & 1) && !(occ >> (i + 2) & 1)) out[k++] = key(t ^ (1u << i) ^ (1u << (i + 2)), f);
  }
  (void)full; return k;
}
// Right moves: a frog slides left, or jumps a single toad.
int rmoves(u32 t, u32 f, u64 *out) {
  u32 occ = t | f; int k = 0;
  for (u32 x = f; x; x &= x - 1) {
    int i = __builtin_ctz(x);
    if (i >= 1 && !(occ >> (i - 1) & 1)) out[k++] = key(t, f ^ (1u << i) ^ (1u << (i - 1)));
    else if (i >= 2 && (t >> (i - 1) & 1) && !(occ >> (i - 2) & 1)) out[k++] = key(t, f ^ (1u << i) ^ (1u << (i - 2)));
  }
  return k;
}
bool le0(u64 s) {
  unsigned char m = memo.get(s); if (m & 1) return m & 2;
  u64 qs[32], rs[32]; bool r = true;
  int nq = lmoves(s >> 32, (u32)s, qs);
  for (int a = 0; a < nq && r; a++) {
    bool ok = false; int nr = rmoves(qs[a] >> 32, (u32)qs[a], rs);
    for (int b = 0; b < nr; b++) if (le0(rs[b])) { ok = true; break; }
    if (!ok) r = false;
  }
  memo.put(s, 1 | (r ? 2 : 0)); return r;
}
bool le0s(u64 s) {
  unsigned char m = memo.get(s); if (m & 4) return m & 8;
  u64 qs[32], rs[32]; bool r = false;
  int nr = rmoves(s >> 32, (u32)s, rs);           // Left takes the *: Right must move in s to a position <= 0
  for (int b = 0; b < nr; b++) if (le0(rs[b])) { r = true; break; }
  if (r) {
    int nq = lmoves(s >> 32, (u32)s, qs);
    for (int a = 0; a < nq && r; a++) {
      if (le0(qs[a])) continue;                     // Right takes the *
      bool ok = false; int nr2 = rmoves(qs[a] >> 32, (u32)qs[a], rs);
      for (int b = 0; b < nr2; b++) if (le0s(rs[b])) { ok = true; break; }
      if (!ok) r = false;
    }
  }
  memo.put(s, 4 | (r ? 8 : 0)); return r;
}
int main(int argc, char **argv) {
  for (int i = 1; i + 1 < argc; i += 2) {
    int a = atoi(argv[i]), b = atoi(argv[i + 1]); n = 2 * a + b;
    if (n > 32) { printf("%d %d skipped (more than 32 cells)\n", a, b); continue; }
    memo.clear(); clock_t c0 = clock();
    u32 t = (a ? (1u << a) - 1 : 0), f = 0;
    for (int j = a + b; j < n; j++) f |= 1u << j;
    u64 s = key(t, f);
    const char *v = le0(s) ? "0" : le0s(s) ? "*" : "other";
    printf("%d %d %s %zu %.1f\n", a, b, v, memo.cnt, (double)(clock() - c0) / CLOCKS_PER_SEC);
    fflush(stdout);
  }
}
