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
// longer infinitesimals; infinitesimality itself is decided by STOPS=1 below, or tools/stops.cpp).
//
// Boards of at most 32 cells: a position is a pair of 32-bit masks (toads, frogs). The memo is a
// table indexed by the rank of the position among all arrangements of a toads, a frogs and b empty
// squares (4 bits per arrangement) when that fits in MEM bytes (environment, default 12e9), and a
// hash table (about 18 bytes per visited position) otherwise.
// Usage: values A B [A B ...]   prints "a b value states seconds" per pair (states: positions
// visited with the hash table, arrangements with the indexed table).
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
// Indexed memo: the rank of a position among all arrangements with its counts (E < T < F).
u64 MN[17][17][33];   // multinomial (t + f + e)! / (t! f! e!)
bool useIdx = false, STOPS = false; vector<unsigned char> nib; u64 idxCount = 0;
u64 rankOf(u64 s) {
  u32 t = s >> 32, f = (u32)s; int rt = __builtin_popcount(t), rf = __builtin_popcount(f), re = n - rt - rf; u64 r = 0;
  for (int i = 0; i < n; i++) {
    int c = (t >> i & 1) ? 1 : (f >> i & 1) ? 2 : 0;
    if (c >= 1 && re > 0) r += MN[rt][rf][re - 1];
    if (c == 2 && rt > 0) r += MN[rt - 1][rf][re];
    if (c == 0) re--; else if (c == 1) rt--; else rf--;
  }
  return r;
}
// value mode: 4 bits per arrangement; STOPS mode: 8 bits (also Lf and Up)
static inline unsigned char mget(u64 s) {
  if (!useIdx) return memo.get(s);
  u64 r = rankOf(s); if (STOPS) return nib[r];
  return (nib[r >> 1] >> (4 * (r & 1))) & 15;
}
static inline void mput(u64 s, unsigned char bits) {
  if (!useIdx) { memo.put(s, bits); return; }
  u64 r = rankOf(s); if (STOPS) { nib[r] |= bits; return; }
  nib[r >> 1] |= bits << (4 * (r & 1));
}
bool le0(u64 s) {
  unsigned char m = mget(s); if (m & 1) return m & 2;
  u64 qs[32], rs[32]; bool r = true;
  int nq = lmoves(s >> 32, (u32)s, qs);
  for (int a = 0; a < nq && r; a++) {
    bool ok = false; int nr = rmoves(qs[a] >> 32, (u32)qs[a], rs);
    for (int b = 0; b < nr; b++) if (le0(rs[b])) { ok = true; break; }
    if (!ok) r = false;
  }
  mput(s, 1 | (r ? 2 : 0)); return r;
}
bool le0s(u64 s) {
  unsigned char m = mget(s); if (m & 4) return m & 8;
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
  mput(s, 4 | (r ? 8 : 0)); return r;
}
// STOPS=1: is the start infinitesimal? For a position equal to its own negative this is "Left stop
// <= 0" (Up): Right, holding a pass, answers Left's pass and every Left move by passing (the position
// is <= 0) or by a move to a position with Left stop <= 0 (the recursion of Cgt/Infinitesimal.lean).
bool Up(u64 s);
bool Lf(u64 s) {   // Right to move, may pass instead
  unsigned char m = mget(s); if (m & 16) return m & 32;
  bool r = le0(s); u64 ts[32];
  if (!r) { int nt = rmoves(s >> 32, (u32)s, ts); for (int b = 0; b < nt; b++) if (Up(ts[b])) { r = true; break; } }
  mput(s, 16 | (r ? 32 : 0)); return r;
}
bool Up(u64 s) {
  unsigned char m = mget(s); if (m & 64) return m & 128;
  bool r = Lf(s); u64 qs[32];
  if (r) { int nq = lmoves(s >> 32, (u32)s, qs); for (int a = 0; a < nq; a++) if (!Lf(qs[a])) { r = false; break; } }
  mput(s, 64 | (r ? 128 : 0)); return r;
}
// NIM=k: is the start equal to the nimber *k? For G = -G, G + *k <= 0 means G = *k. leN(s, m)
// decides s + *m <= 0: every Left option (a move in s, or *m -> *j) has a Right reply <= 0.
// Memo: 2 bits per (position, m), m = 0..NIMK, in a byte per arrangement (NIMK <= 3).
int NIMK = 0;
bool leN(u64 s, int m) {
  unsigned char f = mget(s); if (f >> (2 * m) & 1) return f >> (2 * m + 1) & 1;
  u64 qs[32], ts[32]; bool r = true;
  auto rightAnswers = [&](u64 x, int mm) {   // some Right option of x + *mm is <= 0
    int nt = rmoves(x >> 32, (u32)x, ts); for (int b = 0; b < nt; b++) if (leN(ts[b], mm)) return true;
    for (int i = 0; i < mm; i++) if (leN(x, i)) return true;
    return false; };
  int nq = lmoves(s >> 32, (u32)s, qs);
  for (int a = 0; a < nq && r; a++) if (!rightAnswers(qs[a], m)) r = false;
  for (int j = 0; j < m && r; j++) if (!rightAnswers(s, j)) r = false;
  mput(s, (1 | (r ? 2 : 0)) << (2 * m)); return r;
}
int main(int argc, char **argv) {
  STOPS = getenv("STOPS") != nullptr || getenv("NIM") != nullptr;   // a byte per arrangement
  NIMK = getenv("NIM") ? atoi(getenv("NIM")) : 0;
  double MEM = getenv("MEM") ? atof(getenv("MEM")) : 12e9;
  for (int t = 0; t <= 16; t++) for (int f = 0; f <= 16; f++) for (int e = 0; e <= 32; e++) {
    if (t + f + e > 32) continue;   // only boards of at most 32 cells are used
    u64 c1 = 1; for (int k = 1; k <= t; k++) c1 = c1 * (e + k) / k;           // C(e + t, t)
    u64 c2 = 1; for (int k = 1; k <= f; k++) c2 = c2 * (e + t + k) / k;       // C(e + t + f, f)
    MN[t][f][e] = c1 * c2;
  }
  for (int i = 1; i + 1 < argc; i += 2) {
    int a = atoi(argv[i]), b = atoi(argv[i + 1]); n = 2 * a + b;
    if (n > 32) { printf("%d %d skipped (more than 32 cells)\n", a, b); continue; }
    idxCount = MN[a][a][b]; u64 bytes = STOPS ? idxCount : idxCount / 2 + 1; useIdx = bytes <= MEM;
    memo.clear(); vector<unsigned char>().swap(nib); if (useIdx) nib.assign(bytes, 0);
    clock_t c0 = clock();
    u32 t = (a ? (1u << a) - 1 : 0), f = 0;
    for (int j = a + b; j < n; j++) f |= 1u << j;
    u64 s = key(t, f);
    string nimv; if (NIMK) { nimv = "not *0..*" + to_string(NIMK); for (int k = 0; k <= NIMK; k++) if (leN(s, k)) { nimv = "*" + to_string(k); break; } }
    const char *v = NIMK ? nimv.c_str() : STOPS ? (Up(s) ? "infinitesimal" : "NOT-infinitesimal") : le0(s) ? "0" : le0s(s) ? "*" : "other";
    printf("%d %d %s %llu %.1f%s\n", a, b, v, useIdx ? (unsigned long long)idxCount : (unsigned long long)memo.cnt,
           (double)(clock() - c0) / CLOCKS_PER_SEC, useIdx ? " indexed" : "");
    fflush(stdout);
  }
}
