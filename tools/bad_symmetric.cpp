#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int n;
static inline int cell(u64 s, int i) { return (s >> (2 * i)) & 3; }
static inline u64 setc(u64 s, int i, int v) { return (s & ~(3ULL << (2 * i))) | ((u64)v << (2 * i)); }
static inline int leftMoves(u64 s, u64 *out) { int k = 0;
  for (int i = 0; i < n; i++) if (cell(s, i) == 1) {
    if (i + 1 < n && cell(s, i + 1) == 0) out[k++] = setc(setc(s, i, 0), i + 1, 1);
    else if (i + 2 < n && cell(s, i + 1) == 2 && cell(s, i + 2) == 0) out[k++] = setc(setc(s, i, 0), i + 2, 1); }
  return k; }
static inline int rightMoves(u64 s, u64 *out) { int k = 0;
  for (int i = n - 1; i >= 0; i--) if (cell(s, i) == 2) {
    if (i - 1 >= 0 && cell(s, i - 1) == 0) out[k++] = setc(setc(s, i, 0), i - 1, 2);
    else if (i - 2 >= 0 && cell(s, i - 1) == 1 && cell(s, i - 2) == 0) out[k++] = setc(setc(s, i, 0), i - 2, 2); }
  return k; }
u64 mirror(u64 s) { u64 t = 0; for (int i = 0; i < n; i++) { int c = cell(s, i); t = setc(t, n - 1 - i, c == 1 ? 2 : c == 2 ? 1 : 0); } return t; }
struct H { size_t operator()(u64 x) const { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; } };
unordered_map<u64, uint8_t, H> memo;
bool LF(u64 s); bool RF(u64 s); bool Np(u64 s); bool Mp(u64 s);
bool LF(u64 s) { auto it = memo.find(s); if (it != memo.end() && (it->second & 1)) return it->second & 2;
  u64 mv[64]; int k = leftMoves(s, mv); bool r = false; for (int j = 0; j < k && !r; j++) if (!RF(mv[j])) r = true;
  memo[s] |= 1 | (r ? 2 : 0); return r; }
bool RF(u64 s) { auto it = memo.find(s); if (it != memo.end() && (it->second & 4)) return it->second & 8;
  u64 mv[64]; int k = rightMoves(s, mv); bool r = false; for (int j = 0; j < k && !r; j++) if (!LF(mv[j])) r = true;
  memo[s] |= 4 | (r ? 8 : 0); return r; }
bool Mp(u64 s) { auto it = memo.find(s); if (it != memo.end() && (it->second & 64)) return it->second & 128;
  u64 mv[64]; int k = rightMoves(s, mv); bool r = !LF(s); for (int j = 0; j < k && !r; j++) if (Np(mv[j])) r = true;
  memo[s] |= 64 | (r ? 128 : 0); return r; }
bool Np(u64 s) { auto it = memo.find(s); if (it != memo.end() && (it->second & 16)) return it->second & 32;
  bool r = (mirror(s) == s) ? true : Mp(s);
  if (r) { u64 mv[64]; int k = leftMoves(s, mv); for (int j = 0; j < k && r; j++) if (!Mp(mv[j])) r = false; }
  memo[s] |= 16 | (r ? 32 : 0); return r; }
int main(int argc, char **argv) {
  int h = atoi(argv[1]), odd = atoi(argv[2]);
  n = 2 * h + odd;
  long bad = 0, tot = 0;
  for (int m = 0; m < (1 << h); m++) {
    if (m == 0) continue;
    u64 s = 0; string X;
    for (int i = 0; i < h; i++) { int c = (m >> i) & 1; X += c ? 'T' : '.'; }
    for (int i = 0; i < h; i++) { int c = X[i] == 'T'; s = setc(s, i, c ? 1 : 0); s = setc(s, n - 1 - i, c ? 2 : 0); }
    tot++;
    if (!Np(s)) { bad++; printf("%s\n", X.c_str()); }
  }
  fprintf(stderr, "h=%d odd=%d bad=%ld/%ld\n", h, odd, bad, tot);
}
