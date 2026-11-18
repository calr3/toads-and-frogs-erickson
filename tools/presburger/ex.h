// exact 2v2 solver with dense index, shared header
#include <bits/stdc++.h>
using namespace std;
static int S;
static inline bool toad(int c, int i) { return (c >> i) & 1; }
static int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 4; i++) if (!toad(c, i)) fr++; return tl - fr; }
static int ordOf[16]; static int ords[6];
static vector<long> base; static long blockSize;
static long binom(int n, int k) { if (k < 0 || k > n) return 0; long r = 1; for (int i = 1; i <= k; i++) r = r * (n - k + i) / i; return r; }
static long rankComp(const array<int,5>& g) { int n = g[0] + g[1] + g[2] + g[3] + g[4]; long r = 0; int rem = n;
  for (int i = 0; i < 4; i++) { for (int x = 0; x < g[i]; x++) r += binom(rem - x + (3 - i), 3 - i); rem -= g[i]; } return r; }
static long idx(int c, const array<int,5>& g) { int n = g[0] + g[1] + g[2] + g[3] + g[4]; return ordOf[c] * blockSize + base[n] + rankComp(g); }
static vector<uint8_t> st;
static bool lmc(int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if (!toad(c, i)) return false; h = g; c2 = c;
  if (g[i + 1] > 0) { h[i]++; h[i + 1]--; return true; } if (i + 1 < 4 && !toad(c, i + 1) && g[i + 2] > 0) { h[i]++; h[i + 2]--; c2 ^= 3 << i; return true; } return false; }
static bool rmc(int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if (toad(c, i)) return false; h = g; c2 = c;
  if (g[i] > 0) { h[i]--; h[i + 1]++; return true; } if (i >= 1 && toad(c, i - 1) && g[i - 1] > 0) { h[i - 1]--; h[i + 1]++; c2 ^= 3 << (i - 1); return true; } return false; }
static bool xRF(int c, const array<int,5>& g);
// xLF: Left moving first wins
static bool xLF(int c, const array<int,5>& g) { long e = idx(c, g); if (st[e] & 1) return st[e] & 2;
  bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (lmc(c, g, i, c2, h) && !xRF(c2, h)) r = true; }
  st[e] |= 1 | (r ? 2 : 0); return r; }
static bool xRF(int c, const array<int,5>& g) { long e = idx(c, g); if (st[e] & 4) return st[e] & 8;
  bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (rmc(c, g, i, c2, h) && !xLF(c2, h)) r = true; }
  st[e] |= 4 | (r ? 8 : 0); return r; }
static void initS(int s) { S = s; int n = 0; for (int c = 0; c < 16; c++) if (__builtin_popcount(c) == 2) { ordOf[c] = n; ords[n++] = c; }
  base.assign(S + 2, 0); for (int x = 0; x <= S; x++) base[x + 1] = base[x] + binom(x + 4, 4); blockSize = base[S + 1]; st.assign(6 * blockSize, 0); }
static int abOf(int c, const array<int,5>& g) { int a = 0; for (int k = 0; k < 5; k++) a += coef(c, k) * g[k]; return a; }
