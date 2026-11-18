// exact normal play for three toads and three frogs: piece order c (bit i = piece i is a toad) + 7 gaps
#include <bits/stdc++.h>
using namespace std;
typedef array<int,7> Gp;
static int S;
static inline bool toad(int c, int i) { return (c >> i) & 1; }
static int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 6; i++) if (!toad(c, i)) fr++; return tl - fr; }
static int ordOf[64]; static int ords[20]; static int NO = 0;
static vector<long> base; static long blockSize;
static long binom(int n, int k) { if (k < 0 || k > n) return 0; long r = 1; for (int i = 1; i <= k; i++) r = r * (n - k + i) / i; return r; }
static long rankComp(const Gp& g) { int n = 0; for (int x : g) n += x; long r = 0; int rem = n;
  for (int i = 0; i < 6; i++) { for (int x = 0; x < g[i]; x++) r += binom(rem - x + (5 - i), 5 - i); rem -= g[i]; } return r; }
static long idx(int c, const Gp& g) { int n = 0; for (int x : g) n += x; return ordOf[c] * blockSize + base[n] + rankComp(g); }
static vector<uint8_t> st;
static bool lmc(int c, const Gp& g, int i, int& c2, Gp& h) { if (!toad(c, i)) return false; h = g; c2 = c;
  if (g[i + 1] > 0) { h[i]++; h[i + 1]--; return true; } if (i + 1 < 6 && !toad(c, i + 1) && g[i + 2] > 0) { h[i]++; h[i + 2]--; c2 ^= 3 << i; return true; } return false; }
static bool rmc(int c, const Gp& g, int i, int& c2, Gp& h) { if (toad(c, i)) return false; h = g; c2 = c;
  if (g[i] > 0) { h[i]--; h[i + 1]++; return true; } if (i >= 1 && toad(c, i - 1) && g[i - 1] > 0) { h[i - 1]--; h[i + 1]++; c2 ^= 3 << (i - 1); return true; } return false; }
static bool xRF(int c, const Gp& g);
static bool xLF(int c, const Gp& g) { long e = idx(c, g); if (st[e] & 1) return st[e] & 2;
  bool r = false; for (int i = 0; i < 6 && !r; i++) { int c2; Gp h; if (lmc(c, g, i, c2, h) && !xRF(c2, h)) r = true; }
  st[e] |= 1 | (r ? 2 : 0); return r; }
static bool xRF(int c, const Gp& g) { long e = idx(c, g); if (st[e] & 4) return st[e] & 8;
  bool r = false; for (int i = 0; i < 6 && !r; i++) { int c2; Gp h; if (rmc(c, g, i, c2, h) && !xLF(c2, h)) r = true; }
  st[e] |= 4 | (r ? 8 : 0); return r; }
static void initS(int s) { S = s; for (int c = 0; c < 64; c++) if (__builtin_popcount(c) == 3) { ordOf[c] = NO; ords[NO++] = c; }
  base.assign(S + 2, 0); for (int x = 0; x <= S; x++) base[x + 1] = base[x] + binom(x + 6, 6); blockSize = base[S + 1]; st.assign((size_t)NO * blockSize, 0); }
static int abOf(int c, const Gp& g) { int a = 0; for (int k = 0; k < 7; k++) a += coef(c, k) * g[k]; return a; }
static const char* nm(int c) { static char b[7]; for (int i = 0; i < 6; i++) b[i] = toad(c, i) ? 'T' : 'F'; b[6] = 0; return b; }
