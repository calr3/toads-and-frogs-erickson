// Adjacent conflicts: positions g and g + 6d (d a small direction keeping ab fixed) with the same shape
// (order, gaps capped at C with residue mod 6, exact ab, clamped forms) but different outcomes.
// usage: adjconf S C form:M ...   prints: order side g0..g4 d0..d4
#include <bits/stdc++.h>
using namespace std;
int S, C, NF; vector<array<int,5>> FO; vector<int> FM;
static inline bool toad(int c, int i) { return (c >> i) & 1; }
int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 4; i++) if (!toad(c, i)) fr++; return tl - fr; }
int ordOf[16]; int ords[6]; vector<long> base; long blockSize;
long binom(int n, int k) { if (k < 0 || k > n) return 0; long r = 1; for (int i = 1; i <= k; i++) r = r * (n - k + i) / i; return r; }
long rankComp(const array<int,5>& g) { int n = g[0] + g[1] + g[2] + g[3] + g[4]; long r = 0; int rem = n;
  for (int i = 0; i < 4; i++) { for (int x = 0; x < g[i]; x++) r += binom(rem - x + (3 - i), 3 - i); rem -= g[i]; } return r; }
long idx(int c, const array<int,5>& g) { int n = g[0] + g[1] + g[2] + g[3] + g[4]; return ordOf[c] * blockSize + base[n] + rankComp(g); }
vector<uint8_t> st;
bool lmc(int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if (!toad(c, i)) return false; h = g; c2 = c;
  if (g[i + 1] > 0) { h[i]++; h[i + 1]--; return true; } if (i + 1 < 4 && !toad(c, i + 1) && g[i + 2] > 0) { h[i]++; h[i + 2]--; c2 ^= 3 << i; return true; } return false; }
bool rmc(int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if (toad(c, i)) return false; h = g; c2 = c;
  if (g[i] > 0) { h[i]--; h[i + 1]++; return true; } if (i >= 1 && toad(c, i - 1) && g[i - 1] > 0) { h[i - 1]--; h[i + 1]++; c2 ^= 3 << (i - 1); return true; } return false; }
bool xRF(int c, const array<int,5>& g);
bool xLF(int c, const array<int,5>& g) { long e = idx(c, g); if (st[e] & 1) return st[e] & 2;
  bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (lmc(c, g, i, c2, h) && !xRF(c2, h)) r = true; }
  st[e] |= 1 | (r ? 2 : 0); return r; }
bool xRF(int c, const array<int,5>& g) { long e = idx(c, g); if (st[e] & 4) return st[e] & 8;
  bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (rmc(c, g, i, c2, h) && !xLF(c2, h)) r = true; }
  st[e] |= 4 | (r ? 8 : 0); return r; }
int main(int argc, char** argv) {
  S = atoi(argv[1]); C = atoi(argv[2]);
  for (int a = 3; a < argc; a++) { array<int,5> f; int M; sscanf(argv[a], "%d,%d,%d,%d,%d:%d", &f[0], &f[1], &f[2], &f[3], &f[4], &M); FO.push_back(f); FM.push_back(M); }
  NF = FO.size();
  int n = 0; for (int c = 0; c < 16; c++) if (__builtin_popcount(c) == 2) { ordOf[c] = n; ords[n++] = c; }
  base.assign(S + 2, 0); for (int s = 0; s <= S; s++) base[s + 1] = base[s] + binom(s + 4, 4); blockSize = base[S + 1];
  st.assign(6 * blockSize, 0);
  long found = 0;
  for (int oi = 0; oi < 6; oi++) { int c = ords[oi]; if (c == 12) continue;
    int a[5]; for (int k = 0; k < 5; k++) a[k] = coef(c, k);
    vector<array<int,5>> dirs;
    for (int d0 = -2; d0 <= 2; d0++) for (int d1 = -2; d1 <= 2; d1++) for (int d2 = -2; d2 <= 2; d2++) for (int d3 = -2; d3 <= 2; d3++) for (int d4 = -2; d4 <= 2; d4++) {
      array<int,5> d = {d0, d1, d2, d3, d4}; int g = 0; for (int x : d) g = __gcd(g, abs(x)); if (g != 1) continue;
      int first = 0; for (int x : d) if (x) { first = x; break; } if (first < 0) continue;
      int s = 0; for (int k = 0; k < 5; k++) s += a[k] * d[k]; if (s != 0) continue;
      dirs.push_back(d); }
    for (int a0 = 0; a0 <= S; a0++) for (int a1 = 0; a0 + a1 <= S; a1++) for (int a2 = 0; a0 + a1 + a2 <= S; a2++) for (int a3 = 0; a0 + a1 + a2 + a3 <= S; a3++) for (int a4 = 0; a0 + a1 + a2 + a3 + a4 <= S; a4++) {
      array<int,5> g = {a0, a1, a2, a3, a4};
      for (auto& d : dirs) {
        array<int,5> h; int sum = 0; bool ok = true;
        for (int k = 0; k < 5; k++) { h[k] = g[k] + 6 * d[k]; if (h[k] < 0) ok = false; sum += h[k]; }
        if (!ok || sum > S) continue;
        // same shape? capped values equal, forms equal after clamping
        for (int k = 0; k < 5 && ok; k++) { int x = g[k] < C ? g[k] : C + (g[k] - C) % 6, y = h[k] < C ? h[k] : C + (h[k] - C) % 6; if (x != y) ok = false; }
        for (int j = 0; j < NF && ok; j++) { long x = 0, y = 0; for (int k = 0; k < 5; k++) { x += (long)FO[j][k] * g[k]; y += (long)FO[j][k] * h[k]; }
          if (max((long)-FM[j], min((long)FM[j], x)) != max((long)-FM[j], min((long)FM[j], y))) ok = false; }
        if (!ok) continue;
        for (int side = 0; side < 2; side++) { bool u = side == 0 ? xLF(c, g) : xRF(c, g), v = side == 0 ? xLF(c, h) : xRF(c, h);
          if (u != v) { found++; printf("%d %d %d %d %d %d %d %d %d %d %d %d\n", c, side, g[0], g[1], g[2], g[3], g[4], d[0], d[1], d[2], d[3], d[4]); } } } } }
  fprintf(stderr, "%ld adjacent conflicts\n", found);
}
