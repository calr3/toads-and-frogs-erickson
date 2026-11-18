// For shapes listed in a file (order, capped gaps, ab, clamped forms), enumerate positions with that shape
// (capped gaps C + r + 6t, t <= T, at most SMAX empty squares), solve them exactly, and print pairs of
// positions with the same shape and different outcomes (Left moving first).
// usage: mixed C T SMAX shapes.txt form:M ...
#include <bits/stdc++.h>
using namespace std;
int C, T, SMAX, NF; vector<array<int,5>> FO; vector<int> FM;
static inline bool toad(int c, int i) { return (c >> i) & 1; }
int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 4; i++) if (!toad(c, i)) fr++; return tl - fr; }
unordered_map<uint64_t, uint8_t> memo;
uint64_t encx(int c, const array<int,5>& g) { uint64_t x = c; for (int i = 0; i < 5; i++) x = x * 256 + g[i]; return x; }
bool lmc(int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if (!toad(c, i)) return false; h = g; c2 = c;
  if (g[i + 1] > 0) { h[i]++; h[i + 1]--; return true; } if (i + 1 < 4 && !toad(c, i + 1) && g[i + 2] > 0) { h[i]++; h[i + 2]--; c2 ^= 3 << i; return true; } return false; }
bool rmc(int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if (toad(c, i)) return false; h = g; c2 = c;
  if (g[i] > 0) { h[i]--; h[i + 1]++; return true; } if (i >= 1 && toad(c, i - 1) && g[i - 1] > 0) { h[i - 1]--; h[i + 1]++; c2 ^= 3 << (i - 1); return true; } return false; }
bool xRF(int c, const array<int,5>& g);
bool xLF(int c, const array<int,5>& g) { uint64_t e = encx(c, g); auto it = memo.find(e); if (it != memo.end() && (it->second & 1)) return it->second & 2;
  bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (lmc(c, g, i, c2, h) && !xRF(c2, h)) r = true; }
  memo[e] |= 1 | (r ? 2 : 0); return r; }
bool xRF(int c, const array<int,5>& g) { uint64_t e = encx(c, g); auto it = memo.find(e); if (it != memo.end() && (it->second & 4)) return it->second & 8;
  bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (rmc(c, g, i, c2, h) && !xLF(c2, h)) r = true; }
  memo[e] |= 4 | (r ? 8 : 0); return r; }
int main(int argc, char** argv) {
  C = atoi(argv[1]); T = atoi(argv[2]); SMAX = atoi(argv[3]); const char* fn = argv[4];
  for (int a = 5; a < argc; a++) { array<int,5> f; int M; sscanf(argv[a], "%d,%d,%d,%d,%d:%d", &f[0], &f[1], &f[2], &f[3], &f[4], &M); FO.push_back(f); FM.push_back(M); }
  NF = FO.size(); int LIMIT = getenv("LIMIT") ? atoi(getenv("LIMIT")) : 1000000;
  ifstream in(fn); string line; long nsh = 0, nmixed = 0;
  while (getline(in, line) && nsh < LIMIT) {
    istringstream is(line); int c, v[5], ab, fv[8]; is >> c; for (int i = 0; i < 5; i++) is >> v[i]; is >> ab; for (int j = 0; j < NF; j++) is >> fv[j];
    nsh++;
    vector<int> bigs; for (int i = 0; i < 5; i++) if (v[i] >= C) bigs.push_back(i);
    int nb = bigs.size(); vector<int> t(nb, 0); bool haveW = false, haveL = false; array<int,5> pw, pl;
    while (true) {
      array<int,5> g; for (int i = 0; i < 5; i++) g[i] = v[i]; for (int j = 0; j < nb; j++) g[bigs[j]] += 6 * t[j];
      int sum = 0; for (int i = 0; i < 5; i++) sum += g[i];
      if (sum <= SMAX) {
        long a = 0; for (int k = 0; k < 5; k++) a += coef(c, k) * g[k];
        bool ok = a == ab;
        for (int j = 0; j < NF && ok; j++) { long x = 0; for (int k = 0; k < 5; k++) x += (long)FO[j][k] * g[k]; if (max((long)-FM[j], min((long)FM[j], x)) != fv[j]) ok = false; }
        if (ok) { if (xLF(c, g)) { if (!haveL) { haveL = true; pl = g; } } else { if (!haveW) { haveW = true; pw = g; } } }
      }
      if (haveW && haveL) break;
      int j = 0; while (j < nb && ++t[j] > T) { t[j] = 0; j++; } if (j == nb) break; }
    if (haveW && haveL) { nmixed++;
      printf("%d %d %d %d %d %d  %d %d %d %d %d\n", c, pw[0], pw[1], pw[2], pw[3], pw[4], pl[0], pl[1], pl[2], pl[3], pl[4]); fflush(stdout); }
  }
  fprintf(stderr, "%ld shapes, %ld mixed, memo %zu\n", nsh, nmixed, memo.size());
}
