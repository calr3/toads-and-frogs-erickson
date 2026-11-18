// For TTFF positions (g0,g1,_,g3,g4), find where the outcome along the centre gap g2 becomes periodic with period 6.
#include <bits/stdc++.h>
using namespace std;
static inline bool toad(int c, int i) { return (c >> i) & 1; }
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
  // walk from base g along direction d; base: g - d has a negative coordinate. Print side, base gaps, ab, start of period-6 behaviour in t.
  int c = atoi(argv[1]); int d[5]; sscanf(argv[2], "%d,%d,%d,%d,%d", d, d + 1, d + 2, d + 3, d + 4); int TMAXW = atoi(argv[3]), R = atoi(argv[4]);
  // coordinates that shrink along d start at TMAXW*|d| + (0..R), the others at 0..R
  int lo[5]; for (int i = 0; i < 5; i++) lo[i] = d[i] < 0 ? TMAXW * (-d[i]) : 0;
  for (int a0 = 0; a0 <= R; a0++) for (int a1 = 0; a1 <= R; a1++) for (int a2 = 0; a2 <= R; a2++) for (int a3 = 0; a3 <= R; a3++) for (int a4 = 0; a4 <= R; a4++) {
    array<int,5> g = {a0 + lo[0], a1 + lo[1], a2 + lo[2], a3 + lo[3], a4 + lo[4]};
    bool isBase = false; for (int i = 0; i < 5; i++) if (g[i] - d[i] < 0) isBase = true; if (!isBase) continue;
    bool ok = true; for (int i = 0; i < 5; i++) if (g[i] + TMAXW * d[i] < 0) ok = false; if (!ok) continue;
    int ab = 0; for (int k = 0; k < 5; k++) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 4; i++) if (!toad(c, i)) fr++; ab += (tl - fr) * g[k]; }
    for (int side = 0; side < 2; side++) {
      vector<int> v(TMAXW + 1); for (int t = 0; t <= TMAXW; t++) { array<int,5> h; for (int i = 0; i < 5; i++) h[i] = g[i] + t * d[i]; v[t] = side == 0 ? xLF(c, h) : xRF(c, h); }
      int p0 = TMAXW - 6; while (p0 > 0 && v[p0 - 1] == v[p0 + 5]) p0--;
      printf("%d %d %d %d %d %d %d %d\n", side, g[0], g[1], g[2], g[3], g[4], ab, p0); } }
}
