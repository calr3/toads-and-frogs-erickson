// Solve every 2-toad 2-frog position with at most S empty squares exactly, group positions by shape
// (order, gaps capped at C with residue mod 6, exact ab, clamped linear forms), and print pairs of positions
// with the same shape and different outcomes (both Left-first and Right-first).
// usage: conflict S C form:M ...      (env MAXOUT: pairs to print per kind)
#include <bits/stdc++.h>
using namespace std;
int S, C, NF; vector<array<int,5>> FO; vector<int> FM;
static inline bool toad(int c, int i) { return (c >> i) & 1; }
int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 4; i++) if (!toad(c, i)) fr++; return tl - fr; }
// dense index: order id (0..5) and gaps with sum <= S
int ordOf[16]; int ords[6];
vector<int> base;   // base[sum] offset within an order block for compositions of `sum` into 5 parts
long blockSize;
long binom(int n, int k) { if (k < 0 || k > n) return 0; long r = 1; for (int i = 1; i <= k; i++) r = r * (n - k + i) / i; return r; }
long rankComp(const array<int,5>& g) {   // rank among compositions with the same sum (lexicographic)
  int n = g[0] + g[1] + g[2] + g[3] + g[4]; long r = 0; int rem = n;
  for (int i = 0; i < 4; i++) { for (int x = 0; x < g[i]; x++) r += binom(rem - x + (3 - i), 3 - i); rem -= g[i]; }
  return r; }
long idx(int c, const array<int,5>& g) { int n = g[0] + g[1] + g[2] + g[3] + g[4]; return ordOf[c] * blockSize + base[n] + rankComp(g); }
vector<uint8_t> st;   // bit0 LF known, bit1 LF, bit2 RF known, bit3 RF
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
  NF = FO.size(); int MAXOUT = getenv("MAXOUT") ? atoi(getenv("MAXOUT")) : 400;
  int n = 0; for (int c = 0; c < 16; c++) if (__builtin_popcount(c) == 2) { ordOf[c] = n; ords[n++] = c; }
  base.assign(S + 2, 0); for (int s = 0; s <= S; s++) base[s + 1] = base[s] + binom(s + 4, 4); blockSize = base[S + 1];
  st.assign(6 * blockSize, 0);
  fprintf(stderr, "%ld positions\n", 6 * blockSize);
  // group by shape: key -> first position with Left-first win, with Left-first loss (same for Right-first)
  struct G { long w[2] = {-1, -1}, l[2] = {-1, -1}; };
  unordered_map<uint64_t, G> groups; groups.reserve(1 << 24);
  vector<array<int,6>> posOf;   // not stored; decode on the fly
  auto shapeKey = [&](int c, const array<int,5>& g) { string k; k += char(c);
    long ab = 0; for (int i = 0; i < 5; i++) { k += char(g[i] < C ? g[i] : C + (g[i] - C) % 6); ab += coef(c, i) * g[i]; }
    k += char(ab + 128); for (int j = 0; j < NF; j++) { long x = 0; for (int i = 0; i < 5; i++) x += (long)FO[j][i] * g[i]; k += char(max((long)-FM[j], min((long)FM[j], x)) + 64); }
    return k; };
  vector<pair<array<int,6>, array<int,6>>> conf[2];
  for (int oi = 0; oi < 6; oi++) { int c = ords[oi];
    for (int a = 0; a <= S; a++) for (int b = 0; a + b <= S; b++) for (int d = 0; a + b + d <= S; d++) for (int e = 0; a + b + d + e <= S; e++) for (int f = 0; a + b + d + e + f <= S; f++) {
      array<int,5> g = {a, b, d, e, f}; bool L = xLF(c, g), R = xRF(c, g);
      string k = shapeKey(c, g); uint64_t hk = hash<string>()(k) * 0x9E3779B97F4A7C15ULL ^ (k.size() * 1315423911ULL) ^ hash<string>()(k + "#"); G& gr = groups[hk]; long id = idx(c, g);
      for (int side = 0; side < 2; side++) { bool win = side == 0 ? L : R; long& mine = win ? gr.w[side] : gr.l[side]; long other = win ? gr.l[side] : gr.w[side];
        if (mine < 0) mine = id;
        if (other >= 0 && (long)conf[side].size() < MAXOUT && mine == id) {
          // decode other: store as positions by re-encoding (cheap: keep a side map)
          conf[side].push_back({{c, a, b, d, e, f}, {c, -1, (int)(other >> 32), (int)(other & 0xffffffff), 0, 0}}); } } } }
  // decode ids
  auto decode = [&](long id) { int oi = id / blockSize; long r = id % blockSize; int s = 0; while (base[s + 1] <= r) s++; r -= base[s];
    array<int,5> g; int rem = s; for (int i = 0; i < 4; i++) { int x = 0; while (true) { long cnt = binom(rem - x + (3 - i), 3 - i); if (r < cnt) break; r -= cnt; x++; } g[i] = x; rem -= x; } g[4] = rem;
    return make_pair(ords[oi], g); };
  long nconf[2] = {0, 0};
  for (auto& [k, gr] : groups) for (int side = 0; side < 2; side++) if (gr.w[side] >= 0 && gr.l[side] >= 0) nconf[side]++;
  fprintf(stderr, "%zu shapes; conflicting shapes: Left-first %ld, Right-first %ld\n", groups.size(), nconf[0], nconf[1]);
  for (int side = 0; side < 2; side++) for (auto& [p, q] : conf[side]) {
    long other = ((long)q[2] << 32) | (unsigned)q[3]; auto [c2, g2] = decode(other);
    printf("%d %d %d %d %d %d  %d %d %d %d %d %s\n", p[0], p[1], p[2], p[3], p[4], p[5], g2[0], g2[1], g2[2], g2[3], g2[4], side == 0 ? "LF" : "RF"); }
}
