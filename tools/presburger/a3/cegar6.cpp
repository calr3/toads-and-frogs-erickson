#include "ex6.h"
#include <omp.h>
// Search for a small invariant for the row a = 3 on exact data (at most S empty squares).
// The invariant is one decision tree per slice (piece order, race count): a position is in the invariant if its
// slice has a tree and the tree says "in".  Trees are learned from POS (positions that must be in) against all
// Left wins of the slice; other losses are "don't care".  Loop: every position in the invariant must have, for
// every Left move, a Right reply in the invariant; otherwise the first losing reply in Right's priority order
// is added to POS and the trees of the changed slices are learned again.
// Usage: cegar6 S [OUTPREFIX]      env: PRIO (permutation of 012345, frogs tried in this order), MAXR (rounds)
struct Form { array<int,7> f; };
vector<Form> forms;
struct Test { int form, kind, m, v; };
struct P7 { int8_t g[7]; };
static inline long evalF(const array<int,7>& f, const int8_t* g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
static inline bool evalT(const Test& t, const int8_t* g) { long x = evalF(forms[t.form].f, g); if (t.kind == 0) return x >= t.v; return ((x % t.m) + t.m) % t.m == t.v; }
struct Node { Test t; int yes = -1, no = -1, leaf = -1; long n = 0, npos = 0; int8_t lo[7], hi[7]; };
int WB = 3;   // box hull of the POS points of a leaf: a gap whose maximum reaches WB is unbounded above, lower bounds are capped at WB
const int VR = 34;
mt19937_64 rng(12345);
struct Slice { int c, ab; long nw = 0; vector<P7> wins; set<Gp> pos; vector<Node> nodes; bool dirty = false; int leavesIn = 0;
  bool in(const int8_t* g) const { if (nodes.empty()) return false; int id = 0; while (nodes[id].leaf < 0) id = evalT(nodes[id].t, g) ? nodes[id].yes : nodes[id].no; if (nodes[id].leaf != 0) return false; for (int k = 0; k < 7; k++) if (g[k] < nodes[id].lo[k] || g[k] > nodes[id].hi[k]) return false; return true; } };
const int ABOFF = 16; vector<Slice> SL;   // index: ordOf[c] * 33 + ab + ABOFF
static inline Slice& sliceOf(int c, int ab) { return SL[ordOf[c] * 33 + ab + ABOFF]; }
struct Row { int8_t g[7]; int8_t w; };
int build(vector<Node>& nodes, const vector<Row>& rows, vector<int>& idx, int depth) {
  long n = idx.size(), nw = 0; for (int r : idx) nw += rows[r].w;
  int id = nodes.size(); nodes.push_back(Node()); nodes[id].n = n; nodes[id].npos = n - nw;
  if (nw == 0 || nw == n) { nodes[id].leaf = nw > 0; if (!nw) for (int k = 0; k < 7; k++) { int lo = 127, hi = 0; for (int r : idx) { lo = min<int>(lo, rows[r].g[k]); hi = max<int>(hi, rows[r].g[k]); } nodes[id].lo[k] = min(lo, WB); nodes[id].hi[k] = hi >= WB ? 127 : hi; } return id; }
  int NF = forms.size(); vector<double> bsc(NF, 1e18); vector<Test> bt(NF);
  #pragma omp parallel for schedule(dynamic, 8)
  for (int fi = 0; fi < NF; fi++) { long cnt[2 * VR + 3] = {0}, cw[2 * VR + 3] = {0}, m6[6] = {0}, w6[6] = {0};
    for (int r : idx) { long x = evalF(forms[fi].f, rows[r].g); int b = x < -VR ? 0 : x > VR ? 2 * VR + 2 : (int)(x + VR + 1); cnt[b]++; cw[b] += rows[r].w; int q = ((x % 6) + 6) % 6; m6[q]++; w6[q] += rows[r].w; }
    auto score = [&](long a, long aw) -> double { long b = n - a, bw = nw - aw; if (a == 0 || b == 0) return 1e18;
      return a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b; };
    long a = cnt[2 * VR + 2], aw = cw[2 * VR + 2];
    for (int v = VR; v >= -VR + 1; v--) { int b = v + VR + 1; a += cnt[b]; aw += cw[b]; double s = score(a, aw); if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 0, 0, v}; } }
    for (int r = 0; r < 2; r++) { long a2 = m6[r] + m6[r + 2] + m6[r + 4], w2 = w6[r] + w6[r + 2] + w6[r + 4]; double s = score(a2, w2) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 2, r}; } }
    for (int r = 0; r < 3; r++) { long a3 = m6[r] + m6[r + 3], w3 = w6[r] + w6[r + 3]; double s = score(a3, w3) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 3, r}; } } }
  int best = -1; for (int fi = 0; fi < NF; fi++) if (bsc[fi] < 1e17 && (best < 0 || bsc[fi] + 1e-9 * fi < bsc[best] + 1e-9 * best)) best = fi;
  if (best < 0) { fprintf(stderr, "no split\n"); exit(1); }
  Test t = bt[best]; vector<int> y, no; for (int r : idx) (evalT(t, rows[r].g) ? y : no).push_back(r);
  vector<int>().swap(idx); nodes[id].t = t; int a = build(nodes, rows, y, depth + 1); int b = build(nodes, rows, no, depth + 1); nodes[id].yes = a; nodes[id].no = b; return id; }
void learn(Slice& s) { vector<Row> rows; rows.reserve(s.wins.size() + s.pos.size());
  for (auto& w : s.wins) { Row r; memcpy(r.g, w.g, 7); r.w = 1; rows.push_back(r); }
  for (auto& g : s.pos) { Row r; for (int i = 0; i < 7; i++) r.g[i] = g[i]; r.w = 0; rows.push_back(r); }
  s.nodes.clear(); vector<int> all(rows.size()); iota(all.begin(), all.end(), 0); build(s.nodes, rows, all, 0);
  s.leavesIn = 0; for (auto& n : s.nodes) if (n.leaf == 0) s.leavesIn++; s.dirty = false; }
int NMIN = 0;
template <class F> void forAll(int Smax, F f) { Gp g; function<void(int,int)> rec = [&](int k, int rem) { if (k == 6) { for (int x = max(0, rem - (Smax - NMIN)); x <= rem; x++) { g[6] = x; f(g); } return; } for (int x = 0; x <= rem; x++) { g[k] = x; rec(k + 1, rem - x); } }; rec(0, Smax); }
int main(int argc, char** argv) { initS(atoi(argv[1])); if (getenv("NMIN")) NMIN = atoi(getenv("NMIN")); long WCAP = getenv("WCAP") ? atol(getenv("WCAP")) : 1000000000L; string out = argc > 2 ? argv[2] : ""; int MAXR = getenv("MAXR") ? atoi(getenv("MAXR")) : 1000;
  int prio[6] = {0, 1, 2, 3, 4, 5}; if (getenv("WB")) WB = atoi(getenv("WB")); int FR = getenv("FR") ? atoi(getenv("FR")) : 1, NZ2 = getenv("NZ2") ? atoi(getenv("NZ2")) : 3; if (getenv("PRIO")) for (int i = 0; i < 6; i++) prio[i] = getenv("PRIO")[i] - '0';
  { array<int,7> f; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0, first = 0; for (int x : f) if (x) { nz++; if (!first) first = x; } int gg = 0, mx = 0; for (int x : f) { gg = __gcd(gg, abs(x)); mx = max(mx, abs(x)); } if (!nz || first < 0 || gg != 1) return; if (mx > 1 && nz > NZ2) return; forms.push_back({f}); return; }
      for (int x = -FR; x <= FR; x++) { f[k] = x; rec(k + 1); } }; rec(0); }
  fprintf(stderr, "%zu forms\n", forms.size());
  SL.resize(20 * 33); for (int oi = 0; oi < 20; oi++) for (int a = -ABOFF; a <= ABOFF; a++) { SL[oi * 33 + a + ABOFF].c = ords[oi]; SL[oi * 33 + a + ABOFF].ab = a; }
  for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; forAll(S, [&](const Gp& g) { int ab = abOf(c, g); if (abs(ab) > 12) return; if (xLF(c, g)) { P7 p; for (int i = 0; i < 7; i++) p.g[i] = g[i]; Slice& s = sliceOf(c, ab); s.nw++; if ((long)s.wins.size() < WCAP) s.wins.push_back(p); else { long r = rng() % s.nw; if (r < WCAP) s.wins[r] = p; } } }); }
  fprintf(stderr, "tables ready\n");
  for (int m = max(5, NMIN - 1); m + 1 <= S; m++) { Gp s0 = {0, 0, 1, m, 0, 0, 0}; sliceOf(7, -1).pos.insert(s0); } sliceOf(7, -1).dirty = true;
  for (int round = 1; round <= MAXR; round++) {
    long relearned = 0; for (auto& s : SL) if (s.dirty) { learn(s); relearned++; }
    long added = 0, ing = 0;
    long impure = 0;
    #pragma omp parallel for schedule(dynamic, 1) reduction(+:ing)
    for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; forAll(S, [&](const Gp& g) { int ab = abOf(c, g); if (abs(ab) > 12) return; Slice& s = sliceOf(c, ab); if (s.nodes.empty()) return;
        int8_t gg[7]; for (int i = 0; i < 7; i++) gg[i] = g[i]; if (!s.in(gg)) return; ing++;
        if (xLF(c, g)) { P7 p; memcpy(p.g, gg, 7);
          #pragma omp critical
          { s.wins.push_back(p); s.dirty = true; impure++; }
          return; }
        for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; bool ok = false; int bj = -1; int bc = 0; Gp bq;
          for (int jj = 0; jj < 6 && !ok; jj++) { int j = prio[jj]; int c3; Gp q; if (!rmc(c2, h, j, c3, q)) continue; if (xLF(c3, q)) continue;
            int8_t qq[7]; for (int k = 0; k < 7; k++) qq[k] = q[k]; int ab3 = abOf(c3, q); if (abs(ab3) <= 12 && sliceOf(c3, ab3).in(qq)) { ok = true; break; }
            if (bj < 0 && abs(ab3) <= 12) { bj = j; bc = c3; bq = q; } }
          if (ok) continue; if (bj < 0) { fprintf(stderr, "invariant contains a Left win or leaves the window: %s (%d %d %d %d %d %d %d)\n", nm(c), g[0],g[1],g[2],g[3],g[4],g[5],g[6]); exit(1); }
          Slice& t = sliceOf(bc, abOf(bc, bq));
          #pragma omp critical
          { if (t.pos.insert(bq).second) { t.dirty = true; added++; } } } }); }
    long nsl = 0, leaves = 0, npos = 0; for (auto& s : SL) if (!s.pos.empty()) { nsl++; leaves += s.leavesIn; npos += s.pos.size(); }
    fprintf(stderr, "round %d: relearned %ld, invariant %ld positions, added %ld, impure %ld; %ld slices, %ld in-leaves, %ld POS\n", round, relearned, ing, added, impure, nsl, leaves, npos);
    if (!added && !impure) { printf("closed on S=%d: %ld slices, %ld in-leaves, %ld positions\n", S, nsl, leaves, ing); break; } }
  for (auto& s : SL) if (!s.pos.empty()) printf("%s ab %3d: %7zu POS, %7zu wins, %4d in-leaves\n", nm(s.c), s.ab, s.pos.size(), s.wins.size(), s.leavesIn);
  if (!out.empty()) { FILE* fo = fopen(out.c_str(), "w"); for (auto& s : SL) if (!s.nodes.empty()) { fprintf(fo, "slice %d %d %zu\n", s.c, s.ab, s.nodes.size());
      for (size_t i = 0; i < s.nodes.size(); i++) { auto& n = s.nodes[i]; if (n.leaf == 1) fprintf(fo, "%zu leaf 1\n", i); else if (n.leaf == 0) { fprintf(fo, "%zu leaf 0", i); for (int k = 0; k < 7; k++) fprintf(fo, " %d %d", n.lo[k], n.hi[k]); fprintf(fo, "\n"); } else { auto& f = forms[n.t.form].f; fprintf(fo, "%zu test %d %d %d %d %d %d %d %d %d %d %d %d\n", i, n.t.kind, f[0], f[1], f[2], f[3], f[4], f[5], f[6], n.t.m, n.t.v, n.yes, n.no); } } }
    fclose(fo); } }
