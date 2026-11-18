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
struct Test { int form, kind, m, v; array<int,7> f; };   // f: the coefficients (form < 0: found by regression at this node)
struct P7 { int8_t g[7]; };
static inline long evalF(const array<int,7>& f, const int8_t* g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
static inline bool evalT(const Test& t, const int8_t* g) { long x = evalF(t.f, g); if (t.kind == 0) return x >= t.v; return ((x % t.m) + t.m) % t.m == t.v; }
struct Node { Test t; int yes = -1, no = -1, leaf = -1; long n = 0, npos = 0; int8_t lo[7], hi[7]; };
int WB = 3;   // box hull of the POS points of a leaf: a gap whose maximum reaches WB is unbounded above, lower bounds are capped at WB
const int VR = 34; int LR = 0, SHORT = 0, SUBN = 4000, HC = 0; double LRGAIN = 0.9;   // LR: largest coefficient tried for regression forms; they must beat the pool by this factor
mt19937_64 rng(12345);
struct Slice { int c, ab; long nw = 0; set<Gp> excl; vector<P7> wins; set<Gp> pos; vector<Node> nodes; bool dirty = false; int leavesIn = 0;
  bool in(const int8_t* g) const { if (nodes.empty()) return false; int id = 0; while (nodes[id].leaf < 0) id = evalT(nodes[id].t, g) ? nodes[id].yes : nodes[id].no; if (nodes[id].leaf != 0) return false; for (int k = 0; k < 7; k++) if (g[k] < nodes[id].lo[k] || g[k] > nodes[id].hi[k]) return false; return true; } };
const int ABOFF = 16; vector<Slice> SL;   // index: ordOf[c] * 33 + ab + ABOFF
static inline Slice& sliceOf(int c, int ab) { return SL[ordOf[c] * 33 + ab + ABOFF]; }
struct Row { int8_t g[7]; int8_t w; };
int build(vector<Node>& nodes, const vector<Row>& rows, vector<int>& idx, int depth) {
  long n = idx.size(), nw = 0; for (int r : idx) nw += rows[r].w;
  int id = nodes.size(); nodes.push_back(Node()); nodes[id].n = n; nodes[id].npos = n - nw;
  if (nw == 0 || nw == n) { nodes[id].leaf = nw > 0; if (!nw) for (int k = 0; k < 7; k++) { int lo = 127, hi = 0; for (int r : idx) { lo = min<int>(lo, rows[r].g[k]); hi = max<int>(hi, rows[r].g[k]); } nodes[id].lo[k] = min(lo, WB); nodes[id].hi[k] = hi >= WB ? 127 : hi; } return id; }
  int NF = forms.size(); vector<double> bsc(NF, 1e18); vector<Test> bt(NF);
  // with a large pool, shortlist the forms on a subsample of the node first
  vector<char> use(NF, 1);
  if (SHORT && n > 4 * SUBN) { vector<int> sub(SUBN); for (int i = 0; i < SUBN; i++) sub[i] = idx[((unsigned long)i * 2654435761UL + depth * 97) % n]; long sw = 0; for (int r : sub) sw += rows[r].w;
    vector<pair<double,int>> sc(NF);
    #pragma omp parallel for schedule(dynamic, 64)
    for (int fi = 0; fi < NF; fi++) { long cnt[2 * VR + 3] = {0}, cw[2 * VR + 3] = {0}, m6[6] = {0}, w6[6] = {0}; double bs = 1e18;
      for (int r : sub) { long x = evalF(forms[fi].f, rows[r].g); int b = x < -VR ? 0 : x > VR ? 2 * VR + 2 : (int)(x + VR + 1); cnt[b]++; cw[b] += rows[r].w; int q = ((x % 6) + 6) % 6; m6[q]++; w6[q] += rows[r].w; }
      auto score = [&](long a, long aw) -> double { long b = SUBN - a, bw = sw - aw; if (a == 0 || b == 0) return 1e18;
        return a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b; };
      long a = cnt[2 * VR + 2], aw = cw[2 * VR + 2]; for (int v = VR; v >= -VR + 1; v--) { int b = v + VR + 1; a += cnt[b]; aw += cw[b]; bs = min(bs, score(a, aw)); }
      for (int r = 0; r < 2; r++) bs = min(bs, score(m6[r] + m6[r + 2] + m6[r + 4], w6[r] + w6[r + 2] + w6[r + 4])); for (int r = 0; r < 3; r++) bs = min(bs, score(m6[r] + m6[r + 3], w6[r] + w6[r + 3]));
      sc[fi] = {bs, fi}; }
    sort(sc.begin(), sc.end()); fill(use.begin(), use.end(), 0); for (int i = 0; i < min(NF, SHORT); i++) use[sc[i].second] = 1; }
  #pragma omp parallel for schedule(dynamic, 8)
  for (int fi = 0; fi < NF; fi++) { if (!use[fi]) continue; long cnt[2 * VR + 3] = {0}, cw[2 * VR + 3] = {0}, m6[6] = {0}, w6[6] = {0};
    for (int r : idx) { long x = evalF(forms[fi].f, rows[r].g); int b = x < -VR ? 0 : x > VR ? 2 * VR + 2 : (int)(x + VR + 1); cnt[b]++; cw[b] += rows[r].w; int q = ((x % 6) + 6) % 6; m6[q]++; w6[q] += rows[r].w; }
    auto score = [&](long a, long aw) -> double { long b = n - a, bw = nw - aw; if (a == 0 || b == 0) return 1e18;
      return a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b; };
    long a = cnt[2 * VR + 2], aw = cw[2 * VR + 2];
    for (int v = VR; v >= -VR + 1; v--) { int b = v + VR + 1; a += cnt[b]; aw += cw[b]; double s = score(a, aw); if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 0, 0, v, forms[fi].f}; } }
    for (int r = 0; r < 2; r++) { long a2 = m6[r] + m6[r + 2] + m6[r + 4], w2 = w6[r] + w6[r + 2] + w6[r + 4]; double s = score(a2, w2) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 2, r, forms[fi].f}; } }
    for (int r = 0; r < 3; r++) { long a3 = m6[r] + m6[r + 3], w3 = w6[r] + w6[r + 3]; double s = score(a3, w3) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 3, r, forms[fi].f}; } } }
  int best = -1; for (int fi = 0; fi < NF; fi++) if (bsc[fi] < 1e17 && (best < 0 || bsc[fi] + 1e-9 * fi < bsc[best] + 1e-9 * best)) best = fi;
  if (best < 0) { fprintf(stderr, "no split\n"); exit(1); }
  Test t = bt[best];
  if (LR && n >= 100) {   // oblique candidates: logistic regression on the node, rounded to small integer coefficients
    double mean[7], sd[7]; for (int k = 0; k < 7; k++) { double a = 0, b = 0; for (int r : idx) { a += rows[r].g[k]; b += (double)rows[r].g[k] * rows[r].g[k]; } mean[k] = a / n; sd[k] = sqrt(max(1e-9, b / n - mean[k] * mean[k])); }
    vector<int> sub; if (n > 20000) { for (long i = 0; i < 20000; i++) sub.push_back(idx[(i * 2654435761UL) % n]); } else sub = idx;
    long sn = sub.size(), sw = 0; for (int r : sub) sw += rows[r].w; double w1 = sn / (2.0 * max(1L, sw)), w0 = sn / (2.0 * max(1L, sn - sw));
    double w[8] = {0}; for (int it = 0; it < 60; it++) { double gr[8] = {0};
      for (int r : sub) { double z = w[7]; for (int k = 0; k < 7; k++) z += w[k] * (rows[r].g[k] - mean[k]) / sd[k]; double p = 1 / (1 + exp(-z)); double e = (p - rows[r].w) * (rows[r].w ? w1 : w0);
        for (int k = 0; k < 7; k++) gr[k] += e * (rows[r].g[k] - mean[k]) / sd[k]; gr[7] += e; }
      for (int k = 0; k < 8; k++) w[k] -= 2.0 * gr[k] / sn; }
    double wo[7], mx = 0; for (int k = 0; k < 7; k++) { wo[k] = sd[k] < 1e-4 ? 0 : w[k] / sd[k]; mx = max(mx, fabs(wo[k])); }
    if (mx > 1e-9) for (int sc = 1; sc <= LR; sc++) { array<int,7> f; int gg = 0; for (int k = 0; k < 7; k++) { f[k] = (int)lround(sc * wo[k] / mx); gg = __gcd(gg, abs(f[k])); } if (!gg) continue; for (int& x : f) x /= gg;
      map<long, pair<long,long>> h; for (int r : idx) { auto& e = h[evalF(f, rows[r].g)]; e.first++; e.second += rows[r].w; }
      long a = 0, aw = 0; for (auto it = h.rbegin(); it != h.rend(); ++it) { a += it->second.first; aw += it->second.second; long b = n - a, bw = nw - aw; if (a == 0 || b == 0) continue;
        double s2 = a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b;
        if (s2 < bsc[best] * LRGAIN) { bsc[best] = s2 / LRGAIN; t = {-1, 0, 0, (int)it->first, f}; } } } }
  if (HC && t.kind == 0) {   // hill climbing on the coefficients of the chosen form (oblique split)
    vector<int> sub; if (n > 20000) { sub.resize(20000); for (int i = 0; i < 20000; i++) sub[i] = idx[((unsigned long)i * 2654435761UL) % n]; } else sub = idx;
    long sn = sub.size(), sw = 0; for (int r : sub) sw += rows[r].w;
    auto eval = [&](const array<int,7>& f, const vector<int>& set, long tn, long tw, int& bv) -> double { int lo = INT_MAX, hi = INT_MIN; static thread_local vector<long> xs; xs.resize(set.size());
      for (size_t i = 0; i < set.size(); i++) { xs[i] = evalF(f, rows[set[i]].g); lo = min<long>(lo, xs[i]); hi = max<long>(hi, xs[i]); }
      vector<long> cnt(hi - lo + 2, 0), cw(hi - lo + 2, 0); for (size_t i = 0; i < set.size(); i++) { cnt[xs[i] - lo]++; cw[xs[i] - lo] += rows[set[i]].w; }
      double bs = 1e18; long a = 0, aw = 0; for (int v = hi; v > lo; v--) { a += cnt[v - lo]; aw += cw[v - lo]; long b = tn - a, bw = tw - aw; if (!a || !b) continue;
        double sc = a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b; if (sc < bs) { bs = sc; bv = v; } }
      return bs; };
    array<int,7> f = t.f; int bv = t.v; double cur = eval(f, sub, sn, sw, bv); bool improved = true; int passes = 0;
    while (improved && passes++ < 12) { improved = false;
      for (int k = 0; k < 7; k++) for (int d = -1; d <= 1; d += 2) { array<int,7> f2 = f; f2[k] += d; if (abs(f2[k]) > HC) continue; int gg = 0; for (int x : f2) gg = __gcd(gg, abs(x)); if (gg != 1) continue;
        int v2; double sc = eval(f2, sub, sn, sw, v2); if (sc < cur * 0.98 - 1e-9) { cur = sc; f = f2; improved = true; } } }
    if (f != t.f) { int v2 = 0; double full = eval(f, idx, n, nw, v2); if (full < bsc[best]) { t = {-1, 0, 0, v2, f}; } } }
  vector<int> y, no; for (int r : idx) (evalT(t, rows[r].g) ? y : no).push_back(r);
  vector<int>().swap(idx); nodes[id].t = t; int a = build(nodes, rows, y, depth + 1); int b = build(nodes, rows, no, depth + 1); nodes[id].yes = a; nodes[id].no = b; return id; }
void learn(Slice& s) { vector<Row> rows; rows.reserve(s.wins.size() + s.pos.size());
  for (auto& w : s.wins) { Row r; memcpy(r.g, w.g, 7); r.w = 1; rows.push_back(r); }
  for (auto& g : s.pos) { Row r; for (int i = 0; i < 7; i++) r.g[i] = g[i]; r.w = 0; rows.push_back(r); }
  for (auto& g : s.excl) if (!s.pos.count(g)) { Row r; for (int i = 0; i < 7; i++) r.g[i] = g[i]; r.w = 1; rows.push_back(r); }
  s.nodes.clear(); vector<int> all(rows.size()); iota(all.begin(), all.end(), 0); build(s.nodes, rows, all, 0);
  s.leavesIn = 0; for (auto& n : s.nodes) if (n.leaf == 0) s.leavesIn++; s.dirty = false; }
int NMIN = 0, ROBUST = 0, EXCL = 0, SLIDE = 0;   // SLIDE: when a new reply is needed, prefer a slide to a jump
// fraction (in 1/1000) of losses among the neighbours of a position (one empty square moved from one gap to
// another) whose race count is not better for Right
int robust(int c, const Gp& q) { int a0 = abOf(c, q), tot = 0, los = 0; for (int i = 0; i < 7; i++) if (q[i] > 0) for (int j = 0; j < 7; j++) if (j != i) { Gp z = q; z[i]--; z[j]++; if (abOf(c, z) < a0) continue; tot++; if (!xLF(c, z)) los++; }
  return tot ? 1000 * los / tot : 1000; }
template <class F> void forAll(int Smax, F f) { Gp g; function<void(int,int)> rec = [&](int k, int rem) { if (k == 6) { for (int x = max(0, rem - (Smax - NMIN)); x <= rem; x++) { g[6] = x; f(g); } return; } for (int x = 0; x <= rem; x++) { g[k] = x; rec(k + 1, rem - x); } }; rec(0, Smax); }
int main(int argc, char** argv) { initS(atoi(argv[1])); if (getenv("NMIN")) NMIN = atoi(getenv("NMIN")); if (getenv("ROBUST")) ROBUST = atoi(getenv("ROBUST")); if (getenv("EXCL")) EXCL = atoi(getenv("EXCL")); if (getenv("SLIDE")) SLIDE = atoi(getenv("SLIDE")); long WCAP = getenv("WCAP") ? atol(getenv("WCAP")) : 1000000000L; string out = argc > 2 ? argv[2] : ""; int MAXR = getenv("MAXR") ? atoi(getenv("MAXR")) : 1000;
  int prio[6] = {0, 1, 2, 3, 4, 5}; if (getenv("WB")) WB = atoi(getenv("WB")); if (getenv("LR")) LR = atoi(getenv("LR")); if (getenv("SHORT")) SHORT = atoi(getenv("SHORT")); if (getenv("HC")) HC = atoi(getenv("HC")); if (getenv("SUBN")) SUBN = atoi(getenv("SUBN")); if (getenv("LRGAIN")) LRGAIN = atof(getenv("LRGAIN")); int FR = getenv("FR") ? atoi(getenv("FR")) : 1, NZ2 = getenv("NZ2") ? atoi(getenv("NZ2")) : 3; if (getenv("PRIO")) for (int i = 0; i < 6; i++) prio[i] = getenv("PRIO")[i] - '0';
  { array<int,7> f; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0, first = 0; for (int x : f) if (x) { nz++; if (!first) first = x; } int gg = 0, mx = 0; for (int x : f) { gg = __gcd(gg, abs(x)); mx = max(mx, abs(x)); } if (!nz || first < 0 || gg != 1) return; if (mx > 1 && nz > NZ2) return; forms.push_back({f}); return; }
      for (int x = -FR; x <= FR; x++) { f[k] = x; rec(k + 1); } }; rec(0); }
  // forms with small coefficients in the positions of the pieces (L_i = g_0 + ... + g_i) and the board size N
  if (getenv("PFR")) { int PFR = atoi(getenv("PFR")), PNZ = getenv("PNZ") ? atoi(getenv("PNZ")) : 3; set<array<int,7>> have; for (auto& F : forms) have.insert(F.f);
    array<int,7> c; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0; for (int x : c) if (x) nz++; if (!nz || nz > PNZ) return; array<int,7> f; f.fill(0);
        for (int i = 0; i < 6; i++) for (int j = 0; j <= i; j++) f[j] += c[i]; for (int j = 0; j < 7; j++) f[j] += c[6];
        int gg = 0, first = 0; for (int x : f) { gg = __gcd(gg, abs(x)); if (x && !first) first = x; } if (!gg) return; for (int& x : f) x /= gg; if (first < 0) for (int& x : f) x = -x;
        if (have.insert(f).second) forms.push_back({f}); return; }
      for (int x = -PFR; x <= PFR; x++) { c[k] = x; rec(k + 1); } }; rec(0); }
  fprintf(stderr, "%zu forms\n", forms.size());
  SL.resize(20 * 33); for (int oi = 0; oi < 20; oi++) for (int a = -ABOFF; a <= ABOFF; a++) { SL[oi * 33 + a + ABOFF].c = ords[oi]; SL[oi * 33 + a + ABOFF].ab = a; }
  for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; forAll(S, [&](const Gp& g) { int ab = abOf(c, g); if (abs(ab) > 12) return; if (xLF(c, g)) { P7 p; for (int i = 0; i < 7; i++) p.g[i] = g[i]; Slice& s = sliceOf(c, ab); s.nw++; if ((long)s.wins.size() < WCAP) s.wins.push_back(p); else { long r = rng() % s.nw; if (r < WCAP) s.wins[r] = p; } } }); }
  fprintf(stderr, "tables ready\n");
  for (int m = max(5, NMIN - 1); m + 1 <= S; m++) { Gp s0 = {0, 0, 1, m, 0, 0, 0}; sliceOf(7, -1).pos.insert(s0); } sliceOf(7, -1).dirty = true;
  for (int round = 1; round <= MAXR; round++) {
    long relearned = 0; for (auto& s : SL) if (s.dirty) { learn(s); relearned++; }
    long added = 0, ing = 0;
    long impure = 0, excluded = 0;
    #pragma omp parallel for schedule(dynamic, 1) reduction(+:ing)
    for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; forAll(S, [&](const Gp& g) { int ab = abOf(c, g); if (abs(ab) > 12) return; Slice& s = sliceOf(c, ab); if (s.nodes.empty()) return;
        int8_t gg[7]; for (int i = 0; i < 7; i++) gg[i] = g[i]; if (!s.in(gg)) return; ing++;
        if (xLF(c, g)) { P7 p; memcpy(p.g, gg, 7);
          #pragma omp critical
          { s.wins.push_back(p); s.dirty = true; impure++; }
          return; }
        for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; bool ok = false; int bj = -1; int bc = 0; Gp bq; int bsc = -1;
          for (int jj = 0; jj < 6 && !ok; jj++) { int j = prio[jj]; int c3; Gp q; if (!rmc(c2, h, j, c3, q)) continue; if (xLF(c3, q)) continue;
            int8_t qq[7]; for (int k = 0; k < 7; k++) qq[k] = q[k]; int ab3 = abOf(c3, q); if (abs(ab3) <= 12 && sliceOf(c3, ab3).in(qq)) { ok = true; break; }
            if (abs(ab3) <= 12) { int sc = (ROBUST ? robust(c3, q) : 0) + (SLIDE && c3 == c2 ? 100000 : 0); if (bj < 0 || sc > bsc) { bj = j; bc = c3; bq = q; bsc = sc; } } }
          if (ok) continue; if (bj < 0) { fprintf(stderr, "invariant contains a Left win or leaves the window: %s (%d %d %d %d %d %d %d)\n", nm(c), g[0],g[1],g[2],g[3],g[4],g[5],g[6]); exit(1); }
          if (EXCL && !s.pos.count(g)) {   // a generalised position that cannot be answered inside the set: exclude it
            #pragma omp critical
            { s.excl.insert(g); s.dirty = true; excluded++; }
            return; }
          Slice& t = sliceOf(bc, abOf(bc, bq));
          #pragma omp critical
          { if (t.pos.insert(bq).second) { t.dirty = true; added++; } } } }); }
    long nsl = 0, leaves = 0, npos = 0; for (auto& s : SL) if (!s.pos.empty()) { nsl++; leaves += s.leavesIn; npos += s.pos.size(); }
    fprintf(stderr, "round %d: relearned %ld, invariant %ld positions, added %ld, impure %ld, excluded %ld; %ld slices, %ld in-leaves, %ld POS\n", round, relearned, ing, added, impure, excluded, nsl, leaves, npos);
    if (!added && !impure && !excluded) { printf("closed on S=%d: %ld slices, %ld in-leaves, %ld positions\n", S, nsl, leaves, ing); break; } }
  for (auto& s : SL) if (!s.pos.empty()) printf("%s ab %3d: %7zu POS, %7zu wins, %4d in-leaves\n", nm(s.c), s.ab, s.pos.size(), s.wins.size(), s.leavesIn);
  if (!out.empty()) { FILE* fo = fopen(out.c_str(), "w"); for (auto& s : SL) if (!s.nodes.empty()) { fprintf(fo, "slice %d %d %zu\n", s.c, s.ab, s.nodes.size());
      for (size_t i = 0; i < s.nodes.size(); i++) { auto& n = s.nodes[i]; if (n.leaf == 1) fprintf(fo, "%zu leaf 1\n", i); else if (n.leaf == 0) { fprintf(fo, "%zu leaf 0", i); for (int k = 0; k < 7; k++) fprintf(fo, " %d %d", n.lo[k], n.hi[k]); fprintf(fo, "\n"); } else { auto& f = n.t.f; fprintf(fo, "%zu test %d %d %d %d %d %d %d %d %d %d %d %d\n", i, n.t.kind, f[0], f[1], f[2], f[3], f[4], f[5], f[6], n.t.m, n.t.v, n.yes, n.no); } } }
    fclose(fo); } }
