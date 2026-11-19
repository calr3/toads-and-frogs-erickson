#include "ex6.h"
#include <omp.h>
// Invariant search by separation ("interpolation") on exact data with NMIN <= N <= S empty squares.
//   W_0 = all Left-first losses (race count within +-12).
//   R_k = positions reached from the starts TT.T.^m FFF when Right always replies inside W_k, choosing the reply
//         with the most neighbours in W_k (deepest inside).
//   G_{k+1} = one decision tree per slice (piece order, race count) that keeps R_k and excludes every position
//         outside W_k; the positions of W_k not in R_k are "don't care".
//   W_{k+1} = the largest subset of G_{k+1} closed under "every Left move has a Right reply in the set".
// Stops when G_k = W_k: then G_k is closed on the data.   Usage: itp6 S [OUT]   env: NMIN, MAXR, FR, NZ2
struct Form { array<int,7> f; };
vector<Form> forms;
struct Test { int form, kind, m, v; };
static inline long evalF(const array<int,7>& f, const int8_t* g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
static inline bool evalT(const Test& t, const int8_t* g) { long x = evalF(forms[t.form].f, g); if (t.kind == 0) return x >= t.v; return ((x % t.m) + t.m) % t.m == t.v; }
struct Node { Test t; int yes = -1, no = -1, leaf = -1; };
const int VR = 34;
struct Row { int8_t g[7]; int8_t w; };
struct Slice { int c, ab; vector<Row> rows; vector<Node> nodes; int leavesIn = 0; long nkeep = 0;
  bool in(const int8_t* g) const { if (nodes.empty()) return false; int id = 0; while (nodes[id].leaf < 0) id = evalT(nodes[id].t, g) ? nodes[id].yes : nodes[id].no; return nodes[id].leaf == 0; } };
const int ABM = 12; vector<Slice> SL;
static inline Slice& sliceOf(int c, int ab) { return SL[ordOf[c] * (2 * ABM + 1) + ab + ABM]; }
int build(vector<Node>& nodes, const vector<Row>& rows, vector<int>& idx) {
  long n = idx.size(), nw = 0; for (int r : idx) nw += rows[r].w;
  int id = nodes.size(); nodes.push_back(Node());
  if (nw == 0 || nw == n) { nodes[id].leaf = nw > 0; return id; }
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
  vector<int>().swap(idx); nodes[id].t = t; int a = build(nodes, rows, y); int b = build(nodes, rows, no); nodes[id].yes = a; nodes[id].no = b; return id; }
int NMIN = 0, KEEPDEEP = 0;
template <class F> void forAll(F f) { Gp g; function<void(int,int)> rec = [&](int k, int rem) { if (k == 6) { for (int x = max(0, rem - (S - NMIN)); x <= rem; x++) { g[6] = x; f(g); } return; } for (int x = 0; x <= rem; x++) { g[k] = x; rec(k + 1, rem - x); } }; rec(0, S); }
vector<uint8_t> wst;   // bit 0: W known, bit 1: in W, bit 2: in R
int round_ = 0;
bool inG(int c, const Gp& g) { int ab = abOf(c, g); if (abs(ab) > ABM) return false; if (round_ == 0) return !xLF(c, g); int8_t gg[7]; for (int i = 0; i < 7; i++) gg[i] = g[i]; return sliceOf(c, ab).in(gg); }
bool inW(int c, const Gp& g) { long e = idx(c, g); if (wst[e] & 1) return wst[e] & 2; bool r = inG(c, g);
  if (r && round_ > 0) for (int i = 0; i < 6 && r; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; bool ok = false; for (int j = 0; j < 6 && !ok; j++) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && inW(c3, q)) ok = true; } if (!ok) r = false; }
  wst[e] = (wst[e] & ~3) | 1 | (r ? 2 : 0); return r; }
int depth(int c, const Gp& q) { int tot = 0, in = 0; for (int i = 0; i < 7; i++) if (q[i] > 0) for (int j = 0; j < 7; j++) if (j != i) { Gp z = q; z[i]--; z[j]++; tot++; if (inW(c, z)) in++; } return tot ? 1000 * in / tot : 1000; }
int main(int argc, char** argv) { initS(atoi(argv[1])); string out = argc > 2 ? argv[2] : ""; if (getenv("NMIN")) NMIN = atoi(getenv("NMIN")); if (getenv("KEEPDEEP")) KEEPDEEP = atoi(getenv("KEEPDEEP")); int MAXR = getenv("MAXR") ? atoi(getenv("MAXR")) : 200;
  int FR = getenv("FR") ? atoi(getenv("FR")) : 1, NZ2 = getenv("NZ2") ? atoi(getenv("NZ2")) : 3;
  { array<int,7> f; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0, first = 0, gg = 0, mx = 0; for (int x : f) { if (x) { nz++; if (!first) first = x; } gg = __gcd(gg, abs(x)); mx = max(mx, abs(x)); } if (!nz || first < 0 || gg != 1) return; if (mx > 1 && nz > NZ2) return; forms.push_back({f}); return; }
      for (int x = -FR; x <= FR; x++) { f[k] = x; rec(k + 1); } }; rec(0); }
  SL.resize(20 * (2 * ABM + 1)); for (int oi = 0; oi < 20; oi++) for (int a = -ABM; a <= ABM; a++) { sliceOf(ords[oi], a).c = ords[oi]; sliceOf(ords[oi], a).ab = a; }
  wst.assign(st.size(), 0);
  for (round_ = 0; round_ <= MAXR; round_++) {
    // W_k (lazily, by recursion) and, for k > 0, the comparison of G_k with W_k
    for (auto& x : wst) x = 0;
    long ng = 0, nwk = 0;
    if (round_ > 0) for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; forAll([&](const Gp& g) { if (!inG(c, g)) return; ng++; if (inW(c, g)) nwk++; }); }
    // R_k
    vector<pair<int,Gp>> stk; long nr = 0;
    for (int m = max(5, NMIN - 1); m + 1 <= S; m++) { Gp s0 = {0, 0, 1, m, 0, 0, 0}; if (!inW(7, s0)) { printf("start m=%d is not in W_%d: failed\n", m, round_); return 1; } wst[idx(7, s0)] |= 4; stk.push_back({7, s0}); nr++; }
    while (!stk.empty()) { auto [c, g] = stk.back(); stk.pop_back();
      for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; int bs = -1, bc = 0; Gp bq;
        for (int j = 0; j < 6; j++) { int c3; Gp q; if (!rmc(c2, h, j, c3, q) || !inW(c3, q)) continue; int sc = 2 * depth(c3, q) + ((wst[idx(c3, q)] & 4) ? 1 : 0); if (sc > bs) { bs = sc; bc = c3; bq = q; } }
        if (bs < 0) { fprintf(stderr, "internal error: no reply in W\n"); return 1; }
        long e = idx(bc, bq); if (!(wst[e] & 4)) { wst[e] |= 4; stk.push_back({bc, bq}); nr++; } } }
    long nsl = 0, leaves = 0; for (auto& s : SL) if (!s.nodes.empty()) { nsl++; leaves += s.leavesIn; }
    fprintf(stderr, "round %d: G %ld, W %ld, R %ld; %ld slices, %ld in-leaves\n", round_, ng, nwk, nr, nsl, leaves);
    if (round_ > 0 && ng == nwk) { printf("closed on %d..%d empty squares: %ld slices, %ld in-leaves, %ld positions, %ld reached\n", NMIN, S, nsl, leaves, ng, nr); break; }
    // learn G_{k+1}: keep R_k, exclude everything outside W_k, in the slices that R_k meets
    for (auto& s : SL) { s.rows.clear(); s.nkeep = 0; }
    for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; forAll([&](const Gp& g) { int ab = abOf(c, g); if (abs(ab) > ABM) return; if ((wst[idx(c, g)] & 4) || (KEEPDEEP && inW(c, g) && depth(c, g) >= KEEPDEEP)) sliceOf(c, ab).nkeep++; }); }
    for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; forAll([&](const Gp& g) { int ab = abOf(c, g); if (abs(ab) > ABM) return; Slice& s = sliceOf(c, ab); if (!s.nkeep) return;
        bool keep = wst[idx(c, g)] & 4, w = inW(c, g); if (!keep && w && KEEPDEEP && depth(c, g) >= KEEPDEEP) keep = true; if (!keep && w) return; Row r; for (int i = 0; i < 7; i++) r.g[i] = g[i]; r.w = !keep; s.rows.push_back(r); }); }
    for (auto& s : SL) { s.nodes.clear(); s.leavesIn = 0; if (!s.nkeep) continue; vector<int> all(s.rows.size()); iota(all.begin(), all.end(), 0); build(s.nodes, s.rows, all); for (auto& n : s.nodes) if (n.leaf == 0) s.leavesIn++; vector<Row>().swap(s.rows); } }
  for (auto& s : SL) if (!s.nodes.empty()) printf("%s ab %3d: %7ld reached, %4d in-leaves\n", nm(s.c), s.ab, s.nkeep, s.leavesIn);
  if (!out.empty()) { FILE* fo = fopen(out.c_str(), "w"); for (auto& s : SL) if (!s.nodes.empty()) { fprintf(fo, "slice %d %d %zu\n", s.c, s.ab, s.nodes.size());
      for (size_t i = 0; i < s.nodes.size(); i++) { auto& n = s.nodes[i]; if (n.leaf >= 0) fprintf(fo, "%zu leaf %d\n", i, n.leaf); else { auto& f = forms[n.t.form].f; fprintf(fo, "%zu test %d %d %d %d %d %d %d %d %d %d %d %d\n", i, n.t.kind, f[0], f[1], f[2], f[3], f[4], f[5], f[6], n.t.m, n.t.v, n.yes, n.no); } } }
    fclose(fo); } }
