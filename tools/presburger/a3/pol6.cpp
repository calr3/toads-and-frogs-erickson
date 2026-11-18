#include "ex6.h"
#include <omp.h>
// Learn a small policy for Right: for every piece order, a decision tree that maps the position after Left's
// move to one frog to move.  Loop: play the policy from every start TT.T.^m FFF (NMIN <= m + 1 <= S) against
// all Left moves; whenever the policy's reply is illegal or loses (exact play), record the position with its
// set of winning replies and continue with a winning reply; learn the trees again from all recorded positions
// (every leaf must have one reply that wins for all its positions); stop when a pass records nothing new.
// Usage: pol6 S [OUT]    env: NMIN, PFR, PNZ, MAXR
struct Form { array<int,7> f; };
vector<Form> forms;
struct Test { int kind, m, v; array<int,7> f; };
static inline long evalF(const array<int,7>& f, const int8_t* g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
static inline bool evalT(const Test& t, const int8_t* g) { long x = evalF(t.f, g); if (t.kind == 0) return x >= t.v; return ((x % t.m) + t.m) % t.m == t.v; }
struct Node { Test t; int yes = -1, no = -1, leaf = -1; };   // leaf: frog to move (piece index), -2 = no data
struct Row { int8_t g[7]; uint8_t mask; };
const int VR = 40;
struct Pol { vector<Node> nodes; vector<Row> rows; set<Gp> have; int leaves = 0; };
Pol P[64];
int build(vector<Node>& nodes, const vector<Row>& rows, vector<int>& idx) {
  long n = idx.size(); long cj[6] = {0}; for (int r : idx) for (int j = 0; j < 6; j++) if (rows[r].mask >> j & 1) cj[j]++;
  int id = nodes.size(); nodes.push_back(Node()); int bj = 0; for (int j = 1; j < 6; j++) if (cj[j] > cj[bj]) bj = j;
  if (cj[bj] == n) { nodes[id].leaf = bj; return id; }
  int NF = forms.size(); vector<double> bsc(NF, 1e18); vector<Test> bt(NF);
  #pragma omp parallel for schedule(dynamic, 8)
  for (int fi = 0; fi < NF; fi++) { static thread_local vector<array<int,7>> cnt, m6; cnt.assign(2 * VR + 3, array<int,7>{}); m6.assign(6, array<int,7>{});
    for (int r : idx) { long x = evalF(forms[fi].f, rows[r].g); int b = x < -VR ? 0 : x > VR ? 2 * VR + 2 : (int)(x + VR + 1); int q = ((x % 6) + 6) % 6; cnt[b][6]++; m6[q][6]++;
      for (int j = 0; j < 6; j++) if (rows[r].mask >> j & 1) { cnt[b][j]++; m6[q][j]++; } }
    auto err = [&](const array<long,7>& a) -> double { long mx = 0; for (int j = 0; j < 6; j++) mx = max(mx, a[j]); long mxb = 0; for (int j = 0; j < 6; j++) mxb = max(mxb, cj[j] - a[j]);
      long na = a[6], nb = n - a[6]; if (!na || !nb) return 1e18; return (double)(na - mx) + (nb - mxb) + 1e-3 * fabs((double)na - nb) / n; };
    array<long,7> a{}; for (int j = 0; j < 7; j++) a[j] = cnt[2 * VR + 2][j];
    for (int v = VR; v >= -VR + 1; v--) { int b = v + VR + 1; for (int j = 0; j < 7; j++) a[j] += cnt[b][j]; double s = err(a); if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {0, 0, v, forms[fi].f}; } }
    for (int r = 0; r < 2; r++) { array<long,7> b{}; for (int j = 0; j < 7; j++) b[j] = m6[r][j] + m6[r + 2][j] + m6[r + 4][j]; double s = err(b) + 1e-4; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {1, 2, r, forms[fi].f}; } }
    for (int r = 0; r < 3; r++) { array<long,7> b{}; for (int j = 0; j < 7; j++) b[j] = m6[r][j] + m6[r + 3][j]; double s = err(b) + 1e-4; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {1, 3, r, forms[fi].f}; } } }
  int best = -1; for (int fi = 0; fi < NF; fi++) if (bsc[fi] < 1e17 && (best < 0 || bsc[fi] < bsc[best])) best = fi;
  if (best < 0) { fprintf(stderr, "no split\n"); exit(1); }
  Test t = bt[best]; vector<int> y, no; for (int r : idx) (evalT(t, rows[r].g) ? y : no).push_back(r);
  vector<int>().swap(idx); nodes[id].t = t; int a = build(nodes, rows, y); int b = build(nodes, rows, no); nodes[id].yes = a; nodes[id].no = b; return id; }
int reply(int c, const Gp& h) { auto& nd = P[c].nodes; if (nd.empty()) return -1; int8_t g[7]; for (int i = 0; i < 7; i++) g[i] = h[i]; int id = 0; while (nd[id].leaf == -1) id = evalT(nd[id].t, g) ? nd[id].yes : nd[id].no; return nd[id].leaf; }
int main(int argc, char** argv) { initS(atoi(argv[1])); string out = argc > 2 ? argv[2] : ""; int NMIN = getenv("NMIN") ? atoi(getenv("NMIN")) : 6, MAXR = getenv("MAXR") ? atoi(getenv("MAXR")) : 200;
  { set<array<int,7>> have; array<int,7> f; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0, first = 0; for (int x : f) if (x) { nz++; if (!first) first = x; } if (!nz || first < 0) return; if (have.insert(f).second) forms.push_back({f}); return; }
      for (int x = -1; x <= 1; x++) { f[k] = x; rec(k + 1); } }; rec(0);
    int PFR = getenv("PFR") ? atoi(getenv("PFR")) : 2, PNZ = getenv("PNZ") ? atoi(getenv("PNZ")) : 3;
    array<int,7> c; function<void(int)> rec2 = [&](int k) { if (k == 7) { int nz = 0; for (int x : c) if (x) nz++; if (!nz || nz > PNZ) return; array<int,7> f; f.fill(0);
        for (int i = 0; i < 6; i++) for (int j = 0; j <= i; j++) f[j] += c[i]; for (int j = 0; j < 7; j++) f[j] += c[6];
        int gg = 0, first = 0; for (int x : f) { gg = __gcd(gg, abs(x)); if (x && !first) first = x; } if (!gg) return; for (int& x : f) x /= gg; if (first < 0) for (int& x : f) x = -x;
        if (have.insert(f).second) forms.push_back({f}); return; }
      for (int x = -PFR; x <= PFR; x++) { c[k] = x; rec2(k + 1); } }; rec2(0); }
  fprintf(stderr, "%zu forms\n", forms.size());
  for (int round = 1; round <= MAXR; round++) {
    set<pair<int,Gp>> seen; vector<pair<int,Gp>> stk; long added = 0, wrong = 0, moves = 0;
    for (int m = max(5, NMIN - 1); m + 1 <= S; m++) { Gp s0 = {0, 0, 1, m, 0, 0, 0}; seen.insert({7, s0}); stk.push_back({7, s0}); }
    while (!stk.empty()) { auto [c, g] = stk.back(); stk.pop_back();
      for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; moves++;
        int mask = 0, first = -1; for (int j = 0; j < 6; j++) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && !xLF(c3, q)) { mask |= 1 << j; if (first < 0) first = j; } }
        if (!mask) { fprintf(stderr, "reached a position that is not a loss\n"); return 1; }
        int j = reply(c2, h); if (j < 0 || !(mask >> j & 1)) { wrong++; if (P[c2].have.insert(h).second) { Row r; for (int k = 0; k < 7; k++) r.g[k] = h[k]; r.mask = mask; P[c2].rows.push_back(r); added++; } j = first; }
        else if (P[c2].have.insert(h).second) { Row r; for (int k = 0; k < 7; k++) r.g[k] = h[k]; r.mask = mask; P[c2].rows.push_back(r); }
        int c3; Gp q; rmc(c2, h, j, c3, q); if (seen.insert({c3, q}).second) stk.push_back({c3, q}); } }
    long leaves = 0, rows = 0;
    if (wrong) for (int oi = 0; oi < 20; oi++) { Pol& p = P[ords[oi]]; if (p.rows.empty()) continue; p.nodes.clear(); vector<int> all(p.rows.size()); iota(all.begin(), all.end(), 0); build(p.nodes, p.rows, all); p.leaves = 0; for (auto& n : p.nodes) if (n.leaf >= 0) p.leaves++; }
    for (int oi = 0; oi < 20; oi++) { leaves += P[ords[oi]].leaves; rows += P[ords[oi]].rows.size(); }
    fprintf(stderr, "round %d: reached %zu positions, %ld Left moves, policy wrong at %ld (%ld new); %ld recorded, %ld leaves\n", round, seen.size(), moves, wrong, added, rows, leaves);
    if (!wrong) { printf("policy wins every start with %d..%d empty squares: %ld leaves, %zu positions reached\n", NMIN, S, leaves, seen.size()); break; } }
  for (int oi = 0; oi < 20; oi++) if (P[ords[oi]].leaves) printf("%s: %d leaves, %zu recorded\n", nm(ords[oi]), P[ords[oi]].leaves, P[ords[oi]].rows.size());
  if (!out.empty()) { FILE* fo = fopen(out.c_str(), "w"); for (int oi = 0; oi < 20; oi++) { auto& nd = P[ords[oi]].nodes; if (nd.empty()) continue; fprintf(fo, "order %d %zu\n", ords[oi], nd.size());
      for (size_t i = 0; i < nd.size(); i++) { auto& n = nd[i]; if (n.leaf != -1) fprintf(fo, "%zu leaf %d\n", i, n.leaf); else { auto& f = n.t.f; fprintf(fo, "%zu test %d %d %d %d %d %d %d %d %d %d %d %d\n", i, n.t.kind, f[0], f[1], f[2], f[3], f[4], f[5], f[6], n.t.m, n.t.v, n.yes, n.no); } } }
    fclose(fo); } }
