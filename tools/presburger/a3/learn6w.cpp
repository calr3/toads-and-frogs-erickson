#include "ex6.h"
#include <omp.h>
// Decision-tree learner for "Left moving first wins" of one piece order (three toads, three frogs), on the
// domain of the invariant: race count in [-p - 1, p + 1] (p = passed pairs); for TTTFFF, centre gap <= 1 and
// race count in [-1, 0].  Tests: F(g) >= v, F(g) mod m == r (m = 2, 3), ab >= v, for linear forms F of the gaps.
// Usage: learn6 SL SV ORDER   (learn on at most SL empty squares, validate on at most SV)
// env: FR2=1 adds forms with a coefficient 2 (at most NZ2 nonzero), EXPORT=file, PRINT=1, ERR=1
int passings(int c) { int n = 0; for (int i = 0; i < 6; i++) for (int j = 0; j < i; j++) if (toad(c, i) && !toad(c, j)) n++; return n; }
int CC, PP; set<Gp> RSET; bool useR = false; int RLO = 99, RHI = -99;
bool lab(const Gp& g) { return useR ? !RSET.count(g) : xLF(CC, g); }
bool inDom(const Gp& g, int ab) { if (useR) return ab >= RLO && ab <= RHI; if (CC == 7) return g[3] <= 1 && ab >= -1 && ab <= 0; return ab >= -PP - 1 && ab <= PP + 1; }
struct Form { array<int,7> f; string name; };
vector<Form> forms;   // forms[0] is the race count
struct Test { int form, kind, m, v; };  // kind 0: F >= v; kind 1: F mod m == v
string tname(const Test& t) { return forms[t.form].name + (t.kind == 0 ? ">=" + to_string(t.v) : "%" + to_string(t.m) + "==" + to_string(t.v)); }
struct Row { int8_t g[7]; int8_t w; };
vector<Row> rows;
static inline long evalF(const array<int,7>& f, const int8_t* g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
static inline bool evalT(const Test& t, const int8_t* g) { long x = evalF(forms[t.form].f, g); if (t.kind == 0) return x >= t.v; return ((x % t.m) + t.m) % t.m == t.v; }
struct Node { Test t; int yes = -1, no = -1, leaf = -1; long n = 0; };
vector<Node> nodes;
const int VR = 10;   // thresholds -VR+1 .. VR
int build(vector<int>& idx, int depth) {
  long n = idx.size(), nw = 0; for (int r : idx) nw += rows[r].w;
  int id = nodes.size(); nodes.push_back(Node()); nodes[id].n = n;
  if (nw == 0 || nw == n || depth > 60) { nodes[id].leaf = nw * 2 > n; if (nw && nw != n) fprintf(stderr, "depth limit\n"); return id; }
  int NF = forms.size(); vector<double> bsc(NF, 1e18); vector<Test> bt(NF);
  #pragma omp parallel for schedule(dynamic, 8)
  for (int fi = 0; fi < NF; fi++) { long cnt[2 * VR + 3] = {0}, cw[2 * VR + 3] = {0}, m6[6] = {0}, w6[6] = {0};
    for (int r : idx) { long x = evalF(forms[fi].f, rows[r].g); int b = x < -VR ? 0 : x > VR ? 2 * VR + 2 : (int)(x + VR + 1); cnt[b]++; cw[b] += rows[r].w; int q = ((x % 6) + 6) % 6; m6[q]++; w6[q] += rows[r].w; }
    auto score = [&](long a, long aw) -> double { long b = n - a, bw = nw - aw; if (a == 0 || b == 0) return 1e18;
      return a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b; };
    long a = 0, aw = 0;  // F >= v: buckets with x >= v
    a = cnt[2 * VR + 2]; aw = cw[2 * VR + 2]; for (int v = VR; v >= -VR + 1; v--) { int b = v + VR + 1; a += cnt[b]; aw += cw[b]; double s = score(a, aw); if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 0, 0, v}; } }
    if (fi > 0) { for (int r = 0; r < 2; r++) { long a2 = m6[r] + m6[r + 2] + m6[r + 4], w2 = w6[r] + w6[r + 2] + w6[r + 4]; double s = score(a2, w2) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 2, r}; } }
      for (int r = 0; r < 3; r++) { long a3 = m6[r] + m6[r + 3], w3 = w6[r] + w6[r + 3]; double s = score(a3, w3) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 3, r}; } } } }
  int best = -1; for (int fi = 0; fi < NF; fi++) if (bsc[fi] < 1e17 && (best < 0 || bsc[fi] + 1e-9 * fi < bsc[best] + 1e-9 * best)) best = fi;
  if (best < 0) { nodes[id].leaf = nw * 2 > n; fprintf(stderr, "no split, impure %ld/%ld\n", nw, n); return id; }
  Test t = bt[best]; vector<int> y, no; for (int r : idx) (evalT(t, rows[r].g) ? y : no).push_back(r);
  vector<int>().swap(idx); nodes[id].t = t; int a = build(y, depth + 1); int b = build(no, depth + 1); nodes[id].yes = a; nodes[id].no = b; return id; }
bool predict(const int8_t* g) { int id = 0; while (nodes[id].leaf < 0) id = evalT(nodes[id].t, g) ? nodes[id].yes : nodes[id].no; return nodes[id].leaf; }
void print(int id, int ind) { if (nodes[id].leaf >= 0) { printf("%*s%s (%ld)\n", ind, "", nodes[id].leaf ? "WIN" : "LOSS", nodes[id].n); return; }
  printf("%*sif %s:\n", ind, "", tname(nodes[id].t).c_str()); print(nodes[id].yes, ind + 2); printf("%*selse:\n", ind, ""); print(nodes[id].no, ind + 2); }
template <class F> void forAll(int Smax, F f) { Gp g; function<void(int,int)> rec = [&](int k, int rem) { if (k == 7) { f(g); return; } for (int x = 0; x <= rem; x++) { g[k] = x; rec(k + 1, rem - x); } }; rec(0, Smax); }
int main(int argc, char** argv) { int SL = atoi(argv[1]), SV = atoi(argv[2]); CC = atoi(argv[3]); PP = passings(CC); initS(SV);
  if (getenv("RFILE")) { useR = true; FILE* f = fopen(getenv("RFILE"), "r"); int c; Gp g; while (fscanf(f, "%d %d %d %d %d %d %d %d", &c, &g[0], &g[1], &g[2], &g[3], &g[4], &g[5], &g[6]) == 8) if (c == CC) { RSET.insert(g); int a = abOf(CC, g); RLO = min(RLO, a); RHI = max(RHI, a); } fclose(f); }
  { Form ab; for (int k = 0; k < 7; k++) ab.f[k] = coef(CC, k); ab.name = "ab"; forms.push_back(ab); }
  int FR2 = getenv("FR2") ? atoi(getenv("FR2")) : 0, NZ2 = getenv("NZ2") ? atoi(getenv("NZ2")) : 3; int R = FR2 ? 2 : 1;
  { array<int,7> f; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0, first = 0, gg = 0, mx = 0; for (int x : f) { if (x) { nz++; if (!first) first = x; } gg = __gcd(gg, abs(x)); mx = max(mx, abs(x)); }
        if (!nz || first < 0 || gg != 1) return; if (mx > 1 && nz > NZ2) return; Form F; F.f = f; string s; for (int i = 0; i < 7; i++) if (f[i]) { if (f[i] > 0 && !s.empty()) s += "+"; if (f[i] == -1) s += "-"; else if (f[i] != 1) s += to_string(f[i]); s += "g" + to_string(i); } F.name = s; forms.push_back(F); return; }
      for (int x = -R; x <= R; x++) { f[k] = x; rec(k + 1); } }; rec(0); }
  fprintf(stderr, "%zu forms\n", forms.size());
  forAll(SL, [&](const Gp& g) { int ab = abOf(CC, g); if (!inDom(g, ab)) return; Row r; for (int i = 0; i < 7; i++) r.g[i] = g[i]; r.w = lab(g); rows.push_back(r); });
  long nw = 0; for (auto& r : rows) nw += r.w; fprintf(stderr, "%zu rows, %ld wins\n", rows.size(), nw);
  vector<int> all(rows.size()); iota(all.begin(), all.end(), 0); build(all, 0);
  long leaves = 0; for (auto& n : nodes) if (n.leaf >= 0) leaves++;
  long err = 0, tot = 0; forAll(SV, [&](const Gp& g) { int ab = abOf(CC, g); if (!inDom(g, ab)) return; int8_t gg[7]; for (int i = 0; i < 7; i++) gg[i] = g[i]; tot++;
    if (predict(gg) != lab(g)) { err++; if (getenv("ERR") && err <= 20) printf("err (%d %d %d %d %d %d %d) ab %d actual %d\n", g[0],g[1],g[2],g[3],g[4],g[5],g[6], ab, (int)lab(g)); } });
  printf("%s p=%d: %zu rows (%ld wins), %ld leaves; validation S=%d: %ld errors of %ld\n", nm(CC), PP, rows.size(), nw, leaves, SV, err, tot); fflush(stdout);
  if (getenv("PRINT")) print(0, 0);
  if (getenv("EXPORT")) { FILE* fo = fopen(getenv("EXPORT"), "w"); fprintf(fo, "%d %zu\n", CC, nodes.size());
    for (size_t i = 0; i < nodes.size(); i++) { auto& n = nodes[i]; if (n.leaf >= 0) fprintf(fo, "%zu leaf %d\n", i, n.leaf); else { auto& f = forms[n.t.form].f; fprintf(fo, "%zu test %d %d %d %d %d %d %d %d %d %d %d %d\n", i, n.t.kind, f[0], f[1], f[2], f[3], f[4], f[5], f[6], n.t.m, n.t.v, n.yes, n.no); } }
    fclose(fo); } }
