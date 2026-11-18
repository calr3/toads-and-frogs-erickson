#include <bits/stdc++.h>
#include <omp.h>
using namespace std;
// Decision-tree learner on the sampled files written by gen7: learn on N in [NA, NB], validate on [NC, ND].
// Usage: learnf FILE ORDER NA NB NC ND    env: FR (largest coefficient, default 1), NZ2 (nonzeros when a
// coefficient exceeds 1, default 3), MAXLEAF (stop after this many leaves, best-first), EXPORT=file, PRINT=1
static inline bool toad(int c, int i) { return (c >> i) & 1; }
static int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 6; i++) if (!toad(c, i)) fr++; return tl - fr; }
struct Form { array<int,7> f; string name; };
vector<Form> forms;
struct Test { int form, kind, m, v; array<int,7> f; };
string fstr(const array<int,7>& f) { string s; for (int i = 0; i < 7; i++) if (f[i]) { if (f[i] > 0 && !s.empty()) s += "+"; if (f[i] == -1) s += "-"; else if (f[i] != 1) s += to_string(f[i]); s += "g" + to_string(i); } return s; }
string tname(const Test& t) { return (t.form == 0 ? string("ab") : fstr(t.f)) + (t.kind == 0 ? ">=" + to_string(t.v) : "%" + to_string(t.m) + "==" + to_string(t.v)); }
struct Row { int8_t g[7]; int8_t w; };
vector<Row> rows, vrows;
static inline long evalF(const array<int,7>& f, const int8_t* g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
static inline bool evalT(const Test& t, const int8_t* g) { long x = evalF(t.f, g); if (t.kind == 0) return x >= t.v; return ((x % t.m) + t.m) % t.m == t.v; }
struct Node { Test t; int yes = -1, no = -1, leaf = -1; long n = 0, nw = 0; vector<int> idx; double gain = -1; };
vector<Node> nodes;
const int VR = 60; int HC = 0;
void bestSplit(Node& nd) { long n = nd.idx.size(), nw = nd.nw; nd.gain = -1; if (nw == 0 || nw == n) return;
  int NF = forms.size(); vector<double> bsc(NF, 1e18); vector<Test> bt(NF);
  #pragma omp parallel for schedule(dynamic, 8)
  for (int fi = 0; fi < NF; fi++) { long cnt[2 * VR + 3] = {0}, cw[2 * VR + 3] = {0}, m6[6] = {0}, w6[6] = {0};
    for (int r : nd.idx) { long x = evalF(forms[fi].f, rows[r].g); int b = x < -VR ? 0 : x > VR ? 2 * VR + 2 : (int)(x + VR + 1); cnt[b]++; cw[b] += rows[r].w; int q = ((x % 6) + 6) % 6; m6[q]++; w6[q] += rows[r].w; }
    auto score = [&](long a, long aw) -> double { long b = n - a, bw = nw - aw; if (a == 0 || b == 0) return 1e18;
      return a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b; };
    long a = cnt[2 * VR + 2], aw = cw[2 * VR + 2];
    for (int v = VR; v >= -VR + 1; v--) { int b = v + VR + 1; a += cnt[b]; aw += cw[b]; double s = score(a, aw); if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 0, 0, v, forms[fi].f}; } }
    if (fi > 0) { for (int r = 0; r < 2; r++) { long a2 = m6[r] + m6[r + 2] + m6[r + 4], w2 = w6[r] + w6[r + 2] + w6[r + 4]; double s = score(a2, w2) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 2, r, forms[fi].f}; } }
      for (int r = 0; r < 3; r++) { long a3 = m6[r] + m6[r + 3], w3 = w6[r] + w6[r + 3]; double s = score(a3, w3) + 1e-7; if (s < bsc[fi]) { bsc[fi] = s; bt[fi] = {fi, 1, 3, r, forms[fi].f}; } } } }
  int best = -1; for (int fi = 0; fi < NF; fi++) if (bsc[fi] < 1e17 && (best < 0 || bsc[fi] + 1e-9 * fi < bsc[best] + 1e-9 * best)) best = fi;
  if (best < 0) return; nd.t = bt[best]; double bestsc = bsc[best];
  if (HC && nd.t.kind == 0) { const vector<int>& idx = nd.idx; vector<int> sub; if (n > 30000) { sub.resize(30000); for (int i = 0; i < 30000; i++) sub[i] = idx[((unsigned long)i * 2654435761UL) % n]; } else sub = idx;
    long sn = sub.size(), sw = 0; for (int r : sub) sw += rows[r].w;
    auto eval = [&](const array<int,7>& f, const vector<int>& set, long tn, long tw, int& bv) -> double { long lo = LONG_MAX, hi = LONG_MIN; vector<long> xs(set.size());
      for (size_t i = 0; i < set.size(); i++) { xs[i] = evalF(f, rows[set[i]].g); lo = min(lo, xs[i]); hi = max(hi, xs[i]); }
      vector<long> cnt(hi - lo + 2, 0), cw(hi - lo + 2, 0); for (size_t i = 0; i < set.size(); i++) { cnt[xs[i] - lo]++; cw[xs[i] - lo] += rows[set[i]].w; }
      double bs = 1e18; long a = 0, aw = 0; for (long v = hi; v > lo; v--) { a += cnt[v - lo]; aw += cw[v - lo]; long b = tn - a, bw = tw - aw; if (!a || !b) continue;
        double sc = a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a + b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b; if (sc < bs) { bs = sc; bv = (int)v; } }
      return bs; };
    array<int,7> f = nd.t.f; int bv = nd.t.v; double cur = eval(f, sub, sn, sw, bv); bool improved = true; int passes = 0;
    while (improved && passes++ < 15) { improved = false; double bestc = cur; array<int,7> bf = f;
      #pragma omp parallel for schedule(dynamic, 1)
      for (int kd = 0; kd < 14; kd++) { int k = kd / 2, d = kd % 2 ? 1 : -1; array<int,7> f2 = f; f2[k] += d; if (abs(f2[k]) > HC) continue; int gg = 0; for (int x : f2) gg = __gcd(gg, abs(x)); if (gg != 1) continue;
        int v2; double sc = eval(f2, sub, sn, sw, v2);
        #pragma omp critical
        if (sc < bestc - 1e-9) { bestc = sc; bf = f2; } }
      if (bestc < cur * 0.995) { cur = bestc; f = bf; improved = true; } }
    if (f != nd.t.f) { int v2 = 0; double full = eval(f, idx, n, nw, v2); if (full < bestsc) { bestsc = full; nd.t = {-1, 0, 0, v2, f}; } } }
  double imp = n - (double)nw * nw / n - (double)(n - nw) * (n - nw) / n; nd.gain = imp - bestsc; }
bool predict(const int8_t* g) { int id = 0; while (nodes[id].leaf < 0) id = evalT(nodes[id].t, g) ? nodes[id].yes : nodes[id].no; return nodes[id].leaf; }
void print(int id, int ind) { if (nodes[id].leaf >= 0) { printf("%*s%s (%ld/%ld)\n", ind, "", nodes[id].leaf ? "WIN" : "LOSS", nodes[id].nw, nodes[id].n); return; }
  printf("%*sif %s:\n", ind, "", tname(nodes[id].t).c_str()); print(nodes[id].yes, ind + 2); printf("%*selse:\n", ind, ""); print(nodes[id].no, ind + 2); }
int main(int argc, char** argv) { int CC = atoi(argv[2]), NA = atoi(argv[3]), NB = atoi(argv[4]), NC = atoi(argv[5]), ND = atoi(argv[6]);
  if (getenv("HC")) HC = atoi(getenv("HC"));
  int FR = getenv("FR") ? atoi(getenv("FR")) : 1, NZ2 = getenv("NZ2") ? atoi(getenv("NZ2")) : 3; long MAXLEAF = getenv("MAXLEAF") ? atol(getenv("MAXLEAF")) : 1000000;
  { Form ab; for (int k = 0; k < 7; k++) ab.f[k] = coef(CC, k); ab.name = "ab"; forms.push_back(ab); }
  { array<int,7> f; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0, first = 0, gg = 0, mx = 0; for (int x : f) { if (x) { nz++; if (!first) first = x; } gg = __gcd(gg, abs(x)); mx = max(mx, abs(x)); }
        if (!nz || first < 0 || gg != 1) return; if (mx > 1 && nz > NZ2) return; Form F; F.f = f; string s; for (int i = 0; i < 7; i++) if (f[i]) { if (f[i] > 0 && !s.empty()) s += "+"; if (f[i] == -1) s += "-"; else if (f[i] != 1) s += to_string(f[i]); s += "g" + to_string(i); } F.name = s; forms.push_back(F); return; }
      for (int x = -FR; x <= FR; x++) { f[k] = x; rec(k + 1); } }; rec(0); }
  if (getenv("PFR")) { int PFR = atoi(getenv("PFR")), PNZ = getenv("PNZ") ? atoi(getenv("PNZ")) : 3; set<array<int,7>> have; for (auto& F : forms) have.insert(F.f);
    array<int,7> c; function<void(int)> rec = [&](int k) { if (k == 7) { int nz = 0; for (int x : c) if (x) nz++; if (!nz || nz > PNZ) return; array<int,7> f; f.fill(0);
        for (int i = 0; i < 6; i++) for (int j = 0; j <= i; j++) f[j] += c[i]; for (int j = 0; j < 7; j++) f[j] += c[6];
        int gg = 0, first = 0; for (int x : f) { gg = __gcd(gg, abs(x)); if (x && !first) first = x; } if (!gg) return; for (int& x : f) x /= gg; if (first < 0) for (int& x : f) x = -x;
        if (have.insert(f).second) { Form F; F.f = f; string s2; for (int i = 0; i < 7; i++) if (f[i]) { if (f[i] > 0 && !s2.empty()) s2 += "+"; if (f[i] == -1) s2 += "-"; else if (f[i] != 1) s2 += to_string(f[i]); s2 += "g" + to_string(i); } F.name = s2; forms.push_back(F); } return; }
      for (int x = -PFR; x <= PFR; x++) { c[k] = x; rec(k + 1); } }; rec(0); }
  FILE* fi = fopen(argv[1], "rb"); unsigned char b[9]; while (fread(b, 1, 9, fi) == 9) { Row r; for (int i = 0; i < 7; i++) r.g[i] = b[1 + i]; r.w = b[8]; if (b[0] >= NC && b[0] <= ND) vrows.push_back(r); else if (b[0] >= NA && b[0] <= NB) rows.push_back(r); } fclose(fi);
  fprintf(stderr, "%zu forms, %zu rows, %zu validation rows\n", forms.size(), rows.size(), vrows.size());
  nodes.reserve(4000000); nodes.push_back(Node()); nodes[0].idx.resize(rows.size()); iota(nodes[0].idx.begin(), nodes[0].idx.end(), 0); nodes[0].n = rows.size(); for (auto& r : rows) nodes[0].nw += r.w; bestSplit(nodes[0]);
  priority_queue<pair<double,int>> pq; if (nodes[0].gain > 0) pq.push({nodes[0].gain, 0}); long leaves = 1;
  auto report = [&]() { long err = 0, terr = 0; for (auto& r : vrows) if (predict(r.g) != r.w) err++; for (auto& n : nodes) if (n.yes < 0) terr += min(n.nw, n.n - n.nw);
    printf("%ld leaves: training errors %ld of %zu, validation errors %ld of %zu\n", leaves, terr, rows.size(), err, vrows.size()); fflush(stdout); };
  long nextRep = 25;
  while (!pq.empty() && leaves < MAXLEAF) { int id = pq.top().second; pq.pop(); Node& nd = nodes[id]; Test t = nd.t; int y = nodes.size(); nodes.push_back(Node()); int no = nodes.size(); nodes.push_back(Node());
    for (int r : nodes[id].idx) { Node& ch = nodes[evalT(t, rows[r].g) ? y : no]; ch.idx.push_back(r); ch.nw += rows[r].w; }
    for (int k : {y, no}) { nodes[k].n = nodes[k].idx.size(); nodes[k].leaf = nodes[k].nw * 2 > nodes[k].n; bestSplit(nodes[k]); if (nodes[k].gain > 0) pq.push({nodes[k].gain, k}); }
    vector<int>().swap(nodes[id].idx); nodes[id].yes = y; nodes[id].no = no; nodes[id].leaf = -1; leaves++;
    if (leaves == nextRep) { report(); nextRep *= 2; } }
  nodes[0].leaf = nodes[0].yes < 0 ? (nodes[0].nw * 2 > nodes[0].n) : -1; report();
  if (getenv("DIAG")) { map<array<int,3>, array<long,2>> m; map<int, array<long,2>> mm, mz;
    for (auto& r : vrows) { int ab = 0; for (int k = 0; k < 7; k++) ab += coef(CC, k) * r.g[k]; bool e = predict(r.g) != r.w; int mn = 99, nzero = 0; for (int k = 0; k < 7; k++) if (k != 3) { mn = min<int>(mn, r.g[k]); if (r.g[k] <= 1) nzero++; }
      auto& a = m[{ab, r.g[3], r.w}]; a[0]++; a[1] += e; auto& b = mm[min(mn, 6)]; b[0]++; b[1] += e; auto& z = mz[nzero]; z[0]++; z[1] += e; }
    for (auto& [k, a] : m) printf("ab %d g3 %d win %d: %ld rows, %ld errors (%.1f%%)\n", k[0], k[1], k[2], a[0], a[1], 100.0 * a[1] / a[0]);
    for (auto& [k, a] : mm) printf("min other gap %d: %ld rows, %.1f%% errors\n", k, a[0], 100.0 * a[1] / a[0]);
    for (auto& [k, a] : mz) printf("gaps <= 1 (other than g3): %d: %ld rows, %.1f%% errors\n", k, a[0], 100.0 * a[1] / a[0]); }
  if (getenv("PRINT")) print(0, 0);
  if (getenv("EXPORT")) { FILE* fo = fopen(getenv("EXPORT"), "w"); fprintf(fo, "%d %zu\n", CC, nodes.size());
    for (size_t i = 0; i < nodes.size(); i++) { auto& n = nodes[i]; if (n.leaf >= 0) fprintf(fo, "%zu leaf %d\n", i, n.leaf); else { auto& f = n.t.f; fprintf(fo, "%zu test %d %d %d %d %d %d %d %d %d %d %d %d\n", i, n.t.kind, f[0], f[1], f[2], f[3], f[4], f[5], f[6], n.t.m, n.t.v, n.yes, n.no); } }
    fclose(fo); } }
