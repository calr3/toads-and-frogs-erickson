// Decision-tree learner for "Left moving first wins" in positions with three toads and three frogs (7 gaps).
// usage: learn6 SL SV order [ABLO ABHI]   env: G3MAX (centre gap bound), PRINT, EXPORT=file, NZ2 (max nonzeros of forms with a coefficient 2)
#include "ex6.h"
struct Test { int kind; array<int,7> f; int m, v; };
vector<array<int,7>> FORMS; vector<Test> tests; int NT;
string fname(const array<int,7>& f) { string s; for (int i = 0; i < 7; i++) if (f[i]) { if (f[i] > 0 && !s.empty()) s += "+"; if (f[i] == -1) s += "-"; else if (f[i] != 1) s += to_string(f[i]); s += "g" + to_string(i); } return s; }
string tname(const Test& t) { if (t.kind == 2) return "ab>=" + to_string(t.v); if (t.kind == 0) return fname(t.f) + ">=" + to_string(t.v); return fname(t.f) + "%" + to_string(t.m) + "==" + to_string(t.v); }
struct Row { Gp g; int ab; bool w; };
int ABLO = -100, ABHI = 100, G3MAX = 1000;
bool inDom(const Gp& g, int ab) { return ab >= ABLO && ab <= ABHI && g[3] <= G3MAX; }
long fval(const array<int,7>& f, const Gp& g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
bool evalT(const Test& t, const Gp& g, int ab) { if (t.kind == 2) return ab >= t.v; long x = fval(t.f, g); if (t.kind == 0) return x >= t.v; return ((x % t.m) + t.m) % t.m == t.v; }
vector<Row> rows; vector<vector<uint64_t>> bits; vector<uint64_t> lab; int W;
struct Node { int test = -1, yes = -1, no = -1, leaf = -1; long n = 0; }; vector<Node> nodes;
int build(const vector<uint64_t>& set, int depth) {
  long n = 0, nw = 0; for (int k = 0; k < W; k++) { n += __builtin_popcountll(set[k]); nw += __builtin_popcountll(set[k] & lab[k]); }
  int id = nodes.size(); nodes.push_back(Node()); nodes[id].n = n;
  if (nw == 0 || nw == n || depth > 60) { nodes[id].leaf = nw * 2 > n ? 1 : 0; return id; }
  double best = 1e18; int bt = -1;
  for (int t = 0; t < NT; t++) { long a = 0, aw = 0; const auto& B = bits[t]; for (int k = 0; k < W; k++) { uint64_t x = set[k] & B[k]; a += __builtin_popcountll(x); aw += __builtin_popcountll(x & lab[k]); }
    long b = n - a, bw = nw - aw; if (a == 0 || b == 0) continue;
    double sc = (a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a) + (b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b) + 1e-7 * t;
    if (sc < best) { best = sc; bt = t; } }
  if (bt < 0) { nodes[id].leaf = nw * 2 > n ? 1 : 0; fprintf(stderr, "impure leaf %ld/%ld\n", nw, n); return id; }
  vector<uint64_t> s1(W), s0(W); for (int k = 0; k < W; k++) { s1[k] = set[k] & bits[bt][k]; s0[k] = set[k] & ~bits[bt][k]; }
  nodes[id].test = bt; int y = build(s1, depth + 1); int no = build(s0, depth + 1); nodes[id].yes = y; nodes[id].no = no; return id; }
bool predict(const Gp& g, int ab) { int id = 0; while (nodes[id].leaf < 0) id = evalT(tests[nodes[id].test], g, ab) ? nodes[id].yes : nodes[id].no; return nodes[id].leaf; }
void print(int id, int ind) { if (nodes[id].leaf >= 0) { printf("%*s%s (%ld)\n", ind, "", nodes[id].leaf ? "WIN" : "LOSS", nodes[id].n); return; }
  printf("%*sif %s:\n", ind, "", tname(tests[nodes[id].test]).c_str()); print(nodes[id].yes, ind + 2); printf("%*selse:\n", ind, ""); print(nodes[id].no, ind + 2); }
template <class F> void forAll(int S, F f) { Gp g; function<void(int, int)> rec = [&](int i, int rem) { if (i == 6) { g[6] = 0; for (int x = 0; x <= rem; x++) { g[6] = x; f(g); } return; } for (int x = 0; x <= rem; x++) { g[i] = x; rec(i + 1, rem - x); } }; rec(0, S); }
int main(int argc, char** argv) { int SL = atoi(argv[1]), SV = atoi(argv[2]), c = atoi(argv[3]); if (argc > 5) { ABLO = atoi(argv[4]); ABHI = atoi(argv[5]); }
  if (getenv("G3MAX")) G3MAX = atoi(getenv("G3MAX")); int NZ2 = getenv("NZ2") ? atoi(getenv("NZ2")) : 3;
  initS(SV);
  array<int,7> f; function<void(int)> gen = [&](int i) { if (i == 7) { int nz = 0, mx = 0, gg = 0, first = 0; for (int x : f) { if (x) { nz++; if (!first) first = x; } mx = max(mx, abs(x)); gg = __gcd(gg, abs(x)); }
      if (!nz || first < 0 || gg != 1) return; if (mx > 1 && nz > NZ2) return; FORMS.push_back(f); return; } for (int x = -2; x <= 2; x++) { f[i] = x; gen(i + 1); } };
  gen(0);
  for (auto& F : FORMS) { int nz = 0; for (int x : F) if (x) nz++;
    for (int v = (nz == 1 ? 1 : -8); v <= 8; v++) tests.push_back({0, F, 0, v});
    for (int m : {2, 3}) for (int r = 0; r < m; r++) tests.push_back({1, F, m, r}); }
  for (int v = -12; v <= 12; v++) tests.push_back({2, {}, 0, v});
  NT = tests.size(); fprintf(stderr, "%zu forms, %d tests\n", FORMS.size(), NT);
  forAll(SL, [&](const Gp& g) { int ab = abOf(c, g); if (!inDom(g, ab)) return; rows.push_back({g, ab, xLF(c, g)}); });
  W = (rows.size() + 63) / 64; fprintf(stderr, "%zu rows, bits %.2f GB\n", rows.size(), (double)NT * W * 8 / 1e9);
  bits.assign(NT, vector<uint64_t>(W, 0)); lab.assign(W, 0);
  vector<long> fv(FORMS.size());
  for (size_t r = 0; r < rows.size(); r++) { auto& R = rows[r]; if (R.w) lab[r / 64] |= 1ULL << (r % 64);
    for (size_t j = 0; j < FORMS.size(); j++) fv[j] = fval(FORMS[j], R.g);
    int t = 0; uint64_t bit = 1ULL << (r % 64); size_t w = r / 64;
    for (size_t j = 0; j < FORMS.size(); j++) { int nz = 0; for (int x : FORMS[j]) if (x) nz++; long x = fv[j];
      for (int v = (nz == 1 ? 1 : -8); v <= 8; v++, t++) if (x >= v) bits[t][w] |= bit;
      for (int m : {2, 3}) { long rr = ((x % m) + m) % m; for (int q = 0; q < m; q++, t++) if (rr == q) bits[t][w] |= bit; } }
    for (int v = -12; v <= 12; v++, t++) if (R.ab >= v) bits[t][w] |= bit; }
  vector<uint64_t> all(W, ~0ULL); if (rows.size() % 64) all[W - 1] = (1ULL << (rows.size() % 64)) - 1;
  build(all, 0); long leaves = 0; for (auto& n : nodes) if (n.leaf >= 0) leaves++;
  printf("order %s: %ld leaves (%zu rows)\n", nm(c), leaves, rows.size());
  long err = 0, tot = 0; forAll(SV, [&](const Gp& g) { int ab = abOf(c, g); if (!inDom(g, ab)) return; tot++; if (predict(g, ab) != xLF(c, g)) { err++; if (getenv("ERR") && err <= 20) printf("err (%d %d %d %d %d %d %d) ab %d\n", g[0],g[1],g[2],g[3],g[4],g[5],g[6], ab); } });
  printf("validation S=%d: %ld errors of %ld\n", SV, err, tot); fflush(stdout);
  if (getenv("PRINT")) print(0, 0);
  if (getenv("EXPORT")) { FILE* fo = fopen(getenv("EXPORT"), "w"); fprintf(fo, "%d %zu\n", c, nodes.size());
    for (size_t i = 0; i < nodes.size(); i++) { auto& n = nodes[i]; if (n.leaf >= 0) fprintf(fo, "%zu leaf %d\n", i, n.leaf); else { auto& t = tests[n.test]; fprintf(fo, "%zu test %d", i, t.kind); for (int x : t.f) fprintf(fo, " %d", x); fprintf(fo, " %d %d %d %d\n", t.m, t.v, n.yes, n.no); } }
    fclose(fo); }
}
