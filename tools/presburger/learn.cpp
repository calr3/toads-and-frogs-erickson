#include "ex.h"
// Decision-tree learner for Left-first outcome of order c, over binary tests; learn on S, validate on SV.
struct Test { int kind; array<int,5> f; int m, v; string name; };
// kind 0: F(g) >= v ; kind 1: F(g) mod m == v ; kind 2: ab >= v
vector<Test> tests;
long evalF(const array<int,5>& f, const array<int,5>& g) { long x = 0; for (int i = 0; i < 5; i++) x += (long)f[i] * g[i]; return x; }
bool evalT(const Test& t, const array<int,5>& g, int ab) { if (t.kind == 2) return ab >= t.v; long x = evalF(t.f, g); if (t.kind == 0) return x >= t.v; long r = ((x % t.m) + t.m) % t.m; return r == t.v; }
string fname(const array<int,5>& f) { string s; for (int i = 0; i < 5; i++) if (f[i]) { if (f[i] > 0 && !s.empty()) s += "+"; if (f[i] == -1) s += "-"; else if (f[i] != 1) s += to_string(f[i]); s += "g" + to_string(i); } return s; }
int ABLO = -1000, ABHI = 1000, G4MAX = 1000, G2MAX = 1000;
bool inDom(const array<int,5>& g, int ab) { return ab >= ABLO && ab <= ABHI && g[4] <= G4MAX && g[2] <= G2MAX; }
struct Row { array<int,5> g; int ab; bool w; };
int MAXNZ2 = 3; int NT; vector<Row> rows; vector<vector<uint64_t>> bits; vector<uint64_t> lab; int W;
struct Node { int test = -1; int yes = -1, no = -1; int leaf = -1; long n = 0; };
vector<Node> nodes;
int build(vector<uint64_t> set, int depth) {
  long n = 0, nw = 0; for (int k = 0; k < W; k++) { n += __builtin_popcountll(set[k]); nw += __builtin_popcountll(set[k] & lab[k]); }
  Node nd; nd.n = n; int id = nodes.size(); nodes.push_back(nd);
  if (nw == 0 || nw == n || depth > 40) { nodes[id].leaf = nw * 2 > n ? 1 : 0; if (nw != 0 && nw != n) fprintf(stderr, "depth limit\n"); return id; }
  double best = 1e18; int bt = -1;
  for (int t = 0; t < NT; t++) { long a = 0, aw = 0; for (int k = 0; k < W; k++) { uint64_t x = set[k] & bits[t][k]; a += __builtin_popcountll(x); aw += __builtin_popcountll(x & lab[k]); }
    long b = n - a, bw = nw - aw; if (a == 0 || b == 0) continue;
    double g1 = a - (double)aw * aw / a - (double)(a - aw) * (a - aw) / a, g2 = b - (double)bw * bw / b - (double)(b - bw) * (b - bw) / b;
    double sc = g1 + g2 + 1e-6 * t; if (sc < best) { best = sc; bt = t; } }
  if (bt < 0) { nodes[id].leaf = nw * 2 > n ? 1 : 0; fprintf(stderr, "no split, impure %ld/%ld\n", nw, n); return id; }
  vector<uint64_t> s1(W), s0(W); for (int k = 0; k < W; k++) { s1[k] = set[k] & bits[bt][k]; s0[k] = set[k] & ~bits[bt][k]; }
  nodes[id].test = bt; int y = build(s1, depth + 1); int no = build(s0, depth + 1); nodes[id].yes = y; nodes[id].no = no; return id; }
bool predict(int id, const array<int,5>& g, int ab) { while (nodes[id].leaf < 0) id = evalT(tests[nodes[id].test], g, ab) ? nodes[id].yes : nodes[id].no; return nodes[id].leaf; }
void print(int id, int ind) { if (nodes[id].leaf >= 0) { printf("%*s%s (%ld)\n", ind, "", nodes[id].leaf ? "WIN" : "LOSS", nodes[id].n); return; }
  printf("%*sif %s:\n", ind, "", tests[nodes[id].test].name.c_str()); print(nodes[id].yes, ind + 2); printf("%*selse:\n", ind, ""); print(nodes[id].no, ind + 2); }
int main(int argc, char** argv) { int SL = atoi(argv[1]), SV = atoi(argv[2]), c = atoi(argv[3]); int ABR = argc > 4 ? atoi(argv[4]) : 6; int FR = getenv("FR") ? atoi(getenv("FR")) : 1; MAXNZ2 = getenv("NZ2") ? atoi(getenv("NZ2")) : 3;
  initS(SV); if (getenv("ABLO")) ABLO = atoi(getenv("ABLO")); if (getenv("ABHI")) ABHI = atoi(getenv("ABHI")); if (getenv("G4MAX")) G4MAX = atoi(getenv("G4MAX")); if (getenv("G2MAX")) G2MAX = atoi(getenv("G2MAX"));
  // tests
  for (int x0 = -FR; x0 <= FR; x0++) for (int x1 = -FR; x1 <= FR; x1++) for (int x2 = -FR; x2 <= FR; x2++) for (int x3 = -FR; x3 <= FR; x3++) for (int x4 = -FR; x4 <= FR; x4++) {
    array<int,5> f = {x0, x1, x2, x3, x4}; int nz = 0; for (int x : f) if (x) nz++; if (!nz) continue; int first = 0; for (int x : f) if (x) { first = x; break; } if (first < 0) continue;
    int gg = 0; for (int x : f) gg = __gcd(gg, abs(x)); if (gg != 1) continue;
    int mx = 0; for (int x : f) mx = max(mx, abs(x)); if (mx > 1 && nz > MAXNZ2) continue;
    for (int v = (nz == 1 ? 1 : -8); v <= 8; v++) tests.push_back({0, f, 0, v, fname(f) + ">=" + to_string(v)});
    for (int m : {2, 3}) for (int r = 0; r < m; r++) tests.push_back({1, f, m, r, fname(f) + "%" + to_string(m) + "==" + to_string(r)}); }
  for (int v = -ABR; v <= ABR; v++) tests.push_back({2, {}, 0, v, "ab>=" + to_string(v)});
  NT = tests.size(); fprintf(stderr, "%d tests\n", NT);
  for (int a = 0; a <= SL; a++) for (int b = 0; a + b <= SL; b++) for (int d = 0; a + b + d <= SL; d++) for (int e = 0; a + b + d + e <= SL; e++) for (int f = 0; a + b + d + e + f <= SL; f++) {
    array<int,5> g = {a, b, d, e, f}; int ab = abOf(c, g); if (abs(ab) > ABR) continue; if (!inDom(g, ab)) continue; rows.push_back({g, ab, xLF(c, g)}); }
  W = (rows.size() + 63) / 64; bits.assign(NT, vector<uint64_t>(W, 0)); lab.assign(W, 0);
  for (size_t r = 0; r < rows.size(); r++) { if (rows[r].w) lab[r / 64] |= 1ULL << (r % 64); for (int t = 0; t < NT; t++) if (evalT(tests[t], rows[r].g, rows[r].ab)) bits[t][r / 64] |= 1ULL << (r % 64); }
  fprintf(stderr, "%zu rows\n", rows.size());
  vector<uint64_t> all(W, ~0ULL); if (rows.size() % 64) all[W - 1] = (1ULL << (rows.size() % 64)) - 1;
  build(all, 0); long leaves = 0; for (auto& n : nodes) if (n.leaf >= 0) leaves++;
  printf("order %d: %ld leaves\n", c, leaves);
  // validate
  long err = 0, tot = 0; for (int a = 0; a <= SV; a++) for (int b = 0; a + b <= SV; b++) for (int d = 0; a + b + d <= SV; d++) for (int e = 0; a + b + d + e <= SV; e++) for (int f = 0; a + b + d + e + f <= SV; f++) {
    array<int,5> g = {a, b, d, e, f}; int ab = abOf(c, g); if (abs(ab) > ABR) continue; if (!inDom(g, ab)) continue; tot++; if (predict(0, g, ab) != xLF(c, g)) { err++; if (getenv("ERR") && err <= 25) printf("err (%d %d %d %d %d) ab %d actual %d\n", a, b, d, e, f, ab, xLF(c, g)); } }
  printf("validation S=%d: %ld errors of %ld\n", SV, err, tot);
  if (getenv("PRINT")) print(0, 0);
  if (getenv("EXPORT")) { FILE* fo = fopen(getenv("EXPORT"), "w"); fprintf(fo, "%d %zu\n", c, nodes.size());
    for (size_t i = 0; i < nodes.size(); i++) { auto& n = nodes[i]; if (n.leaf >= 0) fprintf(fo, "%zu leaf %d\n", i, n.leaf); else { auto& t = tests[n.test]; fprintf(fo, "%zu test %d %d %d %d %d %d %d %d %d %d\n", i, t.kind, t.f[0], t.f[1], t.f[2], t.f[3], t.f[4], t.m, t.v, n.yes, n.no); } }
    fclose(fo); }
}
