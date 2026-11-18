// Lazy abstract game for 2 toads + 2 frogs, normal play, Left moving first.
// Shape: order, gaps capped at C (residue mod 6 above), exact ab = A - B, and linear forms of the gaps
// clamped to [-M_j, M_j]. A move acts on shapes; where a shape cannot tell (a capped gap at the cap goes
// down, a clamped form at its bound moves inward) every case is kept, and each case is kept only if some
// position of the predecessor shape satisfies it (search over capped gaps C + r + 6t, t <= TMAX).
// Right's replies are explored lazily: one reply per Right shape, switched when it is refuted.
// usage: lazy C TMAX form:M ...   (form = five coefficients separated by commas)
#include <bits/stdc++.h>
using namespace std;
int C = 8, TMAX = 12; const int PER = 6; int NF = 0; vector<array<int,5>> FO; vector<int> FM;
struct Sh { int c; int v[5]; int ab; int fv[8]; };
static inline bool toad(int c, int i) { return (c >> i) & 1; }
typedef pair<uint64_t, uint64_t> Key;
struct KH { size_t operator()(const Key& k) const { return k.first * 1000003ULL ^ (k.second + 0x9e3779b97f4a7c15ULL + (k.first << 6)); } };
Key enc(const Sh& s) { uint64_t a = s.c; for (int i = 0; i < 5; i++) a = a * 16 + s.v[i]; a = a * 256 + (s.ab + 128);
  uint64_t b = 0; for (int j = 0; j < NF; j++) b = b * 128 + (s.fv[j] + 64); return {a, b}; }
int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if (toad(c, i)) tl++; for (int i = k; i < 4; i++) if (!toad(c, i)) fr++; return tl - fr; }
int clampj(long x, int j) { return (int)max((long)-FM[j], min((long)FM[j], x)); }
Sh shapeOf(int c, const array<int,5>& g) { Sh s; s.c = c; s.ab = 0;
  for (int k = 0; k < 5; k++) { s.v[k] = g[k] < C ? g[k] : C + (g[k] - C) % PER; s.ab += coef(c, k) * g[k]; }
  for (int j = 0; j < NF; j++) { long x = 0; for (int k = 0; k < 5; k++) x += (long)FO[j][k] * g[k]; s.fv[j] = clampj(x, j); }
  return s; }
// --- realizability of a shape with extra constraints
struct Cons { int tz = -1, tp = -1; int fmode[8] = {0}; int fval[8] = {0}; };   // fmode: 1 ==, 2 >=, 3 <=
long nreal = 0;
struct CK { Key k; int tz, tp; int fm[8], fvv[8]; bool operator==(const CK& o) const { if (k != o.k || tz != o.tz || tp != o.tp) return false; for (int j = 0; j < NF; j++) if (fm[j] != o.fm[j] || fvv[j] != o.fvv[j]) return false; return true; } };
struct CKH { size_t operator()(const CK& c) const { size_t h = KH()(c.k) ^ (c.tz * 31 + c.tp * 131); for (int j = 0; j < NF; j++) h = h * 1000003 ^ (c.fm[j] * 7 + c.fvv[j] * 977); return h; } };
unordered_map<CK, char, CKH> rmemo;
// Exact search: unknowns t_j >= 0 for capped gaps (value v + 6 t). Equations: ab, every form strictly inside its clamp,
// every exact case value. Eliminate as many unknowns as there are independent equations; enumerate the others (<= TMAX).
bool NOREAL = getenv("NOREAL") != nullptr;
bool realizableX(const Sh& s, const Cons& cs) {
  if (NOREAL) return true;
  CK ck; ck.k = enc(s); ck.tz = cs.tz; ck.tp = cs.tp; for (int j = 0; j < NF; j++) { ck.fm[j] = cs.fmode[j]; ck.fvv[j] = cs.fval[j]; }
  auto it = rmemo.find(ck); if (it != rmemo.end()) return it->second;
  nreal++;
  vector<int> B; long ab0 = 0; long f0[8] = {0};
  for (int k = 0; k < 5; k++) { ab0 += (long)coef(s.c, k) * s.v[k]; for (int j = 0; j < NF; j++) f0[j] += (long)FO[j][k] * s.v[k]; if (s.v[k] >= C) B.push_back(k); }
  int nb = B.size(); bool ok = false;
  // rows: coefficients over t (times 6) and right-hand side
  vector<vector<long>> E; vector<long> rhs;
  { vector<long> r(nb); for (int j = 0; j < nb; j++) r[j] = 6L * coef(s.c, B[j]); E.push_back(r); rhs.push_back(s.ab - ab0); }
  for (int j = 0; j < NF; j++) { long target; bool eq = false;
    if (s.fv[j] > -FM[j] && s.fv[j] < FM[j]) { eq = true; target = s.fv[j]; }
    if (cs.fmode[j] == 1) { eq = true; target = cs.fval[j]; }
    if (eq) { vector<long> r(nb); for (int x = 0; x < nb; x++) r[x] = 6L * FO[j][B[x]]; E.push_back(r); rhs.push_back(target - f0[j]); } }
  vector<long> lo(nb, 0), hi(nb, TMAX); for (int x = 0; x < nb; x++) { if (B[x] == cs.tz) hi[x] = 0; if (B[x] == cs.tp) lo[x] = 1; }
  // Gaussian elimination over the rationals (fraction-free) to pick pivot unknowns
  int m = E.size(); vector<int> piv; vector<vector<long>> M2 = E; vector<long> r2 = rhs; int row = 0;
  for (int col = 0; col < nb && row < m; col++) {
    int pr = -1; for (int i = row; i < m; i++) if (M2[i][col] != 0) { pr = i; break; }
    if (pr < 0) continue; swap(M2[pr], M2[row]); swap(r2[pr], r2[row]);
    for (int i = 0; i < m; i++) if (i != row && M2[i][col] != 0) { long a1 = M2[row][col], a2 = M2[i][col];
      for (int x = 0; x < nb; x++) M2[i][x] = M2[i][x] * a1 - M2[row][x] * a2; r2[i] = r2[i] * a1 - r2[row] * a2;
      long g = 0; for (int x = 0; x < nb; x++) g = __gcd(g, labs(M2[i][x])); g = __gcd(g, labs(r2[i])); if (g > 1) { for (int x = 0; x < nb; x++) M2[i][x] /= g; r2[i] /= g; } }
    piv.push_back(col); row++; }
  for (int i = row; i < m; i++) if (r2[i] != 0) { rmemo[ck] = 0; return false; }   // inconsistent
  vector<char> isPiv(nb, 0); for (int c : piv) isPiv[c] = 1;
  vector<int> fr; for (int x = 0; x < nb; x++) if (!isPiv[x]) fr.push_back(x);
  int nf = fr.size(); vector<long> t(nb, 0); vector<long> tf(nf); for (int x = 0; x < nf; x++) tf[x] = lo[fr[x]];
  while (true) {
    bool good = true; for (int x = 0; x < nf; x++) t[fr[x]] = tf[x];
    for (int i = 0; i < (int)piv.size() && good; i++) { int c = piv[i]; long num = r2[i]; for (int x = 0; x < nf; x++) num -= M2[i][fr[x]] * tf[x];
      if (num % M2[i][c] != 0) { good = false; break; } long v = num / M2[i][c]; if (v < lo[c] || (hi[c] == 0 && v != 0)) { good = false; break; } t[c] = v; }
    if (good) { bool all = true;
      for (int j = 0; j < NF && all; j++) { long fx = f0[j]; for (int x = 0; x < nb; x++) fx += 6L * FO[j][B[x]] * t[x];
        if (clampj(fx, j) != s.fv[j]) all = false; if (cs.fmode[j] == 1 && fx != cs.fval[j]) all = false; if (cs.fmode[j] == 2 && fx < cs.fval[j]) all = false; if (cs.fmode[j] == 3 && fx > cs.fval[j]) all = false; }
      long a = ab0; for (int x = 0; x < nb; x++) a += 6L * coef(s.c, B[x]) * t[x]; if (a != s.ab) all = false;
      if (all) { ok = true; break; } }
    if (nf == 0) break;
    int x = 0; while (x < nf && ++tf[x] > hi[fr[x]]) { tf[x] = lo[fr[x]]; x++; } if (x == nf) break; }
  if (rmemo.size() > 3000000) rmemo.clear();
  rmemo[ck] = ok; return ok; }
// --- moves on shapes: gap a += 1, gap b -= 1
vector<Sh> apply(const Sh& s, int a, int b, int flip, int d) {
  vector<Sh> out; set<Key> seen;
  vector<pair<int,int>> bc;   // new value of gap b, constraint 0 none / 1 t=0 / 2 t>=1
  if (s.v[b] < C) bc.push_back({s.v[b] - 1, 0}); else if (s.v[b] == C) { bc.push_back({C - 1, 1}); bc.push_back({C + PER - 1, 2}); } else bc.push_back({s.v[b] - 1, 0});
  int na = s.v[a] < C - 1 ? s.v[a] + 1 : (s.v[a] == C - 1 ? C : C + (s.v[a] - C + 1) % PER);
  // cases of each form: list of (new clamped value, mode, value)
  vector<vector<tuple<int,int,int>>> fc(NF);
  for (int j = 0; j < NF; j++) { int D = FO[j][a] - FO[j][b], M = FM[j], v = s.fv[j];
    if (v > -M && v < M) fc[j].push_back({clampj(v + D, j), 0, 0});
    else if (D == 0) fc[j].push_back({v, 0, 0});
    else if (v == M) { if (D > 0) fc[j].push_back({M, 0, 0}); else { for (int x = M; x <= M - D; x++) fc[j].push_back({clampj(x + D, j), 1, x}); fc[j].push_back({M, 2, M - D + 1}); } }
    else { if (D < 0) fc[j].push_back({-M, 0, 0}); else { for (int x = -M; x >= -M - D; x--) fc[j].push_back({clampj(x + D, j), 1, x}); fc[j].push_back({-M, 3, -M - D - 1}); } } }
  // depth-first over forms, pruning infeasible partial case assignments
  for (auto [nbv, bk] : bc) {
    Cons cs; if (bk == 1) cs.tz = b; if (bk == 2) cs.tp = b;
    if (bk && !realizableX(s, cs)) continue;
    Sh t = s; t.v[a] = na; t.v[b] = nbv; t.c ^= flip; t.ab += d;
    function<void(int, Cons&, bool)> rec = [&](int j, Cons& cc, bool constrained) {
      if (j == NF) { if (seen.insert(enc(t)).second) out.push_back(t); return; }
      for (auto [nv, md, val] : fc[j]) {
        cc.fmode[j] = md; cc.fval[j] = val; t.fv[j] = nv;
        if (md && fc[j].size() > 1 && !realizableX(s, cc)) continue;
        rec(j + 1, cc, constrained || md); }
      cc.fmode[j] = 0; cc.fval[j] = 0; };
    rec(0, cs, bk != 0); }
  return out; }
vector<Sh> lmove(const Sh& s, int i) {
  if (!toad(s.c, i)) return {};
  if (s.v[i + 1] > 0) return apply(s, i, i + 1, 0, -1);
  if (i + 1 < 4 && !toad(s.c, i + 1) && s.v[i + 2] > 0) return apply(s, i, i + 2, 3 << i, -2);
  return {}; }
vector<Sh> rmove(const Sh& s, int i) {
  if (toad(s.c, i)) return {};
  if (s.v[i] > 0) return apply(s, i + 1, i, 0, 1);
  if (i >= 1 && toad(s.c, i - 1) && s.v[i - 1] > 0) return apply(s, i + 1, i - 1, 3 << (i - 1), 2);
  return {}; }
// --- lazy game
vector<Sh> L, R; unordered_map<Key, int, KH> idL, idR;
vector<char> lostL, lostR, expL; vector<vector<int>> succL;            // succL[l]: Right shapes after Left's moves
vector<int> curR; vector<int> failR; vector<vector<int>> succR;         // current reply piece, failed pieces mask, successors of the current reply
vector<vector<int>> ldep, rdep;   // ldep[r]: Left shapes with r as successor; rdep[l]: Right shapes whose current reply leads to l
deque<int> toExpand; vector<int> lostQL, lostQR;
int getL(const Sh& s) { Key e = enc(s); auto it = idL.find(e); if (it != idL.end()) return it->second; int n = L.size(); idL[e] = n; L.push_back(s);
  lostL.push_back(0); expL.push_back(0); succL.push_back({}); rdep.push_back({}); toExpand.push_back(n); return n; }
void chooseReply(int r);
int getR(const Sh& s) { Key e = enc(s); auto it = idR.find(e); if (it != idR.end()) return it->second; int n = R.size(); idR[e] = n; R.push_back(s);
  lostR.push_back(0); curR.push_back(-1); failR.push_back(0); succR.push_back({}); ldep.push_back({}); chooseReply(n); return n; }
void chooseReply(int r) {
  // candidates: Right pieces with a move, not failed; prefer the one creating fewest new shapes
  int best = -1; vector<int> bestS; long bestNew = LONG_MAX;
  for (int i = 0; i < 4; i++) { if (failR[r] >> i & 1) continue; Sh s = R[r]; auto ts = rmove(s, i); if (ts.empty()) { failR[r] |= 1 << i; continue; }
    long nw = 0; bool bad = false; for (auto& t : ts) { auto it = idL.find(enc(t)); if (it == idL.end()) nw++; else if (lostL[it->second]) bad = true; }
    if (bad) { failR[r] |= 1 << i; continue; }
    if (nw < bestNew) { bestNew = nw; best = i; } }
  if (best < 0) { if (!lostR[r]) { lostR[r] = 1; lostQR.push_back(r); } curR[r] = -1; return; }
  curR[r] = best; Sh s = R[r]; auto ts = rmove(s, best); succR[r].clear();
  for (auto& t : ts) { int l = getL(t); succR[r].push_back(l); rdep[l].push_back(r); }
  for (int l : succR[r]) if (lostL[l]) { failR[r] |= 1 << best; chooseReply(r); return; } }
void propagate() {
  while (!lostQL.empty() || !lostQR.empty()) {
    while (!lostQR.empty()) { int r = lostQR.back(); lostQR.pop_back();
      for (int l : ldep[r]) if (!lostL[l]) { lostL[l] = 1; lostQL.push_back(l); } }
    while (!lostQL.empty()) { int l = lostQL.back(); lostQL.pop_back();
      vector<int> deps = rdep[l];
      for (int r : deps) if (!lostR[r] && curR[r] >= 0) { bool uses = false; for (int x : succR[r]) if (x == l) uses = true;
        if (uses) { failR[r] |= 1 << curR[r]; chooseReply(r); } } } } }
void expand(int l) {
  if (expL[l] || lostL[l]) return; expL[l] = 1;
  for (int i = 0; i < 4; i++) { Sh s = L[l]; for (auto& t : lmove(s, i)) { int r = getR(t); succL[l].push_back(r); ldep[r].push_back(l); if (lostR[r] && !lostL[l]) { lostL[l] = 1; lostQL.push_back(l); } } }
  propagate(); }
int main(int argc, char** argv) {
  C = atoi(argv[1]); TMAX = atoi(argv[2]);
  for (int a = 3; a < argc; a++) { array<int,5> f; int M; sscanf(argv[a], "%d,%d,%d,%d,%d:%d", &f[0], &f[1], &f[2], &f[3], &f[4], &M); FO.push_back(f); FM.push_back(M); }
  NF = FO.size();
  int KMAX = getenv("KMAX") ? atoi(getenv("KMAX")) : 60;
  vector<pair<int,int>> starts;
  bool TRUEONLY = getenv("TRUESTARTS") != nullptr;
  for (int k = 1; k <= KMAX; k++) {
    bool ta = (k == 3 || k == 4 || (k >= 6 && k % 6 != 5)), tb = (k <= 3 || k % 6 == 0);
    if (!TRUEONLY || ta) starts.push_back({k, getL(shapeOf(3, {0, 1, k, 1, 0}))});
    if (!TRUEONLY || tb) starts.push_back({-k, getL(shapeOf(3, {0, 0, k, 1, 0}))}); }
  long it = 0;
  while (!toExpand.empty()) { int l = toExpand.front(); toExpand.pop_front(); expand(l);
    if (++it % 200000 == 0) { int nl = 0; string ls; for (auto [k, l2] : starts) if (lostL[l2]) { nl++; if (ls.size() < 80) ls += " " + to_string(k); }
      fprintf(stderr, "  %ld expanded, %zu Left, %zu Right shapes, %ld realizability checks; starts lost: %d%s\n", it, L.size(), R.size(), nreal, nl, ls.c_str()); }
    if (L.size() > 40000000) { fprintf(stderr, "too many shapes\n"); break; }
    if (it % 1000000 == 0) { FILE* f = fopen("/proc/self/statm", "r"); long a, b; fscanf(f, "%ld %ld", &a, &b); fclose(f); fprintf(stderr, "  rss %.1f GB, rmemo %zu\n", b * 4096.0 / 1e9, rmemo.size()); if (b * 4096.0 / 1e9 > 12.5) { fprintf(stderr, "memory limit\n"); break; } } }
  propagate();
  string a, b; for (auto [k, l] : starts) if (!lostL[l]) { if (k > 0) a += " " + to_string(k); else b += " " + to_string(-k); }
  if (getenv("LOSTONLY")) { FILE* fo = fopen(getenv("LOSTONLY"), "w"); for (size_t l = 0; l < L.size(); l++) if (lostL[l]) { auto& s = L[l]; fprintf(fo, "%d %d %d %d %d %d %d", s.c, s.v[0], s.v[1], s.v[2], s.v[3], s.v[4], s.ab); for (int j = 0; j < NF; j++) fprintf(fo, " %d", s.fv[j]); fprintf(fo, "\n"); } fclose(fo); }
  printf("C=%d forms=%d: %zu Left, %zu Right shapes explored\n", C, NF, L.size(), R.size());
  printf("T.T.^kF.F proved for k:%s\nTT.^kF.F  proved for k:%s\n", a.c_str(), b.c_str());
  // certificate: won shapes reached from proved starts under the current replies; verify closure
  vector<char> uL(L.size(), 0), uR(R.size(), 0); vector<int> st; long bad = 0;
  for (auto [k, l] : starts) if (!lostL[l] && !uL[l]) { uL[l] = 1; st.push_back(l); }
  while (!st.empty()) { int l = st.back(); st.pop_back(); if (!expL[l]) bad++;
    for (int r : succL[l]) { if (lostR[r]) bad++; if (uR[r]) continue; uR[r] = 1;
      for (int l2 : succR[r]) { if (lostL[l2]) bad++; if (!uL[l2]) { uL[l2] = 1; st.push_back(l2); } } } }
  printf("certificate: %ld Left shapes, %ld Right shapes, %ld closure errors\n", (long)count(uL.begin(), uL.end(), 1), (long)count(uR.begin(), uR.end(), 1), bad);
  if (getenv("DUMP")) { FILE* fo = fopen(getenv("DUMP"), "w");
    for (size_t l = 0; l < L.size(); l++) if (uL[l]) { auto& s = L[l]; fprintf(fo, "L %d %d %d %d %d %d %d", s.c, s.v[0], s.v[1], s.v[2], s.v[3], s.v[4], s.ab); for (int j = 0; j < NF; j++) fprintf(fo, " %d", s.fv[j]); fprintf(fo, "\n"); }
    for (size_t r = 0; r < R.size(); r++) if (uR[r]) { auto& s = R[r]; fprintf(fo, "R %d %d %d %d %d %d %d", s.c, s.v[0], s.v[1], s.v[2], s.v[3], s.v[4], s.ab); for (int j = 0; j < NF; j++) fprintf(fo, " %d", s.fv[j]); fprintf(fo, " reply %d\n", curR[r]); }
    fclose(fo); }
  if (getenv("LOSTDUMP")) { FILE* fo = fopen(getenv("LOSTDUMP"), "w");
    for (size_t l = 0; l < L.size(); l++) if (lostL[l]) { auto& s = L[l]; fprintf(fo, "%d %d %d %d %d %d %d", s.c, s.v[0], s.v[1], s.v[2], s.v[3], s.v[4], s.ab); for (int j = 0; j < NF; j++) fprintf(fo, " %d", s.fv[j]); fprintf(fo, "\n"); }
    fclose(fo); }
}
