// Exact abstract game: shape = (order, gaps capped at C with residue mod 6, exact ab = A - B,
// F = f . g clamped to [-M, M]).  Moves act on shapes; every outcome the abstraction cannot tell
// apart is kept, and a shape is kept only if some position realizes it (searched exactly: capped
// gaps C + r + 6t with t <= TMAX).
#include <bits/stdc++.h>
using namespace std;
int C = 8, M = 12, TMAX = 14; const int PER = 6;
int f[5] = {0, 0, 1, -2, -3};
struct Sh { int c; int v[5]; int ab; int fv; };
static inline bool toad(const Sh& s, int i) { return (s.c >> i) & 1; }
uint64_t enc(const Sh& s) { uint64_t x = s.c; for (int i = 0; i < 5; i++) x = x * 16 + s.v[i]; x = x * 128 + (s.ab + 64); x = x * 64 + (s.fv + 32); return x; }
int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if ((c >> i) & 1) tl++; for (int i = k; i < 4; i++) if (!((c >> i) & 1)) fr++; return tl - fr; }
// Realizability of a shape together with extra constraints from the case of a move:
//   tz: index of a capped gap that must be exactly at its cap value (t = 0), or -1
//   tp: index of a capped gap that must be above it (t >= 1), or -1
//   fmode: 0 none; 1 F == fval; 2 F >= fval; 3 F <= fval  (true, unclamped F of the shape's positions)
map<tuple<uint64_t,int,int,int,int>, char> realMemo;
bool realizableX(const Sh& s, int tz, int tp, int fmode, int fval) {
  auto key = make_tuple(enc(s), tz, tp, fmode, fval); auto it = realMemo.find(key); if (it != realMemo.end()) return it->second;
  vector<int> B; long ab0 = 0, f0 = 0;
  for (int k = 0; k < 5; k++) { ab0 += (long)coef(s.c, k) * s.v[k]; f0 += (long)f[k] * s.v[k]; if (s.v[k] >= C) B.push_back(k); }
  long R1 = s.ab - ab0; bool ok = false;
  auto fOK = [&](long fx) {
    long cl = max((long)-M, min((long)M, fx)); if (cl != s.fv) return false;
    if (fmode == 1) return fx == fval; if (fmode == 2) return fx >= fval; if (fmode == 3) return fx <= fval; return true; };
  if (R1 % 6 != 0) { realMemo[key] = 0; return false; }
  long Q1 = R1 / 6; int nb = B.size();
  vector<long> A(nb), Fc(nb); vector<long> lo(nb, 0), hi(nb, TMAX);
  for (int j = 0; j < nb; j++) { A[j] = coef(s.c, B[j]); Fc[j] = f[B[j]]; if (B[j] == tz) hi[j] = 0; if (B[j] == tp) lo[j] = 1; }
  if (nb == 0) { ok = (Q1 == 0) && fOK(f0); realMemo[key] = ok; return ok; }
  int js = -1; for (int j = nb - 1; j >= 0; j--) if (A[j] != 0) { js = j; break; }
  if (js < 0 && Q1 != 0) { realMemo[key] = 0; return false; }
  vector<int> rest; for (int j = 0; j < nb; j++) if (j != js) rest.push_back(j);
  int nr = rest.size(); vector<long> t(nr); for (int x = 0; x < nr; x++) t[x] = lo[rest[x]];
  if (nr == 0 || true) {
    while (true) {
      bool inr = true; for (int x = 0; x < nr; x++) if (t[x] > hi[rest[x]]) inr = false;
      if (inr) { long q = Q1, fx = f0; for (int x = 0; x < nr; x++) { q -= A[rest[x]] * t[x]; fx += 6 * Fc[rest[x]] * t[x]; }
        if (js < 0) { if (q == 0 && fOK(fx)) { ok = true; break; } }
        else if (q % A[js] == 0) { long ts = q / A[js]; if (ts >= lo[js] && (B[js] != tz || ts == 0) && fOK(fx + 6 * Fc[js] * ts)) { ok = true; break; } } }
      if (nr == 0) break;
      int x = 0; while (x < nr && ++t[x] > hi[rest[x]]) { t[x] = lo[rest[x]]; x++; } if (x == nr) break; }
  }
  realMemo[key] = ok; return ok; }
bool realizable(const Sh& s) { return realizableX(s, -1, -1, 0, 0); }
vector<int> incv(int v) { if (v < C - 1) return {v + 1}; if (v == C - 1) return {C}; return {C + (v - C + 1) % PER}; }
// move: gap a += 1, gap b -= 1; cases are checked jointly with the predecessor shape s
vector<Sh> apply(const Sh& s, int a, int b, int flip, int d) {
  vector<Sh> out; int df = f[a] - f[b];
  // cases for gap b
  vector<pair<int,int>> bcases;   // (new value, constraint: 0 none, 1 t=0, 2 t>=1)
  if (s.v[b] < C) bcases.push_back({s.v[b] - 1, 0}); else if (s.v[b] == C) { bcases.push_back({C - 1, 1}); bcases.push_back({C + PER - 1, 2}); } else bcases.push_back({s.v[b] - 1, 0});
  // cases for F (true value of the predecessor)
  vector<tuple<int,int,int>> fcases;   // (new clamped F, fmode, fval)
  if (s.fv > -M && s.fv < M) fcases.push_back({max(-M, min(M, s.fv + df)), 0, 0});
  else if (s.fv == M) { for (int x = M; x <= M + abs(df); x++) fcases.push_back({max(-M, min(M, x + df)), 1, x}); fcases.push_back({max(-M, min(M, M + abs(df) + 1 + df)), 2, M + abs(df) + 1}); }
  else { for (int x = -M; x >= -M - abs(df); x--) fcases.push_back({max(-M, min(M, x + df)), 1, x}); fcases.push_back({max(-M, min(M, -M - abs(df) - 1 + df)), 3, -M - abs(df) - 1}); }
  set<uint64_t> seen;
  for (auto [nb, bc] : bcases) for (auto [nf, fm, fvv] : fcases) {
    if (!realizableX(s, bc == 1 ? b : -1, bc == 2 ? b : -1, fm, fvv)) continue;
    for (int x : incv(s.v[a])) { Sh t = s; t.v[a] = x; t.v[b] = nb; t.c ^= flip; t.ab += d; t.fv = nf;
      if (seen.insert(enc(t)).second) out.push_back(t); } }
  return out; }
bool pos(int v) { return v > 0; }
vector<Sh> lmove(const Sh& s, int i) {
  if (!toad(s, i)) return {};
  if (pos(s.v[i + 1])) return apply(s, i, i + 1, 0, -1);
  if (i + 1 < 4 && !toad(s, i + 1) && pos(s.v[i + 2])) return apply(s, i, i + 2, 3 << i, -2);
  return {}; }
vector<Sh> rmove(const Sh& s, int i) {
  if (toad(s, i)) return {};
  if (pos(s.v[i])) return apply(s, i + 1, i, 0, 1);
  if (i >= 1 && toad(s, i - 1) && pos(s.v[i - 1])) return apply(s, i + 1, i - 1, 3 << (i - 1), 2);
  return {}; }
Sh shapeOf(int c, array<int, 5> g) { Sh s; s.c = c; int ab = 0, fx = 0;
  for (int k = 0; k < 5; k++) { s.v[k] = g[k] < C ? g[k] : C + (g[k] - C) % PER; ab += coef(c, k) * g[k]; fx += f[k] * g[k]; }
  s.ab = ab; s.fv = max(-M, min(M, fx)); return s; }
int main(int argc, char** argv) {
  if (argc > 1) C = atoi(argv[1]); if (argc > 2) M = atoi(argv[2]);
  if (argc > 3) sscanf(argv[3], "%d,%d,%d,%d,%d", f, f + 1, f + 2, f + 3, f + 4);
  int KMAX = getenv("KMAX") ? atoi(getenv("KMAX")) : 3 * C + 4 * PER;
  vector<pair<int, Sh>> starts;
  for (int k = 1; k <= KMAX; k++) { starts.push_back({k, shapeOf(3, {0, 1, k, 1, 0})}); starts.push_back({-k, shapeOf(3, {0, 0, k, 1, 0})}); }
  unordered_map<uint64_t, int> idL, idR; vector<Sh> L, R; vector<array<vector<int>, 4>> lmv, rmv;
  auto getL = [&](const Sh& s) { uint64_t e = enc(s); auto it = idL.find(e); if (it != idL.end()) return it->second; int n = L.size(); idL[e] = n; L.push_back(s); return n; };
  auto getR = [&](const Sh& s) { uint64_t e = enc(s); auto it = idR.find(e); if (it != idR.end()) return it->second; int n = R.size(); idR[e] = n; R.push_back(s); return n; };
  for (auto& [k, s] : starts) getL(s);
  size_t pl = 0, pr = 0;
  while (pl < L.size() || pr < R.size()) {
    while (pl < L.size()) { Sh s = L[pl]; array<vector<int>, 4> mv; for (int i = 0; i < 4; i++) for (auto& t : lmove(s, i)) mv[i].push_back(getR(t)); lmv.push_back(mv); pl++; }
    while (pr < R.size()) { Sh s = R[pr]; array<vector<int>, 4> mv; for (int i = 0; i < 4; i++) for (auto& t : rmove(s, i)) mv[i].push_back(getL(t)); rmv.push_back(mv); pr++; }
    if (L.size() > 25000000) { fprintf(stderr, "too many shapes\n"); return 1; }
  }
  fprintf(stderr, "C=%d M=%d f=(%d,%d,%d,%d,%d): %zu Left shapes, %zu Right shapes reachable\n", C, M, f[0], f[1], f[2], f[3], f[4], L.size(), R.size());
  vector<char> WL(L.size(), 1), WR(R.size(), 1);
  for (int it = 0;; it++) { bool ch = false;
    for (size_t r = 0; r < R.size(); r++) if (WR[r]) { bool any = false;
      for (int i = 0; i < 4 && !any; i++) if (!rmv[r][i].empty()) { bool all = true; for (int l : rmv[r][i]) if (!WL[l]) { all = false; break; } if (all) any = true; }
      if (!any) { WR[r] = 0; ch = true; } }
    for (size_t l = 0; l < L.size(); l++) if (WL[l]) { bool ok = true;
      for (int i = 0; i < 4 && ok; i++) for (int r : lmv[l][i]) if (!WR[r]) { ok = false; break; }
      if (!ok) { WL[l] = 0; ch = true; } }
    if (!ch) break; }

  if (getenv("MIXED")) {
    unordered_map<uint64_t, uint8_t> memo;
    auto encx = [](int c, const array<int,5>& g) { uint64_t x = c; for (int i = 0; i < 5; i++) x = x * 256 + g[i]; return x; };
    function<bool(int, array<int,5>)> xLF, xRF;
    auto lmc = [](int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if (!((c >> i) & 1)) return false; h = g; c2 = c;
      if (g[i + 1] > 0) { h[i]++; h[i + 1]--; return true; } if (i + 1 < 4 && !((c >> (i + 1)) & 1) && g[i + 2] > 0) { h[i]++; h[i + 2]--; c2 ^= 3 << i; return true; } return false; };
    auto rmc = [](int c, const array<int,5>& g, int i, int& c2, array<int,5>& h) { if ((c >> i) & 1) return false; h = g; c2 = c;
      if (g[i] > 0) { h[i]--; h[i + 1]++; return true; } if (i >= 1 && ((c >> (i - 1)) & 1) && g[i - 1] > 0) { h[i - 1]--; h[i + 1]++; c2 ^= 3 << (i - 1); return true; } return false; };
    xLF = [&](int c, array<int,5> g) -> bool { uint64_t e = encx(c, g); auto it = memo.find(e); if (it != memo.end() && (it->second & 1)) return it->second & 2;
      bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (lmc(c, g, i, c2, h) && !xRF(c2, h)) r = true; }
      memo[e] |= 1 | (r ? 2 : 0); return r; };
    xRF = [&](int c, array<int,5> g) -> bool { uint64_t e = encx(c, g); auto it = memo.find(e); if (it != memo.end() && (it->second & 4)) return it->second & 8;
      bool r = false; for (int i = 0; i < 4 && !r; i++) { int c2; array<int,5> h; if (rmc(c, g, i, c2, h) && !xLF(c2, h)) r = true; }
      memo[e] |= 4 | (r ? 8 : 0); return r; };
    int T3 = atoi(getenv("MIXED"));
    auto reals = [&](const Sh& s) { vector<array<int,5>> out; vector<int> bigs; for (int i = 0; i < 5; i++) if (s.v[i] >= C) bigs.push_back(i);
      int nb = bigs.size(); vector<int> t(nb, 0);
      while (true) { array<int,5> h; for (int i = 0; i < 5; i++) h[i] = s.v[i]; for (int j = 0; j < nb; j++) h[bigs[j]] += 6 * t[j];
        Sh u = shapeOf(s.c, h); if (u.ab == s.ab && u.fv == s.fv) out.push_back(h);
        int j = 0; while (j < nb && ++t[j] > T3) { t[j] = 0; j++; } if (j == nb) break; }
      return out; };
    auto pr = [&](int c, const array<int,5>& g){ string r(g[0], '.'); for (int i = 0; i < 4; i++) { r += ((c >> i) & 1) ? 'T' : 'F'; r += string(g[i + 1], '.'); } return r; };
    // all Left shapes the abstract game loses, reachable from the starts: report those whose realizations disagree
    long nmixed = 0, nlost_allwin = 0, checked = 0;
    for (size_t l = 0; l < L.size() && nmixed < 12; l++) { if (WL[l]) continue;
      auto rs = reals(L[l]); if (rs.empty()) continue; checked++;
      int nw = 0, nl = 0; array<int,5> ew, el;
      for (auto& h : rs) { if (h[0]+h[1]+h[2]+h[3]+h[4] > 70) continue; if (xLF(L[l].c, h)) { nl++; el = h; } else { nw++; ew = h; } }
      if (nw && nl) { nmixed++; printf("mixed Left shape: Right wins at %s, Left wins at %s\n", pr(L[l].c, ew).c_str(), pr(L[l].c, el).c_str()); }
      if (checked > 200000) break; }
    printf("checked %ld lost Left shapes, %ld mixed\n", checked, nmixed);
    return 0;
  }
  string a, b;
  for (auto& [k, s] : starts) if (WL[idL[enc(s)]]) { if (k > 0) a += " " + to_string(k); else b += " " + to_string(-k); }
  printf("T.T.^kF.F proved for k:%s\nTT.^kF.F  proved for k:%s\n", a.c_str(), b.c_str());
  vector<int> rep(R.size(), -1);
  for (size_t r = 0; r < R.size(); r++) if (WR[r]) for (int i = 0; i < 4; i++) if (!rmv[r][i].empty()) { bool all = true; for (int l : rmv[r][i]) if (!WL[l]) all = false; if (all) { rep[r] = i; break; } }
  vector<char> uL(L.size(), 0), uR(R.size(), 0); vector<int> st;
  for (auto& [k, s] : starts) { int l = idL[enc(s)]; if (WL[l] && !uL[l]) { uL[l] = 1; st.push_back(l); } }
  while (!st.empty()) { int l = st.back(); st.pop_back();
    for (int i = 0; i < 4; i++) for (int r : lmv[l][i]) if (!uR[r]) { uR[r] = 1; for (int l2 : rmv[r][rep[r]]) if (!uL[l2]) { uL[l2] = 1; st.push_back(l2); } } }
  printf("certificate: %ld Left shapes, %ld Right shapes\n", count(uL.begin(), uL.end(), 1), count(uR.begin(), uR.end(), 1));
}
