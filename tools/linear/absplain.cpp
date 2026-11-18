// Abstract game on shapes (order, capped gaps, exact ab) for 2 toads + 2 frogs, normal play.
// A gap is kept exactly below C; from C on only C + (g - C) mod 6 is kept. ab = A - B is exact.
// Moves act on shapes; decrementing a capped gap with residue 0 has two outcomes (g = C, or g >= C + 6).
// Right wins from a Left-to-move shape if the greatest fixpoint says so; this is sound for every board.
#include <bits/stdc++.h>
using namespace std;
int C = 12; const int PER = 6;
struct Sh { int c; int v[5]; int ab; };
static inline bool toad(const Sh& s, int i) { return (s.c >> i) & 1; }
uint64_t enc(const Sh& s) { uint64_t x = s.c; for (int i = 0; i < 5; i++) x = x * 32 + s.v[i]; x = x * 128 + (s.ab + 64); return x; }
Sh dec(uint64_t x) { Sh s; s.ab = (int)(x % 128) - 64; x /= 128; for (int i = 4; i >= 0; i--) { s.v[i] = x % 32; x /= 32; } s.c = x; return s; }
bool pos(int v) { return v > 0; }
vector<int> incv(int v) { if (v < C - 1) return {v + 1}; if (v == C - 1) return {C}; return {C + (v - C + 1) % PER}; }
vector<int> decv(int v) { if (v < C) return {v - 1}; if (v == C) return {C - 1, C + PER - 1}; return {v - 1}; }

// Is the shape realized by some position? Exact gaps are fixed; each capped gap is C + r + 6t (t >= 0);
// ab = sum a_i g_i must hold. Reduces to sum_{capped} a_i t_i = Q with t_i >= 0.
int coef(int c, int k) { int tl = 0, fr = 0; for (int i = 0; i < k; i++) if ((c >> i) & 1) tl++; for (int i = k; i < 4; i++) if (!((c >> i) & 1)) fr++; return tl - fr; }
bool realizable(const Sh& s) {
  long R = s.ab; vector<int> a;
  for (int k = 0; k < 5; k++) { int ak = coef(s.c, k);
    if (s.v[k] < C) R -= (long)ak * s.v[k]; else { R -= (long)ak * s.v[k]; a.push_back(ak); } }
  // s.v[k] = C + r for capped gaps, so R is now 6 * (sum a_i t_i)
  if (R % PER != 0) return false; long Q = R / PER;
  bool pos = false, neg = false; int g = 0;
  for (int x : a) { if (x > 0) pos = true; if (x < 0) neg = true; if (x) g = __gcd(g, abs(x)); }
  if (g == 0) return Q == 0;
  if (Q % g != 0) return false;
  if (pos && neg) return true;
  if (pos) { if (Q < 0) return false; bool one = false; for (int x : a) if (x == 1) one = true; return true; }
  return Q <= 0; }
// apply: gap a += 1, gap b -= 1 (all combinations), toggle order bits, ab += d
vector<Sh> apply(const Sh& s, int a, int b, int flip, int d) {
  vector<Sh> out;
  for (int x : incv(s.v[a])) for (int y : decv(s.v[b])) { Sh t = s; t.v[a] = x; t.v[b] = y; t.c ^= flip; t.ab += d; if (!getenv("NOCONS") && !realizable(t)) continue; out.push_back(t); }
  return out; }
// Left move of piece i (type 2i: slide, 2i+1: jump); empty if not available
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
Sh shapeOf(int c, array<int, 5> g) { Sh s; s.c = c; int ab = 0;
  for (int k = 0; k < 5; k++) { s.v[k] = g[k] < C ? g[k] : C + (g[k] - C) % PER;
    int tl = 0, fr = 0; for (int i = 0; i < k; i++) if ((c >> i) & 1) tl++; for (int i = k; i < 4; i++) if (!((c >> i) & 1)) fr++;
    ab += (tl - fr) * g[k]; }
  s.ab = ab; return s; }
int main(int argc, char** argv) {
  if (argc > 1) C = atoi(argv[1]);
  // starts: T.T.^k F.F  and TT.^k F.F, k = 1 .. C + 2*PER
  vector<pair<int, Sh>> starts;
  for (int k = 1; k <= C + 2 * PER; k++) { starts.push_back({k, shapeOf(3, {0, 1, k, 1, 0})}); starts.push_back({-k, shapeOf(3, {0, 0, k, 1, 0})}); }
  // reachability over all moves of both players
  unordered_map<uint64_t, int> idL, idR; vector<Sh> L, R; vector<vector<int>> succL, succRt;  // succL[l]: list of (move index -> R ids) flattened per move
  vector<vector<vector<int>>> lmv, rmv;   // lmv[l][piece] = successor R ids; rmv[r][piece] = successor L ids
  auto getL = [&](const Sh& s) { uint64_t e = enc(s); auto it = idL.find(e); if (it != idL.end()) return it->second; int n = L.size(); idL[e] = n; L.push_back(s); return n; };
  auto getR = [&](const Sh& s) { uint64_t e = enc(s); auto it = idR.find(e); if (it != idR.end()) return it->second; int n = R.size(); idR[e] = n; R.push_back(s); return n; };
  for (auto& [k, s] : starts) getL(s);
  size_t pl = 0, pr = 0;
  while (pl < L.size() || pr < R.size()) {
    while (pl < L.size()) { Sh s = L[pl]; vector<vector<int>> mv(4); for (int i = 0; i < 4; i++) for (auto& t : lmove(s, i)) mv[i].push_back(getR(t)); lmv.push_back(mv); pl++; }
    while (pr < R.size()) { Sh s = R[pr]; vector<vector<int>> mv(4); for (int i = 0; i < 4; i++) for (auto& t : rmove(s, i)) mv[i].push_back(getL(t)); rmv.push_back(mv); pr++; }
  }
  fprintf(stderr, "C=%d: %zu Left shapes, %zu Right shapes reachable\n", C, L.size(), R.size());
  // greatest fixpoint
  vector<char> WL(L.size(), 1), WR(R.size(), 1);
  for (int it = 0;; it++) { bool ch = false;
    for (size_t r = 0; r < R.size(); r++) if (WR[r]) { bool any = false;
      for (int i = 0; i < 4 && !any; i++) if (!rmv[r][i].empty()) { bool all = true; for (int l : rmv[r][i]) if (!WL[l]) { all = false; break; } if (all) any = true; }
      if (!any) { WR[r] = 0; ch = true; } }
    for (size_t l = 0; l < L.size(); l++) if (WL[l]) { bool ok = true;
      for (int i = 0; i < 4 && ok; i++) for (int r : lmv[l][i]) if (!WR[r]) { ok = false; break; }
      if (!ok) { WL[l] = 0; ch = true; } }
    if (!ch) { fprintf(stderr, "fixpoint after %d rounds\n", it); break; } }
  string a, b;
  for (auto& [k, s] : starts) if (WL[idL[enc(s)]]) { if (k > 0) a += " " + to_string(k); else b += " " + to_string(-k); }
  printf("C=%d  T.T.^kF.F <= 0 proved for k:%s\n      TT.^kF.F <= 0 proved for k:%s\n", C, a.c_str(), b.c_str());
  // certificate size: shapes reached when Right plays a fixed winning reply (first winning piece)
  vector<int> rep(R.size(), -1);
  for (size_t r = 0; r < R.size(); r++) if (WR[r]) for (int i = 0; i < 4; i++) if (!rmv[r][i].empty()) { bool all = true; for (int l : rmv[r][i]) if (!WL[l]) all = false; if (all) { rep[r] = i; break; } }
  vector<char> uL(L.size(), 0), uR(R.size(), 0); vector<int> st;
  for (auto& [k, s] : starts) { int l = idL[enc(s)]; if (WL[l] && !uL[l]) { uL[l] = 1; st.push_back(l); } }
  while (!st.empty()) { int l = st.back(); st.pop_back();
    for (int i = 0; i < 4; i++) for (int r : lmv[l][i]) if (!uR[r]) { uR[r] = 1; for (int l2 : rmv[r][rep[r]]) if (!uL[l2]) { uL[l2] = 1; st.push_back(l2); } } }
  printf("certificate: %ld Left shapes, %ld Right shapes\n", count(uL.begin(), uL.end(), 1), count(uR.begin(), uR.end(), 1));
}
