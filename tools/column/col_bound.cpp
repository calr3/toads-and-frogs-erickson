// Smallest bound R on a structural measure such that Right still has a winning strategy for
// "Left stop <= 0" of T^a .^b F^a in which every position after one of Right's replies (and every
// position where Right passes) has measure <= R.  Measures: 0 = live runs (dead TTFF blocks
// count as one separator), 1 = all runs.
// Usage: col_bound B AMIN AMAX [MEASURE [K]]   (with K: also print run statistics of a strategy)
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int n, MEAS = 0, R;
static inline int cell(u64 s, int i) { return (s >> (2 * i)) & 3; }
static inline u64 setc(u64 s, int i, int v) { return (s & ~(3ULL << (2 * i))) | ((u64)v << (2 * i)); }
vector<u64> lmoves(u64 s) {
  vector<u64> o;
  for (int i = 0; i < n; i++) if (cell(s, i) == 1) {
    if (i + 1 < n && cell(s, i + 1) == 0) o.push_back(setc(setc(s, i, 0), i + 1, 1));
    else if (i + 2 < n && cell(s, i + 1) == 2 && cell(s, i + 2) == 0) o.push_back(setc(setc(s, i, 0), i + 2, 1));
  }
  return o;
}
vector<u64> rmoves(u64 s) {
  vector<u64> o;
  for (int i = n - 1; i >= 0; i--) if (cell(s, i) == 2) {
    if (i - 1 >= 0 && cell(s, i - 1) == 0) o.push_back(setc(setc(s, i, 0), i - 1, 2));
    else if (i - 2 >= 0 && cell(s, i - 1) == 1 && cell(s, i - 2) == 0) o.push_back(setc(setc(s, i, 0), i - 2, 2));
  }
  return o;
}
int measure(u64 s) {
  vector<bool> d(n, false);
  if (MEAS == 0)
    for (int i = 0; i + 3 < n; i++)
      if (cell(s, i) == 1 && cell(s, i + 1) == 1 && cell(s, i + 2) == 2 && cell(s, i + 3) == 2) {
        for (int j = i + 1; j >= 0 && cell(s, j) == 1; j--) d[j] = true;
        for (int j = i + 2; j < n && cell(s, j) == 2; j++) d[j] = true;
      }
  int r = 0, prev = -1;
  for (int i = 0; i < n; i++) { int c = d[i] ? 3 : cell(s, i); if (c != prev) r++; prev = c; }
  return r;
}
unordered_map<u64, char> mLE, mUP, mLF;
bool le0(u64 s) {
  auto it = mLE.find(s); if (it != mLE.end()) return it->second;
  bool r = true;
  for (u64 q : lmoves(s)) { bool ok = false; for (u64 t : rmoves(q)) if (measure(t) <= R && le0(t)) { ok = true; break; } if (!ok) { r = false; break; } }
  return mLE[s] = r;
}
bool Up(u64 s);
bool Lf(u64 s) {
  auto it = mLF.find(s); if (it != mLF.end()) return it->second;
  bool r = measure(s) <= R && le0(s);
  if (!r) for (u64 t : rmoves(s)) if (measure(t) <= R && Up(t)) { r = true; break; }
  return mLF[s] = r;
}
bool Up(u64 s) {
  auto it = mUP.find(s); if (it != mUP.end()) return it->second;
  bool r = Lf(s);
  if (r) for (u64 q : lmoves(s)) if (!Lf(q)) { r = false; break; }
  return mUP[s] = r;
}
string str(u64 s) { string t; for (int i = 0; i < n; i++) t += ".TF"[cell(s, i)]; return t; }
vector<pair<int,int>> runsOf(u64 s) {
  vector<pair<int,int>> v;
  for (int i = 0; i < n; i++) { int c = cell(s, i); if (!v.empty() && v.back().first == c) v.back().second++; else v.push_back({c, 1}); }
  return v;
}
// pattern of a position: runs, with long ones (>= K) shown as T+ / F+
string pattern(u64 s, int K) {
  string t; for (auto [c, l] : runsOf(s)) { t += ".TF"[c]; t += l >= K ? "+" : to_string(l); } return t;
}
int nlong(u64 s, int K) { int k = 0; for (auto [c, l] : runsOf(s)) if (l >= K) k++; return k; }
// one strategy at bound R: prefer replies with fewer long runs, then fewer runs
void stats(u64 s0, int K) {
  auto sc = [&](u64 t) { return nlong(t, K) * 100 + measure(t); };
  set<u64> U, N; deque<pair<u64,int>> todo{{s0, 0}};
  while (!todo.empty()) {
    auto [s, kind] = todo.front(); todo.pop_front();
    if (!(kind ? N : U).insert(s).second) continue;
    auto best = [&](u64 q, bool up) { u64 b = 0; int bs = INT_MAX;
      for (u64 t : rmoves(q)) if (measure(t) <= R && (up ? Up(t) : le0(t)) && sc(t) < bs) { bs = sc(t); b = t; }
      return b; };
    if (kind) { for (u64 q : lmoves(s)) todo.push_back({best(q, false), 1}); continue; }
    vector<u64> qs = lmoves(s); qs.push_back(s);
    for (u64 q : qs) { if (measure(q) <= R && le0(q)) { todo.push_back({q, 1}); if (getenv("SHOWU")) printf("    pass at %s%s\n", str(q).c_str(), q == s ? " (Left passed)" : ""); }
      else { u64 r = best(q, true); todo.push_back({r, 0}); if (getenv("SHOWU")) printf("    U %s -> %s -> %s\n", str(s).c_str(), str(q).c_str(), str(r).c_str()); } }
  }
  // shapes: runs capped at K (parity kept); long runs in a dead TTFF block free; the other long
  // runs keep their exact offset from the shortest of them
  auto deadv = [&](u64 s) { vector<bool> d(n, false);
    for (int i = 0; i + 3 < n; i++) if (cell(s, i) == 1 && cell(s, i + 1) == 1 && cell(s, i + 2) == 2 && cell(s, i + 3) == 2) {
      for (int j = i + 1; j >= 0 && cell(s, j) == 1; j--) d[j] = true;
      for (int j = i + 2; j < n && cell(s, j) == 2; j++) d[j] = true; }
    return d; };
  int maxoff = 0; set<string> shapes;
  for (auto *S : {&U, &N}) for (u64 x : *S) {
    vector<bool> d = deadv(x); auto rs = runsOf(x);
    int pos = 0, mn = INT_MAX; vector<int> live;
    for (auto [c, l] : rs) { bool dd = d[pos]; if (l >= K && !dd) mn = min(mn, l); pos += l; }
    string sh; pos = 0;
    for (auto [c, l] : rs) { bool dd = d[pos]; sh += ".TF"[c];
      if (l < K) sh += to_string(l);
      else if (dd) sh += "d" + to_string(K + l % 2);
      else { sh += "+" + to_string(l - mn); maxoff = max(maxoff, l - mn); if (getenv("SHOWOFF") && l - mn >= atoi(getenv("SHOWOFF"))) printf("    off %d %s %s le0=%d\n", l - mn, str(x).c_str(), S == &U ? "U" : "N", (int)le0(x)); }
      pos += l; }
    if (mn != INT_MAX) sh += " m" + to_string(K + (mn >= K + 2 ? 2 : 0) + mn % 2);
    shapes.insert((S == &U ? "U " : "N ") + sh);
  }
  printf("  max live offset %d; distinct shapes %zu\n", maxoff, shapes.size());
  map<int,int> hist; map<string,int> pats;
  for (auto *S : {&U, &N}) for (u64 x : *S) { hist[nlong(x, K)]++; if (nlong(x, K) >= 3) pats[pattern(x, K)]++; }
  printf("  strategy: %zu U + %zu N positions; long runs (>= %d):", U.size(), N.size(), K);
  for (auto [k, c] : hist) printf(" %d:%d", k, c);
  printf("\n  patterns with >= 3 long runs: %zu\n", pats.size());
  vector<pair<int,string>> v; for (auto [p, c] : pats) v.push_back({-c, p}); sort(v.begin(), v.end());
  for (int i = 0; i < min<int>(12, v.size()); i++) printf("    %6d  %s\n", -v[i].first, v[i].second.c_str());
}
int main(int argc, char **argv) {
  int B = atoi(argv[1]), A0 = atoi(argv[2]), A1 = atoi(argv[3]);
  if (argc > 4) MEAS = atoi(argv[4]);
  for (int a = A0; a <= A1; a++) {
    n = 2 * a + B;
    u64 s0 = 0; for (int i = 0; i < a; i++) { s0 = setc(s0, i, 1); s0 = setc(s0, n - 1 - i, 2); }
    for (R = 1; R <= 2 * n; R++) {
      mLE.clear(); mUP.clear(); mLF.clear();
      if (Up(s0)) { printf("a=%d b=%d: smallest bound %d (measure %d)\n", a, B, R, MEAS); fflush(stdout); if (argc > 5) stats(s0, atoi(argv[5])); break; }
    }
  }
}
