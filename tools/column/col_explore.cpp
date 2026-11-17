// Explore Right's strategies for the column T^a .^b F^a (fixed b, growing a).
// Decides "Left stop <= 0" (Up) with Right's single pass, extracts one strategy for Right with a
// reply heuristic, and reports how the positions in it are structured: number of runs (maximal
// blocks of equal cells) and the number of distinct run-length shapes with lengths capped at K.
// Usage: col_explore B AMIN AMAX [K] [HEUR]
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int n;
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
string str(u64 s) { string t; for (int i = 0; i < n; i++) t += ".TF"[cell(s, i)]; return t; }
unordered_map<u64, char> mLE, mUP, mLF;
bool le0(u64 s) {  // normal play, Left to move, Right wins
  auto it = mLE.find(s); if (it != mLE.end()) return it->second;
  bool r = true;
  for (u64 q : lmoves(s)) { bool ok = false; for (u64 t : rmoves(q)) if (le0(t)) { ok = true; break; } if (!ok) { r = false; break; } }
  return mLE[s] = r;
}
bool Up(u64 s);
bool Lf(u64 s) {  // Right to move (Left passed or moved), Right still has its pass
  auto it = mLF.find(s); if (it != mLF.end()) return it->second;
  bool r = le0(s);
  if (!r) for (u64 t : rmoves(s)) if (Up(t)) { r = true; break; }
  return mLF[s] = r;
}
bool Up(u64 s) {
  auto it = mUP.find(s); if (it != mUP.end()) return it->second;
  bool r = Lf(s);
  if (r) for (u64 q : lmoves(s)) if (!Lf(q)) { r = false; break; }
  return mUP[s] = r;
}
// run-length shape with caps
int K = 3;
vector<pair<int,int>> runs(u64 s) {
  vector<pair<int,int>> v;
  for (int i = 0; i < n; i++) { int c = cell(s, i); if (!v.empty() && v.back().first == c) v.back().second++; else v.push_back({c, 1}); }
  return v;
}
string shape(u64 s) {
  string t;
  for (auto [c, l] : runs(s)) { t += ".TF"[c]; t += to_string(l < K ? l : K + (l - K) % 2) ; t += ' '; }
  return t;
}
int nruns(u64 s) { return runs(s).size(); }
// Dead cells (Erickson's dead pieces): around every TTFF, the toad run ending there and the frog
// run starting there never move again.
vector<bool> dead(u64 s) {
  vector<bool> d(n, false);
  for (int i = 0; i + 3 < n; i++)
    if (cell(s, i) == 1 && cell(s, i + 1) == 1 && cell(s, i + 2) == 2 && cell(s, i + 3) == 2) {
      for (int j = i + 1; j >= 0 && cell(s, j) == 1; j--) d[j] = true;
      for (int j = i + 2; j < n && cell(s, j) == 2; j++) d[j] = true;
    }
  return d;
}
// runs of live cells, with dead blocks as single separators
int liveRuns(u64 s) {
  vector<bool> d = dead(s); int r = 0, prev = -1;
  for (int i = 0; i < n; i++) { int c = d[i] ? 3 : cell(s, i); if (c != prev) r++; prev = c; }
  return r;
}
int nDead(u64 s) { vector<bool> d = dead(s); return count(d.begin(), d.end(), true); }
int HEUR = 0;
long score(u64 s) {
  if (HEUR == 0) return nruns(s);
  if (HEUR == 2) return liveRuns(s);
  if (HEUR == 3) return -nDead(s) * 100 + liveRuns(s);
  // HEUR 1: number of runs, then mirror mismatch
  int mm = 0; for (int i = 0; i < n; i++) { int c = cell(s, i), d = cell(s, n - 1 - i); if (c != (d == 1 ? 2 : d == 2 ? 1 : 0)) mm++; }
  return nruns(s) * 1000 + mm;
}
int main(int argc, char **argv) {
  int B = atoi(argv[1]), A0 = atoi(argv[2]), A1 = atoi(argv[3]);
  if (argc > 4) K = atoi(argv[4]);
  if (argc > 5) HEUR = atoi(argv[5]);
  for (int a = A0; a <= A1; a++) {
    n = 2 * a + B; mLE.clear(); mUP.clear(); mLF.clear();
    u64 s0 = 0; for (int i = 0; i < a; i++) { s0 = setc(s0, i, 1); s0 = setc(s0, n - 1 - i, 2); }
    bool up = Up(s0);
    // extract strategy: U-nodes (Up, Left to move), N-nodes (le0, Left to move)
    set<u64> U, N; deque<pair<u64,int>> todo; todo.push_back({s0, 0});
    int maxr = 0;
    set<string> shU, shN;
    while (!todo.empty()) {
      auto [s, kind] = todo.front(); todo.pop_front();
      if (kind == 0) { if (U.count(s)) continue; U.insert(s); shU.insert(shape(s)); }
      else { if (N.count(s)) continue; N.insert(s); shN.insert(shape(s)); }
      maxr = max(maxr, nruns(s));
      if (kind == 1) {
        for (u64 q : lmoves(s)) { u64 best = 0; long bs = LONG_MAX;
          for (u64 t : rmoves(q)) if (le0(t) && score(t) < bs) { bs = score(t); best = t; }
          todo.push_back({best, 1}); }
        continue;
      }
      vector<u64> qs = lmoves(s); qs.push_back(s);  // Left moves, and Left passing
      for (u64 q : qs) {
        if (le0(q)) { todo.push_back({q, 1}); continue; }  // Right passes
        u64 best = 0; long bs = LONG_MAX;
        for (u64 t : rmoves(q)) if (Up(t) && score(t) < bs) { bs = score(t); best = t; }
        if (bs == LONG_MAX) { printf("  no reply?! %s\n", str(q).c_str()); continue; }
        todo.push_back({best, 0});
      }
    }
    if (getenv("SHOW")) { vector<pair<int,u64>> v; for (u64 x : N) v.push_back({-nruns(x), x}); for (u64 x : U) v.push_back({-nruns(x), x});
      sort(v.begin(), v.end()); for (int i = 0; i < min<int>(25, v.size()); i++) printf("  %2d %s %s\n", -v[i].first, str(v[i].second).c_str(), U.count(v[i].second) ? "U" : "N"); }
    int maxl = 0; for (u64 x : U) maxl = max(maxl, liveRuns(x)); for (u64 x : N) maxl = max(maxl, liveRuns(x));
    printf("maxlive=%d ", maxl);
    printf("a=%d b=%d Up=%d  U=%zu N=%zu  maxruns=%d  shapes U=%zu N=%zu  (states %zu)\n", a, B, up, U.size(), N.size(), maxr,
           shU.size(), shN.size(), mLE.size() + mUP.size());
    fflush(stdout);
  }
}
