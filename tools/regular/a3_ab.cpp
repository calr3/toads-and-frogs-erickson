// Abstract closure for the a = 3 row with "race-count shapes".
//
// A shape is (piece order, A - B, cap(g0), ..., cap(g6)) where A - B is the race count (a linear
// form in the gaps whose coefficients depend on the order) and cap(x) = x for x < K and
// K + x mod 2 otherwise.  Two positions with the same order, the same A - B, equal small gaps and
// large gaps >= K + j of equal parity are related with margin j; a move turns margin j + 1 into j
// (gaps change by at most one, A - B by a fixed amount per move type).  So for each shape and
// each pattern of which large gaps are >= K + 2, one witness position suffices.
//
// The closure starts from the shapes of TT.T .^m FFF (all m >= 5) and checks, for every witness
// and every Left move, that some Right reply is <= 0 (exact solver); the reply's shape is added.
//
// Usage: a3_ab K MAXSHAPES
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
const int P = 6;

struct S { int c; int g[P + 1]; };
static inline bool toad(const S& s, int i) { return (s.c >> i) & 1; }
u64 enc(const S& s) { u64 x = s.c; for (int i = 0; i <= P; i++) x = x * 256 + s.g[i]; return x; }

int lms(const S& s, S* out) {
  int k = 0;
  for (int i = 0; i < P; i++) if (toad(s, i)) {
    if (s.g[i + 1] > 0) { S t = s; t.g[i]++; t.g[i + 1]--; out[k++] = t; }
    else if (i + 1 < P && !toad(s, i + 1) && s.g[i + 2] > 0) { S t = s; t.c ^= (3 << i); t.g[i]++; t.g[i + 2]--; out[k++] = t; }
  }
  return k;
}
int rms(const S& s, S* out) {
  int k = 0;
  for (int i = 0; i < P; i++) if (!toad(s, i)) {
    if (s.g[i] > 0) { S t = s; t.g[i]--; t.g[i + 1]++; out[k++] = t; }
    else if (i >= 1 && toad(s, i - 1) && s.g[i - 1] > 0) { S t = s; t.c ^= (3 << (i - 1)); t.g[i - 1]--; t.g[i + 1]++; out[k++] = t; }
  }
  return k;
}
string str(const S& s) {
  string r(s.g[0], '.');
  for (int i = 0; i < P; i++) { r += toad(s, i) ? 'T' : 'F'; r += string(s.g[i + 1], '.'); }
  return r;
}

unordered_map<u64, uint8_t> memo;
bool RF(const S& s);
bool LF(const S& s) {
  u64 e = enc(s); auto it = memo.find(e);
  if (it != memo.end() && (it->second & 1)) return it->second & 2;
  S mv[P]; int k = lms(s, mv); bool r = false;
  for (int j = 0; j < k && !r; j++) if (!RF(mv[j])) r = true;
  memo[e] |= 1 | (r ? 2 : 0); return r;
}
bool RF(const S& s) {
  u64 e = enc(s); auto it = memo.find(e);
  if (it != memo.end() && (it->second & 4)) return it->second & 8;
  S mv[P]; int k = rms(s, mv); bool r = false;
  for (int j = 0; j < k && !r; j++) if (!LF(mv[j])) r = true;
  memo[e] |= 4 | (r ? 8 : 0); return r;
}
bool le0(const S& s) { return !LF(s); }

int coef(int c, int k) {   // coefficient of gap k in A - B
  int tl = 0, fr = 0;
  for (int i = 0; i < k; i++) if ((c >> i) & 1) tl++;
  for (int i = k; i < P; i++) if (!((c >> i) & 1)) fr++;
  return tl - fr;
}
int AB(const S& s) { int r = 0; for (int k = 0; k <= P; k++) r += coef(s.c, k) * s.g[k]; return r; }

int K = 4;
int cap(int x) { return x < K ? x : K + x % 2; }
typedef array<int, 9> Shape;   // c, AB, caps
Shape shape(const S& s) {
  Shape sh; sh[0] = s.c; sh[1] = AB(s);
  for (int k = 0; k <= P; k++) sh[2 + k] = cap(s.g[k]);
  return sh;
}

// Witnesses: for each subset of the large gaps that are "big" (>= K + 2), one solution of the
// A - B equation, if any (searched with big values up to K + 2 + 2*TMAX).
const int TMAX = 12;
vector<S> witnesses(const Shape& sh) {
  vector<S> out;
  int c = sh[0];
  vector<int> large;
  for (int k = 0; k <= P; k++) if (sh[2 + k] >= K) large.push_back(k);
  int L = large.size();
  for (int mask = 0; mask < (1 << L); mask++) {
    S base; base.c = c;
    for (int k = 0; k <= P; k++) base.g[k] = sh[2 + k];   // small gaps exact; large: K + parity
    vector<int> big;
    for (int t = 0; t < L; t++) {
      int k = large[t], par = sh[2 + k] - K;
      base.g[k] = K + par;
      if (mask >> t & 1) { big.push_back(k); base.g[k] = K + 2 + par; }
    }
    int R = sh[1] - AB(base);    // what the big gaps must add (in steps of 2 per unit)
    // search increments x_i >= 0 (gap += 2 x_i) with sum 2 coef_i x_i = R
    if (big.empty()) { if (R == 0) out.push_back(base); continue; }
    if (R % 2 != 0) continue;
    int nb = big.size(); bool found = false;
    vector<int> x(nb, 0);
    function<void(int, int)> rec = [&](int i, int rem) {
      if (found) return;
      if (i == nb) { if (rem == 0) { S w = base; for (int t = 0; t < nb; t++) w.g[big[t]] += 2 * x[t]; out.push_back(w); found = true; } return; }
      for (int v = 0; v <= TMAX && !found; v++) { x[i] = v; rec(i + 1, rem - 2 * coef(c, big[i]) * v); }
    };
    rec(0, R);
  }
  return out;
}

int ABLO = -6, ABHI = 3;

int main(int argc, char** argv) {
  if (argc > 1) K = atoi(argv[1]);
  size_t MAXS = argc > 2 ? atol(argv[2]) : 2000000;
  if (argc > 3) ABLO = atoi(argv[3]);
  if (argc > 4) ABHI = atoi(argv[4]);
  // ---- explore the abstract game graph
  map<Shape, int> id; vector<Shape> shapes;
  // challenges[s] = list of (list of option shape ids) -- one entry per (witness, Left move)
  vector<vector<vector<int>>> chal;
  auto getId = [&](const Shape& sh) {
    auto it = id.find(sh); if (it != id.end()) return it->second;
    int k = shapes.size(); id[sh] = k; shapes.push_back(sh); chal.emplace_back(); return k;
  };
  vector<int> starts;
  for (int m = 5; m <= K + 7; m++) {
    S q; q.c = 0b000111; int g[7] = {0, 0, 1, m, 0, 0, 0}; for (int i = 0; i <= P; i++) q.g[i] = g[i];
    starts.push_back(getId(shape(q)));
  }
  size_t next = 0; long nwit = 0;
  while (next < shapes.size()) {
    if (shapes.size() > MAXS) { printf("stopped: more than %zu shapes\n", MAXS); return 0; }
    Shape sh = shapes[next];
    vector<vector<int>> cs;
    for (const S& w : witnesses(sh)) {
      nwit++;
      S ql[P]; int kl = lms(w, ql);
      for (int i = 0; i < kl; i++) {
        S rr[P]; int kr = rms(ql[i], rr);
        vector<int> opts;
        for (int j = 0; j < kr; j++) {
          int ab = AB(rr[j]);
          if (ab < ABLO || ab > ABHI) continue;
          opts.push_back(getId(shape(rr[j])));
        }
        cs.push_back(opts);
      }
    }
    chal[next] = cs;
    next++;
    if (next % 50000 == 0) { printf("  explored %zu / %zu shapes\n", next, shapes.size()); fflush(stdout); }
  }
  // ---- greatest fixpoint: shapes from which Right wins
  int n = shapes.size();
  vector<char> win(n, 1);
  bool changed = true; int rounds = 0;
  while (changed) {
    changed = false; rounds++;
    for (int s = 0; s < n; s++) if (win[s]) {
      for (auto& opts : chal[s]) {
        bool ok = false;
        for (int o : opts) if (win[o]) { ok = true; break; }
        if (!ok) { win[s] = 0; changed = true; break; }
      }
    }
  }
  int nwin = 0; for (int s = 0; s < n; s++) nwin += win[s];
  printf("K=%d window [%d,%d]: %d shapes explored (%ld witnesses), %d winning for Right, %d rounds\n",
         K, ABLO, ABHI, n, nwit, nwin, rounds);
  bool allStart = true;
  for (int s : starts) { printf("  start shape AB=%d g3cap=%d: %s\n", shapes[s][1], shapes[s][2 + 3], win[s] ? "Right wins" : "LOST"); allStart &= win[s]; }
  if (allStart) {
    // size of the strategy actually used (first winning option)
    set<int> used; vector<int> st(starts.begin(), starts.end());
    while (!st.empty()) {
      int s = st.back(); st.pop_back();
      if (!used.insert(s).second) continue;
      for (auto& opts : chal[s]) for (int o : opts) if (win[o]) { st.push_back(o); break; }
    }
    printf("strategy uses %zu shapes\n", used.size());
  }
}
