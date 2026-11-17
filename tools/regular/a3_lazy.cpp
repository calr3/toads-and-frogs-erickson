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


// Per-gap caps (even): the centre gap g3 gets KC, the others K.
// Per-gap caps: values below the cap are exact; above it only the residue modulo the gap's
// period is kept.  The centre gap g3 has cap KC and period PC, the others cap K and period 2.
int K = 4, KC = 6, PC = 2;
int capk(int k) { return k == 3 ? KC : K; }
int perk(int k) { return k == 3 ? PC : 2; }
int cap(int k, int x) { int c = capk(k); return x < c ? x : c + (x - c) % perk(k); }
typedef array<int, 9> Shape;
Shape shape(const S& s) {
  Shape sh; sh[0] = s.c; sh[1] = AB(s);
  for (int k = 0; k <= P; k++) sh[2 + k] = cap(k, s.g[k]);
  return sh;
}
const int TMAX = 12;
vector<S> witnesses(const Shape& sh) {
  vector<S> out; int c = sh[0];
  vector<int> large;
  for (int k = 0; k <= P; k++) if (sh[2 + k] >= capk(k)) large.push_back(k);
  int L = large.size();
  for (int mask = 0; mask < (1 << L); mask++) {
    S base; base.c = c;
    for (int k = 0; k <= P; k++) base.g[k] = sh[2 + k];
    vector<int> big; bool skip = false;
    for (int t = 0; t < L; t++) {
      int k = large[t], r = sh[2 + k] - capk(k);
      int smallest = capk(k) + r;                       // smallest value in the class
      int bigv = smallest >= capk(k) + 2 ? smallest : smallest + perk(k);   // smallest value >= cap + 2
      if (mask >> t & 1) { big.push_back(k); base.g[k] = bigv; }
      else { if (smallest >= capk(k) + 2) skip = true; base.g[k] = smallest; }   // "small" only if < cap + 2
    }
    if (skip) continue;
    int R = sh[1] - AB(base);
    if (big.empty()) { if (R == 0) out.push_back(base); continue; }
    int nb = big.size(); bool found = false; vector<int> x(nb, 0);
    function<void(int, int)> rec = [&](int i, int rem) {
      if (found) return;
      if (i == nb) { if (rem == 0) { S w = base; for (int t = 0; t < nb; t++) w.g[big[t]] += perk(big[t]) * x[t]; out.push_back(w); found = true; } return; }
      for (int v = 0; v <= TMAX && !found; v++) { x[i] = v; rec(i + 1, rem - perk(big[i]) * coef(c, big[i]) * v); }
    };
    rec(0, R);
  }
  return out;
}

int ABLO = -6, ABHI = 3;
map<Shape, int> id; vector<Shape> shapes;
vector<vector<vector<int>>> chal;   // per node: per challenge: options (ids), in preference order
vector<char> computed, status;      // status: 0 unknown, 1 on stack, 2 win (tentative), 3 lose
vector<vector<int>> choice;
int getId(const Shape& sh) {
  auto it = id.find(sh); if (it != id.end()) return it->second;
  int k = shapes.size(); id[sh] = k; shapes.push_back(sh); chal.emplace_back(); computed.push_back(0);
  status.push_back(0); choice.emplace_back(); return k;
}
void compute(int s) {
  if (computed[s]) return;
  computed[s] = 1;
  Shape sh = shapes[s];
  vector<vector<int>> cs;
  for (const S& w : witnesses(sh)) {
    S ql[P]; int kl = lms(w, ql);
    for (int i = 0; i < kl; i++) {
      S rr[P]; int kr = rms(ql[i], rr);
      vector<pair<int, int>> opts;   // (preference key, id)
      for (int j = 0; j < kr; j++) {
        int ab = AB(rr[j]);
        if (ab < ABLO || ab > ABHI) continue;
        opts.push_back({-ab, getId(shape(rr[j]))});
      }
      sort(opts.begin(), opts.end());
      vector<int> o; for (auto& pr : opts) o.push_back(pr.second);
      cs.push_back(o);
    }
  }
  chal[s] = cs;
  choice[s].assign(cs.size(), -1);
}
long visits = 0;
bool dfs(int s) {
  if (status[s] == 3) return false;
  if (status[s] == 1 || status[s] == 2) return true;
  status[s] = 1; visits++;
  compute(s);
  for (size_t c = 0; c < chal[s].size(); c++) {
    bool ok = false;
    for (int o : chal[s][c]) if (dfs(o)) { ok = true; choice[s][c] = o; break; }
    if (!ok) { status[s] = 3; return false; }
  }
  status[s] = 2; return true;
}

int main(int argc, char** argv) {
  if (argc > 1) K = atoi(argv[1]);
  if (argc > 2) KC = atoi(argv[2]);
  if (argc > 3) ABLO = atoi(argv[3]);
  if (argc > 4) ABHI = atoi(argv[4]);
  if (argc > 5) PC = atoi(argv[5]);
  // sanity: witnesses have the shape they represent
  if (getenv("TRACE")) {
    S q; q.c = 0b000111; int g[7] = {0, 0, 1, atoi(getenv("TRACE")), 0, 0, 0}; for (int i = 0; i <= P; i++) q.g[i] = g[i];
    int s0 = getId(shape(q));
    (void)dfs(s0);
    // explain: follow a challenge with no surviving option
    int s = s0;
    for (int depth = 0; depth < 12; depth++) {
      compute(s);
      Shape sh = shapes[s];
      auto ws = witnesses(sh);
      for (auto& w : ws) if (shape(w) != sh) printf("BUG: witness %s has a different shape\n", str(w).c_str());
      printf("shape AB=%d caps=", sh[1]); for (int k = 0; k <= P; k++) printf("%d ", sh[2 + k]);
      printf(" status=%d  witnesses:", status[s]); for (auto& w : ws) printf(" %s", str(w).c_str()); printf("\n");
      // find the failing challenge
      int ci = 0, next = -1;
      for (auto& w : ws) {
        S ql[P]; int kl = lms(w, ql);
        for (int i = 0; i < kl; i++, ci++) {
          bool any = false; for (int o : chal[s][ci]) if (status[o] != 3) any = true;
          if (!any && next < 0) {
            printf("  Left: %s -> %s ; Right options:", str(w).c_str(), str(ql[i]).c_str());
            S rr[P]; int kr = rms(ql[i], rr);
            for (int j = 0; j < kr; j++) printf(" %s(AB=%d,%s)", str(rr[j]).c_str(), AB(rr[j]), le0(rr[j]) ? "<=0" : "not<=0");
            printf("\n");
            if (!chal[s][ci].empty()) next = chal[s][ci][0];
          }
        }
      }
      if (next < 0) break;
      s = next;
    }
    return 0;
  }
  vector<int> starts;
  for (int m = 5; m <= KC + 2 * PC + 7; m++) {
    S q; q.c = 0b000111; int g[7] = {0, 0, 1, m, 0, 0, 0}; for (int i = 0; i <= P; i++) q.g[i] = g[i];
    starts.push_back(getId(shape(q)));
  }
  for (int iter = 0; iter < 1000; iter++) {
    for (auto& st : status) if (st != 3) st = 0;
    bool ok = true;
    for (int s : starts) if (!dfs(s)) { ok = false; printf("start shape lost (iteration %d)\n", iter); }
    if (!ok) break;
    // verify: the chosen strategy, as a set, is closed under all challenges
    set<int> W; vector<int> st(starts.begin(), starts.end());
    while (!st.empty()) { int s = st.back(); st.pop_back(); if (!W.insert(s).second) continue; for (int o : choice[s]) st.push_back(o); }
    vector<int> bad;
    for (int s : W) for (int o : choice[s]) if (status[o] == 3) { bad.push_back(s); break; }
    printf("iteration %d: strategy uses %zu shapes (explored %zu, visits %ld); %zu rely on lost shapes\n",
           iter, W.size(), shapes.size(), visits, bad.size());
    fflush(stdout);
    if (bad.empty()) { printf("CLOSED: Right wins from every start shape with %zu shapes\n", W.size()); break; }
  }
}
