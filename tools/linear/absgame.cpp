// Threshold abstraction for 2 toads + 2 frogs, normal play.
// Key of a position: piece order, each gap g_i capped (exact below C_i, then C_i + (g_i - C_i) mod P_i),
// and for chosen pairs of gaps that are both capped, clamp(g_j - g_i, -M, M).
// Invariant for Left to move: ab <= TL[key]; for Right to move: ab <= TR[key] (ab = race count A - B).
// TR[r] = max over Right reply types of min over positions q with key r of TL[key(reply(q))] - d(reply)
// TL[k] = min over positions p with key k and Left moves m of TR[key(m(p))] - d(m)   (+inf if no move)
// computed as a greatest fixpoint over every position with at most S empty squares.
#include <bits/stdc++.h>
using namespace std;
const int P = 4, INF = 1000, NEG = -1000;
int S, C[5], PER[5], M; vector<pair<int,int>> PAIRS;
struct St { int c; int g[5]; };
static inline bool toad(const St& s, int i) { return (s.c >> i) & 1; }
// moves with type id: Left: 2*i + jump ; Right: 2*i + jump. d = change of ab
struct Mv { St s; int type, d; };
int lms(const St& s, Mv* o) { int k = 0;
  for (int i = 0; i < P; i++) if (toad(s, i)) {
    if (s.g[i + 1] > 0) { St t = s; t.g[i]++; t.g[i + 1]--; o[k++] = {t, 2 * i, -1}; }
    else if (i + 1 < P && !toad(s, i + 1) && s.g[i + 2] > 0) { St t = s; t.c ^= (3 << i); t.g[i]++; t.g[i + 2]--; o[k++] = {t, 2 * i + 1, -2}; }
  } return k; }
int rms(const St& s, Mv* o) { int k = 0;
  for (int i = 0; i < P; i++) if (!toad(s, i)) {
    if (s.g[i] > 0) { St t = s; t.g[i]--; t.g[i + 1]++; o[k++] = {t, 2 * i, 1}; }
    else if (i >= 1 && toad(s, i - 1) && s.g[i - 1] > 0) { St t = s; t.c ^= (3 << (i - 1)); t.g[i - 1]--; t.g[i + 1]++; o[k++] = {t, 2 * i + 1, 2}; }
  } return k; }
int race(const St& s) { int r = 0;
  for (int k = 0; k <= P; k++) { int tl = 0, fr = 0;
    for (int i = 0; i < k; i++) if (toad(s, i)) tl++;
    for (int i = k; i < P; i++) if (!toad(s, i)) fr++;
    r += (tl - fr) * s.g[k]; }
  return r; }

unordered_map<uint64_t, uint8_t> memo;
uint64_t encx(const St& s) { uint64_t x = s.c; for (int i = 0; i <= 4; i++) x = x * 256 + s.g[i]; return x; }
bool xRF(const St& s);
bool xLF(const St& s) { uint64_t e = encx(s); auto it = memo.find(e); if (it != memo.end() && (it->second & 1)) return it->second & 2;
  Mv m[4]; int k = lms(s, m); bool r = false; for (int j = 0; j < k && !r; j++) if (!xRF(m[j].s)) r = true;
  memo[e] |= 1 | (r ? 2 : 0); return r; }
bool xRF(const St& s) { uint64_t e = encx(s); auto it = memo.find(e); if (it != memo.end() && (it->second & 4)) return it->second & 8;
  Mv m[4]; int k = rms(s, m); bool r = false; for (int j = 0; j < k && !r; j++) if (!xLF(m[j].s)) r = true;
  memo[e] |= 4 | (r ? 8 : 0); return r; }
int capv(int x, int i) { return x < C[i] ? x : C[i] + (x - C[i]) % PER[i]; }
// Runner reduction: strip leading frogs and trailing toads, merging their gaps (Erickson's
// Finished Frogs / Terminal Toads theorems; the integer they contribute is part of ab).
// Key = original order, zero flags of the original gaps (they decide which moves exist),
// reduced pattern, each merged gap capped (CFG), clamped differences of chosen pairs of merged gaps.
int RED = 1, ALLPAIRS = 0;
struct PatCfg { int C[5], PER[5]; vector<pair<int,int>> pairs; int M; int orig = -1; };
map<string, PatCfg> CFG; int ORIGC = 1;   // original gaps: exact below ORIGC (1 = zero flag only)
void loadCfg(const char* fn) {
  ifstream f(fn); string line;
  while (getline(f, line)) { if (line.empty() || line[0] == '#') continue;
    istringstream is(line); string pat; is >> pat; if (pat == "-") pat = "";
    if (pat == "ORIGC") { is >> ORIGC; continue; }
    PatCfg c; c.M = 2; string tok; int j = 0;
    while (is >> tok) {
      if (tok[0] == 'M') { c.M = atoi(tok.c_str() + 1); continue; }
      if (tok[0] == 'O') { c.orig = atoi(tok.c_str() + 1); continue; }
      if (tok.find('-') != string::npos) { int x, y; sscanf(tok.c_str(), "%d-%d", &x, &y); c.pairs.push_back({x, y}); continue; }
      int cc, pp; sscanf(tok.c_str(), "%d/%d", &cc, &pp); c.C[j] = cc; c.PER[j] = pp; j++; }
    CFG[pat == "" ? "N" : pat] = c; }
}
int PLAINC = 0, PLAINP = 6;
string keyOf(const St& s) {
  if (PLAINC) { string x; x += char(s.c); for (int i = 0; i < 5; i++) x += char(s.g[i] < PLAINC ? s.g[i] : PLAINC + (s.g[i] - PLAINC) % PLAINP);
    x += char(64 + race(s)); return x; }
  int lo = 0, hi = P - 1;
  while (lo <= hi && !toad(s, lo)) lo++; while (hi >= lo && toad(s, hi)) hi--;
  string pat; for (int i = lo; i <= hi; i++) pat += toad(s, i) ? 'T' : 'F'; if (pat.empty()) pat = "N";
  string x = pat + "|"; x += char(s.c);
  int oc = ORIGC; { auto it = CFG.find(pat); if (it != CFG.end() && it->second.orig >= 0) oc = it->second.orig; }
  for (int i = 0; i < 5; i++) x += char(min(s.g[i], oc));
  if (getenv("ABKEY")) x += char(64 + race(s)) + string("#");
  if (pat == "N") return x;
  int gg[5], m = 0;
  { int t = 0; for (int i = 0; i <= lo; i++) t += s.g[i]; gg[m++] = t; }
  for (int i = lo + 1; i <= hi; i++) gg[m++] = s.g[i];
  { int t = 0; for (int i = hi + 1; i <= P; i++) t += s.g[i]; gg[m++] = t; }
  const PatCfg& c = CFG.at(pat);
  auto big = [&](int j) { return gg[j] >= c.C[j]; };
  for (int j = 0; j < m; j++) x += char(gg[j] < c.C[j] ? gg[j] : c.C[j] + (gg[j] - c.C[j]) % c.PER[j]);
  for (auto [i, j] : c.pairs) x += char(big(i) || big(j) ? 16 + max(-c.M, min(c.M, gg[j] - gg[i])) : 31);
  return x; }
int main(int argc, char** argv) {
  // args: S M C0 P0 ... C4 P4 [i-j ...]
  S = atoi(argv[1]); M = atoi(argv[2]); if (getenv("PLAIN")) { sscanf(getenv("PLAIN"), "%d/%d", &PLAINC, &PLAINP); } else loadCfg(getenv("CFG"));
  for (int i = 0; i < 5; i++) { C[i] = atoi(argv[3 + 2 * i]); PER[i] = atoi(argv[4 + 2 * i]); }
  for (int a = 13; a < argc; a++) { int i, j; sscanf(argv[a], "%d-%d", &i, &j); PAIRS.push_back({i, j}); }
  vector<St> pos;
  for (int c = 0; c < 16; c++) if (__builtin_popcount(c) == 2)
    for (int a = 0; a <= S; a++) for (int b = 0; a + b <= S; b++) for (int d = 0; a + b + d <= S; d++)
      for (int e = 0; a + b + d + e <= S; e++) for (int f = 0; a + b + d + e + f <= S; f++)
        pos.push_back({c, {a, b, d, e, f}});
  unordered_map<string, int> kid; vector<string> keys;
  auto id = [&](const St& s) { string k = keyOf(s); auto it = kid.find(k); if (it != kid.end()) return it->second;
    int n = keys.size(); kid[k] = n; keys.push_back(k); return n; };
  size_t N = pos.size(); vector<int> K(N);
  for (size_t i = 0; i < N; i++) K[i] = id(pos[i]);
  // transitions
  vector<array<int, 4>> lt(N), lt_d(N), rt(N);  // Left successors' keys and d; Right successors' keys per type (-1 if n/a)
  vector<array<int, 8>> rk(N);
  for (size_t i = 0; i < N; i++) {
    Mv o[4]; int n = lms(pos[i], o);
    for (int j = 0; j < 4; j++) { lt[i][j] = j < n ? id(o[j].s) : -1; lt_d[i][j] = j < n ? o[j].d : 0; }
    n = rms(pos[i], o);
    for (int t = 0; t < 8; t++) rk[i][t] = -1;
    for (int j = 0; j < n; j++) rk[i][o[j].type] = id(o[j].s);
  }
  int NK = keys.size();
  fprintf(stderr, "%zu positions, %d keys\n", N, NK);
  vector<int> AB(N); for (size_t i = 0; i < N; i++) AB[i] = race(pos[i]);
  vector<int> TL(NK, INF), TR(NK, INF);
  vector<array<int, 8>> TT(NK);
  for (int it = 0;; it++) {
    bool ch = false;
    // TR: for each reply type t, the largest bound T such that every q with key r and ab(q) <= T
    // has reply t, landing at ab(q) + d <= TL[key]. A q that fails caps T at ab(q) - 1.
    for (auto& b : TT) b.fill(INF);
    for (size_t i = 0; i < N; i++) { int k = K[i];
      for (int t = 0; t < 8; t++) {
        int d = (t & 1) ? 2 : 1;
        bool bad = rk[i][t] < 0 || AB[i] + d > TL[rk[i][t]];
        if (bad) TT[k][t] = min(TT[k][t], AB[i] - 1);
      } }
    for (int k = 0; k < NK; k++) { int v = NEG; for (int t = 0; t < 8; t++) v = max(v, TT[k][t]); v = max(v, NEG);
      if (v < TR[k]) { TR[k] = v; ch = true; } }
    // TL: a p with key k is bad if some Left move lands above TR of its key
    vector<int> nl(NK, INF);
    for (size_t i = 0; i < N; i++) { int k = K[i];
      for (int j = 0; j < 4; j++) if (lt[i][j] >= 0 && AB[i] + lt_d[i][j] > TR[lt[i][j]]) nl[k] = min(nl[k], AB[i] - 1); }
    for (int k = 0; k < NK; k++) if (nl[k] < TL[k]) { TL[k] = nl[k]; ch = true; }
    if (!ch) { fprintf(stderr, "fixpoint after %d rounds\n", it); break; }
  }
  // sanity: every position in the invariant is a real Right win (Left first loses)
  if (getenv("ABSREACH")) {
    // closure over every position of each shape: Left shapes, all Left moves; Right shapes, one reply type
    vector<vector<int>> members(NK); for (size_t i = 0; i < N; i++) members[K[i]].push_back(i);
    vector<char> inL(NK, 0), inR(NK, 0); vector<int> wl, wr; long lost = 0;
    int kmax = atoi(getenv("ABSREACH"));
    for (int k = 1; k <= kmax; k++) for (int fam = 0; fam < 2; fam++) {
      St st = fam == 0 ? St{3, {0, 1, k, 1, 0}} : St{3, {0, 0, k, 1, 0}};
      int kk = kid[keyOf(st)]; if (race(st) > TL[kk]) continue; if (!inL[kk]) { inL[kk] = 1; wl.push_back(kk); } }
    vector<int> choice(NK, -1);
    while (!wl.empty() || !wr.empty()) {
      while (!wl.empty()) { int k = wl.back(); wl.pop_back();
        for (int i : members[k]) { if (AB[i] > TL[k]) { lost++; continue; }
          for (int j = 0; j < 4; j++) if (lt[i][j] >= 0) { int r = lt[i][j]; if (!inR[r]) { inR[r] = 1; wr.push_back(r); } } } }
      while (!wr.empty()) { int r = wr.back(); wr.pop_back();
        // reply type: a winning type for every member; prefer one whose successors are already in the set
        int bt = -1, bnew = 1 << 30;
        for (int t = 0; t < 8; t++) { bool ok = true; int nw = 0; set<int> sk;
          for (int i : members[r]) { if (AB[i] > TR[r]) { ok = false; break; } int d = (t & 1) ? 2 : 1;
            if (rk[i][t] < 0 || AB[i] + d > TL[rk[i][t]]) { ok = false; break; } sk.insert(rk[i][t]); }
          if (!ok) continue; for (int x : sk) if (!inL[x]) nw++;
          if (nw < bnew) { bnew = nw; bt = t; } }
        if (bt < 0) { lost++; continue; }
        choice[r] = bt;
        for (int i : members[r]) { int x = rk[i][bt]; if (!inL[x]) { inL[x] = 1; wl.push_back(x); } } }
    }
    long nl = 0, nr = 0; for (int k = 0; k < NK; k++) { nl += inL[k]; nr += inR[k]; }
    printf("abstract closure: %ld Left shapes, %ld Right shapes, %ld failures\n", nl, nr, lost);
    return 0;
  }
  if (getenv("REACH")) {
    for (int k = 1; k + 4 <= S; k++) { St a{3, {0, 1, k, 1, 0}}, b{3, {0, 0, k, 1, 0}};
      printf("k=%d A %s B %s\n", k, race(a) <= TL[kid[keyOf(a)]] ? "PROVED" : "-", race(b) <= TL[kid[keyOf(b)]] ? "PROVED" : "-"); }
    // keys visited by Right's key-based strategy from every proved start, grouped by board size
    set<int> seenL, seenR; int K0 = atoi(getenv("REACH"));
    for (int k = 1; k + 4 <= S; k++) for (int fam = 0; fam < 2; fam++) {
      St st = fam == 0 ? St{3, {0, 1, k, 1, 0}} : St{3, {0, 0, k, 1, 0}};
      if (race(st) > TL[kid[keyOf(st)]]) continue;
      vector<St> stack = {st}; unordered_set<uint64_t> vis;
      while (!stack.empty()) { St z = stack.back(); stack.pop_back();
        if (!vis.insert(encx(z)).second) continue;
        int kz = kid[keyOf(z)]; assert(race(z) <= TL[kz]); seenL.insert(kz);
        Mv o[4]; int n = lms(z, o);
        for (int j = 0; j < n; j++) { St q = o[j].s; int r = kid[keyOf(q)]; assert(race(q) <= TR[r]); seenR.insert(r);
          int bt = -1; for (int t = 0; t < 8; t++) if (TT[r][t] == TR[r]) { bt = t; break; }
          Mv oo[4]; int nn = rms(q, oo); bool f = false; for (int jj = 0; jj < nn; jj++) if (oo[jj].type == bt) { stack.push_back(oo[jj].s); f = true; }
          assert(f); } }
      if (k >= K0) printf("after starts up to k=%d (fam %d): %zu Left-to-move keys, %zu Right-to-move keys\n", k, fam, seenL.size(), seenR.size());
    }
    if (getenv("KEYONLY")) {
      // key-only check over EVERY position (any ab) with a reachable key
      vector<char> inL(NK, 0), inR(NK, 0); for (int k : seenL) inL[k] = 1; for (int k : seenR) inR[k] = 1;
      vector<int> rep(NK, -1); for (int r : seenR) { for (int t = 0; t < 8; t++) if (TT[r][t] == TR[r]) { rep[r] = t; break; } }
      long badL = 0, badLout = 0, badR = 0, badRout = 0; set<int> badKeysL, badKeysR;
      for (size_t i = 0; i < N; i++) { int k = K[i];
        if (inL[k]) for (int j = 0; j < 4; j++) if (lt[i][j] >= 0) { int r = lt[i][j];
          if (!inR[r]) { badLout++; badKeysL.insert(k); } else if ((getenv("ABKEY") ? AB[i] : TL[k]) + lt_d[i][j] > TR[r]) { badL++; badKeysL.insert(k); } }
        if (inR[k]) { int t = rep[k]; if (rk[i][t] < 0) { badR++; badKeysR.insert(k); continue; }
          int l = rk[i][t]; int d = (t & 1) ? 2 : 1;
          if (!inL[l]) { badRout++; badKeysR.insert(k); } else if ((getenv("ABKEY") ? AB[i] : TR[k]) + d > TL[l]) { badR++; badKeysR.insert(k); } } }
      printf("key-only: Left fails %ld (+%ld leave the set) in %zu keys; Right fails %ld (+%ld leave the set) in %zu keys\n",
             badL, badLout, badKeysL.size(), badR, badRout, badKeysR.size());
    }
    if (getenv("DUMPKEYS")) { FILE* f = fopen(getenv("DUMPKEYS"), "w");
      for (int k : seenL) { fprintf(f, "L %d", TL[k]); for (unsigned char ch : keys[k]) fprintf(f, " %d", (int)ch); fprintf(f, "\n"); }
      for (int k : seenR) { fprintf(f, "R %d", TR[k]); for (unsigned char ch : keys[k]) fprintf(f, " %d", (int)ch); fprintf(f, "\n"); }
      fclose(f); }
    return 0;
  }
  if (getenv("SHOW")) {
    int c, g[5]; sscanf(getenv("SHOW"), "%d:%d,%d,%d,%d,%d", &c, g, g+1, g+2, g+3, g+4);
    St z{c, {g[0], g[1], g[2], g[3], g[4]}}; int k = kid[keyOf(z)];
    printf("ab=%d TL=%d TR=%d\n", race(z), TL[k], TR[k]); return 0; }
  if (getenv("TRACE2")) {
    int c0, gg[5]; sscanf(getenv("TRACE2"), "%d:%d,%d,%d,%d,%d", &c0, gg, gg+1, gg+2, gg+3, gg+4);
    St z{c0, {gg[0], gg[1], gg[2], gg[3], gg[4]}};
    auto pr = [&](const St& s) { string r(s.g[0], '.'); for (int i = 0; i < 4; i++) { r += toad(s, i) ? 'T' : 'F'; r += string(s.g[i + 1], '.'); } return r; };
    // exact outcomes from np22 data: recompute here with a small solver
    for (int step = 0; step < 30; step++) {
      int k = kid[keyOf(z)];
      printf("L: %-28s ab=%3d TL=%d%s  [truth: %s]\n", pr(z).c_str(), race(z), TL[k], race(z) <= TL[k] ? "" : "   <-- outside invariant", xLF(z) ? "Left wins" : "<= 0");
      if (race(z) > TL[k]) {   // culprits: bad concretizations with the smallest ab
        int shown = 0;
        for (int target = TL[k] + 1; target <= TL[k] + 1 && shown < 4; target++)
        for (size_t i = 0; i < N && shown < 4; i++) if (K[i] == k && AB[i] == target) {
          Mv o2[4]; int n2 = lms(pos[i], o2);
          for (int j = 0; j < n2; j++) { int rr = kid[keyOf(o2[j].s)]; if (AB[i] + o2[j].d > TR[rr]) {
            printf("      culprit p=%s ab=%d [truth %s] -> %s ab=%d TR=%d [truth %s]\n", pr(pos[i]).c_str(), AB[i], xLF(pos[i]) ? "Left wins" : "<= 0",
              pr(o2[j].s).c_str(), AB[i] + o2[j].d, TR[rr], xRF(o2[j].s) ? "Right wins" : "Left wins"); shown++; } } }
      }
      Mv o[4]; int n = lms(z, o); if (!n) { printf("  Left has no move\n"); break; }
      // pick Left's move that is worst for Right in the abstraction
      int wj = 0; for (int j = 0; j < n; j++) if (race(o[j].s) - TR[kid[keyOf(o[j].s)]] > race(o[wj].s) - TR[kid[keyOf(o[wj].s)]]) wj = j;
      if (getenv("FOLLOW")) { for (int j = 0; j < n; j++) if (race(o[j].s) > TR[kid[keyOf(o[j].s)]]) { wj = j; break; } }
      St q = o[wj].s; int r = kid[keyOf(q)];
      printf("R: %-28s ab=%3d TR=%d  [truth: %s]\n", pr(q).c_str(), race(q), TR[r], xRF(q) ? "Right wins" : "Left wins");
      if (race(q) > TR[r] && !getenv("FOLLOW")) {
        // why: for each reply type, the culprit q' in the key with smallest ab
        for (int t = 0; t < 8; t++) { int best = INF; size_t wi = 0;
          for (size_t i = 0; i < N; i++) if (K[i] == r) { int d = (t & 1) ? 2 : 1;
            bool bad = rk[i][t] < 0 || AB[i] + d > TL[rk[i][t]]; if (bad && AB[i] < best) { best = AB[i]; wi = i; } }
          if (best >= INF) continue;
          Mv oo[4]; int nn = rms(pos[wi], oo); string res = "no such reply";
          for (int j = 0; j < nn; j++) if (oo[j].type == t) res = pr(oo[j].s) + " ab=" + to_string(race(oo[j].s)) + " TL=" + to_string(TL[kid[keyOf(oo[j].s)]]);
          printf("     reply %d fails first at q'=%s ab=%d -> %s\n", t, pr(pos[wi]).c_str(), AB[wi], res.c_str());
        }
        break;
      }
      // follow Right's best reply type for this key
      int bt = -1; for (int t = 0; t < 8; t++) if (TT[r][t] == TR[r]) { bt = t; break; }
      Mv oo[4]; int nn = rms(q, oo); for (int j = 0; j < nn; j++) if (oo[j].type == bt) z = oo[j].s;
      if (getenv("FOLLOW")) { for (int j = 0; j < nn; j++) printf("     option %s ab=%d TL=%d truth %s\n", pr(oo[j].s).c_str(), race(oo[j].s), TL[kid[keyOf(oo[j].s)]], xLF(oo[j].s) ? "Left wins" : "<= 0");
        for (int j = 0; j < nn; j++) if (!xLF(oo[j].s)) { z = oo[j].s; break; } }
    }
    return 0;
  }
  // starts: T.T.^k F.F  and TT.^k F.F
  for (int k = 1; k + 4 <= S; k++) {
    St a{3, {0, 1, k, 1, 0}}, b{3, {0, 0, k, 1, 0}};
    printf("k=%2d  T.T.^kF.F: ab=%d TL=%d %s   TT.^kF.F: ab=%d TL=%d %s\n", k, race(a), TL[K[0] * 0 + kid[keyOf(a)]], race(a) <= TL[kid[keyOf(a)]] ? "PROVED" : "-",
           race(b), TL[kid[keyOf(b)]], race(b) <= TL[kid[keyOf(b)]] ? "PROVED" : "-");
  }
}
