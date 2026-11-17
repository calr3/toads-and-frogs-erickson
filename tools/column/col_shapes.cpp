// Abstract search over run-length shapes for the column T^a .^B F^a (all large a at once).
//
// A position is a word over {., T, F}, read as its maximal runs. Runs shorter than K are kept
// exactly. The lengths of the long runs (>= K) are sorted, together with an anchor value K, and
// the shape keeps the gaps between consecutive sorted values: gaps up to M exactly, larger gaps
// only with their parity ("far"). Equivalently, two positions have the same shape iff they have
// the same runs up to long lengths, and every difference between two long lengths, or between a
// long length and K, is equal in both or at least M + 1 in both with equal sign and parity.
// (Plain capped runs fail: dead TTFF blocks absorb toads and frogs unequally, so capping loses
// the race between Left's and Right's reservoirs. Exact differences within clusters fix this; the
// anchor keeps the reservoirs "far" when a short run grows long.)
//
// Dead regions (Erickson): in a block of pieces with no empty square, everything from the first
// TT to the last FF after it never moves again. A dead region is one marker in the shape (witness
// "TTFF"), and its runs take no part in the differences. With DEADRUNS=1 every dead run is kept
// as its own run instead, with "length >= 2" in place of its length (the format of the Lean proof).
//
// Margin: if all these differences agree or are both >= M + 1 + j, they still are (with j - 1)
// after the same move in both positions, because a move changes one long run by 1 and never
// merges two long runs. So, as for the a = 2 row, it suffices to check the witnesses of a shape:
// each far gap c (c in {M + 1, M + 2}) is replaced by c, c + 2, ..., c + MARGIN, which covers the
// normal form of every position of the shape.
//
// The abstract game: a "U" shape (Left stop <= 0, Right still holds his pass) is won if for every
// witness w, Left's pass and every Left move q from w can be answered by Right's pass (q's shape
// is a won "N" shape) or by a reply into a won U shape. An "N" shape (normal play, Right wins
// moving second) is won if every Left move from every witness has a reply into a won N shape.
// Right's replies must keep the number of runs <= RB (and the number of far gaps <= FB). Concrete
// solving of small witnesses is used only to order and prune Right's options (a concretely losing
// option cannot lead to a won shape). With DUMP=file the closed set is written out (mode + shape).
// MINIMIZE=1 then shrinks it: it computes the exact won region of the explored shapes and rebuilds
// Right's choices greedily, preferring shapes already used. EXPLORE=n first solves alternative
// options too (up to n explored shapes). NODEAD=1 turns off dead regions.
//
// FAILFIRST=1 (fast mode): a shape with a challenge whose options are all lost loses at once, the
// most constrained challenges are tried first, options whose witnesses of at most CONC cells lose
// concretely are dropped, duplicate and subsumed challenges are dropped, and lost shapes forget
// their challenges. This changes which closed set is found, not soundness.
// START=S (with AMIN=a0) instead proves the starts T^a .^B F^a, a >= a0, are <= * ("S" shapes): for
// every witness, Left's move in the * (leaving the witness, Right to move) has a Right reply into
// an N shape, and every Left move q is an N shape itself or has a Right reply into an S shape.
// A start that is its own mirror image and <= * equals *.
// PROGRESS=1 prints the number of explored shapes now and then; MAXEXPLORE=n gives up after n
// explored shapes and prints the DFS stack and statistics of the explored shapes. EB=n allows at
// most n long runs after Right's replies. NOPARITY=1 drops the parity of far gaps (a far gap c is
// then witnessed by c, c + 1, ..., c + MARGIN). MINW=1 makes MINIMIZE prefer shapes with few witnesses.
//
// REAL=amin-amax plays Right's concrete strategy on the real boards instead (boards of at most 28
// cells) and counts the shapes it visits; REALPREF picks the reply heuristic, REALOUT=file writes
// the shapes, COMPONENTS=1 also counts the independent components between dead regions.
//
// The certificate b3_shapes.txt is: MARGIN=4 DEADRUNS=1 MINIMIZE=1 DUMP=out col_shapes 3 10 2 2 28
// followed by sort.
//
// Usage: col_shapes B RB [K [M [CONC [FB]]]]   (shapes are classes; witnesses are all normal forms;
//   CONC (<= 28): largest board solved concretely for pruning; FB: most far gaps after Right's replies)
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int FAILFIRST = getenv("FAILFIRST") != nullptr, PROGRESS = getenv("PROGRESS") != nullptr;
long MAXEXPLORE = getenv("MAXEXPLORE") ? atol(getenv("MAXEXPLORE")) : 0;
int K = 4, RB = 10, B = 3, CONC = 28, FB = 99, MARGIN = getenv("MARGIN") ? atoi(getenv("MARGIN")) : 2;
typedef string Pos;
vector<Pos> lm(const Pos &s) {
  vector<Pos> o; int n = s.size();
  for (int i = 0; i < n; i++) if (s[i] == 'T') {
    if (i + 1 < n && s[i + 1] == '.') { Pos t = s; t[i] = '.'; t[i + 1] = 'T'; o.push_back(t); }
    else if (i + 2 < n && s[i + 1] == 'F' && s[i + 2] == '.') { Pos t = s; t[i] = '.'; t[i + 2] = 'T'; o.push_back(t); }
  }
  return o;
}
vector<Pos> rm(const Pos &s) {
  vector<Pos> o; int n = s.size();
  for (int i = n - 1; i >= 0; i--) if (s[i] == 'F') {
    if (i >= 1 && s[i - 1] == '.') { Pos t = s; t[i] = '.'; t[i - 1] = 'F'; o.push_back(t); }
    else if (i >= 2 && s[i - 1] == 'T' && s[i - 2] == '.') { Pos t = s; t[i] = '.'; t[i - 2] = 'F'; o.push_back(t); }
  }
  return o;
}
vector<pair<char,int>> runs(const Pos &s) {
  vector<pair<char,int>> v;
  for (char c : s) { if (!v.empty() && v.back().first == c) v.back().second++; else v.push_back({c, 1}); }
  return v;
}
int nruns(const Pos &s) { int r = 0; for (size_t i = 0; i < s.size(); i++) if (i == 0 || s[i] != s[i - 1]) r++; return r; }
int M = 4;   // gaps (between sorted long runs, starting from the anchor K) up to M are exact
int unbalanced = 0;
// Shape of a position: its runs, with short runs (< K) exact and long runs replaced by their rank
// in the sorted order of long runs; plus the gaps between consecutive sorted long lengths, starting
// from the anchor K, with gaps > M capped to M + 1 + parity. Two positions have the same shape
// iff they are related with margin 0. A witness replaces each capped gap c by c (the position's
// gap was c) or c + 2 (it was >= c + 2); the normal form of a position is one of its witnesses.
typedef string Shape;
int NOPARITY = getenv("NOPARITY") != nullptr, MINW = getenv("MINW") != nullptr;   // far gaps keep only their sign, not their parity
int DEAD = 1, DEADRUNS = getenv("DEADRUNS") != nullptr;   // collapse dead TTFF blocks (their pieces never move; their lengths never matter)
// Dead regions (Erickson): in a block of pieces with no empty square, everything from the first
// TT to the last FF after it can never move again. Its contents never matter.
vector<bool> deadRuns(const vector<pair<char,int>> &rs) {
  int m = rs.size(); vector<bool> d(m, false);
  if (DEAD == 0) return d;
  if (getenv("DEADJ")) {   // junction rule only: a toad run >= 2 directly followed by a frog run >= 2
    for (int k = 0; k + 1 < m; k++)
      if (rs[k].first == 'T' && rs[k + 1].first == 'F' && rs[k].second >= 2 && rs[k + 1].second >= 2) d[k] = d[k + 1] = true;
    return d;
  }
  int i = 0;
  while (i < m) {
    if (rs[i].first == '.') { i++; continue; }
    int j = i; while (j < m && rs[j].first != '.') j++;   // runs i..j-1 form a block of pieces
    int st = -1, en = -1;
    for (int k = i; k < j; k++) if (rs[k].first == 'T' && rs[k].second >= 2) { st = k; break; }
    if (st >= 0) for (int k = j - 1; k > st; k--) if (rs[k].first == 'F' && rs[k].second >= 2) { en = k; break; }
    if (st >= 0 && en >= 0) for (int k = st; k <= en; k++) d[k] = true;
    i = j;
  }
  return d;
}
Shape shapeOf(const Pos &p) {
  auto rs = runs(p); int m = rs.size(); auto dd = deadRuns(rs);
  vector<pair<int,int>> lv;
  for (int i = 0; i < m; i++) if (rs[i].second >= K && !dd[i] && rs[i].first != '.') lv.push_back({rs[i].second, i});
  stable_sort(lv.begin(), lv.end());
  vector<int> rank(m, -1); for (int k = 0; k < (int)lv.size(); k++) rank[lv[k].second] = k;
  Shape t;
  for (int i = 0; i < m; i++) {
    if (dd[i]) {
      if (DEADRUNS) { t += rs[i].first; t += rs[i].second == 1 ? '1' : 'D'; continue; }   // each dead run, length free if >= 2
      if (i == 0 || !dd[i - 1]) t += "XD"; continue; }
    t += rs[i].first; t += rank[i] < 0 ? char('0' + rs[i].second) : char('a' + rank[i]); }
  t += '|';
  int prev = K;
  for (auto [l, i] : lv) { int g = l - prev; prev = l; t += char('0' + (g <= M ? g : NOPARITY ? M + 1 : M + 1 + (g - M - 1) % 2)); }
  return t;
}
vector<Pos> wit(const Shape &s) {
  size_t bar = s.find('|'); string sk = s.substr(0, bar), gs = s.substr(bar + 1);
  int L = gs.size(); vector<int> far; for (int k = 0; k < L; k++) if (gs[k] - '0' > M) far.push_back(k);
  vector<Pos> out;
  // far gap c: with parity, c, c + 2, ..., c + MARGIN; without (NOPARITY), c, c + 1, ..., c + MARGIN
  int base = NOPARITY ? MARGIN + 1 : MARGIN / 2 + 1, step = NOPARITY ? 1 : 2, total = 1; for (size_t j = 0; j < far.size(); j++) total *= base;
  for (int mask = 0; mask < total; mask++) {
    vector<int> g(L); for (int k = 0; k < L; k++) g[k] = gs[k] - '0';
    for (size_t j = 0, mm = mask; j < far.size(); j++, mm /= base) g[far[j]] += step * (mm % base);
    vector<int> len(L); int cur = K; for (int k = 0; k < L; k++) { cur += g[k]; len[k] = cur; }
    Pos p; for (size_t i = 0; i < sk.size(); i += 2) { char c = sk[i], v = sk[i + 1]; if (c == 'X') p += "TTFF"; else p += string(v == 'D' ? 2 : v >= 'a' ? len[v - 'a'] : v - '0', c); }
    // balance check (all game positions have as many toads as frogs)
    if (count(p.begin(), p.end(), 'T') != count(p.begin(), p.end(), 'F')) unbalanced++;   // kept: needed for soundness
    out.push_back(p);
  }
  return out;
}
int deltaOf(const Shape &) { return 0; }
// Concrete bounded solver. A board of n <= 28 cells is a 64-bit code: 2 bits per cell (0 empty,
// 1 toad, 2 frog) and n in the top bits. One table holds all three memos (bit pairs: known, value).
static inline int ncells(u64 s) { return s >> 56; }
static inline int cellc(u64 s, int i) { return (s >> (2 * i)) & 3; }
static inline u64 setc(u64 s, int i, int v) { return (s & ~(3ULL << (2 * i))) | ((u64)v << (2 * i)); }
u64 enc(const Pos &p) { u64 s = (u64)p.size() << 56; for (size_t i = 0; i < p.size(); i++) s |= (u64)(p[i] == 'T' ? 1 : p[i] == 'F' ? 2 : 0) << (2 * i); return s; }
int nrunsc(u64 s) { int n = ncells(s), r = 0, prev = -1; for (int i = 0; i < n; i++) { int c = cellc(s, i); if (c != prev) r++; prev = c; } return r; }
int lmc(u64 s, u64 *o) {
  int n = ncells(s), k = 0;
  for (int i = 0; i < n; i++) if (cellc(s, i) == 1) {
    if (i + 1 < n && cellc(s, i + 1) == 0) o[k++] = setc(setc(s, i, 0), i + 1, 1);
    else if (i + 2 < n && cellc(s, i + 1) == 2 && cellc(s, i + 2) == 0) o[k++] = setc(setc(s, i, 0), i + 2, 1);
  }
  return k;
}
int rmc(u64 s, u64 *o) {
  int n = ncells(s), k = 0;
  for (int i = n - 1; i >= 0; i--) if (cellc(s, i) == 2) {
    if (i >= 1 && cellc(s, i - 1) == 0) o[k++] = setc(setc(s, i, 0), i - 1, 2);
    else if (i >= 2 && cellc(s, i - 1) == 1 && cellc(s, i - 2) == 0) o[k++] = setc(setc(s, i, 0), i - 2, 2);
  }
  return k;
}
// open-addressing table: board code -> flags
struct Memo {
  vector<u64> key; vector<unsigned char> val; size_t cnt = 0, mask = 0;
  Memo() { key.assign(1 << 20, 0); val.assign(1 << 20, 0); mask = (1 << 20) - 1; }
  static size_t h(u64 x) { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; }
  unsigned char &slot(u64 k) {
    if (2 * (cnt + 1) > key.size()) grow();
    size_t i = h(k) & mask;
    while (key[i] && key[i] != k) i = (i + 1) & mask;
    if (!key[i]) { key[i] = k; cnt++; }
    return val[i];
  }
  unsigned char get(u64 k) const { size_t i = h(k) & mask; while (key[i]) { if (key[i] == k) return val[i]; i = (i + 1) & mask; } return 0; }
  void grow() {
    vector<u64> ok; vector<unsigned char> ov; ok.swap(key); ov.swap(val);
    key.assign(ok.size() * 2, 0); val.assign(ok.size() * 2, 0); mask = key.size() - 1; cnt = 0;
    for (size_t i = 0; i < ok.size(); i++) if (ok[i]) { size_t j = h(ok[i]) & mask; while (key[j]) j = (j + 1) & mask; key[j] = ok[i]; val[j] = ov[i]; cnt++; }
  }
} memo;
enum { LE = 0, LF = 2, UP = 4, LS = 6 };
bool le0c(u64 s) {
  unsigned char f = memo.get(s); if (f >> LE & 1) return f >> (LE + 1) & 1;
  bool r = true; u64 qs[64], ts[64];
  int nq = lmc(s, qs);
  for (int a = 0; a < nq && r; a++) { bool ok = false; int nt = rmc(qs[a], ts); for (int b = 0; b < nt; b++) if (nrunsc(ts[b]) <= RB && le0c(ts[b])) { ok = true; break; } if (!ok) r = false; }
  memo.slot(s) |= (1 | (r ? 2 : 0)) << LE; return r;
}
bool Upc(u64 s);
bool Lfc(u64 s) {
  unsigned char f = memo.get(s); if (f >> LF & 1) return f >> (LF + 1) & 1;
  bool r = nrunsc(s) <= RB && le0c(s); u64 ts[64];
  if (!r) { int nt = rmc(s, ts); for (int b = 0; b < nt; b++) if (nrunsc(ts[b]) <= RB && Upc(ts[b])) { r = true; break; } }
  memo.slot(s) |= (1 | (r ? 2 : 0)) << LF; return r;
}
bool Upc(u64 s) {
  unsigned char f = memo.get(s); if (f >> UP & 1) return f >> (UP + 1) & 1;
  bool r = Lfc(s); u64 qs[64];
  if (r) { int nq = lmc(s, qs); for (int a = 0; a < nq; a++) if (!Lfc(qs[a])) { r = false; break; } }
  memo.slot(s) |= (1 | (r ? 2 : 0)) << UP; return r;
}
// s <= *: some Right move reaches a position <= 0 (Left took the *), and every Left move q is <= 0
// itself or has a Right reply <= * (Right's replies keep at most RB runs).
bool LSc(u64 s) {
  unsigned char f = memo.get(s); if (f >> LS & 1) return f >> (LS + 1) & 1;
  bool r = false; u64 qs[64], ts[64];
  int nt = rmc(s, ts); for (int b = 0; b < nt; b++) if (nrunsc(ts[b]) <= RB && le0c(ts[b])) { r = true; break; }
  if (r) { int nq = lmc(s, qs);
    for (int a = 0; a < nq && r; a++) {
      if (nrunsc(qs[a]) <= RB && le0c(qs[a])) continue;
      bool ok = false; int nr = rmc(qs[a], ts); for (int b = 0; b < nr; b++) if (nrunsc(ts[b]) <= RB && LSc(ts[b])) { ok = true; break; }
      if (!ok) r = false; } }
  memo.slot(s) |= (1 | (r ? 2 : 0)) << LS; return r;
}
// string interface; callers only solve boards of at most CONC <= 28 cells
bool le0(const Pos &s) { return le0c(enc(s)); }
bool Up(const Pos &s) { return Upc(enc(s)); }
bool LeS(const Pos &s) { return LSc(enc(s)); }
int farGaps(const Shape &s) { size_t bar = s.find('|'); int f = 0; for (size_t k = bar + 1; k < s.size(); k++) if (s[k] - '0' > M) f++; return f; }
int EB = getenv("EB") ? atoi(getenv("EB")) : 99;   // most long runs (entries) after Right's replies
bool okShape(const Pos &r) { if (nruns(r) > RB) return false; Shape s = shapeOf(r); return farGaps(s) <= FB && (int)(s.size() - s.find('|') - 1) <= EB; }
// abstract game. Node = mode ('U' or 'N') + shape, interned as an id.
typedef string Node;
unordered_map<Node, int> ids; vector<const Node *> nm;
vector<signed char> status;       // 1 on stack, 2 won (tentative), 3 lost
vector<signed char> concv;        // 1 / -1: small witnesses win / lose concretely
vector<long> cplxv; vector<char> isPref, chalDone;
vector<vector<int>> chalv;        // flattened challenges: [count, options...]*
vector<vector<int>> choicev;
set<Node> pref;                   // preferred shapes (file PREF: e.g. the shapes real play uses)
size_t nExplored = 0;
int idOf(const Node &x) {
  auto it = ids.find(x); if (it != ids.end()) return it->second;
  int k = nm.size(); auto r = ids.emplace(x, k); nm.push_back(&r.first->first);
  status.push_back(0); concv.push_back(0); cplxv.push_back(-1); isPref.push_back(pref.count(x) > 0); chalDone.push_back(0); chalv.emplace_back(); choicev.emplace_back();
  return k;
}
int stOf(const Node &x) { auto it = ids.find(x); return it == ids.end() ? 0 : status[it->second]; }
long cplx(int id) {         // complexity of a shape: far gaps first, then witness size
  if (cplxv[id] >= 0) return cplxv[id];
  Shape s = nm[id]->substr(1); size_t bar = s.find('|'); long far = 0;
  for (size_t k = bar + 1; k < s.size(); k++) if (s[k] - '0' > M) far++;
  long len = 0; for (auto &w : wit(s)) len = max(len, (long)w.size());
  long ent = s.size() - bar - 1;   // fast mode: fewest long runs first
  return cplxv[id] = (FAILFIRST ? ent * 1000000 : 0) + far * 10000 + len * 10 + (long)(bar / 2);
}
// A won shape makes every position of the shape good for Right (with at most RB runs), its
// witnesses included. So an option whose small witnesses lose concretely can be dropped (fast mode).
bool concOK(int id) {
  if (concv[id]) return concv[id] > 0;
  const Node &x = *nm[id]; bool ok = true;
  for (auto &w : wit(x.substr(1))) if ((int)w.size() <= CONC && !(x[0] == 'U' ? Up(w) : x[0] == 'S' ? LeS(w) : le0(w))) { ok = false; break; }
  concv[id] = ok ? 1 : -1; return ok;
}
vector<vector<int>> unflat(const vector<int> &f) {
  vector<vector<int>> cs; for (size_t i = 0; i < f.size(); ) { int c = f[i++]; cs.emplace_back(f.begin() + i, f.begin() + i + c); i += c; } return cs;
}
vector<int> path;                 // the DFS stack
void report() {   // when giving up: the DFS stack and statistics of the explored shapes
  printf("gave up: more than %ld shapes explored; DFS depth %zu\n", MAXEXPLORE, path.size());
  for (size_t i = path.size() > 40 ? path.size() - 40 : 0; i < path.size(); i++) printf("  %3zu %s\n", i, nm[path[i]]->c_str());
  map<int, array<long, 4>> byRuns, byEnt, byFar;
  for (size_t x = 0; x < nm.size(); x++) if (chalDone[x] || status[x] == 3) {
    const Node &n = *nm[x]; size_t bar = n.find('|'); int runs = (bar - 1) / 2, ent = n.size() - bar - 1, far = farGaps(n.substr(1));
    int st = status[x] == 3 ? 1 : status[x] == 2 ? 2 : 3;
    byRuns[runs][0]++; byRuns[runs][st]++; byEnt[ent][0]++; byEnt[ent][st]++; byFar[far][0]++; byFar[far][st]++; }
  auto show = [](const char *t, map<int, array<long, 4>> &m) { printf("%s (total / lost / won / open):", t); for (auto &[k, v] : m) printf("  %d: %ld/%ld/%ld/%ld", k, v[0], v[1], v[2], v[3]); printf("\n"); };
  show("by runs", byRuns); show("by entries", byEnt); show("by far gaps", byFar);
  fflush(stdout);
}
vector<vector<int>> challenges(int xid) {
  if (chalDone[xid]) return unflat(chalv[xid]);
  if (PROGRESS && nExplored % 20000 == 0) {
    fprintf(stderr, "  progress: %zu shapes explored, %zu ids, %zu concrete states, %ld s\n", nExplored, nm.size(),
            memo.cnt, (long)(clock() / CLOCKS_PER_SEC));
    fflush(stderr);
  }
  nExplored++;
  if (MAXEXPLORE && (long)nExplored > MAXEXPLORE) { report(); exit(2); }
  Node x = *nm[xid];
  vector<vector<int>> cs; char mode = x[0]; Shape s = x.substr(1);
  for (auto &w : wit(s)) {
    vector<Pos> qs = lm(w); if (mode == 'U') qs.push_back(w);
    if (mode == 'S') {   // Left takes the *: Right must move to a position <= 0
      vector<int> opts; bool conc = (int)w.size() <= CONC;
      for (auto &r : rm(w)) if (okShape(r) && (!conc || le0(r))) opts.push_back(idOf("N" + shapeOf(r)));
      cs.push_back(opts);
    }
    for (auto &q : qs) {
      vector<int> opts;
      bool conc = (int)q.size() <= CONC;   // concrete pruning only on small boards
      if (mode == 'U' || mode == 'S') {
        if (okShape(q) && (!conc || le0(q))) opts.push_back(idOf("N" + shapeOf(q)));
        if (mode == 'U') { for (auto &r : rm(q)) if (okShape(r) && (!conc || Up(r))) opts.push_back(idOf("U" + shapeOf(r))); }
        else for (auto &r : rm(q)) if (okShape(r) && (!conc || LeS(r))) opts.push_back(idOf("S" + shapeOf(r)));
      } else {
        for (auto &r : rm(q)) if (okShape(r) && (!conc || le0(r))) opts.push_back(idOf("N" + shapeOf(r)));
      }
      cs.push_back(opts);
    }
  }
  if (FAILFIRST) {   // drop duplicate options, options losing concretely, duplicate challenges and challenges implied by smaller ones
    for (auto &c : cs) { sort(c.begin(), c.end()); c.erase(unique(c.begin(), c.end()), c.end());
      c.erase(remove_if(c.begin(), c.end(), [](int o) { return !concOK(o); }), c.end()); }
    stable_sort(cs.begin(), cs.end(), [](const vector<int> &a, const vector<int> &b) { return a.size() < b.size(); });
    vector<vector<int>> kept;
    for (auto &c : cs) { bool sub = false; for (auto &k : kept) if (includes(c.begin(), c.end(), k.begin(), k.end())) { sub = true; break; } if (!sub) kept.push_back(c); }
    cs.swap(kept);
  }
  vector<int> f; for (auto &c : cs) { f.push_back(c.size()); f.insert(f.end(), c.begin(), c.end()); }
  f.shrink_to_fit(); chalv[xid].swap(f); chalDone[xid] = 1;
  return cs;
}
bool dfs(int x) {
  int st = status[x];
  if (st == 3) return false;
  if (st == 1 || st == 2) return true;
  status[x] = 1; path.push_back(x);
  vector<int> picks;
  vector<vector<int>> cs = challenges(x);
  auto lose = [&]() { status[x] = 3; path.pop_back(); if (FAILFIRST) { vector<int>().swap(chalv[x]); chalDone[x] = 0; } return false; };
  if (FAILFIRST) {   // fail first: a challenge with no option left loses at once; then the most constrained first
    for (auto &c : cs) { vector<int> v; for (int o : c) if (status[o] != 3) v.push_back(o); if (v.empty()) return lose(); c.swap(v); }
    stable_sort(cs.begin(), cs.end(), [](const vector<int> &a, const vector<int> &b) { return a.size() < b.size(); });
  }
  for (auto &opts : cs) {
    stable_sort(opts.begin(), opts.end(), [](int a, int b) {
      int ka = (status[a] == 2 ? 0 : 2) + (isPref[a] ? 0 : 1), kb = (status[b] == 2 ? 0 : 2) + (isPref[b] ? 0 : 1);
      if (ka != kb) return ka < kb;
      return cplx(a) < cplx(b); });
    bool ok = false;
    for (int o : opts) if (dfs(o)) { picks.push_back(o); ok = true; break; }
    if (!ok) return lose();
  }
  choicev[x] = picks; status[x] = 2; path.pop_back();
  return true;
}
// Explain why a node is lost: the first challenge with no surviving option, then follow one option.
void why(const Node &x, int depth, set<Node> &seen) {
  if (depth > 12 || !seen.insert(x).second) return;
  char mode = x[0]; Shape s = x.substr(1);
  for (auto &w : wit(s)) {
    vector<Pos> qs = lm(w); if (mode == 'U') qs.push_back(w);
    for (auto &q : qs) {
      vector<Node> opts; bool conc = (int)q.size() <= CONC;
      if (mode == 'U') {
        if (okShape(q) && (!conc || le0(q))) opts.push_back("N" + shapeOf(q));
        for (auto &r : rm(q)) if (okShape(r) && (!conc || Up(r))) opts.push_back("U" + shapeOf(r));
      } else for (auto &r : rm(q)) if (okShape(r) && (!conc || le0(r))) opts.push_back("N" + shapeOf(r));
      bool alive = false; for (auto &o : opts) if (stOf(o) != 3) alive = true;
      if (alive) continue;
      bool small = (int)w.size() <= CONC;
      printf("%*s%s  witness %s  %s %s  -> %zu options, all lost%s\n", 2 * depth, "", x.c_str(), w.c_str(),
             q == w ? "pass" : "move", q.c_str(), opts.size(),
             opts.empty() && small ? (mode == 'U' ? (Up(w) ? "" : "  [witness itself loses]") : (le0(w) ? "" : "  [witness itself loses]")) : "");
      if (!opts.empty()) why(opts[0], depth + 1, seen);
      return;
    }
  }
}
// REAL=amin-amax: play Right's concrete strategy (at most RB runs) from T^a .^B F^a for each a,
// choosing replies whose shapes were used before when possible, and report the shapes visited.
// With REALOUT=file the shapes are written out (usable as PREF).
void realPlay(int a0, int a1) {
  set<int> used; vector<int> order;
  auto use = [&](int id) { if (used.insert(id).second) order.push_back(id); };
  int pr = getenv("REALPREF") ? atoi(getenv("REALPREF")) : 0;   // 0: fewest long runs; 1: fewest runs; 2: fewest live runs
  auto score = [&](int id) {
    const Node &n = *nm[id]; size_t bar = n.find('|'); long runsN = (bar - 1) / 2, live = 0;
    for (size_t k = 1; k + 1 < bar; k += 2) if (n[k + 1] != 'D' && !(k + 3 < bar && n[k + 3] == 'D' && n[k] == 'F' && n[k + 1] == '1')) live++;
    long sec = pr == 1 ? runsN * 1000000 + cplx(id) : pr == 2 ? live * 1000000 + cplx(id) : cplx(id);
    return (used.count(id) ? 0L : 1L << 40) + sec; };
  for (int a = a0; a <= a1; a++) {
    Pos s0 = string(a, 'T') + string(B, '.') + string(a, 'F');
    if ((int)s0.size() > 28) { printf("a=%d: board too large\n", a); break; }
    if (!Up(s0)) { printf("a=%d: Right loses with %d runs\n", a, RB); continue; }
    size_t before = used.size();
    set<pair<char, Pos>> seen; deque<pair<char, Pos>> todo{{'U', s0}};
    while (!todo.empty()) {
      auto [mode, p] = todo.front(); todo.pop_front();
      if (!seen.insert({mode, p}).second) continue;
      use(idOf(string(1, mode) + shapeOf(p)));
      vector<Pos> qs = lm(p); if (mode == 'U') qs.push_back(p);
      for (auto &q : qs) {
        long best = LONG_MAX; pair<char, Pos> nxt; 
        auto consider = [&](char m, const Pos &r) { long sc = score(idOf(string(1, m) + shapeOf(r))); if (sc < best) { best = sc; nxt = {m, r}; } };
        if (mode == 'U') {
          if (nruns(q) <= RB && le0(q)) consider('N', q);
          for (auto &r : rm(q)) if (nruns(r) <= RB && Up(r)) consider('U', r);
        } else for (auto &r : rm(q)) if (nruns(r) <= RB && le0(r)) consider('N', r);
        if (best == LONG_MAX) { printf("a=%d: no answer to %s from %s\n", a, q.c_str(), p.c_str()); continue; }
        todo.push_back(nxt);
      }
    }
    if (getenv("COMPONENTS")) {   // split each visited position at its dead regions (walls) into independent components
      static map<string, long> comps; static map<int, long> byEmpties, byCount; size_t c0 = comps.size();
      for (auto &[mode, p] : seen) {
        auto rs = runs(p); auto dd = deadRuns(rs); vector<string> parts; string cur; size_t pos = 0;
        for (size_t i = 0; i < rs.size(); i++) { if (dd[i]) { if (!cur.empty()) parts.push_back(cur); cur.clear(); } else cur += p.substr(pos, rs[i].second); pos += rs[i].second; }
        if (!cur.empty()) parts.push_back(cur);
        int withE = 0;
        for (auto &c : parts) { int e = count(c.begin(), c.end(), '.'); if (!e) continue; withE++; comps[shapeOf(c)]++; byEmpties[e]++; }
        byCount[withE]++;
      }
      printf("  components: %zu distinct shapes (%zu new); by empty squares:", comps.size(), comps.size() - c0);
      for (auto &[k, v] : byEmpties) printf(" %d:%ld", k, v);
      printf("; components with an empty square per position:"); for (auto &[k, v] : byCount) printf(" %d:%ld", k, v); printf("\n");
    }
    int ent = 0; for (int id : order) ent = max(ent, (int)(nm[id]->size() - nm[id]->find('|') - 1));
    printf("a=%d: %zu positions, %zu shapes in total (%zu new), most long runs %d, concrete states %zu\n", a, seen.size(), used.size(), used.size() - before, ent, memo.cnt);
    fflush(stdout);
  }
  if (getenv("REALOUT")) { FILE *f = fopen(getenv("REALOUT"), "w"); for (int id : order) fprintf(f, "%s\n", nm[id]->c_str()); fclose(f); }
}
int main(int argc, char **argv) {
  B = atoi(argv[1]); RB = atoi(argv[2]); if (argc > 3) K = atoi(argv[3]); if (argc > 4) M = atoi(argv[4]); if (argc > 5) CONC = atoi(argv[5]); if (argc > 6) FB = atoi(argv[6]); if (getenv("NODEAD")) DEAD = 0;
  if (CONC > 28) { fprintf(stderr, "CONC must be <= 28\n"); return 1; }
  if (getenv("REAL")) { int a0, a1; sscanf(getenv("REAL"), "%d-%d", &a0, &a1); realPlay(a0, a1); return 0; }
  if (getenv("PREF")) { ifstream f(getenv("PREF")); string l; while (getline(f, l)) if (!l.empty()) pref.insert(l); printf("%zu preferred shapes\n", pref.size()); }
  vector<int> starts;
  { set<Node> st; const char *sm = getenv("START"); int a0 = getenv("AMIN") ? atoi(getenv("AMIN")) : K;
    for (int a = max(K, a0); a < K + M + 8; a++) st.insert((sm && sm[0] == 'S' ? "S" : "U") + shapeOf(string(a, 'T') + string(B, '.') + string(a, 'F')));
    for (auto &x : st) printf("start %s\n", x.c_str());
    for (auto &x : st) starts.push_back(idOf(x)); }
  for (int it = 0; it < 500; it++) {
    for (auto &v : status) if (v != 3) v = 0;
    vector<int> lost;
    for (int s : starts) if (!dfs(s)) lost.push_back(s);
    if (!lost.empty()) { printf("iteration %d: start lost:", it); for (int s : lost) printf(" %s", nm[s]->c_str()); printf("  (%zu nodes explored)\n", nExplored);
      set<Node> seen; why(*nm[lost[0]], 0, seen); return 1; }
    set<int> W; deque<int> todo(starts.begin(), starts.end());
    while (!todo.empty()) { int x = todo.front(); todo.pop_front(); if (!W.insert(x).second) continue; for (int y : choicev[x]) todo.push_back(y); }
    int bad = 0; for (int x : W) for (int y : choicev[x]) if (status[y] == 3) { bad++; break; }
    int nu = 0, maxw = 0, maxlen = 0, maxd = 0;
    for (int x : W) { if ((*nm[x])[0] != 'N') nu++; auto ws = wit(nm[x]->substr(1)); maxw = max(maxw, (int)ws.size()); for (auto &w : ws) maxlen = max(maxlen, (int)w.size()); maxd = max(maxd, abs(deltaOf(nm[x]->substr(1)))); }
    printf("[unbalanced witnesses skipped: %d] ", unbalanced);
    printf("iteration %d: %zu shapes (%d U), %d rely on lost ones; explored %zu; max witnesses %d, max length %d, max |Delta| %d; concrete states %zu\n",
           it, W.size(), nu, bad, nExplored, maxw, maxlen, maxd, memo.cnt);
    fflush(stdout);
    if (!bad) {
      printf("CLOSED\n");
      if (getenv("EXPLORE")) {   // also solve every alternative option of the shapes in use
        size_t cap = atol(getenv("EXPLORE"));
        for (int pass = 0; pass < 3 && nExplored < cap; pass++) {
          vector<int> todo2(W.begin(), W.end());
          for (int x : todo2) { if (nExplored >= cap) break; for (auto &opts : challenges(x)) for (int o : opts) if (status[o] == 0) dfs(o); }
          printf("  explore pass %d: %zu nodes explored\n", pass, nExplored); fflush(stdout);
        }
      }
      if (getenv("MINIMIZE")) {
        // exact won region of the explored graph (greatest fixpoint): any choice inside it is closed
        int N = nm.size(); vector<char> valid(N, 0);
        for (int x = 0; x < N; x++) valid[x] = chalDone[x] && status[x] != 3;
        vector<vector<vector<int>>> ch(N);
        for (int x = 0; x < N; x++) if (valid[x]) ch[x] = unflat(chalv[x]);
        for (bool chg = true; chg; ) { chg = false;
          for (int x = 0; x < N; x++) if (valid[x]) {
            bool ok = true;
            for (auto &opts : ch[x]) { bool any = false; for (int o : opts) if (valid[o]) { any = true; break; } if (!any) { ok = false; break; } }
            if (!ok) { valid[x] = 0; chg = true; } } }
        vector<long> pop(N, 0);
        for (int x = 0; x < N; x++) if (valid[x]) for (auto &opts : ch[x]) for (int o : opts) if (valid[o]) pop[o]++;
        set<int> cur = W;
        for (int round = 0; round < 30; round++) {
          set<int> nw; deque<int> td(starts.begin(), starts.end());
          while (!td.empty()) { int x = td.front(); td.pop_front(); if (!nw.insert(x).second) continue;
            for (auto &opts : ch[x]) { int best = -1; long bs = -1;
              for (int o : opts) if (valid[o]) {
                long sc = (cur.count(o) ? 1000000000L : 0) + (nw.count(o) ? 2000000000L : 0) + pop[o];
                if (MINW) sc -= 1000000L * (long)wit(nm[o]->substr(1)).size();   // MINW=1: fewest witnesses first
                if (sc > bs) { bs = sc; best = o; } }
              td.push_back(best); } }
          printf("  minimise round %d: %zu shapes\n", round, nw.size()); fflush(stdout);
          if (nw.size() >= cur.size() && round > 0) break;
          cur = nw; }
        W = cur;
        int nu2 = 0; for (int x : W) if ((*nm[x])[0] != 'N') nu2++;
        printf("MINIMISED to %zu shapes (%d U)\n", W.size(), nu2);
      }
      if (getenv("DUMP")) { set<Node> out; for (int x : W) out.insert(*nm[x]); FILE *f = fopen(getenv("DUMP"), "w"); for (auto &x : out) fprintf(f, "%s\n", x.c_str()); fclose(f); }
      return 0; }
  }
}
