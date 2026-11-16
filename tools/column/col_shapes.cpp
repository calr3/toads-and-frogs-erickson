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
// "TTFF"), and its runs take no part in the differences.
//
// Margin: if all these differences agree or are both >= M + 1 + j, they still are (with j - 1)
// after the same move in both positions, because a move changes one long run by 1 and never
// merges two long runs. So, as for the a = 2 row, it suffices to check the witnesses of a shape:
// each far gap c (c in {M + 1, M + 2}) is replaced by c or c + 2, which covers the normal form
// of every position of the shape (far gaps lowered to M + 3 or M + 4).
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
// The certificate b3_shapes.txt (2,861 shapes) is: MINIMIZE=1 DUMP=out col_shapes 3 10 2 2
// followed by sort.
//
// Usage: col_shapes B RB [K [M [CONC [FB]]]]   (shapes are classes; witnesses are all normal forms;
//   CONC: largest board solved concretely for pruning; FB: most far gaps allowed after Right's replies)
#include <bits/stdc++.h>
using namespace std;
int K = 4, RB = 10, B = 3, CONC = 28, FB = 99;
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
int nruns(const Pos &s) { return runs(s).size(); }
int M = 4;   // gaps (between sorted long runs, starting from the anchor K) up to M are exact
int unbalanced = 0;
// Shape of a position: its runs, with short runs (< K) exact and long runs replaced by their rank
// in the sorted order of long runs; plus the gaps between consecutive sorted long lengths, starting
// from the anchor K, with gaps > M capped to M + 1 + parity. Two positions have the same shape
// iff they are related with margin 0. A witness replaces each capped gap c by c (the position's
// gap was c) or c + 2 (it was >= c + 2); the normal form of a position is one of its witnesses.
typedef string Shape;
int DEAD = 1;   // collapse dead TTFF blocks (their pieces never move; their lengths never matter)
// Dead regions (Erickson): in a block of pieces with no empty square, everything from the first
// TT to the last FF after it can never move again. Its contents never matter.
vector<bool> deadRuns(const vector<pair<char,int>> &rs) {
  int m = rs.size(); vector<bool> d(m, false);
  if (DEAD == 0) return d;
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
  for (int i = 0; i < m; i++) if (rs[i].second >= K && !dd[i]) lv.push_back({rs[i].second, i});
  stable_sort(lv.begin(), lv.end());
  vector<int> rank(m, -1); for (int k = 0; k < (int)lv.size(); k++) rank[lv[k].second] = k;
  Shape t;
  for (int i = 0; i < m; i++) {
    if (dd[i]) { if (i == 0 || !dd[i - 1]) t += "XD"; continue; }
    t += rs[i].first; t += rank[i] < 0 ? char('0' + rs[i].second) : char('a' + rank[i]); }
  t += '|';
  int prev = K;
  for (auto [l, i] : lv) { int g = l - prev; prev = l; t += char('0' + (g <= M ? g : M + 1 + (g - M - 1) % 2)); }
  return t;
}
vector<Pos> wit(const Shape &s) {
  size_t bar = s.find('|'); string sk = s.substr(0, bar), gs = s.substr(bar + 1);
  int L = gs.size(); vector<int> far; for (int k = 0; k < L; k++) if (gs[k] - '0' > M) far.push_back(k);
  vector<Pos> out;
  for (int mask = 0; mask < (1 << far.size()); mask++) {
    vector<int> g(L); for (int k = 0; k < L; k++) g[k] = gs[k] - '0';
    for (size_t j = 0; j < far.size(); j++) if (mask >> j & 1) g[far[j]] += 2;
    vector<int> len(L); int cur = K; for (int k = 0; k < L; k++) { cur += g[k]; len[k] = cur; }
    Pos p; for (size_t i = 0; i < sk.size(); i += 2) { char c = sk[i], v = sk[i + 1]; if (c == 'X') p += "TTFF"; else p += string(v >= 'a' ? len[v - 'a'] : v - '0', c); }
    // balance check (all game positions have as many toads as frogs)
    if (count(p.begin(), p.end(), 'T') != count(p.begin(), p.end(), 'F')) unbalanced++;   // kept: needed for soundness
    out.push_back(p);
  }
  return out;
}
int deltaOf(const Shape &) { return 0; }
// concrete bounded solver (memoised on strings)
unordered_map<Pos, char> mLE, mUP, mLF;
bool le0(const Pos &s) {
  auto it = mLE.find(s); if (it != mLE.end()) return it->second;
  bool r = true;
  for (auto &q : lm(s)) { bool ok = false; for (auto &t : rm(q)) if (nruns(t) <= RB && le0(t)) { ok = true; break; } if (!ok) { r = false; break; } }
  return mLE[s] = r;
}
bool Up(const Pos &s);
bool Lf(const Pos &s) {
  auto it = mLF.find(s); if (it != mLF.end()) return it->second;
  bool r = nruns(s) <= RB && le0(s);
  if (!r) for (auto &t : rm(s)) if (nruns(t) <= RB && Up(t)) { r = true; break; }
  return mLF[s] = r;
}
bool Up(const Pos &s) {
  auto it = mUP.find(s); if (it != mUP.end()) return it->second;
  bool r = Lf(s);
  if (r) for (auto &q : lm(s)) if (!Lf(q)) { r = false; break; }
  return mUP[s] = r;
}
int farGaps(const Shape &s) { size_t bar = s.find('|'); int f = 0; for (size_t k = bar + 1; k < s.size(); k++) if (s[k] - '0' > M) f++; return f; }
bool okShape(const Pos &r) { return nruns(r) <= RB && farGaps(shapeOf(r)) <= FB; }
// abstract game. Node = mode ('U' or 'N') + shape.
typedef string Node;
set<Node> pref;                   // preferred shapes (file PREF: e.g. the shapes real play uses)
vector<Pos> wit(const Shape &s);
map<Node, long> cplxMemo;
long cplx(const Node &x) {         // complexity of a shape: far gaps first, then witness size
  auto it = cplxMemo.find(x); if (it != cplxMemo.end()) return it->second;
  Shape s = x.substr(1); size_t bar = s.find('|'); long far = 0;
  for (size_t k = bar + 1; k < s.size(); k++) if (s[k] - '0' > M) far++;
  long len = 0; for (auto &w : wit(s)) len = max(len, (long)w.size());
  return cplxMemo[x] = far * 10000 + len * 10 + (long)(bar / 2);
}
map<Node, int> status;            // 1 on stack, 2 won (tentative), 3 lost
map<Node, vector<Node>> choice;
map<Node, vector<vector<Node>>> chal;
const vector<vector<Node>> &challenges(const Node &x) {
  auto it = chal.find(x); if (it != chal.end()) return it->second;
  vector<vector<Node>> cs; char mode = x[0]; Shape s = x.substr(1);
  for (auto &w : wit(s)) {
    vector<Pos> qs = lm(w); if (mode == 'U') qs.push_back(w);
    for (auto &q : qs) {
      vector<Node> opts;
      bool conc = (int)q.size() <= CONC;   // concrete pruning only on small boards
      if (mode == 'U') {
        if (okShape(q) && (!conc || le0(q))) opts.push_back("N" + shapeOf(q));
        for (auto &r : rm(q)) if (okShape(r) && (!conc || Up(r))) opts.push_back("U" + shapeOf(r));
      } else {
        for (auto &r : rm(q)) if (okShape(r) && (!conc || le0(r))) opts.push_back("N" + shapeOf(r));
      }
      cs.push_back(opts);
    }
  }
  return chal[x] = cs;
}
bool dfs(const Node &x) {
  int st = status[x];
  if (st == 3) return false;
  if (st == 1 || st == 2) return true;
  status[x] = 1;
  vector<Node> picks;
  for (auto opts : challenges(x)) {
    stable_sort(opts.begin(), opts.end(), [](const Node &a, const Node &b) {
      int ka = (status[a] == 2 ? 0 : 2) + (pref.count(a) ? 0 : 1), kb = (status[b] == 2 ? 0 : 2) + (pref.count(b) ? 0 : 1);
      if (ka != kb) return ka < kb;
      return cplx(a) < cplx(b); });
    bool ok = false;
    for (auto &o : opts) if (dfs(o)) { picks.push_back(o); ok = true; break; }
    if (!ok) { status[x] = 3; return false; }
  }
  choice[x] = picks; status[x] = 2;
  return true;
}
// Explain why a node is lost: the first challenge with no surviving option, then follow one option.
map<Node, pair<Pos, Pos>> failAt;   // witness and Left move (or pass) that could not be answered
void why(const Node &x, int depth, set<Node> &seen) {
  if (depth > 12 || !seen.insert(x).second) return;
  char mode = x[0]; Shape s = x.substr(1);
  for (auto &w : wit(s)) {
    vector<Pos> qs = lm(w); if (mode == 'U') qs.push_back(w);
    for (auto &q : qs) {
      vector<Node> opts;
      if (mode == 'U') {
        if (nruns(q) <= RB && le0(q)) opts.push_back("N" + shapeOf(q));
        for (auto &r : rm(q)) if (nruns(r) <= RB && Up(r)) opts.push_back("U" + shapeOf(r));
      } else for (auto &r : rm(q)) if (nruns(r) <= RB && le0(r)) opts.push_back("N" + shapeOf(r));
      bool alive = false; for (auto &o : opts) if (status[o] != 3) alive = true;
      if (alive) continue;
      printf("%*s%s  witness %s  %s %s  -> %zu options, all lost%s\n", 2 * depth, "", x.c_str(), w.c_str(),
             q == w ? "pass" : "move", q.c_str(), opts.size(),
             opts.empty() ? (mode == 'U' ? (Up(w) ? "" : "  [witness itself loses]") : (le0(w) ? "" : "  [witness itself loses]")) : "");
      if (!opts.empty()) why(opts[0], depth + 1, seen);
      return;
    }
  }
}
int main(int argc, char **argv) {
  B = atoi(argv[1]); RB = atoi(argv[2]); if (argc > 3) K = atoi(argv[3]); if (argc > 4) M = atoi(argv[4]); if (argc > 5) CONC = atoi(argv[5]); if (argc > 6) FB = atoi(argv[6]); if (getenv("NODEAD")) DEAD = 0;
  if (getenv("PREF")) { ifstream f(getenv("PREF")); string l; while (getline(f, l)) if (!l.empty()) pref.insert(l); printf("%zu preferred shapes\n", pref.size()); }
  vector<Node> starts;
  { set<Node> st; for (int a = K; a < K + M + 8; a++) st.insert("U" + shapeOf(string(a, 'T') + string(B, '.') + string(a, 'F')));
    for (auto &x : st) printf("start %s\n", x.c_str());
    starts.assign(st.begin(), st.end()); }
  for (int it = 0; it < 500; it++) {
    for (auto &[k, v] : status) if (v != 3) v = 0;
    vector<Node> lost;
    for (auto &s : starts) if (!dfs(s)) lost.push_back(s);
    if (!lost.empty()) { printf("iteration %d: start lost:", it); for (auto &s : lost) printf(" %s", s.c_str()); printf("  (%zu nodes explored)\n", chal.size());
      set<Node> seen; why(lost[0], 0, seen); return 1; }
    set<Node> W; deque<Node> todo(starts.begin(), starts.end());
    while (!todo.empty()) { Node x = todo.front(); todo.pop_front(); if (!W.insert(x).second) continue; for (auto &y : choice[x]) todo.push_back(y); }
    int bad = 0; for (auto &x : W) for (auto &y : choice[x]) if (status[y] == 3) { bad++; break; }
    int nu = 0, maxw = 0, maxlen = 0, maxd = 0;
    for (auto &x : W) { if (x[0] == 'U') nu++; auto ws = wit(x.substr(1)); maxw = max(maxw, (int)ws.size()); for (auto &w : ws) maxlen = max(maxlen, (int)w.size()); maxd = max(maxd, abs(deltaOf(x.substr(1)))); }
    printf("[unbalanced witnesses skipped: %d] ", unbalanced);
    printf("iteration %d: %zu shapes (%d U), %d rely on lost ones; explored %zu; max witnesses %d, max length %d, max |Delta| %d; concrete states %zu\n",
           it, W.size(), nu, bad, chal.size(), maxw, maxlen, maxd, mLE.size() + mUP.size());
    fflush(stdout);
    if (!bad) {
      printf("CLOSED\n");
      if (getenv("EXPLORE")) {   // also solve every alternative option of the shapes in use
        size_t cap = atol(getenv("EXPLORE"));
        for (int pass = 0; pass < 3 && chal.size() < cap; pass++) {
          vector<Node> todo2(W.begin(), W.end());
          for (auto &x : todo2) { if (chal.size() >= cap) break; for (auto opts : challenges(x)) for (auto &o : opts) if (status[o] == 0) dfs(o); }
          printf("  explore pass %d: %zu nodes explored\n", pass, chal.size()); fflush(stdout);
        }
      }
      if (getenv("MINIMIZE")) {
        // exact won region of the explored graph (greatest fixpoint): any choice inside it is closed
        set<Node> valid; for (auto &[x, cs] : chal) valid.insert(x);
        for (bool ch = true; ch; ) { ch = false;
          for (auto it = valid.begin(); it != valid.end(); ) {
            bool ok = true;
            for (auto &opts : chal[*it]) { bool any = false; for (auto &o : opts) if (valid.count(o)) { any = true; break; } if (!any) { ok = false; break; } }
            if (!ok) { it = valid.erase(it); ch = true; } else ++it; } }
        map<Node, long> pop;
        for (auto &x : valid) for (auto &opts : chal[x]) for (auto &o : opts) if (valid.count(o)) pop[o]++;
        set<Node> cur = W;
        for (int round = 0; round < 30; round++) {
          set<Node> nw; deque<Node> td(starts.begin(), starts.end());
          while (!td.empty()) { Node x = td.front(); td.pop_front(); if (!nw.insert(x).second) continue;
            for (auto &opts : chal[x]) { Node best; long bs = -1;
              for (auto &o : opts) if (valid.count(o)) { long sc = (cur.count(o) ? 1000000000L : 0) + (nw.count(o) ? 2000000000L : 0) + pop[o]; if (sc > bs) { bs = sc; best = o; } }
              td.push_back(best); } }
          printf("  minimise round %d: %zu shapes\n", round, nw.size()); fflush(stdout);
          if (nw.size() >= cur.size() && round > 0) break;
          cur = nw; }
        W = cur;
        int nu2 = 0; for (auto &x : W) if (x[0] == 'U') nu2++;
        printf("MINIMISED to %zu shapes (%d U)\n", W.size(), nu2);
      }
      if (getenv("DUMP")) { FILE *f = fopen(getenv("DUMP"), "w"); for (auto &x : W) fprintf(f, "%s\n", x.c_str()); fclose(f); }
      return 0; }
  }
}
