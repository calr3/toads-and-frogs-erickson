// Does Right win T^a .^B F^a with a component-local strategy?
//
// Dead regions (Erickson: in a block of pieces with no empty square, everything from the first TT
// to the last FF after it) never move, and no piece can move into or across one. So a position is
// a sum of independent components, the stretches between dead regions. A component-local strategy
// for Right answers every Left move inside the component Left moved in, and keeps
//   * in normal play: every component <= 0 on its own (LeN);
//   * while Right still holds his pass: one component with Left stop <= 0 (Up1), all others
//     <= 0 (LeN). Right's pass is spent in that component.
// If this holds for the start, Right's strategy only ever needs component positions, never
// combinations of them. MEAS=1 additionally caps the runs of every component Right moves to at
// RB (default: no cap); with STATS=1 one strategy is extracted and its component shapes counted.
//
// Usage: col_local B AMIN AMAX [RB]
#include <bits/stdc++.h>
using namespace std;
typedef string Pos;
int B, RB = 1000;
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
int nruns(const Pos &s) { int r = 0; for (size_t i = 0; i < s.size(); i++) if (i == 0 || s[i] != s[i - 1]) r++; return r; }
// components: maximal stretches outside dead regions that contain an empty square and a piece
vector<Pos> comps(const Pos &p) {
  int n = p.size(); vector<bool> dead(n, false);
  for (int i = 0; i < n; ) {
    if (p[i] == '.') { i++; continue; }
    int j = i; while (j < n && p[j] != '.') j++;
    int st = -1, en = -1;
    for (int k = i; k + 1 < j; k++) if (p[k] == 'T' && p[k + 1] == 'T') { st = k; break; }
    if (st >= 0) for (int k = j - 1; k - 1 > st; k--) if (p[k] == 'F' && p[k - 1] == 'F') { en = k; break; }
    if (st >= 0 && en >= 0) for (int k = st; k <= en; k++) dead[k] = true;
    i = j;
  }
  vector<Pos> out; Pos cur;
  auto flush = [&]() { if (cur.find('.') != string::npos && cur.find_first_not_of('.') != string::npos) out.push_back(cur); cur.clear(); };
  for (int i = 0; i < n; i++) { if (dead[i]) flush(); else cur += p[i]; }
  flush();
  return out;
}
unordered_map<Pos, char> mN, mU, mL;
bool leN1(const Pos &c);
bool leNall(const Pos &s) { for (auto &c : comps(s)) if (!leN1(c)) return false; return true; }
bool okR(const Pos &r) { for (auto &c : comps(r)) if (nruns(c) > RB) return false; return true; }
bool leN1(const Pos &c) {   // a single component, <= 0 with local replies
  auto it = mN.find(c); if (it != mN.end()) return it->second;
  bool r = true;
  for (auto &q : lm(c)) { bool ok = false; for (auto &t : rm(q)) if (okR(t) && leNall(t)) { ok = true; break; } if (!ok) { r = false; break; } }
  return mN[c] = r;
}
bool Up1(const Pos &c);
bool Upall(const Pos &s) {   // one component with Left stop <= 0, the others <= 0
  auto cs = comps(s); int bad = -1;
  for (int i = 0; i < (int)cs.size(); i++) if (!leN1(cs[i])) { if (bad >= 0) return false; bad = i; }
  return bad < 0 || Up1(cs[bad]);
}
bool Lf(const Pos &s) {      // Right to move in this region, still holding his pass
  auto it = mL.find(s); if (it != mL.end()) return it->second;
  bool r = leNall(s);
  if (!r) for (auto &t : rm(s)) if (okR(t) && Upall(t)) { r = true; break; }
  return mL[s] = r;
}
bool Up1(const Pos &c) {     // a single component, Left stop <= 0 with Right's pass
  auto it = mU.find(c); if (it != mU.end()) return it->second;
  bool r = Lf(c);
  if (r) for (auto &q : lm(c)) if (!Lf(q)) { r = false; break; }
  return mU[c] = r;
}
int main(int argc, char **argv) {
  B = atoi(argv[1]); int a0 = atoi(argv[2]), a1 = atoi(argv[3]); if (argc > 4) RB = atoi(argv[4]);
  for (int a = a0; a <= a1; a++) {
    Pos s = string(a, 'T') + string(B, '.') + string(a, 'F');
    bool u = Up1(s);
    printf("a=%d b=%d: component-local strategy %s (memo %zu / %zu / %zu)\n", a, B, u ? "WINS" : "fails", mN.size(), mU.size(), mL.size());
    fflush(stdout);
  }
}
