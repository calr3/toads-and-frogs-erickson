// Check a closed shape set directly on the real game tree of T^a .^B F^a: Left plays every move
// (and every pass in the Left-stop phase); Right answers with a reply (or pass) whose normal form is
// in the set. Every real position reached must itself satisfy the closure conditions. For a given
// a this is a complete proof that T^a .^B F^a has Left stop <= 0, independent of the margin lemma.
// Usage: col_realcheck SHAPES B AMIN AMAX [K M]   (SHAPES: the DUMP output of col_shapes)
#include <bits/stdc++.h>
using namespace std;
int K = 4, M = 4, B = 3;
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
// shape (class) exactly as in col_shapes.cpp
Pos norm(const Pos &p) {
  vector<pair<char,int>> rs;
  for (char c : p) { if (!rs.empty() && rs.back().first == c) rs.back().second++; else rs.push_back({c, 1}); }
  int m = rs.size(); vector<pair<int,int>> lv;
  for (int i = 0; i < m; i++) if (rs[i].second >= K) lv.push_back({rs[i].second, i});
  stable_sort(lv.begin(), lv.end());
  vector<int> rank(m, -1); for (int k = 0; k < (int)lv.size(); k++) rank[lv[k].second] = k;
  string t;
  for (int i = 0; i < m; i++) { t += rs[i].first; t += rank[i] < 0 ? char('0' + rs[i].second) : char('a' + rank[i]); }
  t += '|'; int prev = K;
  for (auto [l, i] : lv) { int g = l - prev; prev = l; t += char('0' + (g <= M ? g : M + 1 + (g - M - 1) % 2)); }
  return t;
}
unordered_set<Pos> U, N;
int main(int argc, char **argv) {
  ifstream f(argv[1]); string line;
  while (getline(f, line)) { if (line.empty()) continue; (line[0] == 'U' ? U : N).insert(line.substr(1)); }
  B = atoi(argv[2]); int A0 = atoi(argv[3]), A1 = atoi(argv[4]);
  if (argc > 6) { K = atoi(argv[5]); M = atoi(argv[6]); }
  for (int a = A0; a <= A1; a++) {
    Pos s0 = string(a, 'T') + string(B, '.') + string(a, 'F');
    unordered_set<Pos> seenU, seenN; deque<pair<Pos,char>> todo{{s0, 'U'}};
    long fails = 0;
    if (!U.count(norm(s0))) { printf("a=%d: start shape not in the set\n", a); continue; }
    while (!todo.empty()) {
      auto [p, mode] = todo.front(); todo.pop_front();
      if (!(mode == 'U' ? seenU : seenN).insert(p).second) continue;
      if (mode == 'N') {
        for (auto &q : lm(p)) { bool ok = false;
          for (auto &r : rm(q)) if (N.count(norm(r))) { todo.push_back({r, 'N'}); ok = true; break; }
          if (!ok) { if (fails++ < 5) printf("  N fail at %s after %s\n", p.c_str(), q.c_str()); } }
        continue;
      }
      vector<Pos> qs = lm(p); qs.push_back(p);
      for (auto &q : qs) {
        if (N.count(norm(q))) { todo.push_back({q, 'N'}); continue; }
        bool ok = false;
        for (auto &r : rm(q)) if (U.count(norm(r))) { todo.push_back({r, 'U'}); ok = true; break; }
        if (!ok) { if (fails++ < 5) printf("  U fail at %s after %s\n", p.c_str(), q.c_str()); }
      }
    }
    if (getenv("DUMPREAL")) { FILE *g = fopen(getenv("DUMPREAL"), "a");
      for (auto &x : seenU) fprintf(g, "U%s\n", norm(x).c_str()); for (auto &x : seenN) fprintf(g, "N%s\n", norm(x).c_str()); fclose(g); }
    printf("a=%d: %zu U + %zu N real positions, %ld failures\n", a, seenU.size(), seenN.size(), fails);
    fflush(stdout);
  }
}
