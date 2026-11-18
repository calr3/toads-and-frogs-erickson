#include "ex6.h"
// Reachable Left-to-move positions from TT.T.^m FFF under: front frog in TTTFFF (g3 >= 2), else first winning reply.
// Per order: count, race-count range, and growth with m.
int main(int argc, char** argv) { initS(atoi(argv[1])); const int C = 7;
  for (int m = 8; m + 1 <= S; m += 4) { Gp s0 = {0,0,1,m,0,0,0};
    set<pair<int,Gp>> seen; vector<pair<int,Gp>> stk = {{C, s0}}; seen.insert({C, s0});
    while (!stk.empty()) { auto [c, g] = stk.back(); stk.pop_back();
      for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; int pick = -1;
        if (c2 == C && h[3] >= 2) pick = 3;
        else for (int j = 0; j < 6; j++) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && !xLF(c3, q)) { pick = j; break; } }
        int c3; Gp q; if (pick < 0 || !rmc(c2, h, pick, c3, q)) { printf("no reply!\n"); continue; }
        if (!seen.count({c3, q})) { seen.insert({c3, q}); stk.push_back({c3, q}); } } }
    map<int, array<long,3>> st; for (auto& [c, g] : seen) { int a = abOf(c, g); auto it = st.find(c); if (it == st.end()) st[c] = {1, a, a}; else { it->second[0]++; it->second[1] = min(it->second[1], (long)a); it->second[2] = max(it->second[2], (long)a); } }
    printf("m=%d: %zu positions, %zu orders\n", m, seen.size(), st.size());
    for (auto& [c, v] : st) printf("   %s %6ld  ab [%ld,%ld]\n", nm(c), v[0], v[1], v[2]); fflush(stdout); }
}
