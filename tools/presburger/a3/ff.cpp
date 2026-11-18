#include "ex6.h"
// Claim: TT.T.^m FFF <= 0 (m >= 5). Test the policy "Right always moves the front frog while the centre gap is >= G2MIN".
int main(int argc, char** argv) { initS(atoi(argv[1])); int G2MIN = argc > 2 ? atoi(argv[2]) : 2; const int C = 7; // TTTFFF = bits 0,1,2
  for (int m = 5; m + 1 <= S; m++) { Gp s0 = {0,0,1,m,0,0,0}; printf("m=%2d start %s", m, xLF(C, s0) ? "LEFT WINS" : "ok");
    // explore under policy: TTTFFF Right replies front frog (piece 3) when g3 >= G2MIN, else any winning reply; report failures
    set<pair<int,Gp>> seen; vector<pair<int,Gp>> stk = {{C, s0}}; seen.insert({C, s0}); long fails = 0, ttt = 0;
    while (!stk.empty()) { auto [c, g] = stk.back(); stk.pop_back(); if (c == C) ttt++;
      for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; bool done = false;
        if (c2 == C && h[3] >= G2MIN) { int c3; Gp q; if (rmc(c2, h, 3, c3, q) && !xLF(c3, q)) { done = true; if (!seen.count({c3, q})) { seen.insert({c3, q}); stk.push_back({c3, q}); } } else { fails++; if (fails <= 3) printf("\n   front frog fails after Left -> (%d %d %d %d %d %d %d)", h[0],h[1],h[2],h[3],h[4],h[5],h[6]); } }
        if (!done) for (int j = 0; j < 6 && !done; j++) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && !xLF(c3, q)) { done = true; if (c3 == C || true) if (!seen.count({c3, q})) { seen.insert({c3, q}); stk.push_back({c3, q}); } } }
      } }
    printf("   reached %zu (TTTFFF %ld), front-frog failures %ld\n", seen.size(), ttt, fails); fflush(stdout); }
}
