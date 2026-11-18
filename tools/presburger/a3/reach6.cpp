#include "ex6.h"
// Positions (Left to move) reached from TT.T.^m FFF, 5 <= m <= S - 1, when Right answers every Left move by the
// first winning reply in a fixed priority order of his frogs.  POL=0: leftmost frog first; 1: rightmost first.
// Prints, per piece order: number of positions, race-count range, and the range of every gap.
int main(int argc, char** argv) { initS(atoi(argv[1])); int POL = argc > 2 ? atoi(argv[2]) : 0;
  set<pair<int,Gp>> seen; vector<pair<int,Gp>> stk;
  for (int m = 5; m + 1 <= S; m++) { Gp s0 = {0,0,1,m,0,0,0}; if (xLF(7, s0)) { printf("m=%d not a loss\n", m); continue; } if (seen.insert({7, s0}).second) stk.push_back({7, s0}); }
  while (!stk.empty()) { auto [c, g] = stk.back(); stk.pop_back();
    for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; bool done = false;
      for (int jj = 0; jj < 6 && !done; jj++) { int j = POL == 0 ? jj : 5 - jj; int c3; Gp q; if (rmc(c2, h, j, c3, q) && !xLF(c3, q)) { done = true; if (seen.insert({c3, q}).second) stk.push_back({c3, q}); } }
      if (!done) { printf("no reply?!\n"); return 1; } } }
  if (getenv("DUMP")) { FILE* f = fopen(getenv("DUMP"), "w"); for (auto& [c, g] : seen) fprintf(f, "%d %d %d %d %d %d %d %d\n", c, g[0],g[1],g[2],g[3],g[4],g[5],g[6]); fclose(f); }
  map<int, array<int,17>> st; map<int,long> cnt;
  for (auto& [c, g] : seen) { if (!cnt.count(c)) { auto& a = st[c]; a[0] = 99; a[1] = -99; for (int k = 0; k < 7; k++) { a[2 + 2 * k] = 99; a[3 + 2 * k] = -99; } }
    cnt[c]++; auto& a = st[c]; int ab = abOf(c, g); a[0] = min(a[0], ab); a[1] = max(a[1], ab); for (int k = 0; k < 7; k++) { a[2 + 2 * k] = min(a[2 + 2 * k], g[k]); a[3 + 2 * k] = max(a[3 + 2 * k], g[k]); } }
  long tot = 0; for (auto& [c, n] : cnt) { auto& a = st[c]; printf("%s %7ld  ab %d..%d  gaps", nm(c), n, a[0], a[1]); for (int k = 0; k < 7; k++) printf(" %d..%d", a[2 + 2 * k], a[3 + 2 * k]); printf("\n"); tot += n; }
  printf("total %ld\n", tot); }
