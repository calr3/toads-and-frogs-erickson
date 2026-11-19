#include "ex6.h"
// Can Right win TT.T.^m FFF (Left moving first) with at most K jumps of his own?  A position with j Right jumps
// so far has race count -1 - (Left jumps) + j, so j is determined by the piece order and the race count.
// Usage: rj6 M     prints, for K = 0..4 and every m from 5 to M, whether Right wins.
int K; map<pair<int,Gp>, bool> memo;
int passings(int c) { int n = 0; for (int i = 0; i < 6; i++) for (int j = 0; j < i; j++) if (toad(c, i) && !toad(c, j)) n++; return n; }
bool wins(int c, const Gp& g) {   // Left to move; true if Right wins within the budget
  auto key = make_pair(c, g); auto it = memo.find(key); if (it != memo.end()) return it->second; bool r = true;
  for (int i = 0; i < 6 && r; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; bool ok = false;
    for (int j = 0; j < 6 && !ok; j++) { int c3; Gp q; if (!rmc(c2, h, j, c3, q)) continue; if (xLF(c3, q)) continue;
      int p = passings(c3), a = abOf(c3, q); int rj = (a + 1 + p) / 2;   // a = -1 - (p - rj) + rj
      if (rj > K) continue; if (wins(c3, q)) ok = true; }
    if (!ok) r = false; }
  return memo[key] = r; }
int main(int argc, char** argv) { int M = atoi(argv[1]); initS(M + 1);
  for (K = 0; K <= 4; K++) { printf("K=%d:", K); memo.clear(); for (int m = 5; m <= M; m++) { Gp s0 = {0, 0, 1, m, 0, 0, 0}; printf(" %d%c", m, wins(7, s0) ? '+' : '-'); fflush(stdout); } printf("\n"); } }
