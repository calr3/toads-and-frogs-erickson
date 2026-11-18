#include "ex6.h"
// Family under front-frog: TTTFFF (g0,g1,g2, g3, g4 = AB + 3g0 + 2g1 + g2, 0, 0), race count AB. Left to move.
// For each N: count Left wins in the family, and front-frog failures (g3 >= G2MIN).
int main(int argc, char** argv) { initS(atoi(argv[1])); int AB = atoi(argv[2]); int G2MIN = argc > 3 ? atoi(argv[3]) : 2; const int C = 7;
  for (int N = 4; N <= S; N++) { long tot = 0, lw = 0, ff = 0; string ex;
    for (int g0 = 0; g0 <= N; g0++) for (int g1 = 0; g0 + g1 <= N; g1++) for (int g2 = 0; g0 + g1 + g2 <= N; g2++) {
      int g4 = AB + 3*g0 + 2*g1 + g2; if (g4 < 0) continue; int g3 = N - g0 - g1 - g2 - g4; if (g3 < 0) continue;
      Gp g = {g0, g1, g2, g3, g4, 0, 0}; tot++;
      if (xLF(C, g)) { lw++; if (ex.size() < 80) { char b[64]; sprintf(b, " (%d %d %d %d %d)", g0, g1, g2, g3, g4); ex += b; } continue; }
      if (g3 < G2MIN) continue;
      for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(C, g, i, c2, h)) continue; int c3; Gp q; if (c2 != C) continue;
        if (!(rmc(c2, h, 3, c3, q) && !xLF(c3, q))) ff++; } }
    printf("N=%2d: %4ld positions, %3ld Left wins, front-frog failures %ld%s\n", N, tot, lw, ff, ex.c_str()); fflush(stdout); }
}
