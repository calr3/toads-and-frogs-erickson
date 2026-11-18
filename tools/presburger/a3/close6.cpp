#include "ex6.h"
// Brute-force closure of the candidate invariant on boards with at most S empty squares.
// good(c, g): TTTFFF: approach family (g5 = g6 = 0, race count -1, N >= 6), or centre gap <= K, race count in
// [A0, A1] and an exact loss;  other orders: race count in [-p + DL, p + DH] (p = passed toad-frog pairs) and an exact loss.
// Usage: close6 S K A0 A1 DL DH
int K, A0, A1, DL, DH;
int passings(int c) { int n = 0; for (int i = 0; i < 6; i++) for (int j = 0; j < i; j++) if (toad(c, i) && !toad(c, j)) n++; return n; }
bool good(int c, const Gp& g) { int a = abOf(c, g);
  if (c == 7) { int N = 0; for (int x : g) N += x; if (g[5] == 0 && g[6] == 0 && a == -1 && N >= 6) return true; return g[3] <= K && a >= A0 && a <= A1 && !xLF(c, g); }
  int p = passings(c); return a >= -p + DL && a <= p + DH && !xLF(c, g); }
int main(int argc, char** argv) { initS(atoi(argv[1])); K = atoi(argv[2]); A0 = atoi(argv[3]); A1 = atoi(argv[4]); DL = atoi(argv[5]); DH = atoi(argv[6]);
  long totbad = 0;
  for (int oi = 0; oi < NO; oi++) { int c = ords[oi]; long ng = 0, bad = 0; string ex; Gp g;
    function<void(int,int)> rec = [&](int k, int rem) { if (k == 6) { g[6] = rem; 
        for (int last = 0; last <= rem; last++) { g[6] = last; if (!good(c, g)) continue; ng++;
          for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; bool ok = false;
            for (int j = 0; j < 6 && !ok; j++) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && good(c3, q)) ok = true; }
            if (!ok) { bad++; if (ex.size() < 150) { char b[80]; sprintf(b, " (%d %d %d %d %d %d %d;L%d;ab%d)", g[0],g[1],g[2],g[3],g[4],g[5],g[6], i, abOf(c, g)); ex += b; } } } }
        return; }
      for (int x = 0; x <= rem; x++) { g[k] = x; rec(k + 1, rem - x); } };
    rec(0, S);
    printf("%s p=%d: %ld good, %ld unanswered%s\n", nm(c), passings(c), ng, bad, ex.c_str()); totbad += bad; }
  printf("total unanswered %ld\n", totbad); }
