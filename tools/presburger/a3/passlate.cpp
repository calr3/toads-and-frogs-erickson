#include "ex6.h"
// "Left stop <= 0" of T^3 .^b F^3 (Right holds one pass) when Right may use his pass only once at least P0
// toad-frog pairs have passed each other.  Usage: passlate BMAX     prints + / - for b = 6..BMAX and P0 = 0..9.
int P0;
int passings(int c) { int n = 0; for (int i = 0; i < 6; i++) for (int j = 0; j < i; j++) if (toad(c, i) && !toad(c, j)) n++; return n; }
unordered_map<long, char> mU, mL;
bool Up(int c, const Gp& g);
bool Lf(int c, const Gp& g) { long e = idx(c, g); auto it = mL.find(e); if (it != mL.end()) return it->second;
  bool r = passings(c) >= P0 && !xLF(c, g);
  for (int j = 0; j < 6 && !r; j++) { int c3; Gp q; if (rmc(c, g, j, c3, q) && Up(c3, q)) r = true; }
  return mL[e] = r; }
bool Up(int c, const Gp& g) { long e = idx(c, g); auto it = mU.find(e); if (it != mU.end()) return it->second;
  bool r = Lf(c, g);
  for (int i = 0; i < 6 && r; i++) { int c2; Gp h; if (lmc(c, g, i, c2, h) && !Lf(c2, h)) r = false; }
  return mU[e] = r; }
int main(int argc, char** argv) { int B = atoi(argv[1]); initS(B);
  for (P0 = 0; P0 <= 9; P0++) { printf("P0=%d:", P0); mU.clear(); mL.clear(); for (int b = 6; b <= B; b++) { Gp s = {0, 0, 0, b, 0, 0, 0}; printf(" %d%c", b, Up(7, s) ? '+' : '-'); fflush(stdout); } printf("\n"); } }
