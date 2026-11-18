#include "ex6.h"
// Does a fixed rule for Right (no look-ahead) win TT.T.^m FFF with Left moving first?
// RULE 1: leftmost frog that can move.  2: leftmost frog that can move and still has a toad on its left; if none,
// the leftmost runner.  3: as 2 but runners rightmost first.  4: a jump if there is one (leftmost), else rule 2.
// 5: rightmost frog that can move.   Prints, for each m, whether the rule wins and (if not) the exact-play verdict.
int RULE;
bool runner(int c, int j) { for (int i = 0; i < j; i++) if (toad(c, i)) return false; return true; }
bool reply(int c, const Gp& g, int& c3, Gp& q) { vector<int> mv; for (int j = 0; j < 6; j++) { int cc; Gp h; if (rmc(c, g, j, cc, h)) mv.push_back(j); }
  if (mv.empty()) return false; int pick = -1;
  if (RULE == 1) pick = mv[0]; else if (RULE == 5) pick = mv.back();
  else { if (RULE == 4) for (int j : mv) { int cc; Gp h; rmc(c, g, j, cc, h); if (cc != c) { pick = j; break; } }
    if (pick < 0) for (int j : mv) if (!runner(c, j)) { pick = j; break; }
    if (pick < 0) pick = RULE == 3 ? mv.back() : mv[0]; }
  return rmc(c, g, pick, c3, q); }
map<pair<int,Gp>, bool> memo;
bool rightWins(int c, const Gp& g) {   // Left to move, Right follows the rule
  auto key = make_pair(c, g); auto it = memo.find(key); if (it != memo.end()) return it->second; bool r = true;
  for (int i = 0; i < 6 && r; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; int c3; Gp q; if (!reply(c2, h, c3, q) || !rightWins(c3, q)) r = false; }
  return memo[key] = r; }
int main(int argc, char** argv) { int M = atoi(argv[1]); initS(M + 1);
  for (RULE = 1; RULE <= 5; RULE++) { printf("rule %d:", RULE); for (int m = 5; m <= M; m++) { memo.clear(); Gp s0 = {0, 0, 1, m, 0, 0, 0}; printf(" %d%c", m, rightWins(7, s0) ? '+' : '-'); } printf("\n"); } }
