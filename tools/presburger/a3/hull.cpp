#include "ex6.h"
// Reachable Left-to-move positions under a Right policy (priority list of frogs: env PRI = "front" (leftmost movable frog first) or "rear");
// per order: count, gap maxima, and the dimension of the affine hull (rank of [g,1] rows), with the linear relations found.
int main(int argc, char** argv) { initS(atoi(argv[1])); int m = atoi(argv[2]); const int C = 7; bool rear = getenv("REAR") != nullptr;
  Gp s0 = {0,0,1,m,0,0,0}; set<pair<int,Gp>> seen; vector<pair<int,Gp>> stk = {{C, s0}}; seen.insert({C, s0}); long fb = 0;
  while (!stk.empty()) { auto [c, g] = stk.back(); stk.pop_back();
    for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; int pick = -1;
      vector<int> order; for (int j = 0; j < 6; j++) if (!toad(c2, j)) order.push_back(j); if (rear) reverse(order.begin(), order.end());
      if (c2 == C && h[3] >= 2) order = {3};
      for (int j : order) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && !xLF(c3, q)) { pick = j; break; } }
      if (pick < 0) { for (int j = 0; j < 6; j++) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && !xLF(c3, q)) { pick = j; break; } } fb++; }
      int c3; Gp q; if (pick < 0 || !rmc(c2, h, pick, c3, q)) { printf("no reply\n"); continue; }
      if (!seen.count({c3, q})) { seen.insert({c3, q}); stk.push_back({c3, q}); } } }
  map<int, vector<Gp>> by; for (auto& [c, g] : seen) by[c].push_back(g);
  printf("m=%d: %zu positions, fallbacks %ld\n", m, seen.size(), fb);
  for (auto& [c, v] : by) { Gp mx{}; for (auto& g : v) for (int k = 0; k < 7; k++) mx[k] = max(mx[k], g[k]);
    // rank over rationals of rows [g0..g6, 1]
    vector<vector<double>> M; for (auto& g : v) { vector<double> r(8); for (int k = 0; k < 7; k++) r[k] = g[k]; r[7] = 1; M.push_back(r); }
    int rank = 0; vector<int> piv; for (int col = 0; col < 8 && rank < (int)M.size(); col++) { int p = -1; for (size_t i = rank; i < M.size(); i++) if (fabs(M[i][col]) > 1e-9) { p = i; break; } if (p < 0) continue; swap(M[p], M[rank]);
      for (size_t i = 0; i < M.size(); i++) if ((int)i != rank && fabs(M[i][col]) > 1e-9) { double f = M[i][col] / M[rank][col]; for (int k = 0; k < 8; k++) M[i][k] -= f * M[rank][k]; } rank++; }
    printf("   %s %6zu  max (%d %d %d %d %d %d %d)  affine dim %d\n", nm(c), v.size(), mx[0], mx[1], mx[2], mx[3], mx[4], mx[5], mx[6], rank - 1); }
}
