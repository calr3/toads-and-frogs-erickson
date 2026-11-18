#include "ex6.h"
// Test the runner reduction: for each order, the outcome should depend on the runners' own gaps only through ab
// (and possibly [gap >= 1] of the gap next to the core). Check: positions with the same core gaps, same ab, and the runner
// gaps differing (all >= T) have the same outcome. Report conflicts.
int main(int argc, char** argv) { initS(atoi(argv[1])); int T = atoi(argv[2]);
  for (int oi = 0; oi < NO; oi++) { int c = ords[oi];
    // leading frogs: pieces 0..L-1 frogs; trailing toads: pieces 6-R..5 toads
    int L = 0; while (L < 6 && !toad(c, L)) L++; int R = 0; while (R < 6 && toad(c, 5 - R)) R++;
    if (L == 6 || L + R >= 6) { printf("%s: all runners\n", nm(c)); continue; }
    // runner gaps: gaps 0..L-1 (left of/among leading frogs) and gaps 7-R..6 (among/right of trailing toads)
    vector<int> rg; for (int k = 0; k < L; k++) rg.push_back(k); for (int k = 7 - R; k < 7; k++) rg.push_back(k);
    map<vector<int>, int> seen; long conf = 0, tot = 0;
    Gp g; function<void(int, int)> rec = [&](int i, int rem) {
      if (i == 7) { bool ok = true; for (int k : rg) if (g[k] < T) ok = false; if (!ok) return;
        vector<int> key; for (int k = 0; k < 7; k++) { bool isr = find(rg.begin(), rg.end(), k) != rg.end(); key.push_back(isr ? -1 : g[k]); } key.push_back(abOf(c, g));
        int o = xLF(c, g); tot++; auto it = seen.find(key); if (it == seen.end()) seen[key] = o; else if (it->second != o) conf++; return; }
      for (int x = 0; x <= rem; x++) { g[i] = x; rec(i + 1, rem - x); } };
    rec(0, S);
    printf("%s: runners L=%d R=%d, core %d pieces: %ld positions, %ld conflicts\n", nm(c), L, R, 6 - L - R, tot, conf); fflush(stdout); }
}
