#include "ex6.h"
#include <omp.h>
// Check an invariant written by cegar6 on the boards with N0 <= N <= N1 empty squares, by exact play:
// how many of its positions are Left wins, and how many (position, Left move) pairs have no reply in it.
// Usage: check6 INV N0 N1
struct Test { int kind, m, v; array<int,7> f; };
struct Node { Test t; int yes = -1, no = -1, leaf = -1; int lo[7], hi[7]; };
map<pair<int,int>, vector<Node>> SL;
static inline long evalF(const array<int,7>& f, const Gp& g) { long x = 0; for (int i = 0; i < 7; i++) x += (long)f[i] * g[i]; return x; }
bool in(int c, const Gp& g) { auto it = SL.find({c, abOf(c, g)}); if (it == SL.end()) return false; auto& nd = it->second; int id = 0;
  while (nd[id].leaf < 0) { auto& t = nd[id].t; long x = evalF(t.f, g); bool y = t.kind == 0 ? x >= t.v : ((x % t.m) + t.m) % t.m == t.v; id = y ? nd[id].yes : nd[id].no; }
  if (nd[id].leaf != 0) return false; for (int k = 0; k < 7; k++) if (g[k] < nd[id].lo[k] || g[k] > nd[id].hi[k]) return false; return true; }
int main(int argc, char** argv) { int N0 = atoi(argv[2]), N1 = atoi(argv[3]); initS(N1);
  { FILE* f = fopen(argv[1], "r"); char w[16]; vector<Node>* cur = nullptr; int a, b, n;
    while (fscanf(f, "%15s", w) == 1) { if (!strcmp(w, "slice")) { if (fscanf(f, "%d %d %d", &a, &b, &n) != 3) return 1; cur = &SL[{a, b}]; cur->assign(n, Node()); continue; }
      int i = atoi(w); char k[16]; if (fscanf(f, "%15s", k) != 1) return 1; Node& nd = (*cur)[i];
      if (k[0] == 'l') { if (fscanf(f, "%d", &nd.leaf) != 1) return 1; if (nd.leaf == 0) for (int q = 0; q < 7; q++) if (fscanf(f, "%d %d", &nd.lo[q], &nd.hi[q]) != 2) return 1; }
      else { auto& t = nd.t; if (fscanf(f, "%d %d %d %d %d %d %d %d %d %d %d %d", &t.kind, &t.f[0], &t.f[1], &t.f[2], &t.f[3], &t.f[4], &t.f[5], &t.f[6], &t.m, &t.v, &nd.yes, &nd.no) != 12) return 1; } }
    fclose(f); }
  for (int N = N0; N <= N1; N++) { long ng = 0, wins = 0, pairs = 0, bad = 0; bool startIn = true; if (N >= 6) { Gp s0 = {0, 0, 1, N - 1, 0, 0, 0}; startIn = in(7, s0); }
    #pragma omp parallel for schedule(dynamic, 1) reduction(+:ng, wins, pairs, bad)
    for (int oi = 0; oi < 20; oi++) { int c = ords[oi]; Gp g; function<void(int,int)> rec = [&](int k, int rem) { if (k == 6) { g[6] = rem; if (!in(c, g)) return; ng++; if (xLF(c, g)) { wins++; return; }
          for (int i = 0; i < 6; i++) { int c2; Gp h; if (!lmc(c, g, i, c2, h)) continue; pairs++; bool ok = false; for (int j = 0; j < 6 && !ok; j++) { int c3; Gp q; if (rmc(c2, h, j, c3, q) && in(c3, q)) ok = true; } if (!ok) bad++; } return; }
        for (int x = 0; x <= rem; x++) { g[k] = x; rec(k + 1, rem - x); } }; rec(0, N); }
    printf("N=%d: start %s, %ld positions in the invariant, %ld Left wins (%.2f%%), %ld of %ld Left moves unanswered (%.2f%%)\n", N, startIn ? "in" : "NOT in", ng, wins, 100.0 * wins / max(1L, ng), bad, pairs, 100.0 * bad / max(1L, pairs)); fflush(stdout); } }
