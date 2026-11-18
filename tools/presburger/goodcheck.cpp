// Brute-force sanity check: every position (at most S empty squares) in `good` is a Left-first loss in exact play.
#include "ex.h"
struct Nd { bool leaf; int val, kind, m, v, yes, no; array<int,5> f; };
map<int, vector<Nd>> T;
void load(int c, const char* fn) { FILE* f = fopen(fn, "r"); int cc, n; if (fscanf(f, "%d %d", &cc, &n) != 2) exit(1); vector<Nd> v(n);
  for (int k = 0; k < n; k++) { int i; char w[16]; if (fscanf(f, "%d %s", &i, w) != 2) exit(1); if (w[0] == 'l') { v[i].leaf = true; if (fscanf(f, "%d", &v[i].val) != 1) exit(1); }
    else { v[i].leaf = false; if (fscanf(f, "%d %d %d %d %d %d %d %d %d %d", &v[i].kind, &v[i].f[0], &v[i].f[1], &v[i].f[2], &v[i].f[3], &v[i].f[4], &v[i].m, &v[i].v, &v[i].yes, &v[i].no) != 10) exit(1); } }
  T[c] = v; fclose(f); }
bool treeLoss(int c, const array<int,5>& g) { auto& v = T[c]; int i = 0; int a = abOf(c, g);
  while (!v[i].leaf) { auto& n = v[i]; long x = 0; for (int k = 0; k < 5; k++) x += (long)n.f[k] * g[k]; bool t = n.kind == 0 ? x >= n.v : n.kind == 1 ? (((x % n.m) + n.m) % n.m) == n.v : a >= n.v; i = t ? n.yes : n.no; }
  return v[i].val == 0; }
int passings(int c) { int n = 0; for (int i = 0; i < 4; i++) for (int j = 0; j < i; j++) if (toad(c, i) && !toad(c, j)) n++; return n; }
bool good(int c, const array<int,5>& g) { int a = abOf(c, g), P = passings(c); if (a < -P || a > P + 1) return false;
  if (c == 3) { int N = g[0] + g[1] + g[2] + g[3] + g[4];
    if (a == 0 && g[4] == 0 && N >= 9 && (N % 6 == 3 || N % 6 == 5)) return true;
    if (a == 1 && g[4] == 0 && N >= 7 && N % 6 == 1) return true;
    return g[2] <= 1 && (a == 0 || a == 1) && treeLoss(c, g); }
  return treeLoss(c, g); }
int main(int argc, char** argv) { initS(atoi(argv[1])); load(3, "tree3.txt"); load(5, "tree5.txt"); load(6, "tree6.txt"); load(9, "tree9.txt"); load(10, "tree10.txt"); load(12, "tree12.txt");
  long ng = 0, bad = 0;
  for (int oi = 0; oi < 6; oi++) { int c = ords[oi]; for (int a = 0; a <= S; a++) for (int b = 0; a + b <= S; b++) for (int d = 0; a + b + d <= S; d++) for (int e = 0; a + b + d + e <= S; e++) for (int f = 0; a + b + d + e + f <= S; f++) {
    array<int,5> g = {a, b, d, e, f}; if (!good(c, g)) continue; ng++; if (xLF(c, g)) { bad++; if (bad < 10) printf("good but Left wins: %d (%d %d %d %d %d)\n", c, a, b, d, e, f); } } }
  printf("S=%d: %ld good positions, %ld of them Left wins\n", S, ng, bad);
}
