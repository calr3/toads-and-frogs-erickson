// Strategy tables for Right: the data of a Lean proof that Right, moving first from T^a .^b F^a,
// reaches a position <= 0 and one <= * (Cgt/Table.lean; generated into Lean by scripts/gen_table.py).
//
// The solver of tools/values.cpp (included below) decides le0 (s <= 0) and le0s (s + * <= 0, that is
// s <= *). From each Right move of the start that is <= 0, and from one that is <= *, the program
// follows one winning reply of Right to every Left move and records the positions met:
//   N: positions <= 0. Every Left move has a reply in N.
//   S: positions <= *. Some Right move is in N (Right's answer to Left taking the *), and every Left
//      move is in N (Right takes the *) or has a reply in S.
// A reply already in the table is preferred; otherwise the first winning one (frogs from the left).
//
// Usage: strategy A B   (environment DUMP=PREFIX writes PREFIX_N.txt and PREFIX_S.txt: one position
// code per line, sorted; the code of cells c_0 ... c_{n-1} is 4^n + sum code(c_i) 4^i with
// E = 0, T = 1, F = 2, as `Table.encode`). Memory: about 0.75 bytes per arrangement of the board.
#define main values_main
#include "values.cpp"
#undef main

vector<u64> visN, visS;   // bitsets over arrangements (by rank): positions in N and in S
static inline bool tst(const vector<u64> &v, u64 r) { return v[r >> 6] >> (r & 63) & 1; }
static inline void setb(vector<u64> &v, u64 r) { v[r >> 6] |= 1ULL << (r & 63); }
u64 edges = 0;
vector<u64> codesN, codesS;
u64 codeOf(u64 s) {
  u32 t = s >> 32, f = (u32)s; u64 c = 1ULL << (2 * n);
  for (int i = 0; i < n; i++) c += (u64)((t >> i & 1) ? 1 : (f >> i & 1) ? 2 : 0) << (2 * i);
  return c;
}
string show(u64 s) {
  string o; u32 t = s >> 32, f = (u32)s;
  for (int i = 0; i < n; i++) o += (t >> i & 1) ? 'T' : (f >> i & 1) ? 'F' : '.';
  return o;
}
// Depth-first, with an explicit stack: (position, is it claimed <= * rather than <= 0).
void extract(u64 root, bool star) {
  vector<pair<u64, bool>> st; st.push_back({root, star});
  while (!st.empty()) {
    auto [s, isS] = st.back(); st.pop_back();
    u64 r = rankOf(s);
    if (isS) { if (tst(visS, r)) continue; setb(visS, r); codesS.push_back(codeOf(s)); }
    else { if (tst(visN, r)) continue; setb(visN, r); codesN.push_back(codeOf(s)); }
    u64 qs[32], rs[32];
    if (isS) {   // Right's answer to Left taking the *: a move w <= 0
      int nr = rmoves(s >> 32, (u32)s, rs); int got = -1;
      for (int b = 0; b < nr && got < 0; b++) if (tst(visN, rankOf(rs[b])) && le0(rs[b])) got = b;
      for (int b = 0; b < nr && got < 0; b++) if (le0(rs[b])) got = b;
      if (got < 0) { fprintf(stderr, "no answer to * at %s\n", show(s).c_str()); exit(1); }
      st.push_back({rs[got], false});
    }
    int nq = lmoves(s >> 32, (u32)s, qs);
    for (int a = 0; a < nq; a++) {
      edges++;
      u64 q = qs[a];
      if (isS && le0(q)) { st.push_back({q, false}); continue; }   // Right takes the *
      int nr = rmoves(q >> 32, (u32)q, rs); int got = -1;
      for (int b = 0; b < nr && got < 0; b++)
        if (tst(isS ? visS : visN, rankOf(rs[b])) && (isS ? le0s(rs[b]) : le0(rs[b]))) got = b;
      if (got >= 0) continue;   // the reply is already in the table
      for (int b = 0; b < nr && got < 0; b++) if (isS ? le0s(rs[b]) : le0(rs[b])) got = b;
      if (got < 0) { fprintf(stderr, "no reply at %s\n", show(q).c_str()); exit(1); }
      st.push_back({rs[got], isS});
    }
  }
}
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: strategy A B\n"); return 1; }
  for (int t = 0; t <= 16; t++) for (int f = 0; f <= 16; f++) for (int e = 0; e <= 32; e++) {
    if (t + f + e > 32) continue;
    u64 c1 = 1; for (int k = 1; k <= t; k++) c1 = c1 * (e + k) / k;
    u64 c2 = 1; for (int k = 1; k <= f; k++) c2 = c2 * (e + t + k) / k;
    MN[t][f][e] = c1 * c2;
  }
  int a = atoi(argv[1]), b = atoi(argv[2]); n = 2 * a + b;
  if (n > 32) { fprintf(stderr, "more than 32 cells\n"); return 1; }
  idxCount = MN[a][a][b]; useIdx = true; nib.assign(idxCount / 2 + 1, 0);
  visN.assign(idxCount / 64 + 1, 0); visS.assign(idxCount / 64 + 1, 0);
  u32 t = (a ? (1u << a) - 1 : 0), f = 0; for (int j = a + b; j < n; j++) f |= 1u << j;
  u64 rs[32]; int nr = rmoves(t, f, rs), k1 = -1, k2 = -1;
  for (int k = 0; k < nr; k++) {
    bool z = le0(rs[k]), s = le0s(rs[k]);
    printf("Right move %s: <= 0 %d, <= * %d\n", show(rs[k]).c_str(), (int)z, (int)s); fflush(stdout);
    if (z && k1 < 0) k1 = k;
    if (s && k2 < 0) k2 = k;
  }
  if (k1 >= 0) extract(rs[k1], false);
  printf("<= 0 from %s: %zu N positions\n", k1 >= 0 ? show(rs[k1]).c_str() : "-", codesN.size());
  if (k2 >= 0) extract(rs[k2], true);
  printf("<= * from %s: %zu S + %zu N positions in all, %llu Left moves checked\n",
         k2 >= 0 ? show(rs[k2]).c_str() : "-", codesS.size(), codesN.size(), edges);
  if (getenv("DUMP")) {
    string pre = getenv("DUMP");
    for (int w = 0; w < 2; w++) {
      auto &v = w ? codesS : codesN; sort(v.begin(), v.end());
      FILE *o = fopen((pre + (w ? "_S.txt" : "_N.txt")).c_str(), "w");
      for (u64 c : v) fprintf(o, "%llu\n", c);
      fclose(o);
    }
  }
  return 0;
}
