// Approach phase of the a = 3 row: exact normal-play outcomes of pre-contact positions
// □^g0 T □^g1 T □^g2 T □^g3 F □^g4 F □^g5 F □^g6.  Usage: a3_approach NMAX GINNER GTAIL > table
// (columns g0..g6, A - B, 1 if <= 0).  See docs/RESEARCH_NOTES.md §10.2.
// Abstract closure for the a = 3 row with "race-count shapes".
//
// A shape is (piece order, A - B, cap(g0), ..., cap(g6)) where A - B is the race count (a linear
// form in the gaps whose coefficients depend on the order) and cap(x) = x for x < K and
// K + x mod 2 otherwise.  Two positions with the same order, the same A - B, equal small gaps and
// large gaps >= K + j of equal parity are related with margin j; a move turns margin j + 1 into j
// (gaps change by at most one, A - B by a fixed amount per move type).  So for each shape and
// each pattern of which large gaps are >= K + 2, one witness position suffices.
//
// The closure starts from the shapes of TT.T .^m FFF (all m >= 5) and checks, for every witness
// and every Left move, that some Right reply is <= 0 (exact solver); the reply's shape is added.
//
// Usage: a3_ab K MAXSHAPES
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
const int P = 6;

struct S { int c; int g[P + 1]; };
static inline bool toad(const S& s, int i) { return (s.c >> i) & 1; }
u64 enc(const S& s) { u64 x = s.c; for (int i = 0; i <= P; i++) x = x * 256 + s.g[i]; return x; }

int lms(const S& s, S* out) {
  int k = 0;
  for (int i = 0; i < P; i++) if (toad(s, i)) {
    if (s.g[i + 1] > 0) { S t = s; t.g[i]++; t.g[i + 1]--; out[k++] = t; }
    else if (i + 1 < P && !toad(s, i + 1) && s.g[i + 2] > 0) { S t = s; t.c ^= (3 << i); t.g[i]++; t.g[i + 2]--; out[k++] = t; }
  }
  return k;
}
int rms(const S& s, S* out) {
  int k = 0;
  for (int i = 0; i < P; i++) if (!toad(s, i)) {
    if (s.g[i] > 0) { S t = s; t.g[i]--; t.g[i + 1]++; out[k++] = t; }
    else if (i >= 1 && toad(s, i - 1) && s.g[i - 1] > 0) { S t = s; t.c ^= (3 << (i - 1)); t.g[i - 1]--; t.g[i + 1]++; out[k++] = t; }
  }
  return k;
}
string str(const S& s) {
  string r(s.g[0], '.');
  for (int i = 0; i < P; i++) { r += toad(s, i) ? 'T' : 'F'; r += string(s.g[i + 1], '.'); }
  return r;
}

unordered_map<u64, uint8_t> memo;
bool RF(const S& s);
bool LF(const S& s) {
  u64 e = enc(s); auto it = memo.find(e);
  if (it != memo.end() && (it->second & 1)) return it->second & 2;
  S mv[P]; int k = lms(s, mv); bool r = false;
  for (int j = 0; j < k && !r; j++) if (!RF(mv[j])) r = true;
  memo[e] |= 1 | (r ? 2 : 0); return r;
}
bool RF(const S& s) {
  u64 e = enc(s); auto it = memo.find(e);
  if (it != memo.end() && (it->second & 4)) return it->second & 8;
  S mv[P]; int k = rms(s, mv); bool r = false;
  for (int j = 0; j < k && !r; j++) if (!LF(mv[j])) r = true;
  memo[e] |= 4 | (r ? 8 : 0); return r;
}
bool le0(const S& s) { return !LF(s); }

int coef(int c, int k) {   // coefficient of gap k in A - B
  int tl = 0, fr = 0;
  for (int i = 0; i < k; i++) if ((c >> i) & 1) tl++;
  for (int i = k; i < P; i++) if (!((c >> i) & 1)) fr++;
  return tl - fr;
}
int AB(const S& s) { int r = 0; for (int k = 0; k <= P; k++) r += coef(s.c, k) * s.g[k]; return r; }


// Tabulate le0 for pre-contact positions T T T | F F F with gaps g0..g6 and board length <= NMAX.
// Output: g0 g1 g2 g3 g4 g5 g6 AB le0
int main(int argc, char** argv) {
  int NMAX = atoi(argv[1]), GI = atoi(argv[2]), GT = atoi(argv[3]);
  long cnt = 0;
  for (int g3 = 0; g3 <= NMAX; g3++)
  for (int g1 = 0; g1 <= GI; g1++) for (int g2 = 0; g2 <= GI; g2++)
  for (int g4 = 0; g4 <= GI; g4++) for (int g5 = 0; g5 <= GI; g5++)
  for (int g0 = 0; g0 <= GT; g0++) for (int g6 = 0; g6 <= GT; g6++) {
    int n = 6 + g0 + g1 + g2 + g3 + g4 + g5 + g6;
    if (n > NMAX) continue;
    S s; s.c = 0b000111; int g[7] = {g0, g1, g2, g3, g4, g5, g6};
    for (int i = 0; i <= P; i++) s.g[i] = g[i];
    printf("%d %d %d %d %d %d %d %d %d\n", g0, g1, g2, g3, g4, g5, g6, AB(s), (int)le0(s));
    cnt++;
  }
  fprintf(stderr, "%ld positions, memo %zu\n", cnt, memo.size());
}
