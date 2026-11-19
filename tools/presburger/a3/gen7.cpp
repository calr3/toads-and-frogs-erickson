#include "ex6.h"
// Sampled exact data on large boards.  The number N of empty squares never changes during play, so each N
// is solved on its own (table of 20 * C(N+6, 6) bytes).  For every N in [N0, N1] and every piece order, writes
// a random sample of the positions in the race-count window [-p - 1, p + 1] (TTTFFF: centre gap <= 1, race
// count -1 or 0) with their exact outcome to OUT.<order>: records of 9 bytes (N, g0..g6, Left-first win).
// Usage: gen7 N0 N1 ROWS_PER_N OUT [ORDER ...]
int passings(int c) { int n = 0; for (int i = 0; i < 6; i++) for (int j = 0; j < i; j++) if (toad(c, i) && !toad(c, j)) n++; return n; }
int main(int argc, char** argv) { int N0 = atoi(argv[1]), N1 = atoi(argv[2]); double want = atof(argv[3]); string out = argv[4];
  vector<int> sel; for (int i = 5; i < argc; i++) sel.push_back(atoi(argv[i]));
  for (int c = 0; c < 64; c++) if (__builtin_popcount(c) == 3) { ordOf[c] = NO; ords[NO++] = c; }
  mt19937_64 rng(777); map<int, FILE*> fo;
  for (int N = N0; N <= N1; N++) { S = N; base.assign(N + 2, 0); blockSize = binom(N + 6, 6); st.assign((size_t)NO * blockSize, 0);
    for (int oi = 0; oi < NO; oi++) { int c = ords[oi]; if (!sel.empty() && find(sel.begin(), sel.end(), c) == sel.end()) continue; int p = passings(c);
      if (!fo.count(c)) fo[c] = fopen((out + "." + to_string(c)).c_str(), "wb");
      // count the window first, then sample
      for (int pass = 0; pass < 2; pass++) { static long cnt; if (pass == 0) cnt = 0; double pr = pass ? min(1.0, want / max(1L, cnt)) : 0; long wrote = 0;
        Gp g; function<void(int,int,int)> rec = [&](int k, int rem, int ab) { if (k == 6) { g[6] = rem; int a = ab + coef(c, 6) * rem;
            bool in = c == 7 ? (g[3] <= 1 && a >= -1 && a <= 0) : (a >= -p - 1 && a <= p + 1); if (!in) return;
            if (pass == 0) { cnt++; return; } if (pr < 1 && (rng() >> 11) * (1.0 / 9007199254740992.0) >= pr) return;
            unsigned char b[9]; b[0] = N; for (int i = 0; i < 7; i++) b[1 + i] = g[i]; b[8] = xLF(c, g); fwrite(b, 1, 9, fo[c]); wrote++; return; }
          for (int x = 0; x <= rem; x++) { g[k] = x; rec(k + 1, rem - x, ab + coef(c, k) * x); } };
        rec(0, N, 0); if (pass) fprintf(stderr, "N=%d %s: window %ld, wrote %ld\n", N, nm(c), cnt, wrote); } } }
  for (auto& [c, f] : fo) fclose(f); }
