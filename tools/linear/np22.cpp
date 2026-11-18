// Exact normal play for 2 toads + 2 frogs: piece order (bitmask, bit i = piece i is a toad) and
// five gaps. Writes every position with g0+..+g4 <= S: order g0 g1 g2 g3 g4 LF RF
// (LF: Left moving first wins; RF: Right moving first wins).
#include <bits/stdc++.h>
using namespace std;
const int P = 4;
struct St { int c; int g[P + 1]; };
static inline bool toad(const St& s, int i) { return (s.c >> i) & 1; }
int lms(const St& s, St* o) { int k = 0;
  for (int i = 0; i < P; i++) if (toad(s, i)) {
    if (s.g[i + 1] > 0) { St t = s; t.g[i]++; t.g[i + 1]--; o[k++] = t; }
    else if (i + 1 < P && !toad(s, i + 1) && s.g[i + 2] > 0) { St t = s; t.c ^= (3 << i); t.g[i]++; t.g[i + 2]--; o[k++] = t; }
  } return k; }
int rms(const St& s, St* o) { int k = 0;
  for (int i = 0; i < P; i++) if (!toad(s, i)) {
    if (s.g[i] > 0) { St t = s; t.g[i]--; t.g[i + 1]++; o[k++] = t; }
    else if (i >= 1 && toad(s, i - 1) && s.g[i - 1] > 0) { St t = s; t.c ^= (3 << (i - 1)); t.g[i - 1]--; t.g[i + 1]++; o[k++] = t; }
  } return k; }
unordered_map<uint64_t, uint8_t> memo;
uint64_t enc(const St& s) { uint64_t x = s.c; for (int i = 0; i <= P; i++) x = x * 256 + s.g[i]; return x; }
bool RF(const St& s);
bool LF(const St& s) { uint64_t e = enc(s); auto it = memo.find(e); if (it != memo.end() && (it->second & 1)) return it->second & 2;
  St m[P]; int k = lms(s, m); bool r = false; for (int j = 0; j < k && !r; j++) if (!RF(m[j])) r = true;
  memo[e] |= 1 | (r ? 2 : 0); return r; }
bool RF(const St& s) { uint64_t e = enc(s); auto it = memo.find(e); if (it != memo.end() && (it->second & 4)) return it->second & 8;
  St m[P]; int k = rms(s, m); bool r = false; for (int j = 0; j < k && !r; j++) if (!LF(m[j])) r = true;
  memo[e] |= 4 | (r ? 8 : 0); return r; }
int main(int argc, char** argv) {
  int S = atoi(argv[1]);
  for (int c = 0; c < 16; c++) if (__builtin_popcount(c) == 2)
    for (int a = 0; a <= S; a++) for (int b = 0; a + b <= S; b++) for (int d = 0; a + b + d <= S; d++)
      for (int e = 0; a + b + d + e <= S; e++) for (int f = 0; a + b + d + e + f <= S; f++) {
        St s; s.c = c; s.g[0] = a; s.g[1] = b; s.g[2] = d; s.g[3] = e; s.g[4] = f;
        printf("%d %d %d %d %d %d %d %d\n", c, a, b, d, e, f, (int)LF(s), (int)RF(s));
      }
}
