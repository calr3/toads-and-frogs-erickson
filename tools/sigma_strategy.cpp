// Test the "mirror-or-pass" strategy: from symmetric S (Left to move), for each Left move Q:
// if Q <= 0 (normal play) Right passes; else Right must mirror to a symmetric S' (recursively OK).
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
int n;
static inline int cell(u64 s, int i) { return (s >> (2 * i)) & 3; }
static inline u64 setc(u64 s, int i, int v) { return (s & ~(3ULL << (2 * i))) | ((u64)v << (2 * i)); }
static inline int leftMoves(u64 s, u64 *out) { int k = 0;
  for (int i = 0; i < n; i++) if (cell(s, i) == 1) {
    if (i + 1 < n && cell(s, i + 1) == 0) out[k++] = setc(setc(s, i, 0), i + 1, 1);
    else if (i + 2 < n && cell(s, i + 1) == 2 && cell(s, i + 2) == 0) out[k++] = setc(setc(s, i, 0), i + 2, 1); }
  return k; }
static inline int rightMoves(u64 s, u64 *out) { int k = 0;
  for (int i = n - 1; i >= 0; i--) if (cell(s, i) == 2) {
    if (i - 1 >= 0 && cell(s, i - 1) == 0) out[k++] = setc(setc(s, i, 0), i - 1, 2);
    else if (i - 2 >= 0 && cell(s, i - 1) == 1 && cell(s, i - 2) == 0) out[k++] = setc(setc(s, i, 0), i - 2, 2); }
  return k; }
u64 mirror(u64 s) { u64 t = 0; for (int i = 0; i < n; i++) { int c = cell(s, i); t = setc(t, n - 1 - i, c == 1 ? 2 : c == 2 ? 1 : 0); } return t; }
struct H { size_t operator()(u64 x) const { x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33; return x; } };
unordered_map<u64, uint8_t, H> memo;
bool LF(u64 s); bool RF(u64 s);
bool LF(u64 s) { auto it = memo.find(s); if (it != memo.end() && (it->second & 1)) return it->second & 2;
  u64 mv[64]; int k = leftMoves(s, mv); bool r = false; for (int j = 0; j < k && !r; j++) if (!RF(mv[j])) r = true;
  memo[s] |= 1 | (r ? 2 : 0); return r; }
bool RF(u64 s) { auto it = memo.find(s); if (it != memo.end() && (it->second & 4)) return it->second & 8;
  u64 mv[64]; int k = rightMoves(s, mv); bool r = false; for (int j = 0; j < k && !r; j++) if (!LF(mv[j])) r = true;
  memo[s] |= 4 | (r ? 8 : 0); return r; }
string dec(u64 s) { string r; for (int i = 0; i < n; i++) r += ".TF"[cell(s, i)]; return r; }
unordered_map<u64, int, H> res; // 1 ok, 2 fail, 3 in progress
int fails = 0; long symCount = 0, passCount = 0;
bool Np(u64 s); bool Mp(u64 s);
unordered_map<u64, uint8_t, H> memo2;
bool Mp(u64 s) { auto it = memo2.find(s); if (it != memo2.end() && (it->second & 64)) return it->second & 128;
  u64 mv[64]; int k = rightMoves(s, mv); bool r = !LF(s); for (int j = 0; j < k && !r; j++) if (Np(mv[j])) r = true;
  memo2[s] |= 64 | (r ? 128 : 0); return r; }
bool Np(u64 s) { auto it = memo2.find(s); if (it != memo2.end() && (it->second & 16)) return it->second & 32;
  bool r = (mirror(s) == s) ? true : Mp(s);
  if (r) { u64 mv[64]; int k = leftMoves(s, mv); for (int j = 0; j < k && r; j++) if (!Mp(mv[j])) r = false; }
  memo2[s] |= 16 | (r ? 32 : 0); return r; }
map<string,long> used;
bool ok(u64 s) { // symmetric s, Left to move
  auto it = res.find(s); if (it != res.end()) return it->second == 1;
  res[s] = 3; symCount++;
  bool good = true;
  u64 mv[64]; int k = leftMoves(s, mv);
  for (int j = 0; j < k; j++) {
    u64 q = mv[j];
    u64 want = q, mq = mirror(q);
    for (int t = 0; t < n; t++) if (cell(s, t) != cell(q, t)) want = setc(want, n - 1 - t, cell(mq, n - 1 - t));
    u64 rm[64]; int kr = rightMoves(q, rm); bool legal = false;
    for (int t = 0; t < kr; t++) if (rm[t] == want) legal = true;
    if (legal && ok(want)) { used["mirror"]++; continue; }
    if (!LF(q)) { passCount++; used["pass"]++; continue; }
    int from = -1, to = -1;
    for (int t = 0; t < n; t++) { if (cell(s, t) == 1 && cell(q, t) == 0) from = t; if (cell(s, t) == 0 && cell(q, t) == 1) to = t; }
    if (to == from + 1 && to + 1 < n && cell(q, to + 1) == 2 && cell(q, from) == 0) {
      u64 u = setc(setc(setc(q, to + 1, 0), from, 2), to, 1); if (Np(u)) { used["jumpA"]++; continue; } }
    if (to == from + 2) { u64 u = setc(setc(q, from + 1, 0), from, 2); if (Np(u)) { used["refillC"]++; continue; } }
    { int fi = -1; for (int t = 0; t < n; t++) if (cell(q, t) == 2) { fi = t; break; }
      if (fi > 0 && cell(q, fi - 1) == 0) { u64 u = setc(setc(q, fi, 0), fi - 1, 2); if (Np(u)) { used["frontAdv"]++; continue; } } }
    good = false;
    if (fails < 20) { fails++; printf("FAIL at S=%s Q=%s mirror=%s\n", dec(s).c_str(), dec(q).c_str(), legal ? "bad" : "illegal"); }
    break;
  }
  res[s] = good ? 1 : 2;
  return good;
}
int main(int argc, char **argv) {
  int amin = atoi(argv[1]), amax = atoi(argv[2]), bmin = atoi(argv[3]), bmax = atoi(argv[4]);
  for (int a = amin; a <= amax; a++) for (int b = bmin; b <= bmax; b++) {
    n = 2 * a + b; if (n > 32) continue;
    memo.clear(); memo2.clear(); res.clear(); fails = 0; symCount = passCount = 0; used.clear();
    u64 s = 0; string str = string(a, 'T') + string(b, '.') + string(a, 'F');
    for (int i = 0; i < n; i++) s = setc(s, i, str[i] == 'T' ? 1 : str[i] == 'F' ? 2 : 0);
    bool r = ok(s);
    printf("a=%d b=%d sigma: %s  (sym=%ld)", a, b, r ? "WORKS" : "fails", symCount);
    for (auto &kv : used) printf(" %s=%ld", kv.first.c_str(), kv.second); printf("\n");
    fflush(stdout);
  }
}
