// Exploration for the a = 3 row: positions with three toads and three frogs, encoded as a
// piece order plus seven gaps (as in Cgt/Four.lean, with six pieces).
//
//   a3_explore reduce M          : is TT.T .^m FFF <= 0 (normal play, Left first) for m <= M?
//   a3_explore bounded M D       : can Right keep |g6-g0|, |g5-g1|, |g4-g2| <= D from T T.T.^m FFF?
//   a3_explore prerunner M D     : the same, but only until a frog passes every toad or a toad
//                                  passes every frog (later positions just need to be <= 0)
//   a3_explore shapes M D K      : shapes reached by the bounded strategy, per m (DIST=1: more)
#include <bits/stdc++.h>
using namespace std;
typedef unsigned long long u64;
const int P = 6;

struct S {
  int c;            // bit i set: piece i is a toad
  int g[P + 1];
};

static inline bool toad(const S& s, int i) { return (s.c >> i) & 1; }

u64 enc(const S& s) {
  u64 x = s.c;
  for (int i = 0; i <= P; i++) x = x * 256 + s.g[i];
  return x;
}

int lms(const S& s, S* out) {
  int k = 0;
  for (int i = 0; i < P; i++) if (toad(s, i)) {
    if (s.g[i + 1] > 0) { S t = s; t.g[i]++; t.g[i + 1]--; out[k++] = t; }
    else if (i + 1 < P && !toad(s, i + 1) && s.g[i + 2] > 0) {
      S t = s; t.c ^= (3 << i); t.g[i]++; t.g[i + 2]--; out[k++] = t;
    }
  }
  return k;
}

int rms(const S& s, S* out) {
  int k = 0;
  for (int i = 0; i < P; i++) if (!toad(s, i)) {
    if (s.g[i] > 0) { S t = s; t.g[i]--; t.g[i + 1]++; out[k++] = t; }
    else if (i >= 1 && toad(s, i - 1) && s.g[i - 1] > 0) {
      S t = s; t.c ^= (3 << (i - 1)); t.g[i - 1]--; t.g[i + 1]++; out[k++] = t;
    }
  }
  return k;
}

string str(const S& s) {
  string r(s.g[0], '.');
  for (int i = 0; i < P; i++) { r += toad(s, i) ? 'T' : 'F'; r += string(s.g[i + 1], '.'); }
  return r;
}

// ---- exact normal play: LF = Left (moving first) wins
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

// ---- bounded strategy
int D = 2;
bool bounded(const S& s) {
  for (int k = 0; k < P / 2; k++) if (abs(s.g[P - k] - s.g[k]) > D) return false;
  return true;
}
int asym(const S& s) { int a = 0; for (int k = 0; k < P / 2; k++) a += abs(s.g[P - k] - s.g[k]); return a; }
unordered_map<u64, int8_t> wmemo;
bool winB(const S& z) {      // Left to move at z
  u64 e = enc(z); auto it = wmemo.find(e);
  if (it != wmemo.end()) return it->second;
  bool ok = true;
  S ql[P]; int kl = lms(z, ql);
  for (int i = 0; i < kl && ok; i++) {
    S rr[P]; int kr = rms(ql[i], rr); bool found = false;
    for (int j = 0; j < kr && !found; j++) if (bounded(rr[j]) && winB(rr[j])) found = true;
    if (!found) ok = false;
  }
  wmemo[e] = ok; return ok;
}
bool reply(const S& q, S& out) {
  S rr[P]; int kr = rms(q, rr); bool have = false; int best = 1 << 30; u64 be = 0;
  for (int j = 0; j < kr; j++) if (bounded(rr[j]) && winB(rr[j])) {
    int a = asym(rr[j]); u64 e = enc(rr[j]);
    if (!have || a < best || (a == best && e < be)) { have = true; best = a; be = e; out = rr[j]; }
  }
  return have;
}

// A runner: a frog left of every toad, or a toad right of every frog.
bool hasRunner(const S& s) { return !toad(s, 0) || toad(s, P - 1); }
unordered_map<u64, int8_t> w2memo;
bool winB2(const S& z) {   // bounded until the first runner; positions with a runner just need <= 0
  u64 e = enc(z); auto it = w2memo.find(e);
  if (it != w2memo.end()) return it->second;
  bool ok = true;
  S ql[P]; int kl = lms(z, ql);
  for (int i = 0; i < kl && ok; i++) {
    S rr[P]; int kr = rms(ql[i], rr); bool found = false;
    for (int j = 0; j < kr && !found; j++) {
      if (hasRunner(rr[j])) { if (le0(rr[j])) found = true; }
      else if (bounded(rr[j]) && winB2(rr[j])) found = true;
    }
    if (!found) ok = false;
  }
  w2memo[e] = ok; return ok;
}

S qstart(int m) {   // TT.T .^m FFF
  S s; s.c = 0b000111;  // pieces 0,1,2 toads
  int g[P + 1] = {0, 0, 1, m, 0, 0, 0};
  for (int i = 0; i <= P; i++) s.g[i] = g[i];
  return s;
}

int K = 4;
int cap(int x) { return x < K ? x : K + x % 2; }
typedef array<int, 8> Shape;
Shape shape(const S& s) {
  return {s.c, s.g[6] - s.g[0], s.g[5] - s.g[1], s.g[4] - s.g[2], cap(min(s.g[0], s.g[6])),
          cap(min(s.g[1], s.g[5])), cap(min(s.g[2], s.g[4])), cap(s.g[3])};
}

int main(int argc, char** argv) {
  string mode = argv[1]; int M = atoi(argv[2]);
  if (argc > 3) D = atoi(argv[3]);
  if (argc > 4) K = atoi(argv[4]);
  if (mode == "reduce") {
    for (int m = 1; m <= M; m++) {
      S q = qstart(m);
      printf("m=%d %s <= 0: %s  (memo %zu)\n", m, str(q).c_str(), le0(q) ? "yes" : "NO", memo.size());
      fflush(stdout);
    }
  } else if (mode == "bounded") {
    for (int m = 1; m <= M; m++) {
      S q = qstart(m);
      printf("m=%d D=%d: %s  (memo %zu)\n", m, D, winB(q) ? "Right keeps the bound" : "FAILS", wmemo.size());
      fflush(stdout);
    }
  } else if (mode == "prerunner") {
    for (int m = 1; m <= M; m++) {
      S q = qstart(m);
      printf("m=%d D=%d: %s\n", m, D, winB2(q) ? "bounded until a runner appears" : "FAILS");
      fflush(stdout);
    }
  } else if (mode == "shapes") {
    set<Shape> all;
    map<Shape, set<pair<int, int>>> rtype;
    for (int m = 1; m <= M; m++) {
      S q0 = qstart(m);
      if (!winB(q0)) { printf("m=%d: no bounded strategy\n", m); continue; }
      unordered_set<u64> seen; vector<S> st = {q0}; size_t added = 0;
      while (!st.empty()) {
        S z = st.back(); st.pop_back();
        if (!seen.insert(enc(z)).second) continue;
        if (all.insert(shape(z)).second) added++;
        S ql[P]; int kl = lms(z, ql);
        for (int i = 0; i < kl; i++) {
          S r; bool ok = reply(ql[i], r); assert(ok);
          st.push_back(r);
        }
      }
      printf("m=%d: %zu positions, %zu shapes (+%zu)\n", m, seen.size(), all.size(), added);
      if (getenv("DIST")) {
        map<int, int> h0, h1, h2, hs, h01;
        for (u64 e : seen) {
          S z; z.c = 0; u64 x = e;
          for (int i = P; i >= 0; i--) { z.g[i] = x % 256; x /= 256; }
          z.c = x;
          int d0 = z.g[6] - z.g[0], d1 = z.g[5] - z.g[1], d2 = z.g[4] - z.g[2];
          h0[d0]++; h1[d1]++; h2[d2]++; hs[d0 + d1 + d2]++; h01[d0 + d1]++;
        }
        auto pr = [](const char* n, map<int, int>& h) { printf("   %s:", n); for (auto& kv : h) printf(" %d:%d", kv.first, kv.second); printf("\n"); };
        pr("g6-g0", h0); pr("g5-g1", h1); pr("g4-g2", h2); pr("sum", hs); pr("d0+d1", h01);
        map<string, pair<int, int>> byOrder;   // order -> (positions, positions with max|d| > 3)
        for (u64 e : seen) {
          S z; u64 x = e;
          for (int i = P; i >= 0; i--) { z.g[i] = x % 256; x /= 256; }
          z.c = x;
          string o; for (int i = 0; i < P; i++) o += toad(z, i) ? 'T' : 'F';
          int mx = 0; for (int k = 0; k < P / 2; k++) mx = max(mx, abs(z.g[P - k] - z.g[k]));
          byOrder[o].first++; if (mx > 3) byOrder[o].second++;
        }
        printf("   by order (positions / with max|d|>3):");
        for (auto& kv : byOrder) printf(" %s:%d/%d", kv.first.c_str(), kv.second.first, kv.second.second);
        printf("\n");
      }
      fflush(stdout);
    }
  }
}
