// The shape abstraction of col_shapes.cpp, played on real boards only.
//
// A shape is bad if one of its real positions (on the boards T^a .^B F^a, AMIN <= a <= AMAX) is
// lost for Right when he may only reply into shapes that are not bad. Starting from the truly
// lost positions, this is iterated to a fixpoint. If a start T^a .^B F^a is lost at the fixpoint,
// no closed set of these shapes exists: a fast necessary condition for col_shapes to succeed,
// and the bad shapes show which positions the shapes fail to tell apart.
//
// Usage: col_conflict B RB K M FB AMIN AMAX   (environment as for col_shapes: NOPARITY, DEADRUNS, ...)
//   SHOW=n prints n bad shapes of the first round with a won and a lost member each.
//   DUMP=file writes every real position met in the first round (mode, shape id, true outcome,
//   live long runs) and stops; used to look for the linear forms that separate wins from losses.
#define main col_shapes_main
#include "col_shapes.cpp"
#undef main

static Pos dec(u64 s) { int n = ncells(s); Pos p(n, '.'); for (int i = 0; i < n; i++) { int c = cellc(s, i); p[i] = c == 1 ? 'T' : c == 2 ? 'F' : '.'; } return p; }
static unordered_map<u64, int> shId;            // board -> shape id (mode-free), -1 if not allowed
static unordered_map<string, int> shNames; static vector<string> shName;
static int shapeId(u64 s) {
  auto it = shId.find(s); if (it != shId.end()) return it->second;
  Pos p = dec(s); int id = -1;
  if (okShape(p)) { Shape sh = shapeOf(p); auto jt = shNames.find(sh); if (jt == shNames.end()) { id = shName.size(); shNames[sh] = id; shName.push_back(sh); } else id = jt->second; }
  return shId[s] = id;
}
static vector<char> badN, badU; static long newBad;
static FILE *dumpF = nullptr;   // DUMP=file: one line per real position, "mode shape-id truly-won runs", runs = live long runs as T5 F3 ...
static void dumpPos(char mode, int id, bool won, u64 s) {
  if (!dumpF || id < 0) return;
  Pos p = dec(s); auto rs = runs(p); auto dd = deadRuns(rs);
  fprintf(dumpF, "%c %d %d", mode, id, won ? 1 : 0);
  for (size_t i = 0; i < rs.size(); i++) if (rs[i].first != '.' && rs[i].second >= K && !dd[i]) fprintf(dumpF, " %c%d", rs[i].first, rs[i].second);
  fprintf(dumpF, "\n");
}
static unordered_map<int, u64> wonEx[2], lostEx[2];
static unordered_map<u64, char> mN, mU;
static void mark(vector<char> &bad, int id, int mode, u64 s) {
  if (id < 0) return;
  if ((int)bad.size() <= id) bad.resize(id + 1, 0);
  if (!bad[id]) { bad[id] = 1; newBad++; lostEx[mode][id] = s; }
}
static bool isBad(const vector<char> &bad, int id) { return id < 0 || (id < (int)bad.size() && bad[id]); }
static bool Nq(u64 s) {
  auto it = mN.find(s); if (it != mN.end()) return it->second;
  int id = shapeId(s); bool r;
  dumpPos('N', id, le0c(s), s);
  if (!le0c(s)) r = false;
  else {
    r = true; u64 qs[64], ts[64]; int nq = lmc(s, qs);
    for (int a = 0; a < nq; a++) {
      bool ok = false; int nt = rmc(qs[a], ts);
      for (int b = 0; b < nt; b++) { int tid = shapeId(ts[b]); if (tid < 0) continue; bool w = Nq(ts[b]); if (w && !isBad(badN, tid)) ok = true; }
      if (!ok) r = false;
    }
  }
  mN[s] = r;
  if (!r) mark(badN, id, 0, s); else if (id >= 0) wonEx[0].emplace(id, s);
  return r;
}
static bool Uq(u64 s);
static bool Lfq(u64 q) {
  bool ok = false; int id = shapeId(q);
  if (id >= 0) { bool w = Nq(q); if (w && !isBad(badN, id)) ok = true; }
  u64 ts[64]; int nt = rmc(q, ts);
  for (int b = 0; b < nt; b++) { int tid = shapeId(ts[b]); if (tid < 0) continue; bool w = Uq(ts[b]); if (w && !isBad(badU, tid)) ok = true; }
  return ok;
}
static bool Uq(u64 s) {
  auto it = mU.find(s); if (it != mU.end()) return it->second;
  int id = shapeId(s); bool r;
  dumpPos('U', id, Upc(s), s);
  if (!Upc(s)) r = false;
  else {
    mU[s] = true;   // positions only get smaller in the measure; no cycles, placeholder is never read
    r = Lfq(s); u64 qs[64]; int nq = lmc(s, qs);
    for (int a = 0; a < nq; a++) if (!Lfq(qs[a])) r = false;
  }
  mU[s] = r;
  if (!r) mark(badU, id, 1, s); else if (id >= 0) wonEx[1].emplace(id, s);
  return r;
}
int main(int argc, char **argv) {
  if (argc < 8) { fprintf(stderr, "usage: col_conflict B RB K M FB AMIN AMAX\n"); return 1; }
  B = atoi(argv[1]); RB = atoi(argv[2]); K = atoi(argv[3]); M = atoi(argv[4]); FB = atoi(argv[5]);
  int a0 = atoi(argv[6]), a1 = atoi(argv[7]); int show = getenv("SHOW") ? atoi(getenv("SHOW")) : 0;
  if (getenv("DUMP")) dumpF = fopen(getenv("DUMP"), "w");
  for (int round = 0;; round++) {
    mN.clear(); mU.clear(); newBad = 0; string res;
    for (int a = a0; a <= a1; a++) { Pos p = string(a, 'T') + string(B, '.') + string(a, 'F'); bool w = Uq(enc(p)) && !isBad(badU, shapeId(enc(p))); res += w ? 'W' : 'L'; }
    long nb = count(badN.begin(), badN.end(), 1) + count(badU.begin(), badU.end(), 1);
    printf("round %d: starts a=%d..%d %s, %zu N and %zu U positions, %zu shapes, %ld bad (%ld new)\n", round, a0, a1, res.c_str(), mN.size(), mU.size(), shName.size(), nb, newBad);
    fflush(stdout);
    if (dumpF) { fclose(dumpF); dumpF = nullptr; printf("dump written\n"); return 0; }
    if (round == 0 && show) {
      int shown = 0;
      for (int mode = 0; mode < 2 && shown < show; mode++) for (auto &kv : lostEx[mode]) {
        auto wt = wonEx[mode].find(kv.first); if (wt == wonEx[mode].end()) continue;
        printf("  %c%s  won %s  lost %s\n", "NU"[mode], shName[kv.first].c_str(), dec(wt->second).c_str(), dec(kv.second).c_str());
        if (++shown >= show) break;
      }
    }
    if (newBad == 0 || res.find('W') == string::npos) break;
  }
  return 0;
}
