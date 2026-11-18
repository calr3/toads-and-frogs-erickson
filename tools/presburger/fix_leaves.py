# Parse a lake build log for omega failures, map them to leaves (by the "-- leaf N" comments in the
# current files), and choose a case split over a small range of one gap for each.
import re, sys, json, pickle, os, z3
from gen_lean import lit_z3, G, NONNEG
LEAVES = pickle.load(open('leaves.pkl', 'rb'))
STRAT = json.load(open('strategies.json')) if os.path.exists('strategies.json') else {}
log = open(sys.argv[1]).read()
fails = set()
for m in re.finditer(r"error: (Cgt/RowA2Odd/\S+\.lean):(\d+):\d+:", log):
    fn, ln = m.group(1), int(m.group(2))
    lines = open('../../' + fn).read().split('\n'); k = ln - 1; mm = None
    while k >= 0 and k >= ln - 4:
        mm = re.search(r"-- leaf (\d+)", lines[k])
        if mm: break
        k -= 1
    if mm: fails.add(int(mm.group(1)))
    else: print("error not on a leaf line:", fn, ln, lines[ln - 1][:100])
print("failing leaves:", sorted(fails))
def gap_max(lits, k):
    o = z3.Optimize(); o.add(NONNEG); o.add([lit_z3(l, G) for l in lits]); h = o.maximize(G[k])
    if o.check() != z3.sat: return None
    u = o.upper(h)
    return u.as_long() if z3.is_int_value(u) else None
for lid in sorted(fails):
    region, t = LEAVES[lid]
    lits = region if t[0] != 'dead' else region[:-1]
    tried = STRAT.get(str(lid))
    best = None
    for k in range(5):
        if tried and tried[1] == f"g{k}": continue
        hi = gap_max(lits, k)
        if hi is not None and hi <= 15 and (best is None or hi < best[1]): best = (k, hi)
    if best is None:
        # residues mod 6 of the gaps that occur in modular literals
        vs = sorted({k for (a, op, m, v) in lits if op in ('mod', 'nmod') for k in range(5) if a[k] != 0})
        print("leaf", lid, "needs a residue split: run try_leaves.py", lid); continue
    k, hi = best
    STRAT[str(lid)] = ['vals', f"g{k}", list(range(0, hi + 1))]; print("leaf", lid, "split", f"g{k}", 0, "..", hi)
json.dump(STRAT, open('strategies.json', 'w'))
