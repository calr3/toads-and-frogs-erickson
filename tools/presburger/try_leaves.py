# For hard leaves, write a Lean file of `example`s trying several case splits, compile it, report what works.
import pickle, sys, subprocess, re, json, os
from gen_lean import lit_lean, subst
LEAVES = pickle.load(open('leaves.pkl', 'rb')); cells, plan = pickle.load(open('plan.pkl', 'rb'))
N = ['g0', 'g1', 'g2', 'g3', 'g4']
def goal_of(lid):
    region, t = LEAVES[lid]
    hyps = " ".join(f"(h{i} : {lit_lean(l, N)})" for i, l in enumerate(region))
    if t[0] == 'dead': return hyps, "False"
    _, j, kind, c3, dT, ti = t
    return hyps, " ∧ ".join("(" + lit_lean(subst(l, dT), N) + ")" for l in cells[c3][ti])
def cands():
    out = [("omega", "omega")]
    for m in (2, 3, 6):
        for k in range(5):
            alts = " ∨ ".join(f"g{k} % {m} = {r}" for r in range(m)); pat = " | ".join(["hr"] * m)
            out.append((f"res g{k} mod {m}", f"rcases (show {alts} by omega) with {pat} <;> omega"))
    for m in (2, 3):
        for k in range(5):
            for k2 in range(k + 1, 5):
                a1 = " ∨ ".join(f"g{k} % {m} = {r}" for r in range(m)); a2 = " ∨ ".join(f"g{k2} % {m} = {r}" for r in range(m)); pat = " | ".join(["hr"] * m)
                out.append((f"res g{k},g{k2} mod {m}", f"rcases (show {a1} by omega) with {pat} <;> rcases (show {a2} by omega) with {pat} <;> omega"))
    return out
lids = [int(x) for x in sys.argv[1:]]
lines = []; where = {}
for lid in lids:
    hyps, goal = goal_of(lid)
    for name, tac in cands():
        where[len(lines) + 1] = (lid, name)
        lines.append(f"example (g0 g1 g2 g3 g4 : Nat) {hyps} : {goal} := by {tac}")
open('/tmp/claude-0/-home-user/61ff2dc0-a148-580e-9c0f-783ba0446bbb/scratchpad/try.lean', 'w').write("\n".join(lines) + "\n")
r = subprocess.run(["lean", "/tmp/claude-0/-home-user/61ff2dc0-a148-580e-9c0f-783ba0446bbb/scratchpad/try.lean"], capture_output=True, text=True, env=dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + ":" + os.environ["PATH"]))
bad = set(int(m.group(1)) for m in re.finditer(r"try\.lean:(\d+):\d+: error", r.stdout + r.stderr))
ok = {}
for ln, (lid, name) in where.items():
    if ln not in bad: ok.setdefault(lid, []).append(name)
for lid in lids: print(lid, ok.get(lid, [])[:6])
json.dump({str(k): v for k, v in ok.items()}, open('try_result.json', 'w'))
