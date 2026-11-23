"""Turn the plans of tplan.py into Lean lemmas.

Usage: python3 gen.py NAME 'C M D KIND K' ['C M D KIND K' ...]
Writes Cgt/Sum/Gen/NAME.lean (inner nodes and Blocking Rule leaves) and prints the statements of
the library leaves it uses (to be proved in Cgt/Sum/Gen/NAMELib.lean).
"""
import sys, os
import tplan
from tplan import cost, collect, nodes, shift, BIG, lmoves, rmoves

SIMP_L = '[lmovesR, lmovesAux, moveAt, leftPartRev, rightPart]'
SIMP_R = '[rmovesR, mirrorRL, Cell.swap, lmovesR, lmovesAux, moveAt, leftPartRev, rightPart]'

def runs(s):
    out = []
    for ch in s:
        c = {'T': 'T', 'F': 'F', '.': 'E'}[ch]
        if out and out[-1][0] == c: out[-1][1] += 1
        else: out.append([c, 1])
    return out
def rl(t):
    c, M, d = t; parts = []
    if c is not None: parts.append(f'(T, x + {c})')
    parts += [f'({ch}, {n})' for ch, n in runs(M)]
    if d is not None: parts.append(f'(F, y + {d})')
    return '[' + ', '.join(parts) + ']'
def bexpr(b):
    sx, sy, k = b; s = ''
    if sx: s += ('(x : Int)' if sx == 1 else f'{sx} * (x : Int)')
    if sy: s += (' - (y : Int)' if sy == 1 else f' - {sy} * (y : Int)')
    if not s: return f'({k} : Int)'
    return s + (f' + {k}' if k >= 0 else f' - {-k}')
def binders(t, conds):
    c, M, d = t; s = ''
    if c is not None: s += ' (x : Nat)'
    if d is not None: s += ' (y : Nat)'
    for i, cd in enumerate(conds): s += f' (h{i} : {bexpr(cd)} < 0)'
    return s
def args(t, conds, extra=None):
    """Arguments for calling the lemma of claim (t, conds); `extra` is the name of a new hypothesis for the last cond."""
    c, M, d = t; s = ''
    if c is not None: s += ' x'
    if d is not None: s += ' y'
    for i, cd in enumerate(conds):
        s += f' {extra}' if (extra and i == len(conds) - 1) else f' h{i}'
    return s
def call(names, key, extra=None, cur_conds=()):
    t, kind, b, conds = key
    # hypotheses of the child: those of the current lemma come first, in the same order
    s = names[key] + args(t, conds, extra if len(conds) > len(cur_conds) else None)
    return s
def cast(names, key, extra=None, cur_conds=()):
    fn = 'starZ' if key[1] == 'star' else 'zint'
    return f'VR_cast ({call(names, key, extra, cur_conds)}) (by first | rfl | simp) (congrArg {fn} (by omega))'

def statement(names, key):
    t, kind, b, conds = key
    fn = 'starZ' if kind == 'star' else 'zint'
    return f'theorem {names[key]}{binders(t, conds)} :\n    le (VR {rl(t)}) ({fn} ({bexpr(b)}))'

def proof(names, key, plan):
    t, kind, b, conds = key; L = []
    if plan[0] == 'EMPTY':
        return ['  exfalso; omega']
    if plan[0] == 'BR':
        _, Xt, bx, Yt, by = plan
        kx = (Xt, 'int', bx, ()); ky = (Yt, 'int', by, ())
        return [f'  exact VR_split (RX := {rl(Xt)}) (RY := {rl(Yt)})',
                f'    (by simp [List.replicate_succ]) ({call(names, kx)}) ({call(names, ky)}) (by omega)']
    assert plan[0] == 'NODE'
    steps, ropt = plan[1], plan[2]
    L.append(f'  apply {"VR_le_starZ" if kind == "star" else "VR_le_zint"} (by simp [maxB, okFrom])')
    L.append('  · intro X hX')
    L.append(f'    simp {SIMP_L} at hX')
    if len(steps) == 1: L.append('    subst hX')
    elif len(steps) > 1: L.append('    rcases hX with ' + ' | '.join(['rfl'] * len(steps)))
    for st in steps:
        pre = '    · ' if len(steps) > 1 else '    '
        if st[0] == 'direct':
            ck = (st[2], 'int', shift(b, -1) if kind == 'int' else b, conds)
            L.append(f'{pre}exact Or.inl ({cast(names, ck)})')
        else:
            ck = (st[4], kind, b, conds)
            L.append(f'{pre}exact Or.inr ⟨{rl(st[4])}, by simp {SIMP_R}, {cast(names, ck)}⟩')
    if kind == 'star':
        rn, r, rb, rc = ropt
        L.append(f'  · exact ⟨{rl(r)}, by simp {SIMP_R}, {cast(names, (r, "int", rb, rc))}⟩')
    else:
        if ropt:
            rn, r, rb, rc = ropt
            L.append('  · intro hneg')
            L.append(f'    exact ⟨{rl(r)}, by simp {SIMP_R}, {cast(names, (r, "int", rb, rc), "hneg", conds)}⟩')
        else:
            L.append('  · intro hneg; exfalso; omega')
    return L

def main():
    name = sys.argv[1]; order = []; roots = []
    for spec in sys.argv[2:]:
        a = spec.split()
        c = None if a[0] == '-' else int(a[0]); M = a[1]; d = None if a[2] == '-' else int(a[2])
        t = (c, M, d); b = (1 if c is not None else 0, 1 if d is not None else 0, int(a[4]))
        if cost(t, a[3], b, ())[0] >= BIG: print('NO PLAN for', spec); sys.exit(1)
        collect(t, a[3], b, ()); roots.append((t, a[3], b, ()))
    # post-order: children before parents
    done = set(); seq = []
    def visit(key):
        if key in done: return
        done.add(key); plan = nodes[key]; t, kind, b, conds = key
        if plan[0] == 'BR':
            visit((plan[1], 'int', plan[2], ())); visit((plan[3], 'int', plan[4], ()))
        if plan[0] == 'NODE':
            for st in plan[1]:
                visit((st[2], 'int', shift(b, -1) if kind == 'int' else b, conds) if st[0] == 'direct' else (st[4], kind, b, conds))
            if plan[2]: visit((plan[2][1], 'int', plan[2][2], plan[2][3]))
        seq.append(key)
    for key in list(nodes): visit(key)
    names = {}; nlib = 0; nn = 0
    for key in seq:
        if nodes[key][0] in ('NODE', 'BR', 'EMPTY'): nn += 1; names[key] = f'{name}_c{nn}'
        else: nlib += 1; names[key] = f'{name}_lib{nlib}'
    cats = {'PURE': 'Pure', 'DEAD': 'Dead', 'T1U': 'Upper', 'T1L': 'Lower', 'NEED': 'Hand', 'HAND': 'Hand'}
    libs = {v: [f'import Cgt.Sum.Rules\n\n/-! Library leaves of the plan `{name}`, kind {v} (statements generated by `tools/sum/gen.py`). -/\n\nnamespace Cgt\nnamespace Col\nopen Cell TF Game\n'] for v in set(cats.values())}
    main_ = [''.join(f'import Cgt.Sum.Gen.{name}{v}\n' for v in sorted(set(cats.values()))) + f'\n/-! Generated by `tools/sum/gen.py`: the plan `{name}`. -/\n\nset_option maxRecDepth 4000\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\nnamespace Cgt\nnamespace Col\nopen Cell TF Game\n']
    for key in seq:
        plan = nodes[key]
        if plan[0] in ('NODE', 'BR', 'EMPTY'):
            main_.append(statement(names, key) + ' := by\n' + '\n'.join(proof(names, key, plan)) + '\n')
        else:
            libs[cats[plan[0]]].append(f'/-- {plan} -/\n' + statement(names, key) + ' := by\n  sorry\n')
    os.makedirs('../../Cgt/Sum/Gen', exist_ok=True)
    open(f'../../Cgt/Sum/Gen/{name}.lean', 'w').write('\n'.join(main_) + '\nend Col\nend Cgt\n')
    for v, body in libs.items():
        fn = f'../../Cgt/Sum/Gen/{name}{v}.lean'
        if not os.path.exists(fn) or os.environ.get('WRITELIB'):
            open(fn, 'w').write('\n'.join(body) + '\nend Col\nend Cgt\n')
        print(v, len(body) - 1)
    for r in roots: print('root', names[r], tplan.tname(r[0]), r[1], tplan.bname(r[2]))
    print(f'{nn} generated lemmas, {nlib} library leaves; last lemma {names[seq[-1]]}')

if __name__ == '__main__':
    tplan.NEED = bool(os.environ.get('NEED'))
    main()
