#!/usr/bin/env python3
"""Print the README's table of proved cases, read from the Lean sources.

A case is marked proved (however it is proved) if it is covered by
* a whole family: a <= 2 (Cgt/RowA2.lean, FamilyA1, Basic), b <= 1, or b = 2 with a >= 4;
* a single case checked by kernel `decide`: the `start a b` cases in Cgt/FiniteCases.lean;
* a strategy certificate: the CgtCerts roots in lakefile.toml.
(3, 2) is proved not infinitesimal. Otherwise a case is confirmed by the exact solver (README
"Computational evidence") or not computed.

Usage: gen_grid.py   (run from the repository root)
"""
import re

# Largest b confirmed by the exact solver, per a (README "Computational evidence").
SOLVER = {2: 28, 3: 26, 4: 24, 5: 16, 6: 10, 7: 8, 8: 6, 9: 5, 10: 4, 11: 4, 12: 4, 13: 3, 14: 3}

kernel = {(int(a), int(b)) for a, b in re.findall(r'start (\d+) (\d+)', open('Cgt/FiniteCases.lean').read())}
certs = {(int(a), int(b)) for a, b in re.findall(r'Case_(\d+)_(\d+)', open('lakefile.toml').read())}

# Explicit columns and rows up to the last a and b where anything changes; beyond them every
# column looks like the last one ("≥ AMAX + 1") and every row like the last one ("≥ BMAX + 1").
AMAX = max(SOLVER)
BMAX = max(b for a, b in SOLVER.items() if a > 2)
INF = 10 ** 6


def mark(a, b):
    if (a, b) == (3, 2):
        return '🔷'
    if a <= 2 or b <= 1 or (b == 2 and a >= 4) or (a, b) in kernel or (a, b) in certs:
        return '🟩'
    if b <= SOLVER.get(a, -1):
        return '·'
    return ''


assert all(a <= AMAX and b <= BMAX for a, b in kernel | certs)
cols = [str(a) for a in range(AMAX + 1)] + [f'≥ {AMAX + 1}']
print('| **b** \\ **a** | ' + ' | '.join(cols) + ' |')
print('|---:|' + ':-:|' * len(cols))
for b, label in [(b, str(b)) for b in range(BMAX + 1)] + [(INF, f'≥ {BMAX + 1}')]:
    cells = [mark(a, b) for a in range(AMAX + 1)] + [mark(INF, b)]
    print(f'| **{label}** | ' + ' | '.join(cells) + ' |')
