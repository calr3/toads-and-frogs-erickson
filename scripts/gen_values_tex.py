#!/usr/bin/env python3
"""Write paper/values_table.tex: the table of values of T^a .^b F^a for paper/new_results.tex.

Reuses the data of scripts/gen_values.py. New cells (computed here, not in [WW], [E96] or [T11],
including the four cells [T11] lists only as "≠ 0", and not counting b ≤ 3, where the
values follow from [T11] and [Th08]) are shaded; values proved in Lean are bold.
Run from the repository root.
"""
import contextlib
import io
import runpy
import sys

sys.argv = ['gen_values.py']
with contextlib.redirect_stdout(io.StringIO()):
    g = runpy.run_path('scripts/gen_values.py')
pub, comp, cell, AMAX, BMAX = g['pub'], g['comp'], g['cell'], g['AMAX'], g['BMAX']


def proved(a, b):
    return a == 2 or b in (3, 4) or (a, b) == (6, 12)


TEX = {'∗': r'\ast', '0': '0', '±⅛': r'\pm\frac18', 'N': r'\mathrm{N}', '≠0,∗': r'\dagger'}
rows = []
for b in range(1, BMAX + 1):
    cells = []
    for a in range(1, AMAX + 1):
        v = cell(a, b)
        if not v:
            cells.append('')
            continue
        s = TEX[v]
        s = rf'\boldsymbol{{{s}}}' if proved(a, b) else s
        s = f'${s}$'
        if b > 3 and (a, b) in comp and ((a, b) not in pub or pub[(a, b)][0] == '≠0'):
            s = r'\new ' + s
        cells.append(s)
    rows.append(rf'\textbf{{{b}}} & ' + ' & '.join(cells) + r' \\')
open('paper/values_table.tex', 'w').write('\n'.join(rows) + '\n')
