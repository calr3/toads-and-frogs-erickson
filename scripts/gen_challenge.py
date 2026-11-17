#!/usr/bin/env python3
"""Generate Challenge.lean (the trusted statement for Comparator) from Cgt/Statement.lean.

Challenge.lean is the body of Cgt/Statement.lean, copied verbatim, followed by the main theorems
with `sorry`. Comparator checks that every declaration the theorem statements use is identical in
Challenge and in Solution, so the copy must not be edited by hand: change Cgt/Statement.lean and
rerun this script.

Usage: python3 scripts/gen_challenge.py   (from the repository root)
"""
import re

HEADER = '''/-!
# Challenge for Comparator

The statements of the main theorems, proved in `Cgt/Conjecture5.lean` (imported by
`Solution.lean`). Everything before the theorems is a verbatim copy of `Cgt/Statement.lean`, made
by `scripts/gen_challenge.py`; it uses Lean core only. See `comparator/README.md`.
-/

'''

THEOREMS = '''

/-! ## Main theorems -/

namespace Cgt
open Game

/-- The exception really is an exception: `TTT□□FFF` is not infinitesimal. -/
theorem not_infinitesimal_3_2 : ¬ Infinitesimal (tf (start 3 2)) := by
  sorry

/-- **Main theorem.** Erickson's Conjecture 5 holds if it holds in the cases left open
(`OpenCases`: `a ≥ 3`, `b ≥ 4`, `2a + b ≥ 13`). -/
theorem conjecture5_of_openCases (h : OpenCases) : Conjecture5 := by
  sorry

end Cgt
'''

src = open('Cgt/Statement.lean').read()
body = re.sub(r'\A/-!.*?-/\n\n', '', src, count=1, flags=re.S)   # drop the module docstring
assert 'import' not in body.split('namespace Cgt')[0], 'Statement.lean must import nothing'
open('Challenge.lean', 'w').write(HEADER + body.rstrip('\n') + THEOREMS)
print('wrote Challenge.lean')
