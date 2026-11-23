# Proof plans by one-step rules and the Blocking Rule

Tools behind `Cgt/Sum/` (`three_empty_value`: `Tᵃ□³Fᵇ = {a − b | a − b}` for `a, b ≥ 4`).
Positions are strings such as `TT.TTF.F`.

| Tool | What it does |
| --- | --- |
| `explore.py` | Exact `le_int(p, n)`, `ge_int(p, n)`, `le_star(p, n)` for any position and any integer `n`, by Conway's one-step rules; `ub`, `lb` (least and greatest integer bounds); `node` prints how each Left move of a family can be answered. |
| `plan.py POSITION star\|int N` | The smallest proof tree for one concrete position, with Blocking Rule leaves. |
| `tplan.py C M D star\|int K` | The same for a family `T^(x+C) M F^(y+D)`, uniformly in `x, y ≥ 0` (`-` for no reservoir). Leaves must be things already proved: positions of one colour, a dead frog, or a bound of the one-frog theorem (`Cgt/OneFrog`). `NEED=1` also accepts other one-frog or one-toad claims, at a high cost, and lists them: these have to be proved by hand. |
| `gen.py NAME 'C M D KIND K' …` | Runs `tplan` on the given families and writes `Cgt/Sum/Gen/NAME.lean` (one lemma per inner node and per Blocking Rule leaf) and, with `WRITELIB=1`, the statements of the library leaves in `Cgt/Sum/Gen/NAME{Pure,Dead,Upper,Lower,Hand}.lean`, to be proved separately. |

The three-empty-squares proof is

    NEED=1 python3 gen.py T3 "5 ... 5 star 0" "- TTTT... 5 star -1" "5 ...FFFF - star 1" "- TTTT...FFFF - star 0"

(261 generated lemmas and 68 library leaves, two of them proved by hand). A plan is tested on a
grid of `x, y ≤ 3`; that it holds for all `x, y` is what Lean checks.
