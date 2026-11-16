# Columns: `Tᵃ □ᵇ Fᵃ` with `b` fixed and `a` growing

Tools for finding an argument that covers a whole column, starting with `b = 3`. The idea is
the dual of the `a = 2` row (`Cgt/RowA2.lean`). There, a few pieces are separated by long gaps.
Here, a few empty squares are separated by long runs of pieces. **Status: a finite description of
Right's strategy for every `a` was found and checked, but not yet formalised.** See
`docs/RESEARCH_NOTES.md` §13.

Build each tool with `g++ -O2 -std=c++17 -o NAME NAME.cpp`.

| Tool | What it does |
| --- | --- |
| `col_explore.cpp` | Exact solver for "Left stop `≤ 0`" with Right's one pass. Extracts a strategy with a reply heuristic and reports how its positions are structured. |
| `col_bound.cpp` | The smallest bound on the number of runs (maximal blocks of equal cells) with which Right still wins. With a cap `K`, it also prints run statistics of one such strategy. |
| `col_shapes.cpp` | Abstract search over run shapes. Finds a set of shapes closed under Left's moves and Right's replies that contains the start shape of every `a ≥ 4`. |
| `col_realcheck.cpp` | Checks a shape set on the real game tree of `Tᵃ□ᵇFᵃ`. Every real position Right's strategy reaches must satisfy the closure conditions itself. For each `a` this is a complete proof, independent of the margin argument. |

## Results for `b = 3`

* **Bounded structure.** Right can win while keeping at most 10 runs, for every `a` from 4 to 12
  (`col_bound 3 3 12 1`). Counting each dead `TTFF` block as one run gives the same bound. The
  columns `b = 4` and `b = 5` behave the same way, with bounds 12 (`a` = 4 to 8) and 13 (`a` = 4
  to 7).
* **Plain capped shapes fail.** Capping long runs at 4 (keeping parity, as for the `a = 2` row)
  loses the start shape. The reason is a race: Left's toad reservoir in front of 2 empty squares
  is worth twice its length in moves. Meanwhile a dead block can hold unequal numbers of toads and
  frogs, so the balance "`a` toads, `a` frogs" no longer pins the race down.
* **Clustered shapes close.** `col_shapes 3 10 4 4` keeps exact differences between long runs
  that are within 4 of each other or of the anchor 4, and only parity across larger gaps. It finds
  a closed set of 646,574 shapes (9,567 of them in the Left-stop phase), with every witness
  checked, balanced or not. An independent re-check of the closure found no failures.
* **Real game trees.** `col_realcheck` on that set finds no failure for any `a` from 4 to 40.
  At `a = 40` that is 758 + 33,789 real positions. So `Tᵃ□³Fᵃ` is infinitesimal for every
  `a ≤ 40`, well beyond the exact solver's limit of about `a = 14`.

Open problems:

* **Size.** The set is far too large for a kernel check, and its witnesses reach 195 cells.
  Restricting Right to at most 1, 2 or 3 far gaps loses the start shape.
* **Formalisation.** A Lean framework for positions with any number of runs: the margin lemma
  for pairwise run differences, normal forms, and soundness for the Left stop (not only `≤ 0`).
