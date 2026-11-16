# Columns: `Tᵃ □ᵇ Fᵃ` with `b` fixed and `a` growing

Tools for finding an argument that covers a whole column, starting with `b = 3`. The idea is
the dual of the `a = 2` row (`Cgt/RowA2.lean`). There, a few pieces are separated by long gaps.
Here, a few empty squares are separated by long runs of pieces. **Status: a finite description of
Right's strategy for every `a` was found and checked (2,861 shapes), but not yet formalised.** See
`docs/RESEARCH_NOTES.md` §13.

Build each tool with `g++ -O2 -std=c++17 -o NAME NAME.cpp`.

| Tool | What it does |
| --- | --- |
| `col_explore.cpp` | Exact solver for "Left stop `≤ 0`" with Right's one pass. Extracts a strategy with a reply heuristic and reports how its positions are structured. |
| `col_bound.cpp` | The smallest bound on the number of runs (maximal blocks of equal cells) with which Right still wins. With a cap `K`, it also prints run statistics of one such strategy. |
| `col_shapes.cpp` | Abstract search over run shapes. Finds a set of shapes closed under Left's moves and Right's replies that contains the start shape of every `a ≥ 4`. |
| `col_realcheck.cpp` | Checks a shape set on the real game tree of `Tᵃ□ᵇFᵃ`. Every real position Right's strategy reaches must satisfy the closure conditions itself. For each `a` this is a complete proof, independent of the margin argument. |
| `verify_shapes.py` | An independent re-implementation (moves, runs, dead regions, shapes, witnesses) that checks a shape set exactly as a kernel check would. |
| `b3_shapes.txt` | The certificate for `b = 3`: 2,861 shapes (`U` = Left-stop phase, `N` = normal play). |

## Results for `b = 3`

* **Bounded structure.** Right can win while keeping at most 10 runs, for every `a` from 4 to 12
  (`col_bound 3 3 12 1`). Counting each dead `TTFF` block as one run gives the same bound. The
  columns `b = 4` and `b = 5` behave the same way, with bounds 12 (`a` = 4 to 8) and 13 (`a` = 4
  to 7).
* **Plain capped shapes fail.** Capping long runs at 4 (keeping parity, as for the `a = 2` row)
  loses the start shape. The reason is a race: Left's toad reservoir in front of 2 empty squares
  is worth twice its length in moves. Meanwhile a dead block can hold unequal numbers of toads and
  frogs, so the balance "`a` toads, `a` frogs" no longer pins the race down.
* **Clustered shapes close.** Keep exact differences between long runs that are within `M` of
  each other or of the anchor `K`, and only sign and parity across larger gaps. With `K = M = 4`
  the search closes with 646,574 shapes, every witness checked, balanced or not.
* **Dead regions shrink it.** A block of pieces with no empty square is dead from its first `TT`
  to its last `FF` after it (Erickson): those pieces never move again. Collapsing each dead region
  to one marker brings the set to 11,034 shapes.
* **Smaller parameters and minimisation.** `K = M = 2` plus greedy minimisation (`MINIMIZE=1`)
  gives **2,861 shapes**: 390 in the Left-stop phase and 2,471 in normal play. They have 5,451
  witnesses, averaging 25 cells, at most 69, and only 9,871 Left moves and passes to answer. That
  is in the range the kernel handles for the `a = 2` row.

| Shapes | Setting |
| --- | --- |
| 646,574 | `K = M = 4`, no dead regions |
| 42,359 | `K = M = 4`, dead `TTFF` junctions only |
| 11,034 | `K = M = 4`, all dead regions |
| 8,947 / 6,796 | `K = 4, M = 3` / `K = 3, M = 1` |
| 2,861 | `K = M = 2`, minimised (`b3_shapes.txt`) |

  Allowing more runs makes it worse (19,077 shapes with at most 11 runs, 191,789 with 12). With
  no exact differences (`M = 0`) the start shape is lost.
* **Checks of `b3_shapes.txt`.**
  * `verify_shapes.py b3_shapes.txt 3 2 2 2 60` finds no failing witness. The start shape of every
    `a` from 2 to 60 is in the set; beyond `a = 4` it depends only on the parity of `a`.
  * `col_realcheck b3_shapes.txt 3 4 40 2 2` finds no failure on the real game trees for any `a`
    from 4 to 40. So `Tᵃ□³Fᵃ` is infinitesimal for every `a ≤ 40`, well beyond the exact solver's
    limit of about `a = 14`.
  * The search is deterministic and reproduces the file exactly.

Open: a Lean framework for positions with any number of runs. It needs the margin lemma for
pairwise run differences, dead regions, normal forms, and soundness for the Left stop (not only
`≤ 0`). Then a kernel check of `b3_shapes.txt` would prove the whole column `b = 3`.
