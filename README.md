# Toads and Frogs: Erickson's Conjecture 5 in Lean 4

**Erickson's Conjecture 5 (1996).** For Toads and Frogs, the starting position
`Tᵃ □ᵇ Fᵃ` (`a` toads, `b` empty squares, `a` frogs) is infinitesimal for every
`(a, b)` except `(a, b) = (3, 2)`. (Conjecture 7.5 in [[E96]](#references).)

This repository is a self-contained Lean 4 development aimed at this conjecture. It
uses Lean core only (no Mathlib) and has no `sorry`.

## What is new

* **New, as far as we know: the column `b = 3`.** `Tᵃ□³Fᵃ` is infinitesimal for every `a`
  (`infinitesimal_start_b_three`). The only column previously proved for every `a` is `b = 2`
  [[T11]](#references); `b = 3` was known numerically only for small `a`. The proof is a
  computer-found strategy over 3,031 "run shapes", kernel-checked, with a general margin argument
  for positions with any number of runs. See [docs/COLUMN_B3.md](docs/COLUMN_B3.md).
* **New, as far as we know: the row `a = 2`.** `TT□ᵇFF` is infinitesimal for every
  `b` (`infinitesimal_start_two`). Before this, the row was known only numerically: Erickson
  tabulated `b ≤ 6` [[E96]](#references) and Thanatipanonda `b ≤ 103` [[T11]](#references). The
  method is in the spirit of Thanatipanonda and Zeilberger's symbolic finite-state approach
  [[TZ07]](#references). Our literature check covered those three papers, the Wikipedia article
  and web searches; it was not exhaustive. See
  [docs/ROW_A2.md §10](docs/ROW_A2.md#10-related-work).
* **Also new, as far as we know: the exact values of that row for every even `b`.**
  `TT□ᵇFF = 0` for every even `b ≥ 6` (`start_two_equiv_zero`), by the same method with 1,038
  shapes. Together with kernel checks of each `b ≤ 30`, this gives the value predicted by the data
  (below) for every even `b` and every `b ≤ 30` (`start_two_value`). The values for `b ≤ 30` were
  already known numerically [[T11]](#references); only their formal proof is new.
* **Everything else is a formal proof of a known (or trivial) result.** The *Origin* column below
  gives the source of each.
* **Observations, not theorems.** `docs/RESEARCH_NOTES.md` and `tools/` record computational
  experiments and negative findings, for example why the `a = 2` method does not extend to
  `a = 3`.
* **Still open:**
  * the full conjecture;
  * the exact values of the `a = 2` row for odd `b ≥ 31` (`ExactValuesA2`). The values computed
    so far are `∗` when `1 ≤ b ≤ 4` or `b ≡ 1 (mod 6)` and `0` otherwise: up to `b = 103` in
    [[T11]](#references), and up to `b = 80` by our solver here. For odd `b`, Right has to let
    the position drift from symmetry by an amount that grows with `b`, so the shape method does
    not apply as it stands ([docs/ROW_A2.md §8](docs/ROW_A2.md#8-exact-values)).

## Status

| What | Lean | Origin |
| --- | --- | --- |
| Statement of the conjecture (`Conjecture5 : Prop`) | `Cgt/Conjecture5.lean` | Erickson [[E96]](#references), Conjecture 7.5 |
| `(3, 2)` is **not** infinitesimal (`TTT□□FFF = ±1/8`) | `not_infinitesimal_3_2` | Known: the value `±1/8` is in [[E96]](#references) |
| `a = 0`, all `b` | `infinitesimal_start_a_zero` | Trivial (no pieces) |
| `a = 1`, all `b` (`T □ᵇ F`) | `infinitesimal_start_one` | Known: `T□ᵇF = b·∗` ([[WW]](#references); [[E96]](#references) Lemma 5.1) |
| **`a = 2`, all `b` (`TT □ᵇ FF`)**: machine-checked strategy over 1,543 shapes | `infinitesimal_start_two` (`Cgt/RowA2.lean`) | **New** as far as we know; values computed for `b ≤ 103` in [[T11]](#references) |
| **Exact values of `TT □ᵇ FF`**: `0` for every even `b ≥ 6` (1,038 shapes); `0` or `∗` as the data predict for every even `b` and every `b ≤ 30` | `start_two_equiv_zero`, `start_two_value` (`Cgt/RowA2Values.lean`) | **New** for all even `b`, as far as we know; `b ≤ 30` known numerically ([[T11]](#references)), `b ≤ 6` in [[E96]](#references) |
| `b = 0`, all `a` | `infinitesimal_start_b_zero` | Trivial (no moves) |
| `b = 1`, all `a` (`Tᵃ □ Fᵃ`) | `infinitesimal_start_b_one` | Known ([[WW]](#references), as cited in [[E96]](#references) §7) |
| `b = 2`, all `a ≥ 4` (incl. Lemma C.1) | `infinitesimal_start_b_two`, `upperZero_c1` | Known: Thanatipanonda's theorem [[T11]](#references) |
| **`b = 3`, all `a` (`Tᵃ □³ Fᵃ`)**: machine-checked strategy over 3,031 run shapes | `infinitesimal_start_b_three` (`Cgt/Col/Column3.lean`) | **New** as far as we know; values known numerically for small `a` ([[E96]](#references), [[T11]](#references) tables) |
| One-sided Death Leap Principle, general | `le_zero_of_dlp` | Known: [[T11]](#references); the two-sided version is in [[E96]](#references) |
| Every case with `2a + b ≤ 12`, kernel-checked | `Cgt/FiniteCases.lean` | Known numerically ([[E96]](#references), [[T11]](#references) tables) |
| `(3,7)` to `(3,12)`, `(4,5)`, `(5,3)`, `(6,3)`: strategy certificates | `Cgt/Cert/` (`lake build CgtCerts`) | Known numerically ([[T11]](#references) table) |
| Combined partial result | `conjecture5_partial`, `conjecture5_provedRegion` | Combines the rows above |
| **General case** | — | **Open** since 1996 |

The full conjecture is **not** proved here. It has been open since 1996 and is the only one of
Erickson's conjectures still open. The main earlier partial result is Thanatipanonda's proof of
the column `b = 2` for `a ≥ 4` [[T11]](#references).

## Grid of proved cases

Each cell is the case `Tᵃ □ᵇ Fᵃ`: `a` toads and frogs across the top, `b` empty squares down
the side. Generated from the Lean sources by `scripts/gen_grid.py`.

| **b** \ **a** | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | ≥ 15 |
|---:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| **0** | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 |
| **1** | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 |
| **2** | 🟩 | 🟩 | 🟩 | 🔷 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 |
| **3** | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 |
| **4** | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · | · | · | · | · |  |  |  |
| **5** | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · | · |  |  |  |  |  |  |
| **6** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · | · |  |  |  |  |  |  |  |
| **7** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · |  |  |  |  |  |  |  |  |
| **8** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · |  |  |  |  |  |  |  |  |
| **9** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |
| **10** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |
| **11** | 🟩 | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |
| **12** | 🟩 | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |
| **13** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **14** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **15** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **16** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **17** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **18** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **19** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **20** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **21** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **22** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **23** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **24** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **25** | 🟩 | 🟩 | 🟩 | · |  |  |  |  |  |  |  |  |  |  |  |  |
| **26** | 🟩 | 🟩 | 🟩 | · |  |  |  |  |  |  |  |  |  |  |  |  |
| **≥ 27** | 🟩 | 🟩 | 🟩 |  |  |  |  |  |  |  |  |  |  |  |  |  |

| Mark | Meaning |
| :-: | --- |
| 🟩 | Proved infinitesimal in Lean. |
| 🔷 | `(3, 2)`: the exception in the conjecture, proved **not** infinitesimal (`TTT□□FFF = ±1/8`, `not_infinitesimal_3_2`). |
| · | Not proved in Lean, but confirmed by the exact solver (see below). |
| *(blank)* | Not computed. |

How a cell is proved:

* `a ≤ 2` (every `b`), `b ≤ 1` (every `a`), `b = 2` with `a ≥ 4`, and `b = 3` (every `a`): one
  theorem per family.
  These continue beyond the edges of the table.
* The other cells are single cases:
  * most are checked by kernel `decide` (`Cgt/FiniteCases.lean`). With the families above they
    make up `ProvedRegion`, covered by `conjecture5_provedRegion`;
  * `(3, 7)` to `(3, 12)` and `(4, 5)` are proved by strategy certificates
    (`Cgt.Cert_a_b.infinitesimal` in `Cgt/Cert/`, checked by `lake build CgtCerts`). The
    certificates for `(5, 3)` and `(6, 3)` predate the `b = 3` theorem, which now covers them.

`Cgt/Cert/` also contains a certificate for `(4, 6)`. Checking it ran out of memory, so it is
not built with `CgtCerts` and is shown as · above.

## Contents

* `Cgt/Game.lean`: short partizan games as finite option lists, Conway's order
  (reflexive, transitive), negation, equivalence.
* `Cgt/Infinitesimal.lean`: the numbers `2⁻ⁿ`, and `Infinitesimal G := ∀ n, -2⁻ⁿ < G < 2⁻ⁿ`.
  It proves that `G ≤ 2⁻ⁿ` for all `n` (Left stop `≤ 0`) is equivalent to a purely
  combinatorial recursion (`upperZero_iff`, `lfZero_iff`).
* `Cgt/ToadsFrogs.lean`: the rules, the game tree `tf`, `start a b = Tᵃ □ᵇ Fᵃ`, and mirror
  symmetry `tf (mirror p) = -tf p`. Since `start a b` is mirror-symmetric, being
  infinitesimal reduces to having Left stop `≤ 0` (`infinitesimal_start_iff`).
* `Cgt/Decide.lean`: kernel-reducible evaluators for `≤ 0`, Left stop `≤ 0` and Right stop
  `≤ 0`, with soundness proofs.
* `Cgt/Moves.lean`, `Cgt/FamilyA1.lean`, `Cgt/FamilyB1.lean`, `Cgt/Basic.lean`: symbolic proofs
  for whole families.
* `Cgt/FamilyB2.lean`: Thanatipanonda's proof for `b = 2` (Lemma C.1 plus a short case tree).
* `Cgt/DLP.lean`: the one-sided Death Leap Principle (Left can only jump and there are no
  two adjacent empty squares, so the position is `≤ 0`).
* `Cgt/Four.lean`, `Cgt/Shape4.lean`, `Cgt/RowA2.lean`: the row `a = 2`. See
  [The row a = 2](#the-row-a--2) below.
* `Cgt/Col/`: the column `b = 3`. Positions as run lists, dead runs, keys, the margin relation, the
  soundness theorem, and the kernel-checked data. See [docs/COLUMN_B3.md](docs/COLUMN_B3.md).
* `Cgt/RowA2Zero.lean`, `Cgt/RowA2Values.lean`: exact values in the row `a = 2`.

Build with `lake build` (Lean `v4.36.0-rc2`).

* `Cgt/Certificate.lean` and `scripts/gen_cert.py`: turn an explicit Right strategy found by a
  solver into a Lean proof, with one small kernel-checked lemma per position. `lake build
  CgtCerts` checks the generated certificates in `Cgt/Cert/` for `(3, 4)`, `(3, 7)` to `(3, 12)`,
  `(4, 5)`, `(5, 3)` and `(6, 3)`. These are cases that plain kernel `decide` cannot handle
  within memory. The larger ones take 10 to 50 minutes each and run to tens of thousands of
  lemmas.

## The row a = 2

`infinitesimal_start_two : ∀ b, Infinitesimal (tf (start 2 b))`, in `Cgt/RowA2.lean`. In short:

1. **Reduction.** For `b ≥ 2`, Left's only move from `TT□ᵇFF` is to `T□T□ᵇ⁻¹FF`. That position is
   `≤ 0` (Right, moving second, wins), so Right can pass. The row reduces to
   `T□T□ᵐFF ≤ 0` for all `m ≥ 1`.
2. **Strategy.** Right keeps the differences between mirror-image gaps, `g₄ − g₀` and `g₃ − g₁`,
   within 2. Every position reached then falls into one of 1,543 *shapes*: piece order,
   mirrored differences, and the small gaps capped at 4 with their parity.
3. **Finite check.** One move turns "same shape with margin `j + 1`" into "same shape with margin
   `j`", so checking finitely many witnesses per shape covers every position of that shape
   (`le_zero_of_good`). The kernel checks all 1,543 shapes in about 30 seconds.

**Exact values.** `TT□ᵇFF` is symmetric, and each player has one move. So `TT□ᵇFF = 0` follows
from `T□T□ᵇ⁻²F□F ≤ 0`, and `TT□ᵇFF = ∗` from `TT□ᵇ⁻¹F□F ≤ 0`. For even `b`, the first claim
yields to the same method: Right keeps the mirrored differences within 4, over 1,038 shapes
(`scripts/search_row2.py`). For odd `b`, Right needs differences that grow with `b`, so that case
is open beyond `b = 30`. The cases `b ≤ 30` are checked one by one by the kernel.

**[docs/ROW_A2.md](docs/ROW_A2.md)** has the full account: background, the strategy with an
example line, the margin lemma and soundness proof, the data, the exact values (§8), and a map of
the files.

## The column b = 3

`infinitesimal_start_b_three : ∀ a, Infinitesimal (tf (start a 3))`, in `Cgt/Col/Column3.lean`. In
short:

1. **Runs.** With only three empty squares, a position is a few empty squares between long runs
   of pieces. Positions are handled as run lists, and moves on run lists are proved equal to moves
   on cells.
2. **Shapes.** Right's strategy, found by computer, uses 3,031 shapes. A shape records each run's
   cell and short lengths. It also records the exact differences between long live runs whose
   lengths are close, and only parity across large gaps. Runs in dead blocks (Erickson's dead
   pieces) are recorded without their lengths.
3. **Margin.** A move changes every recorded difference by at most 2, so checking each shape
   through finitely many witnesses covers every position of that shape (`margin_left`,
   `margin_right`, `wit_complete`). The kernel checks the witnesses in 16 chunks of about two
   minutes each.

**[docs/COLUMN_B3.md](docs/COLUMN_B3.md)** has the full account.

## Computational evidence beyond the formal results

An exact C++ solver for "Left stop `≤ 0`" (the same recursion as `Cgt/Infinitesimal.lean`)
confirms the conjecture for all of the following:

* `a ≤ 14` with `b = 3`;
* `a = 2` with `b ≤ 28`;
* `a = 3` with `b ≤ 26`;
* `a = 4` with `b ≤ 24`;
* `a = 5` with `b ≤ 16`;
* `a = 6` with `b ≤ 10`;
* `a = 7` with `b ≤ 8`;
* `a = 8` with `b ≤ 6`;
* `a = 9` with `b ≤ 5`;
* `a = 10` and `a = 11` with `b ≤ 4`;
* `a = 12` with `b ≤ 4`, and `a = 13, 14` with `b ≤ 3`.

The column `b = 3` is now proved for every `a` (`infinitesimal_start_b_three`). Independently of
that proof, `tools/column/col_realcheck.cpp` checks Right's strategy on the real boards for every
`a ≤ 40`.

## What we learned about a general proof

See `docs/RESEARCH_NOTES.md` for the full record (strategies tried, data, obstructions). The
exact solvers are in `tools/` (`stops.cpp` decides "Left stop `≤ 0`" for `Tᵃ□ᵇFᵃ`).


* The naive mirror strategy (Right copies Left's move reflected through the centre) does
  **not** prove the conjecture. Left can steer into symmetric positions that are hot, for
  example `T...TT.FF...F = {{1|1/4}|{-1/4|-1}}`. Whether a symmetric position is hot
  depends on non-local counts, such as the number of empty squares behind Left's leading
  block of toads.
* A strategy that worked in every case tested (`2 ≤ a ≤ 6`, `2 ≤ b ≤ 12`): Right mirrors.
  When mirroring is impossible or leads to a hot position, Right instead does one of:
  * passes (Left's move was a mistake: the position is `≤ 0`);
  * jumps the toad that slid into the centre square;
  * refills the square vacated by a toad's jump at the centre;
  * advances his front frog.
* After such a deviation, the asymmetry does not stay bounded. It spreads over about `2a`
  squares as crossed pieces travel to the far ends. So a proof by finitely many local
  "defect" types cannot work as is.
* For `a = 2` (all `b ≥ 2`) and `a = 3` (all `b ≥ 6`), "mirror, otherwise pass" suffices.
  The proof then reduces to a few parametric normal-play claims. For `a = 2` these are:
  * `□ⁱT□ʲ⁺¹FT□ʲ⁻¹F□ⁱ ≤ 0`;
  * `□ⁱT□ʲ⁺¹TF□ʲF□ⁱ ≤ 0`;
  * `□ⁱ⁺¹TT□F□F□ⁱ ≤ 0`.
* An invariant recognised by finite automata, on the board folded at its centre, would prove
  every case at once. `tools/regular/` can check such a candidate exactly for every board
  size, but none was found. Learned invariants need more than 10 states already for boards of
  at most 8 cells. For the `a = 2` row, the normal-play part needs hundreds of states and does
  not generalise. See `tools/regular/README.md`.

## References

* **[E96]** Jeff Erickson, *New Toads and Frogs Results*. In R. J. Nowakowski (ed.), *Games of No
  Chance*, MSRI Publications 29, Cambridge University Press, 1996, pp. 299–310.
* **[TZ07]** Thotsaporn Thanatipanonda and Doron Zeilberger, *A Symbolic Finite-State Approach
  for Automated Proving of Theorems in Combinatorial Game Theory*. arXiv:0710.4951, 2007.
* **[T11]** Thotsaporn Thanatipanonda, *Further Hopping with Toads and Frogs*. Electronic Journal
  of Combinatorics 18(1), 2011, #P67. arXiv:0804.0640.
* **[WW]** Elwyn Berlekamp, John Conway and Richard Guy, *Winning Ways for your Mathematical
  Plays*. Academic Press, 1982.
