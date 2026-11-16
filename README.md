# Toads and Frogs: Erickson's Conjecture 5 in Lean 4

**Erickson's Conjecture 5 (1996).** For Toads and Frogs, the starting position
`Tᵃ □ᵇ Fᵃ` (`a` toads, `b` empty squares, `a` frogs) is infinitesimal for every
`(a, b)` except `(a, b) = (3, 2)`.

This repository is a self-contained Lean 4 development aimed at this conjecture. It
uses Lean core only (no Mathlib) and has no `sorry`.

## Status

| What | Where |
| --- | --- |
| Statement of the conjecture (`Conjecture5 : Prop`) | `Cgt/Conjecture5.lean` |
| `(3, 2)` is **not** infinitesimal (`TTT□□FFF = ±1/8`) | `not_infinitesimal_3_2` |
| `a = 0`, all `b` | `infinitesimal_start_a_zero` |
| `a = 1`, all `b` (`T □ᵇ F`) | `infinitesimal_start_one` |
| **`a = 2`, all `b` (`TT □ᵇ FF`)**: machine-checked strategy over 1,543 shapes | `infinitesimal_start_two` (`Cgt/RowA2.lean`) |
| `b = 0`, all `a` | `infinitesimal_start_b_zero` |
| `b = 1`, all `a` (`Tᵃ □ Fᵃ`) | `infinitesimal_start_b_one` |
| `b = 2`, all `a ≥ 4` (Thanatipanonda's theorem, incl. his Lemma C.1) | `infinitesimal_start_b_two`, `upperZero_c1` |
| One-sided Death Leap Principle (Thanatipanonda), general | `le_zero_of_dlp` |
| Every case with `2a + b ≤ 12`, kernel-checked | `Cgt/FiniteCases.lean` |
| `(3,7)` to `(3,12)`, `(4,5)`, `(5,3)`, `(6,3)`: strategy certificates | `Cgt/Cert/` (`lake build CgtCerts`) |
| Combined partial result | `conjecture5_partial`, `conjecture5_provedRegion` |
| **General case** | **open** |

The full conjecture is **not** proved here. It has been open since 1996: Thanatipanonda
proved the column `b = 2` for `a ≥ 4` (2008), and Conjecture 5 is the only one of Erickson's
conjectures still open.

## Grid of proved cases

Each cell is the case `Tᵃ □ᵇ Fᵃ`, with `a` down the side and `b` across the top.

```
                              1 1 1 1 1 1 1 1 1 1 2 2 2 2 2 2 2 2 2
      b = 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8
a = 0     S S S S S S S S S S S S S S S S S S S S S S S S S S S S S
a = 1     S S S S S S S S S S S S S S S S S S S S S S S S S S S S S
a = 2     S S S S S S S S S S S S S S S S S S S S S S S S S S S S S
a = 3     S S X K K K K C C C C C C . . . . . . . . . . . . . .
a = 4     S S S K K C . . . . . . . . . . . . . . . . . . .
a = 5     S S S C . . . . . . . . . . . . .
a = 6     S S S C . . . . . . .
a = 7     S S S . . . . . .
a = 8     S S S . . . .
a = 9     S S S . . .
a = 10    S S S . .
a = 11    S S S . .
a = 12    S S S . .
a = 13    S S S .
a = 14    S S S .
a ≥ 15    S S S
```

| Mark | Meaning |
| --- | --- |
| `S` | Proved by a theorem for a whole family: `a ≤ 2`, `b ≤ 1`, or `b = 2` with `a ≥ 4`. These rows and columns continue for every `a` and `b`. |
| `K` | Single case checked by kernel `decide` (`Cgt/FiniteCases.lean`). |
| `C` | Single case proved by a strategy certificate: `Cgt.Cert_a_b.infinitesimal` in `Cgt/Cert/`, checked by `lake build CgtCerts`. |
| `X` | `(3, 2)`: proved **not** infinitesimal (`not_infinitesimal_3_2`). |
| `.` | Not proved in Lean, but confirmed by the exact solver (see below). |
| blank | Not computed. |

Apart from `(3, 2)`, the `S` and `K` cells are exactly `ProvedRegion`, which
`conjecture5_provedRegion` covers in one theorem. The `C` cells are separate theorems, one per case.

`Cgt/Cert/` also contains a certificate for `(4, 6)`. Checking it ran out of memory, so it is
not built with `CgtCerts` and is shown as `.` above.

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

Build with `lake build` (Lean `v4.36.0-rc2`).

* `Cgt/Certificate.lean` and `scripts/gen_cert.py`: turn an explicit Right strategy found by a
  solver into a Lean proof, with one small kernel-checked lemma per position. `lake build
  CgtCerts` checks the generated certificates in `Cgt/Cert/` for `(3, 4)`, `(3, 7)` to `(3, 12)`,
  `(4, 5)`, `(5, 3)` and `(6, 3)`. These are cases that plain kernel `decide` cannot handle
  within memory. The larger ones take 10 to 50 minutes each and run to tens of thousands of
  lemmas.

## The row a = 2

`infinitesimal_start_two : ∀ b, Infinitesimal (tf (start 2 b))`. The proof has four steps.

1. **One position.** For `b ≥ 2`, Left's only move from `TT□ᵇFF` is to `T□T□ᵇ⁻¹FF`. If that
   position is `≤ 0`, Right can answer by passing, so the symmetric start has Left stop `≤ 0`.
   So the row reduces to one claim: `T□T□ᵐFF ≤ 0` for all `m ≥ 1`.
2. **Shapes.** A position with two toads and two frogs is a piece order plus five gaps
   `g₀…g₄` (`Cgt/Four.lean`). Its *shape* (`Cgt/Shape4.lean`) records:
   * the order;
   * the mirrored differences `g₄ − g₀` and `g₃ − g₁`;
   * the smaller gap of each mirrored pair and the centre gap, capped at 4 (above that only
     the parity is kept).
3. **Shapes behave uniformly.** One move turns "same shape with margin `j + 1`" into "same
   shape with margin `j`". Every position has the same shape, with margin 2, as one of finitely
   many witnesses of its shape. So "every Left move from this shape has a good Right reply" is
   a finite check, and `le_zero_of_good` turns it into a proof for every position of every
   shape in a list.
4. **The finite check.** `scripts/gen_row2.py` finds 1,543 shapes containing every
   `T□T□ᵐFF` and closed under Left moves and Right's replies. Right keeps the mirrored
   differences within 2, a strategy found with the exact solver. The kernel checks the list
   (`checkA2`, about 30 seconds).

Simpler strategies fail: mirroring Left's move one turn late breaks down when the pieces meet,
and a greedy "closest to symmetric" reply lets the asymmetry grow without bound for even `m`.

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
