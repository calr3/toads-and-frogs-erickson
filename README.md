# Toads and Frogs: Erickson's Conjecture 5 in Lean 4

**Erickson's Conjecture 5 (1996).** For Toads and Frogs, the starting position
`Tᵃ □ᵇ Fᵃ` (`a` toads, `b` empty squares, `a` frogs) is infinitesimal for every
`(a, b)` except `(a, b) = (3, 2)`. (Conjecture 7.5 in [[E96]](#references).)

For the rules of the game see [Toads and Frogs](https://en.wikipedia.org/wiki/Toads_and_Frogs) on
Wikipedia; for game values, infinitesimals and `∗` see
[Combinatorial game theory](https://en.wikipedia.org/wiki/Combinatorial_game_theory) and
[Star (game theory)](https://en.wikipedia.org/wiki/Star_(game_theory)).

This repository is a self-contained Lean 4 development aimed at this conjecture. It
uses Lean core only (no Mathlib) and has no `sorry`. Everything in the default build is checked
by Lean's kernel. The one exception is the column `b = 4` and its exact values (🟦 below): their
finite checks are too large for the kernel and are evaluated by `native_decide`, which also trusts
Lean's compiler. They are built separately, with `lake build CgtNative`.

## What is new

* **New, as far as we know: the column `b = 3`.** `Tᵃ□³Fᵃ` is infinitesimal for every `a`
  (`infinitesimal_start_b_three`). The only column previously proved for every `a` is `b = 2`
  [[T11]](#references); `b = 3` was known numerically only for small `a`. The proof is a
  computer-found strategy over 3,031 "run shapes", kernel-checked, with a general margin argument
  for positions with any number of runs. See [docs/COLUMN_B3.md](docs/COLUMN_B3.md).
* **New, as far as we know: the exact values of the column `b = 3`.** `Tᵃ□³Fᵃ = ∗` for every
  `a ≥ 4` (`start_three_equiv_star`); with the small cases, `Tᵃ□³Fᵃ` is `0` for `a = 0, 3` and `∗`
  otherwise (`start_three_value`). This is the case `b = 3` of Thanatipanonda's conjecture that
  `Tᵃ□ᵇFᵃ = ∗` whenever `a > b > 0` and `b ≠ 2` [[T11]](#references); the values were known for
  `a ≤ 10`.
  The proof is the `b = 3` method with "`≤ ∗`" in place of "Left stop `≤ 0`": a strategy over
  1,263 run shapes, kernel-checked.
* **New, as far as we know: the exact values of the column `b = 4`, proved with `native_decide`.**
  `Tᵃ□⁴Fᵃ = ∗` for every `a ≥ 5`; with the small cases, `0` for `a = 0, 1, 4` and `∗` otherwise
  (`start_four_value`). The same `≤ ∗` method, with gaps exact up to 2 and no parity; Right's
  strategy uses 361,981 run shapes, and the finite check (3.5 million witnesses) is evaluated by
  `native_decide`, like the `b = 4` theorem below.
* **New, as far as we know: the column `b = 4`, proved with `native_decide`.** `Tᵃ□⁴Fᵃ` is
  infinitesimal for every `a` (`infinitesimal_start_b_four`). The method is that of `b = 3`, with
  far gaps between long runs recorded without their parity; Right's strategy uses 233,087 run
  shapes. Its finite check (2.8 million witnesses, about 270 times the `b = 3` one) is evaluated by
  `native_decide`, so this theorem trusts Lean's compiler as well as the kernel: `#print axioms`
  lists, besides the usual three, one axiom per `native_decide` use, asserting the result of that
  compiled evaluation. It is kept out of the default build and of `conjecture5_provedRegion`.
  The shape set is also checked by two independent programs, and on the real game trees for
  every `a ≤ 24`. See [docs/RESEARCH_NOTES.md §14](docs/RESEARCH_NOTES.md).
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
* **New, as far as we know: counterexamples to Thanatipanonda's Conjecture 4 (computed, not
  proved in Lean).** [[T11]](#references) conjectures that `Tᵃ□ᵇFᵃ` is `0` or `∗` for every
  `b ≥ a > 0`. Our exhaustive solver finds that `T⁶□¹²F⁶` and `T⁷□¹⁰F⁷` are neither. Both are
  still infinitesimal, as Erickson's conjecture predicts, and neither is `∗2` or `∗3`
  either. This is Thanatipanonda's own Conjecture 4, not Erickson's Conjecture 4 (which
  Thanatipanonda and Zeilberger disproved). Our literature and web searches found no earlier
  report. See [Values of the starting positions](#values-of-the-starting-positions).
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
| **Exact values of `Tᵃ □³ Fᵃ`**: `∗` for every `a ≥ 4` (and `0` for `a = 0, 3`, `∗` for `a = 1, 2`); machine-checked strategy over 1,263 run shapes | `start_three_value`, `start_three_equiv_star` (`Cgt/Col/Value3.lean`) | **New** as far as we know; conjectured in [[T11]](#references), values known for `a ≤ 10` |
| **Exact values of `Tᵃ □⁴ Fᵃ`**: `∗` for every `a ≥ 5` (and `0` for `a = 0, 1, 4`, `∗` for `a = 2, 3`); strategy over 361,981 run shapes; 🟦 finite check by `native_decide` | `start_four_value`, `start_four_equiv_star` (`Cgt/Col/Value4.lean`; `lake build CgtNative`) | **New** as far as we know; conjectured in [[T11]](#references), values known for `a ≤ 10` |
| **`b = 4`, all `a` (`Tᵃ □⁴ Fᵃ`)**: strategy over 233,087 run shapes; 🟦 finite check by `native_decide` (trusts the compiler) | `infinitesimal_start_b_four` (`Cgt/Col/Column4.lean`; `lake build CgtNative`) | **New** as far as we know; values known numerically for small `a` ([[E96]](#references), [[T11]](#references) tables) |
| One-sided Death Leap Principle, general | `le_zero_of_dlp` | Known: [[T11]](#references); the two-sided version is in [[E96]](#references) |
| Every case with `2a + b ≤ 12`, kernel-checked | `Cgt/FiniteCases.lean` | Known numerically ([[E96]](#references), [[T11]](#references) tables) |
| `(3,7)` to `(3,12)`, `(4,5)`, `(5,3)`, `(6,3)`: strategy certificates | `Cgt/Cert/` (`lake build CgtCerts`) | Known numerically ([[T11]](#references) table) |
| Combined partial result | `conjecture5_partial`, `conjecture5_provedRegion` | Combines the rows above |
| **`T⁶□¹²F⁶` and `T⁷□¹⁰F⁷` are neither `0` nor `∗`** (infinitesimal), against [[T11]](#references)'s Conjecture 4 | — (computed by `tools/values.cpp`, not formalised) | **New** as far as we know |
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
| **4** | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | 🟦 | 🟦 | 🟦 | 🟦 | 🟦 | 🟦 | 🟦 | 🟦 | 🟦 | 🟦 | 🟦 |
| **5** | 🟩 | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · | · | · |  |  |  |  |  |
| **6** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · | · | · |  |  |  |  |  |  |
| **7** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · | · |  |  |  |  |  |  |  |
| **8** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · | · |  |  |  |  |  |  |  |
| **9** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · |  |  |  |  |  |  |  |  |
| **10** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · |  |  |  |  |  |  |  |  |
| **11** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · | · |  |  |  |  |  |  |  |  |
| **12** | 🟩 | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |
| **13** | 🟩 | 🟩 | 🟩 | · | · | · | · |  |  |  |  |  |  |  |  |  |
| **14** | 🟩 | 🟩 | 🟩 | · | · | · | · |  |  |  |  |  |  |  |  |  |
| **15** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **16** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **17** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **18** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **19** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **20** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **21** | 🟩 | 🟩 | 🟩 | · | · | · |  |  |  |  |  |  |  |  |  |  |
| **22** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **23** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **24** | 🟩 | 🟩 | 🟩 | · | · |  |  |  |  |  |  |  |  |  |  |  |
| **25** | 🟩 | 🟩 | 🟩 | · |  |  |  |  |  |  |  |  |  |  |  |  |
| **26** | 🟩 | 🟩 | 🟩 | · |  |  |  |  |  |  |  |  |  |  |  |  |
| **≥ 27** | 🟩 | 🟩 | 🟩 |  |  |  |  |  |  |  |  |  |  |  |  |  |

| Mark | Meaning |
| :-: | --- |
| 🟩 | Proved infinitesimal in Lean, checked by the kernel. |
| 🟦 | Proved infinitesimal in Lean with a finite check by `native_decide`, which trusts Lean's compiler as well as the kernel (the column `b = 4`; `lake build CgtNative`). |
| 🔷 | `(3, 2)`: the exception in the conjecture, proved **not** infinitesimal (`TTT□□FFF = ±1/8`, `not_infinitesimal_3_2`). |
| · | Not proved in Lean, but confirmed by an exact solver (see [below](#computational-evidence-beyond-the-formal-results)). |
| *(blank)* | Not computed. |

How a cell is proved:

* `a ≤ 2` (every `b`), `b ≤ 1` (every `a`), `b = 2` with `a ≥ 4`, and `b = 3` (every `a`): one
  theorem per family.
  These continue beyond the edges of the table.
* `b = 4` (every `a`, 🟦 where not proved otherwise too): one theorem,
  `infinitesimal_start_b_four`, whose finite check is evaluated by `native_decide`.
* The other cells are single cases:
  * most are checked by kernel `decide` (`Cgt/FiniteCases.lean`). With the families above they
    make up `ProvedRegion`, covered by `conjecture5_provedRegion`;
  * `(3, 7)` to `(3, 12)` and `(4, 5)` are proved by strategy certificates
    (`Cgt.Cert_a_b.infinitesimal` in `Cgt/Cert/`, checked by `lake build CgtCerts`). The
    certificates for `(5, 3)` and `(6, 3)` predate the `b = 3` theorem, which now covers them.

`Cgt/Cert/` also contains a certificate for `(4, 6)`. Checking it ran out of memory, so it is
not built with `CgtCerts` and is shown as · above.

## Values of the starting positions

The exact value of `Tᵃ □ᵇ Fᵃ` where it is known, and where it comes from. Generated by
`scripts/gen_values.py` from the published tables and from `tools/values.txt`. Every value
except `(3, 2)` is infinitesimal: `0` and [`∗`](https://en.wikipedia.org/wiki/Star_(game_theory))
are the simplest infinitesimals, and `∗2`, `∗3` below are
[nimbers](https://en.wikipedia.org/wiki/Nimber).

<!-- values table: begin -->
| **b** \ **a** | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | ≥ 15 |
|---:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|:-:|
| **1** | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ |
| **2** | 🔵 0 | 🔵 ∗ | 🔵 ±⅛ | 🔵 N | 🔵 N | 🔵 N | 🔵 N | 🔵 N | 🔵 N | 🔵 N | 🟠 N | 🟠 N | 🟠 N | 🟠 N |  |
| **3** | 🔵 ∗ | 🔵 ∗ | 🔵 0 | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🟠 ∗ | 🟠 ∗ | 🟠 ∗ | 🟠 ∗ |  |
| **4** | 🔵 0 | 🔵 ∗ | 🔵 ∗ | 🔵 0 | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🟠 ∗ |  |  |  |  |
| **5** | 🔵 ∗ | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🔵 ∗ | 🟠 ∗ | 🟠 ∗ |  |  |  |  |  |
| **6** | 🔵 0 | 🔵 0 | 🔵 ∗ | 🔵 0 | 🔵 0 | 🔵 ∗ | 🟠 ∗ | 🟠 ∗ | 🟠 ∗ |  |  |  |  |  |  |
| **7** | 🔵 ∗ | 🔵 ∗ | 🔵 0 | 🔵 0 | 🔵 ∗ | 🔵 ∗ | 🟠 ∗ | 🟠 ∗ |  |  |  |  |  |  |  |
| **8** | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 ∗ | 🔵 0 | 🟠 ∗ | 🟠 0 | 🟠 ∗ |  |  |  |  |  |  |  |
| **9** | 🔵 ∗ | 🔵 0 | 🔵 0 | 🔵 ∗ | 🔵 0 | 🟠 ∗ | 🟠 ∗ |  |  |  |  |  |  |  |  |
| **10** | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 0 | 🟠 ≠0,∗ |  |  |  |  |  |  |  |  |
| **11** | 🔵 ∗ | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 ∗ | 🟠 ∗ | 🟠 ∗ |  |  |  |  |  |  |  |  |
| **12** | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 ≠0,∗ |  |  |  |  |  |  |  |  |  |
| **13** | 🔵 ∗ | 🔵 ∗ | 🔵 0 | 🔵 0 | 🟠 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |
| **14** | 🔵 0 | 🔵 0 | 🔵 ∗ | 🔵 0 | 🟠 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |
| **15** | 🔵 ∗ | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |
| **16** | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |
| **17** | 🔵 ∗ | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 ∗ |  |  |  |  |  |  |  |  |  |  |
| **18** | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |
| **19** | 🔵 ∗ | 🔵 ∗ | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |
| **20** | 🔵 0 | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |
| **21** | 🔵 ∗ | 🔵 0 | 🔵 0 | 🟠 0 | 🟠 ∗ |  |  |  |  |  |  |  |  |  |  |
| **22** | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |  |
| **23** | 🔵 ∗ | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |  |
| **24** | 🔵 0 | 🔵 0 | 🔵 0 | 🟠 0 |  |  |  |  |  |  |  |  |  |  |  |
| **25** | 🔵 ∗ | 🔵 ∗ | 🔵 0 |  |  |  |  |  |  |  |  |  |  |  |  |
| **26** | 🔵 0 | 🔵 0 | 🔵 0 |  |  |  |  |  |  |  |  |  |  |  |  |
| **27** | 🔵 ∗ | 🔵 0 | 🔵 0 |  |  |  |  |  |  |  |  |  |  |  |  |
| **28** | 🔵 0 | 🔵 0 | 🔵 0 |  |  |  |  |  |  |  |  |  |  |  |  |
| **29** | 🔵 ∗ | 🔵 0 | 🔵 ∗ |  |  |  |  |  |  |  |  |  |  |  |  |
| **30** | 🔵 0 | 🔵 0 | 🔵 0 |  |  |  |  |  |  |  |  |  |  |  |  |
<!-- values table: end -->

| Mark | Meaning |
| :-: | --- |
| 🔵 | Published: *Winning Ways* [[WW]](#references) (`a = 1` and `b = 1`), Erickson [[E96]](#references) or Thanatipanonda [[T11]](#references). Recomputed here wherever in reach, with no disagreement. |
| 🟠 | Not in those tables: computed here by exhaustive search (not a Lean proof). This includes the four cells that [[T11]](#references) lists only as "≠ 0", `(5, 11)`, `(6, 8)`, `(7, 6)` and `(7, 7)`: all four are `∗`. |
| `±⅛` | `(3, 2)`, the exception in the conjecture. |
| `N` | An infinitesimal other than `0` and `∗`, with a long canonical form ([[E96]](#references) writes out `a = 4, 5, 6`). |
| `≠0,∗` | Infinitesimal, but neither `0` nor `∗`: `(6, 12)` and `(7, 10)`, against [[T11]](#references)'s Conjecture 4 (see below). |
| *(blank)* | Not known. |

* **Beyond the table.** `a = 1` gives `∗` for odd `b` and `0` for even `b`, and `b = 1` gives `∗`,
  for every `a` and `b` [[WW]](#references). For `a = 2` and `31 ≤ b ≤ 103` the value is `0`,
  except `∗` when `b ≡ 1 (mod 6)`; for `a = 3` and `31 ≤ b ≤ 53` it is `0` [[T11]](#references).
* **What is proved in Lean.** The row `a = 2`: every `b ≤ 30` and every even `b`
  (`start_two_value`, `start_two_equiv_zero`). The row `b = 3`: every `a` (`start_three_value`).
  The row `b = 4`: every `a` (`start_four_value`, with `native_decide`). The other values are not
  formalised; the grid above shows which cells are proved infinitesimal.
* **How the values are computed.** `Tᵃ □ᵇ Fᵃ` is its own mirror image (reverse the board, swap
  toads and frogs), so its value `G` satisfies `G = −G`. Hence `G ≤ 0` already means `G = 0`, and
  `G + ∗ ≤ 0` means `G = ∗`. `tools/values.cpp` decides both by exhaustive search on boards of up
  to 32 cells; [[T11]](#references)'s program likewise decides comparisons, not values. Every
  computed value is `0` or `∗`, except `(3, 2)`, the column `b = 2`, `(6, 12)` and `(7, 10)`.
* **`(6, 12)` and `(7, 10)` contradict a conjecture of Thanatipanonda.** [[T11]](#references)
  conjectures that `Tᵃ□ᵇFᵃ` is `0` or `∗` whenever `b ≥ a > 0` (Conjecture 4); its table stops at
  `b = 8` for `a = 6` and at `b = 7` for `a = 7`. Both cells are neither. Both are infinitesimal
  (`STOPS=1`, which decides "Left stop `≤ 0`", equivalent to infinitesimal when `G = −G`), so
  they agree with Erickson's conjecture. Neither is `∗2` or `∗3` either (`NIM=3`, a separate
  recursion that also confirms they are not `0` or `∗`). The same solver reproduces all 114 published values in reach. These are computations,
  not Lean proofs.
* **"New" means "not in the tables above".** Our literature search covered those papers,
  [[TZ07]](#references) and web searches; it was not exhaustive.

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
* `Cgt/Col/`: the columns `b = 3` and `b = 4`. Positions as run lists, dead runs, keys, the
  margin relation (for any gap rule), the soundness theorem, the kernel-checked data of `b = 3`
  and the `native_decide`-checked data of `b = 4` (`Cgt/Col/B4*.lean`, `Column4.lean`, generated by
  `scripts/gen_b4.py`). See [docs/COLUMN_B3.md](docs/COLUMN_B3.md).
* `Cgt/RowA2Zero.lean`, `Cgt/RowA2Values.lean`: exact values in the row `a = 2`.

Build with `lake build` (Lean `v4.36.0-rc2`). `lake build CgtNative` builds the column `b = 4`
(about 15 minutes; it uses `native_decide`).

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

**The exact values** (`start_three_value`, `Cgt/Col/Value3.lean`) come from the same framework with
"`≤ ∗`" in place of "Left stop `≤ 0`" (`chkS`, `soundS` in `Cgt/Col/SoundStar.lean`): a position is
`≤ ∗` if Right has a move to a position `≤ 0`, and every Left move leads to a position `≤ 0` or one
with a Right reply `≤ ∗`. Right's strategy uses 1,263 shapes (`tools/column/b3_star_shapes.txt`),
checked by the kernel in 6 files of up to about three minutes. Since `Tᵃ□³Fᵃ` is its own mirror
image, `≤ ∗` means `= ∗`.

**The column `b = 4`** (`infinitesimal_start_b_four`, `Cgt/Col/Column4.lean`) uses the same
framework with another gap rule: far gaps between long runs keep only their sign, not their parity
(`ruleF`; `b = 3` uses `ruleP`). Right needs 13 runs and 233,087 shapes
(`tools/column/b4_shapes.txt.gz`). The finite check is about 270 times the size of the `b = 3`
one. It is evaluated by `native_decide` in 8 files, so this theorem trusts Lean's compiler as well
as the kernel (`docs/RESEARCH_NOTES.md` §14). The exact values of `b = 4` (`start_four_value`,
`Cgt/Col/Value4.lean`) follow the `b = 3` pattern with the gap rule `ruleF2` (exact up to 2, no
parity), 361,981 shapes (`tools/column/b4_star_shapes.txt.gz`) and 9 `native_decide` files.

## Computational evidence beyond the formal results

Two exact C++ solvers confirm the conjecture beyond the proved cases: `tools/stops.cpp`, which
decides "Left stop `≤ 0`" (the same recursion as `Cgt/Infinitesimal.lean`), and
`tools/values.cpp`, whose values `0` and `∗` are infinitesimal and which also has a `STOPS=1`
mode for the other cells (results in `tools/values.txt`). Together they cover:

* `a = 3` with `b ≤ 26`;
* `a = 4` with `b ≤ 24`;
* `a = 5` with `b ≤ 21`;
* `a = 6` with `b ≤ 14`;
* `a = 7` with `b ≤ 11`;
* `a = 8` with `b ≤ 8`;
* `a = 9` with `b ≤ 6`;
* `a = 10` with `b ≤ 5`.

With the proved row `a = 2` and columns `b ≤ 4`, this is every board of at most 24 squares
(`2a + b ≤ 24`). The smallest board size not fully checked is 25: `(8, 9)` and `(9, 7)` are still
running. The solvers also reached `a = 2` with `b ≤ 28` and `a ≤ 14` with
`b = 3`, before those families were proved.

The column `b = 3` is now proved for every `a` (`infinitesimal_start_b_three`). Independently of
that proof, `tools/column/col_realcheck.cpp` checks Right's strategy on the real boards for every
`a ≤ 40`. For `b = 4` the same check of the 233,087-shape strategy passes for every `a ≤ 24`.

`tools/values.cpp` goes further on the same boards and determines the exact value whenever it is
`0` or `∗`. The results, compared with the published tables, are in
[Values of the starting positions](#values-of-the-starting-positions).

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
