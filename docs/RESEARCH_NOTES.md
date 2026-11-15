# Research notes on Erickson's Conjecture 5

These notes record what was tried in attempting a general proof that `Tᵃ □ᵇ Fᵃ` is
infinitesimal for all `(a, b) ≠ (3, 2)`, and why each approach stopped short. The formal
results are in `Cgt/` (see `README.md`); the tools used are in `tools/` and `scripts/`.

## 1. Reformulation used throughout

* `start a b` is mirror-symmetric (`tf (mirror p) = -tf p`), so it is infinitesimal iff its
  Left stop is `≤ 0` (`infinitesimal_start_iff`).
* "Left stop `≤ 0`" (`UpperZero`) and "Right stop `≤ 0`" (`LfZero`) satisfy, with no reference
  to numbers:
  * `UpperZero G ⟺ LfZero G ∧ ∀ Gᴸ, LfZero Gᴸ`;
  * `LfZero G ⟺ G ≤ 0 ∨ ∃ Gᴿ, UpperZero Gᴿ`.

  This is normal play in which Right owns a single "pass" (using it ends all passing: the rest
  must be a normal-play win, `G ≤ 0`), while Left may pass freely.
* For a symmetric position, `LfZero` holds automatically.

`tools/stops.cpp` decides `UpperZero` for `start a b` exactly with this recursion.

## 2. Computational evidence

The conjecture holds in every case computed. That includes:

* `a = 2` for `b ≤ 28`;
* `a = 3` for `b ≤ 26`;
* `a = 4` for `b ≤ 24`;
* `a = 5` for `b ≤ 16`;
* `a = 6` for `b ≤ 10`;
* `a = 7` for `b ≤ 8`;
* `a = 8` for `b ≤ 6`;
* `a = 9` for `b ≤ 5`;
* `a ≤ 12` for `b ≤ 4`;
* `a ≤ 14` for `b ≤ 3`.

The limit is memory: around 5·10⁸ states.

## 3. The mirror strategy and why it is not enough

Right answers each Left move by its mirror image. This fails in only three local ways at the
centre:

* (A) `b` odd: `T□F → □TF`.
* (B) `b` odd: `TF□TF → □FTTF`.
* (C) `b` even: `□TF□ → □□FT`.

The trouble is that Left can steer into symmetric positions that are **hot**. Examples:

| position | value |
| --- | --- |
| `.TT.FF.` | `±1/4` |
| `T...TT.FF...F` | `{{1|1/4}|{-1/4|-1}}` |
| `....TTT.FFF....` | `{{1|1}|{-1|-1}}` |

Writing a symmetric uncrossed position as `X·X̄` (`b` even) or `X·□·X̄` (`b` odd), with `X` the
left half read left to right, the hot ones ("BAD") include:

* `b` odd, `|X| = 8`: `......TT TT....TT T.T...TT .TT...TT T..T..TT .T.T..TT ....T.TT T...T.TT
  .T..T.TT .....TTT T....TTT .T...TTT TT...TTT`
* `b` odd, `|X| = 9`: `.......TT T..T...TT .T.T...TT T...T..TT .T..T..TT ..T.T..TT T....T.TT
  .T...T.TT ..T..T.TT .TT..T.TT` and every `Z...TTT` (`Z` any 3 cells)
* `b` even, `|X| = 8`: `....TTT. T...TTT. .T..TTT. ..T.TTT. ...TTTT. T..TTTT. ....TT.T T...TT.T
  .T..TT.T ..T.TT.T ...TTT.T T..TTT.T`

Being BAD needs a block of toads at the front with enough empty squares behind it, which a
crossing frog can later use. Exactly which `X` are BAD depends on non-local counts; for
example `....T.TT` (odd) is BAD but `T.....TT` is not. `tools/bad_symmetric.cpp` enumerates the
BAD set.

## 4. Mirror plus local deviations (`tools/sigma_strategy.cpp`)

Strategy σ: Right mirrors when the mirrored position is good. Otherwise Right uses the first
of the following replies that is good:

1. **Pass**: Left's move was a mistake, i.e. the position is `≤ 0`.
2. **Jump**, case (A): the frog jumps the toad that slid into the centre.
3. **Refill**, case (C): the jumped frog slides into the square the toad vacated.
4. **Front advance**: the front frog advances.

σ wins for every `2 ≤ a ≤ 6`, `2 ≤ b ≤ 12` except `(3, 2)`. "Mirror or pass" alone already
wins for:

* `a = 2`, all `2 ≤ b ≤ 28`;
* `a = 3`, all `6 ≤ b ≤ 26`;
* most `a = 4` cases (it fails at `b = 11, 21, 23`).

For `a = 2` the passes occur exactly at these normal-play claims, verified numerically:

* `□ⁱT□ʲ⁺¹FT□ʲ⁻¹F□ⁱ ≤ 0`;
* `□ⁱT□ʲ⁺¹TF□ʲF□ⁱ ≤ 0`;
* `□ⁱ⁺¹TT□F□F□ⁱ ≤ 0`.

The right replies inside these are context dependent. No simple priority rule (refill, jump,
slide leftmost or rightmost frog, …) wins them all.

**Obstruction.** After a deviation, the position stays asymmetric. The asymmetry is not
bounded:

* *Hamming distance*: under the best choice of replies, the mirror-mismatched region grows to
  about `2a` cells.
* *Move distance*: most positions in Right's winning strategy are at least four moves (by
  either player) away from every symmetric position. At `a = 5, b = 6` this is 84% of them.

So neither "symmetric plus a bounded defect" nor "symmetric up to a bounded number of tempi"
yields a finite description. Learning a window-local strategy (a lookup table keyed by the
cells near the centre) produced conflicts in every window size tried.

## 5. Death Leap / Lemma C.1 trees

For `b = 2`, a strategy with only three kinds of leaf exists and is formalised in
`Cgt/FamilyB2.lean`:

* one-sided Death Leap positions;
* Lemma C.1 positions `L Tᵃ F□ Tᵏ FT□ Fᵇ` (with `L` an inert prefix);
* a jammed mirror chain.

For `b = 3` the analogous trees grow without bound in `a`. With all three leaf types plus
"separated, with Right having at least as many moves" and "`TTFF`-jammed" leaves, the number of
distinct shapes still grows (over 1,300 at `a = 10`, with more than 200 leaves needing separate
normal-play proofs). The same happens along the row `a = 2` as `b` grows.

## 6. Other strategies that fail

* *Frogs always kept as a solid block* (so toads can never jump them): loses already at
  `(2, 2)`, and in most cases with `a ≥ 3`.
* *Simple priority rules* for normal-play positions: none works for the `a = 2` pass points.

## 7. What a proof would seem to need

A description of the hot symmetric positions (or of a richer invariant) that is

* closed under Left's moves combined with an explicit Right reply, and
* free of hot positions, and
* uniform in both `a` and `b`.

Every finite-window or bounded-defect version of this tried here fails. The values
`Tᵃ□ᵇFᵃ ∈ {0, *}` for `b ≥ 3` (Thanatipanonda's Conjectures 3 and 4) suggest that some
parity-type invariant controls the exact value, but its form is unknown.
