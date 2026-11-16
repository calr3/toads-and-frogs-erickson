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

## 8. Automaton invariants on the folded board (approach 1)

Fold the board: pair cell `i` with cell `n−1−i`. Then mirror symmetry is a letter-by-letter
condition and every move is a local rewrite, so the move relation is a finite transducer. A pair
of regular languages `(N, Z)` satisfying the recursions of §1 would prove the conjecture for all
`(a, b)` at once. Whether a given pair works is decidable by automaton constructions, and
`tools/regular/folded.py` implements that check exactly, for every board size.

The search for such a pair (`tools/regular/`, details and tables in its README) found none:

* *Exact SAT learning*, full conjecture. The smallest invariant has 4 states for boards of at
  most 4 cells and 8 states for at most 6 cells. For at most 8 cells it needs more than 10 (ends
  inwards) or more than 11 (centre outwards), and the solver stalls. Boards of 9–10 cells alone
  need more than 6.
* *The `a = 2` row.* "Mirror, otherwise pass" reduces it to a normal-play set `Z` containing three
  regular families of pass positions: `□ⁱT□ʲ⁺¹TF□ʲF□ⁱ`, `□ⁱT□ʲ⁺¹FT□ʲ⁻¹F□ⁱ` and `□ⁱ⁺¹TT□F□F□ⁱ`.
  All members up to 40 cells are `≤ 0`. But `Z` needs more than 8 states already for boards of
  at most 12 cells.
  * The closure under a fixed local Right strategy needs 592 states when trained up to 16
    cells, and 971 up to 20. Those automata do not generalise.
  * State merging (RPNI) did not converge.
* *Hot symmetric positions* need a growing number of states (up to 7–9 at half-length 10).

None of this proves that no regular invariant exists. It does show that any such invariant is
large, and that letting a learner choose Right's replies does not produce one. A hand-designed
Right strategy that keeps the reachable set regular would be needed. The checker can then
verify it for every board size.

## 9. The row `a = 2` (proved: `Cgt/RowA2.lean`; full account in `docs/ROW_A2.md`)

* **Reduction.** For `b ≥ 2`, Left's only move from `TT□ᵇFF` is to `T□T□ᵇ⁻¹FF`, and that
  position is `≤ 0` (every `m = b − 1 ≥ 1` up to 40 checked first). So Right passes, and the
  row reduces to the normal-play claim `T□T□ᵐFF ≤ 0`. The same happens for `(3, 7)`, `(3, 8)`
  and `(3, 9)`, which suggests the same reduction for the row `a = 3`.
* **Exact outcome rules don't help.** Over *all* two-toad two-frog positions, "`≤ 0`" is
  mostly the race count `A ≤ B`, but near `A − B = 0` it depends on comparisons of gap lengths
  that no small table of capped gaps captures.
* **A strategy with bounded asymmetry does.**
  * Pair each gap with its mirror image.
  * Delayed mirroring (copy Left's previous move) fails at contact.
  * Greedy "closest to symmetric" replies keep the differences of mirrored gaps bounded for
    odd `m` but not for even `m`.
  * With lookahead, Right can always keep both differences within 2. The positions reached
    then fall into 1,543–1,612 shapes (piece order, mirrored differences, capped minima with
    parity), the same for all `m ≥ 29`, and Right's choice depends only on the shape.
* **Formal proof.**
  * Because one move changes each gap by at most one, shapes can be checked through
    finitely many witnesses (`Rel`, `norm`, `wit` in `Cgt/Shape4.lean`).
  * The kernel checks the generated list of shapes in about 30 seconds.
  * `tools/regular/a2_strategy.py` and `a2_abstract.py` are the exploratory versions;
    `scripts/gen_row2.py` generates the Lean data.

## 10. The row `a = 3`: the `a = 2` method does not extend

`tools/regular/a3_explore.cpp` (positions as piece order plus seven gaps).

* **The reduction holds.** `TT□T□ᵐFFF ≤ 0` for every `m` from 5 to 20 (it fails for `m = 1, 2, 4`).
  So for `b ≥ 6`, Right can again pass after Left's only move, and the row reduces to this
  normal-play claim.
* **But no bounded-asymmetry strategy exists.**
  * The bound on the mirrored gap differences `|g₆ − g₀|, |g₅ − g₁|, |g₄ − g₂|` that Right can
    maintain has to grow with the board. A bound of 4 suffices up to about `m = 11`, 6 up to
    about 15, and 8 up to about 21. It fails beyond, for every strategy.
  * Requiring the bound only until the first frog passes all toads (or a toad all frogs) does not
    help: 4 suffices only up to `m = 16`.
  * Under a bound of 8, the shapes reached do not stabilise (161,000 at `m = 21`, still growing
    by about 40,000 per `m`), and the large differences occur in almost every piece order.
* **What this suggests.** With three toads, Right's winning play needs asymmetry linear in the
  board length already in the approach phase. A finite-shape argument would need shapes with
  unbounded linear parameters (for example the difference `g₆ − g₀` kept exactly, with the
  outcome a linear condition on it), not just capped values. Doing this is open.
* **Columns.** For `b = 3` and `b = 4`, Left's first move is not `≤ 0` once `a ≥ 3` (resp.
  `a ≥ 4`). So a column proof would also need the symmetric (`UpperZero`) part, not just normal
  play.

### 10.1 Race-count shapes (`tools/regular/a3_ab.cpp`, `a3_lazy.cpp`)

* **Why the race count.** Left advances its toads as a tight block and Right must *not* mirror
  it: a frog block with space behind it is the hot pattern of §3. So Right keeps its frogs spread
  out, and the mirrored gaps drift apart. But the race count `A − B` stays in a fixed window
  (about `[−10, 3]` for every board size tried).
* **Shapes.** Piece order, exact `A − B`, each gap capped at `K` with its residue modulo a period
  above the cap. They are compatible with moves: each move shifts `A − B` by a fixed amount, so
  "same shape with margin `j`" is preserved as for `a = 2`. One witness per pattern of "which
  large gaps exceed the cap by 2" suffices, found by solving the linear equation for `A − B`.
* **Solving the abstract game.** Exploring all of Right's replies (window `[−6, 3]`, cap 6) passed
  3 million shapes. A lazy depth-first search (losing verdicts sound for the abstract game) gave:

  | Outer cap | Centre cap / period | Window | Result |
  | --- | --- | --- | --- |
  | 4 | 6 / 2 | `[−6, 3]` | every start shape lost |
  | 6 | 6 / 2 | `[−8, 4]` | every start shape lost |
  | 4 | 6 / 3, 4, 6 | `[−8, 4]` | every start shape lost |
  | 6 | 8 / 2, 3, 4, 6 | `[−8, 4]` | ran out of memory or time |

* **Where it breaks.** Traces show the losing chains in the *approach* phase. All concrete
  replies there are `≤ 0`, but positions that the shapes merge (centre gap 6 or 8, say) need
  *different* replies. Which frog Right should advance depends on the distance to contact and on
  how the spare empty squares behind each side are distributed. That is waiting moves and
  zugzwang at contact, which capped gaps (even with a residue) do not record.
* **A possible next step.** Split the proof into an approach phase with an exact rule (outcome
  as a function of each side's arrangement and the distance, if it has a clean form) and a
  contact phase with the centre gap small, where finite shapes may work.

### 10.2 The approach phase has no simple rule (at testable sizes)

`tools/regular/a3_approach.cpp` tabulates the exact normal-play outcome of every pre-contact
position `□^g₀ T □^g₁ T □^g₂ T □^g₃ F □^g₄ F □^g₅ F □^g₆` on boards of up to 32 cells
(398,126 positions).

* **The tails are not summarised by `A − B`.** Fixing the waiting-room gaps `g₁, g₂, g₄, g₅`, the
  distance `g₃` and `A − B` (which then fixes `g₆ − g₀`) still leaves both outcomes in about 3.5%
  of groups, even with both tails at least 3. Example: `....T..T..T.....F...F.F....` is `≤ 0`
  but the same with tails 6 instead of 4 is a Left win.
* **Not a threshold in `A − B`.** For about a quarter of the (waiting rooms, distance) pairs, the
  outcome is not monotone in `A − B`.
* **Not periodic in the distance.** `.T..TT` followed by `F..F...F` at distance 9, 11, 13, 15, 17
  is lost, won, lost, lost, lost for Right.
* **Caps don't fix it.** Capping the waiting rooms, the distance (with residue modulo 2, 4 or 6)
  and the shorter tail, with the tail difference exact, still leaves 300–3,000 ambiguous groups
  for caps up to 12 on the distance and 5 on the tails. The count shrinks only slowly.

These irregular positions have `A − B` near 0, which is exactly where Right's play from
`TT□T□ᵐFFF` stays. Whether the behaviour becomes regular on larger boards is open: the exact
solver needs more memory than available beyond 32 cells. So the two-phase plan of §10.1 has no
clean approach-phase rule to build on, at least not at these sizes.

## 11. Literature (read late; references in `README.md`)

These notes were written before reading Erickson's paper [E96] and the Thanatipanonda–Zeilberger
paper [TZ07]. Several observations above have precedents there:

* **Jammed blocks (§5).** Erickson's *dead pieces* rule says that a contiguous block from two
  toads to two frogs never moves again, so the board splits into independent sums there.
* **Runners (§10).** His *Terminal Toads Theorem* `XT□ⁿ = X□ⁿ + n` and *Finished Frogs Formula*
  replace a piece with no opposing piece ahead of it by an integer. This is exactly the "replace
  runners by their move counts" reduction considered for `a = 3`. It is the right tool once
  pieces have fully crossed, but the obstruction found in §10.1–10.2 arises before that, in the
  approach phase.
* **Shapes (§9).** [TZ07]'s symbolic finite-state method (finitely many symbolic states, values
  guessed and proved by induction) is the same idea. Their class B (fixed pieces, variable gaps)
  stalled at `TTF`. The `a = 2` proof here succeeds for `TTFF` by proving only `≤ 0` via a
  strategy, with mirrored gap differences in the shapes.
* **Exact values for `a = 2`.** [T11] computes `T²□ᵇF²` for `b ≤ 103`. The values fit "`∗` when
  `b ≤ 4` or `b ≡ 1 (mod 6)`, otherwise `0`". Proving this would mean showing `G + ∗ = 0` or
  `G = 0`. Both are normal-play statements about a sum with an extra `T□F` component
  (`T□F = ∗`, [E96] Lemma 5.1), so the shape machinery might extend to them. Untried.
