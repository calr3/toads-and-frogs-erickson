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
* `a = 5` for `b ≤ 22`;
* `a = 6` for `b ≤ 15`;
* `a = 7` for `b ≤ 11`;
* `a = 8` for `b ≤ 9`;
* `a = 9` for `b ≤ 7`;
* `a = 10` for `b ≤ 5`;
* `a ≤ 12` for `b ≤ 4`;
* `a ≤ 14` for `b ≤ 3`.

That is every board of at most 25 squares. The limit is memory. `tools/stops.cpp` (a hash table)
reaches around 5·10⁸ states; `tools/values.cpp` with its table indexed by the rank of the
arrangement (4 bits per arrangement for the value, a byte for `STOPS=1`) reaches about 2.6·10¹⁰
arrangements (`(8, 9)`) in 13 GB. The open cells of size 26, `(7, 12)`, `(8, 10)`, `(9, 8)` and
`(10, 6)`, have 3.3·10¹⁰ to 7.6·10¹⁰.

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
parity-type invariant controls the exact value, but its form is unknown. (Later computation found
that Conjecture 4, "`0` or `∗` for `b ≥ a > 0`", fails at `(6, 12)` and `(7, 10)`: both are
infinitesimal but neither `0` nor `∗`. See the values section of `README.md`.)

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
* **The column `b = 3`.** Thanatipanonda's thesis (2008, Theorem 5.6.1, found only in a later
  literature search) proves `Tᵃ□³Fᵇ = {a − b | a − b}` for all `a, b ≥ 4` by hand, so §13's
  column and its values were known; the proof here is independent. See `docs/LITERATURE.md`.
* **Exact values for `a = 2`.** [T11] computes `T²□ᵇF²` for `b ≤ 103`. The values fit "`∗` when
  `1 ≤ b ≤ 4` or `b ≡ 1 (mod 6)`, otherwise `0`". See §12: this turned out to need no sum with
  `T□F`, only one more `≤ 0` claim per value.

## 12. Exact values of the row `a = 2` (`Cgt/RowA2Zero.lean`, `Cgt/RowA2Values.lean`, `Cgt/RowA2Odd.lean`)

* **Reduction.** `G = TT□ᵇFF` is symmetric, and for `b ≥ 2` each side has one move. Left's
  leads to `T□T□ᵇ⁻¹FF ≤ 0` (§9). So `G = 0` ⟸ `T□T□ᵇ⁻²F□F ≤ 0` (Right's only answer), and
  `G = ∗` ⟸ `TT□ᵇ⁻¹F□F ≤ 0` (then `G ≤ ∗`, and `∗ ≤ G` by symmetry).
* **Even `b`: proved for all `b`.** In `T□T□ᵏF□F` with `k` even, Right can keep the mirrored
  differences within 4. The greedy generator of §9 does not close (it reaches shapes where every
  reply leads outside the bound), so `scripts/search_row2.py` solves the game on shapes with
  backtracking. With cap 4, parity and bound 4 it closes with 1,038 shapes. Longer periods
  (residues mod 6) and larger caps were not needed.
* **Odd `b`: the asymmetry is unbounded.** The smallest bound with which Right still wins
  (`tools/regular/a2_exact_bounds.py`) is:
  * 4, 6, 8, 10, 12, 14 for `T□T□ᵏF□F`, `k` = 3, 7, 9, 13, 15, 19 (value `0` at `b = k + 2`);
  * 5, 9, 13, 17, 21 for `TT□ᵏF□F`, `k` = 6, 12, 18, 24, 30 (value `∗` at `b = k + 1`).

  So on odd boards Right must let the mirrored gaps drift apart by about `2k/3`. These are exact
  computations on concrete boards. Shapes store both differences exactly, so a finite set of
  shapes bounds them, and no such set can serve every odd `b`.
* **Small cases.** Kernel `decide` on `leZeroB` grows roughly like `k³` here (24 s for 23 cells),
  so every `b ≤ 30` is checked individually. `TT□FF` (`b = 1`) needs one more level, because
  Left's option `T□TFF` is not `≤ 0`.
* **Odd `b`: proved for all `b`** with a linear invariant instead of shapes; see §15.

## 13. The column `b = 3`: runs of pieces instead of gaps (`tools/column/`)

The `a = 2` row works because a few pieces are separated by long gaps. In a column (`b` fixed,
`a` growing) the roles swap: a few empty squares are separated by long runs of pieces.

* **Right needs only boundedly many runs.** The smallest bound on the number of runs (maximal
  blocks of equal cells) with which Right still wins is:
  * `b = 3`: 10, for every `a` from 4 to 12;
  * `b = 4`: 12, for every `a` from 4 to 8;
  * `b = 5`: 13, for every `a` from 4 to 7.

  This is the column analogue of the bounded asymmetry of the `a = 2` row, and it holds at every
  size tested. Greedy strategies (fewest runs, most dead pieces) do not show it: their run counts
  grow like `2a`, through long interleavings `TFTF…`.
* **The Left-stop phase cannot be skipped.** Unlike the `a = 2` row, Left's first move from
  `Tᵃ□³Fᵃ` is not `≤ 0` for `a ≥ 3`. So Right must keep replying while he holds his pass, and the
  abstraction must handle the Left stop, not only `≤ 0`.
* **Plain capped runs lose a race.** Capping long runs (cap 4 with parity) loses the start
  shape. The first lost line ends in `TTTTTT..FTTTTFFFFFF.FFF`. There Left's reservoir `T⁶` in
  front of two empty squares is worth 12 moves, while the dead block `TTTTFFFFFF` holds 4 toads and
  6 frogs. The same shape also contains positions with a 4-toad reservoir, and Right may win those.
  Because dead blocks absorb pieces unequally, the global balance (`a` toads, `a` frogs) does not
  pin down the race between the live reservoirs.
* **Clusters of exact differences work.** The shape keeps the exact difference between any two
  long runs, and between a long run and the cap, when it is at most `M = 4`, and only sign and
  parity when it is larger. The cap acts as an anchor. Without it, a short run that grows long
  would land next to reservoirs that are far above it in one position and close to it in another.
  * One move changes one long run by 1 and never merges two long runs, so the usual margin
    argument applies. Each far gap is witnessed by its own value or that value plus 2.
  * The abstract search (`col_shapes 3 10 4 4`, before dead regions) closes with 646,574 shapes,
    every witness checked.
  * An independent re-check of the closure found no failures.
  * A first attempt that used single normal forms as shapes also "closed", with 4,309. It was
    unsound: the real-tree check below failed at `a = 13`, because "same shape with margin 0"
    did not imply "same normal form".
* **Every `a ≤ 40` checked directly.** `col_realcheck` builds the real game tree of `Tᵃ□³Fᵃ`, with
  Right's replies taken from the set, and checks every real position it reaches. It finds no
  failure for any `a` from 4 to 40. Each such run is a complete proof for that `a`, independent of
  the margin argument. The exact solver reached only `a ≈ 14`.
* **Shrinking the certificate.**
  * Collapsing dead regions brings 646,574 shapes down to 11,034. A dead region is everything
    from the first `TT` to the last `FF` in a block of pieces with no empty square. Erickson's
    dead-pieces rule says these pieces never move, so their lengths never matter. The extra
    ingredient checks out: the real game trees for `a = 4…40` still pass.
  * Smaller parameters help: cap `K = 2` and cluster gap `M = 2`.
  * A greedy minimisation helps too. It computes the exact won region of the explored shapes,
    then rebuilds Right's choices preferring shapes already in use.
  * Result: **2,861 shapes** (`tools/column/b3_shapes.txt`), with 5,451 witnesses averaging 25
    cells and 9,871 Left moves and passes to answer. That is about the size of the `a = 2`
    certificate.
  * `tools/column/verify_shapes.py` re-implements everything independently and finds it closed.
    It also confirms that every start `Tᵃ□³Fᵃ`, `a ≥ 2`, has a shape in the set.
* **Formalised.** `Tᵃ□³Fᵃ` is infinitesimal for every `a` (`infinitesimal_start_b_three`;
  [docs/COLUMN_B3.md](COLUMN_B3.md)). Three changes to the search made the margin argument provable
  with the same certificate size (3,031 shapes):
  * margin 2 per move, not per round, because one Left move can change two toad runs (`TᵃETᵇ`
    becomes `Tᵃ⁻¹ETᵇ⁺¹`);
  * dead runs kept one by one, so that real positions and witnesses have the same runs;
  * runs of empty squares kept exact.
* **Exact values.** With "`≤ ∗`" in place of "Left stop `≤ 0`", the same search closes at once
  (1,263 shapes) and proves `Tᵃ□³Fᵃ = ∗` for every `a ≥ 4` (`start_three_value`,
  [docs/COLUMN_B3.md](COLUMN_B3.md) §9).
* **Other columns.** The same framework applies to any fixed `b`; only the data changes. For
  `b = 4` the shape search closes once far gaps lose their parity, with 233,087 shapes (§14).

## 14. The column `b = 4`: a closed set once parity is dropped (`tools/column/`)

**Result (proved in Lean, finite check by `native_decide`).** Right has a strategy for `Tᵃ□⁴Fᵃ`,
every `a ≥ 2`, over **233,087 run shapes** (`tools/column/b4_shapes.txt.gz`), and
`infinitesimal_start_b_four` (`Cgt/Col/Column4.lean`) proves the column. It was known numerically
only up to `a ≈ 12`. Besides the Lean check, the closure is checked by two independent programs,
and the strategy directly on the real game trees for every `a ≤ 24`.

### 14.1 The `b = 3` settings fail

* **Right's run bound.** The smallest number of runs with which Right still wins (`col_bound`,
  all runs counted) is 12 for every `a` from 4 to 9, and 13 for `a = 10, 11, 12`. So the bound
  steps up once and then holds, as far as we can test.
* **With 12 runs the start is lost** (after 3,814 shapes; settings of `b = 3`: cap `K = 2`,
  cluster gap `M = 2`, parity kept, margin 4, dead runs kept). After `T⁷□⁴F⁷` and a toad slide,
  only one of Right's replies stays within 12 runs at `a = 7`, and it fails at `a = 10`.
* **With 13 runs and parity the search does not close.** It explores millions of shapes. The
  search stack runs 1,000 to 10,000 shapes deep through shapes with four or five long runs that
  differ only in the order, exact spacing and parity of their lengths, for example
  `Tᵇ □ [dead] □ Fᶜ T □ Fᵃ T F □ Fᵈ`. Capping the long runs at 3 loses the start, capping at 4
  still explodes; `M = 0` loses, `M = 1`, `M = 2` and `K = 3` explode.
* **Real play is much richer than for `b = 3`.** Right's concrete strategy (13 runs, replies
  reusing shapes) visits 126,203 shapes over `a = 4…12`, about 20,000 new ones per step of `a`;
  for `b = 3` the same count is 4,738, about 500 per step. Most of the variety is in the
  arrangement of runs: those shapes have 37,090 distinct skeletons, about 3.4 shapes each.
  Collapsing dead regions saves only 15%.

### 14.2 What does not help

* **Component-local strategies.** A dead region is a wall, so a position is a sum of independent
  components. If Right always answered inside the component Left moved in, only component shapes
  would be needed. But such strategies lose: for `b = 3` from `a = 4` and for `b = 4` from
  `a = 5` (`col_local.cpp`). Right has to coordinate across components, typically a race between
  a component holding Left's free moves and one holding Right's.
* **Values of components.** Over every position reachable from `T⁶□⁴F⁶`, the components with
  both kinds of pieces take 54,082 distinct canonical values: numbers, `n∗`, `{n|n}` and hot games
  of temperature up to 1 (`tools/cgt_values.py`). A key built from values would need parametric
  families of values.

### 14.3 Dropping parity closes it

* **The change.** A gap between consecutive sorted long runs is kept exactly up to `M`; above `M`
  only "far" is kept, without parity (`NOPARITY=1`). The margin argument never used parity: two
  positions are related with margin `j` if every pairwise difference of long runs (and the anchor)
  is equal in both, or at least `M + 1 + j` in both with the same sign. A move changes each
  difference by at most 2, a new long run starts at the anchor, and a run that dies drops out, as
  before. A far gap now has `MARGIN + 1 = 5` witnesses (`c`, `c + 1`, …, `c + 4`) instead of 3.
* **Calibration on `b = 3`.** Without parity the `b = 3` search still closes, at `M = 1, 2, 3`
  (minimised: 2,777, 4,042 and 3,403 shapes).
* **`b = 4`.** With `K = 2`, `M = 1`, 13 runs and no parity, the search closes: 557,015 shapes,
  minimised to 212,020 with 10,244,048 witnesses. Allowing at most 3 far gaps after Right's
  replies (`FB = 3`; with 2 the start is lost) and preferring shapes with few witnesses in the
  minimisation (`MINW=1`) gives the certificate: **233,087 shapes (32,853 in the Left-stop phase),
  2,789,119 witnesses, 6,277,071 Left moves and passes**.

      NOPARITY=1 MINW=1 FAILFIRST=1 MARGIN=4 DEADRUNS=1 MINIMIZE=1 DUMP=out col_shapes 4 13 2 1 28 3

  The search takes about 5 minutes and less than 6 GB; it is deterministic and reproduces the file.
* **Checks.**
  * `verify_shapes.py` (independent of the search) finds every witness answered and every start
    `Tᵃ□⁴Fᵃ`, `a = 2…60`, in the set. For `a ≥ 4` the start has the same shape, so this covers
    every `a ≥ 2`. It takes 2 minutes. The 212,020-shape set also passes (10.2 million witnesses).
  * `col_realcheck` plays Right's strategy from the set on the real game tree of `Tᵃ□⁴Fᵃ` and
    finds no failure for any `a` from 2 to 24 (713,499 positions at `a = 24`). Each of these is a
    complete proof for that `a`, independent of the margin argument; the exact solver reached only
    `a = 12`.

### 14.4 In Lean

* **The framework takes a gap rule.** `GapRule` (`Cgt/Col/Key.lean`) says how a gap is recorded:
  exactly up to `m`, above that "far", with its parity unless `par = 0`. `close`, `Rel`, the
  witnesses (`gapChoices`, `comp`), `wit_complete`, the margin lemmas and `sound` are proved for
  every rule. The column `b = 3` uses `ruleP = ⟨2, 1⟩` and still has the same keys and the same
  kernel check; the column `b = 4` uses `ruleF = ⟨1, 0⟩`. In the margin lemma only one constant
  changed: a moving toad run with a far length is now known to have length `≥ 5` instead of `≥ 6`.
* **The finite check uses `native_decide`.** The kernel would need about 150 CPU hours (0.19 s per
  witness in the `b = 3` check), and the keys would be about 23 MB of Lean terms. Instead,
  `Cgt/Col/B4Data.lean` holds one witness per key as run-length text (5.7 MB), the key trees are
  computed from it (`Cgt/Col/Text.lean`), and the check runs in 8 files evaluated by
  `native_decide`. Each use adds an axiom asserting the result of the compiled evaluation (13 in
  all, listed by `#print axioms`): the theorem trusts Lean's compiler and runtime as well as the
  kernel. It is therefore built separately (`lake build CgtNative`) and is
  not part of `conjecture5_provedRegion`.
* **Generated by** `scripts/gen_b4.py` from `tools/column/b4_shapes.txt.gz`.

### 14.5 Exact values

The `≤ ∗` search (`START=S`, as for `b = 3`) needs the gap threshold 2: with threshold 1 the start
shape of `a ≥ 4` contains `T⁴□⁴F⁴ = 0`, which is not `≤ ∗`. With threshold 2 and no parity it
closes with 361,981 shapes (692 `≤ ∗`), 3,457,633 witnesses
(`tools/column/b4_star_shapes.txt.gz`). `verify_shapes.py` finds no failure and every start
`a = 5…60` present; the strategy passes the real game trees for `a = 5…22`. In Lean,
`start_four_value` (`Cgt/Col/Value4.lean`, `native_decide`, 9 check files of 2 to 24 minutes):
`Tᵃ□⁴Fᵃ = ∗` for every `a ≥ 5`.

## 15. Odd `b` of the row `a = 2`: a linear invariant (`tools/linear/`, `tools/presburger/`, `Cgt/RowA2Odd.lean`)

Goal: `T□T□ᵏF□F ≤ 0` for `k ≡ 1, 3 (mod 6)` and `TT□ᵏF□F ≤ 0` for `k ≡ 0 (mod 6)` (§12).

* **First attempt: shapes with a race counter (`tools/linear/`).** Shapes kept the piece order,
  gaps capped at `C` with their residue mod 6, the exact race count `A − B`, and linear forms of
  the gaps clamped to `±M`; an abstract game on such shapes is sound for every board size. With
  `C = 14` and six forms found from conflicts in exact data, no two positions with at most 68 empty
  squares share a shape and differ in outcome, and the abstract game keeps every true start. But
  it ran out of memory after 25 million shapes. The part under Right's chosen replies had about 11
  million shapes, far too many to check in Lean.
* **The approach phase is simple once Right's move is fixed.** In `TTFF`, if Right always moves the
  front frog, then `A − B` stays at its start value (0 for `T□T□ᵏF□F`, 1 after
  `TT□ᵏF□F → T□T□ᵏ⁻¹F□F → T□T□ᵏ⁻²F□□F`). The rear frog never moves, so the positions form the
  two-parameter family `(g₀, g₁, N − 3g₀ − 2g₁ − c, 2g₀ + g₁ + c, 0)`. Exact play: every position
  of the family is a loss for Left moving first when `N ≡ 3, 5 (mod 6)` (`c = 0`) or
  `N ≡ 1 (mod 6)` (`c = 1`), up to `N = 50`. This explains the period 6. By contrast, the general
  `TTFF` loss set needs comparisons such as `g₂ ≥ g₀ − 2g₃ + 3g₄ + 4`, which is where the six
  forms came from.
* **After the first jump the positions are cold.** Canonical values (`tools/presburger/cgt.py`) are
  numbers or numbers plus `∗` except at a few contact points. Accordingly, for each later order the
  outcome is a threshold in `A − B` once a few features are fixed. A decision-tree learner over
  linear forms with coefficients in `{−2, …, 2}`, residues mod 2 and 3, and `A − B`
  (`tools/presburger/learn.cpp`) finds exact descriptions: 2, 6, 16, 32 and 49 leaves for `FFTT`,
  `FTFT`, `FTTF`, `TFFT` and `TFTF`, and 19 for the contact region of `TTFF`. They were validated
  on 40 to 46 empty squares. For example, `FTFT` (a runner at each end) is a loss for Left moving
  first (for `|A − B| ≤ 6`) exactly when `A − B < 0`, or `A − B ∈ {0, 1}` and either `g₁ ≤ g₃ − 2` or
  (`g₁ − g₃ ∈ {−1, 0}` and `g₂` is even).
* **Closure, for every board size.** Z3 checks that the union of these sets (with
  `−p ≤ A − B ≤ p + 1`, where `p` counts toad–frog pairs already passed) is closed: every Left move
  from it has a Right reply back into it (`tools/presburger/verify.py`, one second). Exact play
  agrees on all 574,840 such positions with at most 44 empty squares (`goodcheck.cpp`).
* **Lean.** The invariant becomes 67 linear cases (`Cgt/RowA2Odd/Inv.lean`). Z3 splits each
  (order, Left move, case) into regions with one Right reply and one target case, 379 in all, and
  each region is a short `omega` proof. `omega` does not do the dark shadow of the Omega test, so
  about twenty regions failed at first with "possible counterexample". Splitting on the values of a
  bounded gap, or on the parity of one gap, fixed all of them (`fix_leaves.py`,
  `try_leaves.py`). The new files build in about a minute, with no `native_decide`.

## 16. The row `a = 3` with the front-frog policy (`tools/presburger/a3/`)

The method of §15 applied to `TT□T□ᵐFFF ≤ 0` (`m ≥ 5`), which gives the row `a = 3` for `b ≥ 6`.

* **The approach phase passes.** Right always moves the front frog (piece 4) while the centre gap is
  at least 2. The race count, with coefficients `(−3, −2, −1, 0, 1, 2, 3)` on the seven gaps,
  stays at its start value `−1`, and the two rear frogs never move. So the approach positions are
  the three-parameter family `□^g₀ T □^g₁ T □^g₂ T □^g₃ F □^(3g₀+2g₁+g₂−1) F F`.
  * Exact play: every position of the family is a loss for Left moving first for every number of
    empty squares from 6 to 34, with no congruence condition. At 5, all eight are wins, which
    matches the failure of the claim at `m = 4`.
  * The front-frog reply wins from every family position with centre gap at least 2, so the
    policy never has to deviate before contact. Checked for every `m ≤ 21` (`ff`) and every family
    position up to 34 empty squares (`fam`).
* **Contrast with §10.** §10.1–10.2 tried to describe *every* approach position and found no
  simple rule. Fixing Right's approach move avoids that, as it did for `a = 2`.
* **After contact: much harder than for `a = 2`.** All 19 later orders occur, the race count ranges
  over −10 to 6, and the positions reached fill all six dimensions in every order (`hull`).
  * Trees learned on boards of at most 18 empty squares have 100 to 1,200 leaves and fail on
    24 squares. For `a = 2`, trees that generalised needed 30 to 38 squares, which is beyond the
    present learner with seven gaps.
  * A single runner's gap matters only through the race count, so such orders reduce to a core of
    five or four pieces (`core`). With two or more runners this fails as stated.
  * The hard orders are those without runners (`TTFTFF`, `TFTTFF`, `TTFFTF`, `TFTFTF`, `TFFTTF`),
    whose cores have all six pieces.

## 17. The row `a = 3` after contact: exact loss sets are too large (`tools/presburger/a3/`)

An attempt to finish §16 by the method of §15. It did not succeed; the row `a = 3` is still open
beyond the cases checked one by one. All numbers are exact play with three toads and three frogs.

* **A windowed exact invariant exists on the data.** Take the approach family of §16, the
  `TTTFFF` losses with centre gap at most 1 and race count −1 or 0, and for every other order the
  losses with race count in `[−p − 1, p + 1]` (`p` = toad–frog pairs already passed). On every
  board with at most 22 empty squares this set is closed (`close6`). The window `[−p, p + 1]` of
  the row `a = 2` is not enough: the first jump from `TTTFFF` needs race count `−2` in `TTFTFF`.
* **But the loss sets have no small description at these sizes.** The tree learner of §15
  (forms with coefficients in `{−1, 0, 1}`, residues mod 2 and 3, the race count), learned on at
  most 18 empty squares and validated on at most 24 (`learn6w`):

  | Orders | Leaves | Errors on validation |
  | --- | --- | --- |
  | `FFFTTT`, `FFTFTT` | 2, 6 | none |
  | `FFTTFT`, `FTFFTT`, `FTFTFT`, `FTTFFT` | 127 to 253 | 0.5% to 0.6% |
  | `TTTFFF` (contact region) | 211 | 9% |
  | the other 13 orders | 476 to 1,345 | 1.5% to 7% |

  For the row `a = 2` the largest tree had 49 leaves and no errors. Forms with coefficients up to
  2 or 3 do not help (`TTTFFF`: 219 and 223 leaves). This is the irregularity of §10.2 again, now
  after contact as well as before it.
* **The reachable set is no simpler.** With Right taking the first winning reply in a fixed order
  of his frogs (`reach6`), the positions reached have full affine dimension in 18 of the 20 orders
  and grow like the fourth or fifth power of the board size. Learning that set exactly gives 27
  leaves for `TTTFFF` but 353 for `TTFTFF` and 205 to 690 for the last two orders, again with
  errors on larger boards: the choice "first winning reply" inherits the irregular loss sets.
* **No fixed rule wins.** Five rules without look-ahead (leftmost movable frog; leftmost frog
  that is not yet a runner; variants preferring jumps or the rightmost frog) all lose
  `TT□T□ᵐFFF` for every `m` from 5 to 20 (`rule6`).
* **A search for a small closed subset of the losses** (`cegar6`). One tree per (order, race
  count), learned from the positions that must be in the set against the Left wins of the slice,
  with all other losses left free; whenever a position of the set has a Left move with no reply
  in the set, the first losing reply is added and the trees are learned again. This always closes
  on the data, in 20 to 35 rounds, over 94 or 95 slices, but the set does not stay small:

  | Boards (empty squares) | In-leaves | Positions in the set |
  | --- | --- | --- |
  | at most 14 | 929 | 203,840 |
  | at most 18 | 1,763 | 738,687 |
  | at most 22 | about 2,900 (stopped at round 20) | 2.1 million |
  | 20 to 24 only | 2,081 | 2,423,009 |

  That is about a sixth of the exact trees, but it grows with the board, and it is spread evenly:
  at 18 squares no slice has more than 96 leaves and dozens have 60 or more. Restricting each
  leaf to the box hull of its positions, or adding forms with coefficients 2 and 3, changes the
  totals by less than 20%.
* **Reading.** For `a = 2` the positions after the first jump were cold and the exact loss sets
  were small, so "approach family + exact losses" was a short certificate. For `a = 3` the
  position after the first jump is a second approach (two toads against a frog on one side, a
  toad against two frogs on the other), and neither the exact losses nor a greedily grown subset
  are small on boards of up to 24 empty squares. A proof along these lines needs a strategy for
  Right chosen for its regularity after contact too, as the front frog was before it. Right has
  room for one: he starts a tempo ahead (race count −1, and the whole family is lost with no
  congruence condition), and typically has several winning replies.
* **Untried.**
  * Cells that are lattice cones (a base position plus multiples of the net effect of a Left move
    and its fixed reply), which is what the approach family is; grow them by accelerating such
    loops instead of by trees.
  * Learning on boards of 35 to 45 empty squares (the table fits in memory up to about 48), in
    case the sets become regular only when several gaps are large.

## 18. The row `a = 3`: further searches for an invariant, all too large (`tools/presburger/a3/`)

A second, longer attempt at `TT□T□ᵐFFF ≤ 0` for every `m ≥ 5`. It did not produce a proof, and the
measurements below say why the approach of §15 (a closed set described by linear cases, checked by
`omega`) is out of reach for six pieces as far as we can compute. The row `a = 3` stays open.

**What the position is.**

* `TT□T□ᵐFFF` is a number: `0, −⅛, −⅛, −⅛, −¼, −¼, −¼, −¼, 0, −¼, −½, −¼, −¼, −½` for
  `m = 5, …, 18` (`tools/cgt_values.py`). So Left's first move costs him a fraction of a move, but
  not uniformly: at `m = 13` (where `T³□¹⁴F³ = ∗`) the value is exactly `0` again, and Right cannot
  do better there by delaying his pass. There is no spare tempo to build a robust strategy on.
* Right has to jump. With at most four jumps of his own he loses most `m` up to 22 (`rj6`): when
  Left refuses to jump, Right wins by blocking toads, not by the race count.
* In "Left stop `≤ 0`" Right must use his pass before the first crossing (`passlate`).
* On a board of 45 to 50 empty squares the loss sets look regular in two-dimensional sections:
  polygons with edges of slope 1, 2 and ½, plus thin stripes of period 6.

**Learning the exact loss sets on large boards fails.** The number of empty squares never changes,
so each board size can be solved on its own (`gen7`). For the contact region of `TTTFFF`, trees
learned on 28–33 and 40–46 empty squares and tested on 34–39 (`learnf`) keep 7% to 8% errors at
every size up to 2,240 leaves (zero training errors); `TTFTFF`: 4%. Forms in the positions of the
pieces, hill-climbed oblique splits, and hand-made features (waiting moves of the rear toads and
frogs) do not change this. The errors are spread over generic positions, not small gaps.

**Searching for a smaller closed set.** `cegar6` grows a set from the starts (one tree per piece
order and race count; when a position of the set has a Left move with no reply in the set, a
losing reply is added). It always closes on the data. Sizes (in-leaves, i.e. linear cases):

| Boards (empty squares) | Plain forms | + position forms | + oblique splits |
| --- | --- | --- | --- |
| at most 14 | 929 | 797 | 767 |
| at most 18 | 1,763 | 1,547 | |
| 26 to 28 | 1,646 | 1,352 | 1,272 |
| 32 to 34 | more than 2,485 (stopped) | more than 1,796 (stopped) | |
| 22 to 30 | | | 3,589 |

* **It does not level off.** Three sizes around 27 need about 1,300 cases, three around 33 clearly
  more, and the nine sizes 22–30 need 3,589.
* **It does not extrapolate.** The 26–28 set, checked by exact play on 24, 25 and 29–31 empty
  squares (`check6`), contains 2.4% to 3.9% Left wins. The 22–30 set still contains 1.0% to 2.5% on
  19–21 and 31–33, and the starts of 31 and 33 are not even in it.
* **Where the cases are.** Slices in which Left did the jumping are trivial (one to four cases).
  The cases sit where Right had to jump, and where frogs still have to pass packed toads
  (`FTTTFF`: 319 of 1,352).
* **Variants, all worse or no better.** Preferring replies deep inside the losses, or slides to
  jumps: within 5%. Excluding generalised positions that cannot be answered instead of growing:
  5,361 cases at 14 squares. Separating the reached positions from everything that cannot be
  defended (`itp6`): 2,027 at 14. A policy instead of a set, one tree per order choosing the frog
  to move (`pol6`): 840 leaves up to 16 squares, 1,470 on 22–24.

**The Lean side at this size.** `Cgt/Six.lean` and `Cgt/RowA3/Moves.lean` formalise six-piece
positions, their moves and the closure induction (`le_zero_of_closed6`); they build. `z3check6.py`
checks closure for unbounded gaps (it agrees with the brute-force check on the 929-case set, bounded
to 14 squares). `gen_lean6.py` and `emit_lean6.py` turn a set into closure lemmas. On that 929-case
set the plan has about 17,700 regions; `omega` needed about 3 seconds per region and failed on
several of the first 169 ("possible counterexample"), which for `a = 2` needed case splits by hand.

**Conclusion.** Every description we could learn grows with the board and breaks just outside the
sizes it was learned on, and already the smallest one is two orders of magnitude beyond what the
`omega` route handled for `a = 2`. A proof of the row `a = 3` needs a different idea: an explicit
strategy with a structural reason, or an invariant language in which the thin period-6 stripes
and the blocking of toads are primitive.

## 19. Positions with one frog: Conjecture T1 (`Cgt/OneFrog/`, `tools/onefrog/`)

**Result (proved in Lean, kernel only).** `conjectureT1`: the values of `□ˡTᵃ□ᵇF□ʳ` for `a ≥ 1`,
`l ≤ r`, from a theorem on one-frog positions with the toads anywhere. Full account in
`docs/ONE_FROG.md`; this section records how it went.

* **Why T1 was tried first.** Of the conjectures still open (T1, T3, T5), T5 starts with the row
  `a = 3` of §16–18, and T3 needs an argument uniform in `b`. For T1, of the one-frog positions
  with at most 4 toads on at most 13 squares, 95% are numbers and 4.5% numbers plus `∗`.
* **Bounds instead of values.** The frog has at most one move, so `G ≤ n` and `G ≥ n` are one-step
  recursions (`tools/onefrog/bounds.py`). They agree with canonical forms on all 20,480 positions
  of at most 11 squares and are cheap up to 15.
* **The potential.** `phi` (every toad left of the frog jumps, the frog walks home) changes by
  −1, +1, +3 under a Left move, a frog slide, a frog jump. On all positions of at most 14 squares
  with `phi ≥ 0`: the value is never below `phi`; and the excess of the integer upper bound over
  `phi` is 0 exactly when `room ≥ 2`, 0 or 1 when `room = 1`, 1 or 2 when `room = 0`, and grows as
  `room` falls.
* **Exact values for `room = 1, 0`** depend only on the parity of the gap (2,036 + 1,013 + 652 +
  316 positions with `room = 1`, and as many with `room = 0`, on at most 12 squares, no exception
  with `phi ≥ 0`). For `room = −1` with an odd gap they do not: `3/2`, `7/4`, `{2|2}` and hotter
  games occur.
* **The induction was checked before it was formalised.** `check_rules.py` verifies each claim from
  the claims one or two moves later. The first version failed at 69 claims on boards of at most 12
  squares, all with `phi = −1`: `T□³F`-like single toads and packed blocks such as `□□TTF□`. Two
  extra families fixed it (1,094,386 claims on at most 15 squares, no failure).
* **In Lean.** A position is two lists around the frog (`pos L B`, the left one read from the
  frog), so the frog's moves and the nearest toad's moves act on list heads. The lower bounds
  compiled as first written. The degenerate families are stated with `phi = −2` and `phi = −1`
  instead of shapes, and three inequalities (`phi ≥ room − 1` and variants) rule out the cases
  that cannot occur.
* **The statement.** For `TᵃF` the conjecture's formula is negative; the truth is `0`.

## 20. The column `b = 5`: the `b = 4` shapes do not close (`tools/column/`)

A first attempt at `Tᵃ□⁵Fᵃ` with the method of §13–14 (the next open column of Erickson's
conjecture and of Conjecture T3). No certificate was found. All runs used `NOPARITY=1 FAILFIRST=1
MARGIN=4 DEADRUNS=1`, short-run cap `K = 2` unless noted, and `col_shapes 5 RB K M 28 FB`.

* **Real play looks only twice as rich as `b = 4`.** Right's concrete strategy (`REAL=4-11`, 13
  runs) visits 183,235 shapes over `a = 4…11`, 16,000 to 40,000 new ones per step of `a`. For
  `b = 4` the count was 126,203 over `a = 4…12` (§14.1).
* **Right's run bound is 13** for every `a` from 4 to 11 (`col_bound 5 4 11 1`), with no step up.
* **The abstract search does not follow.**

  | Runs `RB` | Gap threshold `M` | Far gaps `FB` | Outcome |
  | --- | --- | --- | --- |
  | 13 | 1 | 3 | start lost after 311,368 shapes (39 s) |
  | 13 | 1 | 4 | start lost after 395,032 |
  | 13 | 1 | 99 | start lost after 452,010 |
  | 13 | 2 | 4 | start lost after 1,337,504 |
  | 13 | 1, `K = 3` | 4 | start lost after 660,159 |
  | 14 | 1 | 3 | start lost after 3,669,179 (11 min) |
  | 14 | 1 | 4 | start lost after 7,277,289 (44 min) |
  | 14 | 2 | 4 | no verdict: 29.4 million shapes explored in 100 minutes, under 20 GB |
  | 15 | 1 | 4 | no verdict: out of an 8 GB limit after 2 million shapes |

* **Reading.** With threshold 1 and no parity, the setting that proved `b = 4`, the start is lost
  with 13 and with 14 runs, whatever the number of far gaps. Since real play needs only 13 runs,
  the shapes are too coarse, not the run bound too low. The losing line starts with Left's first
  slide and Right's mirror reply, each with a single option that does not lose concretely, and
  runs through positions whose long runs have 4 or 5 pieces: with `K = 2`, `M = 1` a run is "far"
  from the anchor from length 4 on, so small and large `a` share shapes. Threshold 2 at 14 runs
  neither closes nor loses within 29 million shapes, over 50 times the 557,015 explored for
  `b = 4`; a certificate of that size would be far beyond the `native_decide` check of §14.4.
* **On real boards the same shapes survive.** `col_conflict` plays the abstraction on real
  positions only: a shape is bad if one of its real positions is lost when Right may only reply
  into shapes that are not bad, iterated to a fixpoint. For `b = 5` and `a = 4…8` every start
  survives, with 13 runs (3.6 million positions, 2.6 million shapes, 1.04 million bad) and with 14
  (10 million positions), for thresholds 1 and 2. (For `b = 4`, `a = 4…8`: 1.3 million positions,
  0.94 million shapes, 0.41 million bad.) So the abstract loss comes from positions larger than
  these boards.
* **Root cause: a race with slope 2.** `WHYROOT` searches the lost shapes for challenges with no
  candidate reply at all. For 13 runs and threshold 1 there are 8, all of one kind: the reply wins,
  but its shape has a witness that loses. In each the difference between a toad reservoir and a
  frog run is "far" in both positions, for example `.T⁵.TTFF..FT.FFF` (Right wins) against
  `.T⁸.TTFF..FT.FFF` (Left wins); the `TTFF` block is dead, so its lengths are free and such
  positions are balanced on real boards. Exact play on these families (Right wins moving second):

  | Family | Right wins if and only if |
  | --- | --- |
  | `.Tˣ.TTFF..FT.Fʸ` | `x ≤ 2y + 1` |
  | `.Tˣ.TTFF.FF.T.Fʸ` | `x ≤ 2y + 1` |
  | `.Tˣ.TTFF.F.FFTFʸ.` | `x ≤ y + 4` |

  (checked for `2 ≤ x ≤ 12`, `2 ≤ y ≤ 7`). The third needs differences exact up to about 5. The
  first two cannot be recorded by any bounded set of differences: the threshold is in `x − 2y`,
  and `x − y` is unbounded along it. This is the race of §13 ("a toad reservoir in front of empty
  squares is worth twice its length"), which for `b = 3` and `b = 4` Right could keep out of the
  positions he needs.
* **Reading.** For `b = 5` a shape must record some weighted differences `x − 2y` (clamped, as
  the plain differences are), for the pairs of runs that race. The margin lemma would need the
  same extension: one move changes `x − 2y` by at most 2. That is a change to the key and to
  `Cgt/Col/`, not a matter of parameters.
* **Not tried.** Shapes with weighted differences; choosing which pairs of runs get them.

