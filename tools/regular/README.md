# Automaton invariants on the folded board

Tools for approach 1 of the research plan: look for a proof of Conjecture 5 in the form of
an invariant described by finite automata, which a single finite check would verify for every
board size at once. **Result so far: no such invariant was found.** Every measurement grew
with the board size (see [Results](#results)).

## The folded board

A position `w` with `n` cells is read as the word of pairs `(w[i], w[n-1-i])`, followed by the
middle cell when `n` is odd (`folded.fold`). The default reads from the ends of the board
inwards; set `FOLD_ORIENT=in` to read from the centre outwards.

* Mirror symmetry becomes a letter-by-letter condition.
* Every move rewrites at most three consecutive letters. Moves that cross the centre rewrite
  the last letters (or the first ones, centre outwards).
* So the move relation is recognised by a finite transducer (`folded.PL`, `folded.PR`).

## Invariants

A pair of languages `(N, Z)` is an invariant if:

* every position of `Z` has, for each Left move, a Right reply back into `Z` (so `Z` positions
  are `≤ 0`);
* every position of `N` is in `LF`, and so are all its Left options, where
  `LF = symmetric ∪ Z ∪ {q : some Right move from q lands in N}` (so `N` positions have Left
  stop `≤ 0`);
* `N` contains every start `Tᵃ□ᵇFᵃ` except `(3, 2)`.

These are the recursions `upperZero_iff`, `lfZero_iff` and `le_iff` of `Cgt/`. So by induction on
the game, a regular invariant would prove the conjecture for all `(a, b)` at once.

`folded.check(N, Z, maxlen=None, n0=0, starts=None)` decides these conditions for automata `N`
and `Z`. It covers every board size, or only boards with `n0 ≤ n ≤ 2·maxlen` cells, and returns
a shortest counterexample. It searches for a violating position, a Left move and the resulting
position simultaneously, letter by letter. Only "has a Right reply into `N` (or `Z`)" needs a
subset construction, and that is built lazily along the search. `starts` replaces the start
language, for example by `starts_rows({2})` for a single row.

## Scripts

* `learn.py`: counterexample-guided search for a small invariant. A SAT solver (python-sat)
  proposes a `k`-state automaton with two acceptance flags, consistent with the constraints
  gathered so far. `check` refutes it with a counterexample, and `k` grows when the
  constraints become unsatisfiable or a solver call runs out of time. Options: `--n0` (only
  boards of at least `n0` cells), `--rows` (only the starts of these rows), `--budget`.
* `learn_z.py`, `learn_n.py`: the same for the two halves separately, for the `a = 2` row.
* `canonical_z.py`, `rpni_z.py`: the `a = 2` normal-play set built from a fixed local Right
  strategy, and learned by state merging (RPNI) instead of SAT.
* `a2_strategy.py`, `a2_abstract.py`: the strategy for the `a = 2` row that *did* work, by
  arithmetic shapes rather than automata. It became the Lean proof in `Cgt/RowA2.lean`; see
  `docs/RESEARCH_NOTES.md` §9.
* `a2_exact_bounds.py`: for the exact values of the `a = 2` row, the smallest bound on the
  mirrored gap differences with which Right still wins `T□T□ᵏF□F` or `TT□ᵏF□F`. It is 4 for
  even `k` and grows with `k` for odd `k`; see `docs/RESEARCH_NOTES.md` §12.
* `forced.py`: lower bounds on the number of states of *any* invariant. They come from
  positions every invariant must contain (starts, and Right's only good reply to a Left move
  from such a position) and positions none may contain (losing ones).

`test_folded.py` compares `fold`, the move rewrites, `pre`, `check` and the regular sets
against brute force on all boards up to 10 cells, in both reading directions (run it with
`FOLD_ORIENT=out` and `FOLD_ORIENT=in`).

## Results

Smallest automaton invariant (shared states for `N` and `Z`). "More than k" means the SAT
solver proved that no automaton with k states exists. "None found" means a 2-minute SAT call
timed out.

| Problem | Boards | Smallest invariant |
| --- | --- | --- |
| Full conjecture, ends inwards | ≤ 4 / ≤ 6 / ≤ 8 cells | 4 / 8 / more than 10 (none found with 11 to 15) |
| Full conjecture, centre outwards | ≤ 4 / ≤ 6 / ≤ 8 cells | 3 / 8 / more than 11 (none found with 12 to 19) |
| Full conjecture | 9 and 10 cells only | more than 6 |
| `a = 2` row | ≤ 8 cells / 12–16 cells | more than 9 / more than 6 |
| `a = 2` row, normal-play part `Z` only | ≤ 12 cells | more than 8 |

Lower bound valid for every invariant (`forced.py`): at least 11 states for boards of at most
14 cells. The witnesses are mostly small-board exceptions such as `(3, 2)`, so this bound says
little about large boards.

**The `a = 2` row in more detail.**

* "Mirror, otherwise pass" wins for `b ≤ 20`. The symmetric positions it visits are a simple
  regular family.
* The positions where Right passes fall into three regular families, and every member up to 40
  cells is `≤ 0`:
  * `□ⁱT□ʲ⁺¹TF□ʲF□ⁱ`;
  * `□ⁱT□ʲ⁺¹FT□ʲ⁻¹F□ⁱ`;
  * `□ⁱ⁺¹TT□F□F□ⁱ`.
* The hard part is the normal-play set `Z` that continues from them.
  * Copying Left's moves in mirror image never works from these positions.
  * The closure under a fixed "most local good reply" strategy needs automata of 592 states
    (trained on boards up to 16 cells) and 971 states (up to 20 cells). These automata fail on
    boards just beyond the training size, so they do not generalise.
  * Letting state merging choose `Z` freely gave automata of 130 to 900 states that had not
    converged after 1,500 rounds.

**Hot symmetric positions** (no piece crossed). The number of states needed to recognise them
grows from 3 to 7 (ends inwards) and from 2 to 9 (centre outwards) between half-lengths 7 and
10.

**Reading.** These numbers do not prove that no regular invariant exists. They show that a
regular invariant, if one exists, has at least tens and probably hundreds of states. That is
beyond exact SAT learning, and the learned strategies do not generalise. Approach 1 could
still work with a Right strategy designed by hand to keep the invariant regular. `check` would
then verify it for every board size.
