# What was known before: literature search (November 2026)

The README calls a result *new* when this search found no earlier statement of it as a theorem;
its opening paragraph lists the sources checked. This note records what each source says, and
what could not be reached.

## What earlier work establishes

| Result in this repository | Earlier work |
| --- | --- |
| `Tᵃ□³Fᵃ` infinitesimal for every `a`; `Tᵃ□³Fᵃ = ∗` for every `a ≥ 4` | **Known.** Thanatipanonda's thesis [Th08], Theorem 5.6.1 (pp. 89–93), proves `Tᵃ□³Fᵇ = {a − b \| a − b}` for all `a, b ≥ 4` by hand; `a ≤ 3` is in Erickson's table [E96]. The same statement is Theorem D.3 of the arXiv preprint of [T11] (proof deferred to a supplement); the journal version of [T11] omits it. Our proof is independent and machine-checked. |
| `Tᵃ□⁴Fᵃ` infinitesimal for every `a` | **Conjectured only:** the case `b = 4` of Erickson's Conjecture 7.5 [E96]. Values computed for `a ≤ 10` [T11]. [Th08] (p. 89) lists `Tᵃ□⁴Fᵇ` as open. |
| `Tᵃ□⁴Fᵃ = ∗` for every `a ≥ 5` | **Conjectured only:** the case `b = 4` of Thanatipanonda's Conjecture T3 [T11] (`Tᵃ□ᵇFᵃ = ∗` whenever `a > b > 0`, `b ≠ 2`). |
| `TT□ᵇFF` infinitesimal for every `b` | **Conjectured only:** Erickson's Conjecture 7.5 for `a = 2`; also implied by Thanatipanonda's Conjecture T2. Computed for `b ≤ 103` [T11], and for `b ≤ 70` by [sen-ltd]. [Th08] (p. 18) found the class containing `TTFF` too complicated for the finite-state method. |
| `TT□ᵇFF = ∗` if `2 ≤ b ≤ 4` or `b ≡ 1 (mod 6)`, else `0`, for every `b` | **Conjectured only:** Conjecture T2 [T11] (`TT□ᵇFF = ∗` when `b = 7 + 6n`, otherwise `0`, for `b ≥ 7`), plus the table values for `b ≤ 6` [E96]. Computed for `b ≤ 103` [T11]. Proved here for every `b` (even `b` first, then odd `b`). |
| The values of `□ˡTᵃ□ᵇF□ʳ` (`l ≤ r`), and of one-frog positions with the toads anywhere | **Partly known.** [E96] proves the starting positions `Tᵃ□ᵇF` (`l = r = 0`; Theorem 5.2, with the exception `Tᵃ□F = {{a − 2 \| 1} \| 0}`) and the blocks `□ˡTᵃF□ʳ` (`b = 0`, every `l`, `r`; Lemmas 4.1, 4.3, 4.4). **Conjectured only** otherwise (a gap `b ≥ 1` with empty squares at the ends): Conjecture T1 of [T11] (Conjecture 1 of the preprint). The preprint proves nothing about positions with one frog and lists the class as future work. For at most five empty squares in all, the values were known from Thanatipanonda's library of finite-state results (see "What [T11b] adds"). Statement read in the preprint only; as printed it fails at `TᵃF` (`a ≥ 2`). See `docs/ONE_FROG.md`. |
| `T⁶□¹²F⁶` and `T⁷□¹⁰F⁷` are neither `0` nor `∗` | **Not reported anywhere.** They contradict Conjecture T4 of [T11] (`0` or `∗` whenever `b ≥ a > 0`; Conjecture 4 in the preprint and in [Th08]), which the journal version restates unchanged in 2011. Not to be confused with Erickson's Conjecture 4, which [T11] refutes. |
| Exact values beyond the published tables | **Not reported anywhere.** The largest published table is Figure 2 of the arXiv preprint of [T11] (= Figure 4.1 of [Th08]): `a ≤ 4` to `b = 20`, `a = 5` to `b = 12`, `a = 6` to `b = 8`, `a = 7` to `b = 7`, `a = 8` to `b = 5`, `a = 9, 10` to `b = 4`, and `a = 2` to `b = 103`, `a = 3` to `b = 53` in its notes. Its four "≠ 0" cells, `(5, 11)`, `(6, 8)`, `(7, 6)` and `(7, 7)`, are blank in the journal version; all four are `∗`. The table's entries come from a program that compares with `0` and `∗`, not from computed values. |
| A Lean formalisation of Toads and Frogs | **None found.** The only other formalisation is an unmerged Rocq pull request (bloomberg/game-trees #17, July 2026) for boards of at most four squares, including `T□F = ∗`. Nothing on Toads and Frogs in Mathlib, vihdzp/combinatorial-games, the Isabelle and Coq libraries we could search, or formal-conjectures. |

## Erickson's other conjectures

[E96] ends with six conjectures, 7.1 to 7.6; the README's "Conjecture 5" is 7.5. The arXiv preprint
of [T11] (Section 4 and Appendix D) reports on the others:

* 7.1 (`Tᵃ□□Fᵇ = {{a−3 | a−b} | {∗ | 3−b}}`, `a > b ≥ 2`) and 7.3 (`Tᵃ□³F³ = a − 7/2`, `a ≥ 5`)
  are Theorems D.2 and D.1 there, with proofs deferred to the supplement *Three (More) Results of
  Combinatorial Game Toads and Frogs*, whose contents are in [Th08]. A later manuscript, [T11b],
  gives the proofs in full (Appendices A and B), with that of `Tᵃ□³Fᵇ = {a − b | a − b}`
  (Section 3).
* 7.2 (`Tᵃ□³FF = (a−2)∗`, `a ≥ 2`) was proved by Thanatipanonda and Zeilberger [TZ07].
* 7.4 (`Tᵃ□ᵃFᵃ⁻¹ = 1` or `1∗`) is false: `T⁷□⁷F⁶ > 2`.
* 7.6 (Toads and Frogs is NP-hard) was proved by Jesse Hull in 2000, as reported there (we did not
  find Hull's own write-up).
* 7.5 is open.

[T11]'s own conjectures, 1 to 5 in the preprint and T1 to T5 in the journal version, are: values
of every position with one frog, `□ᴸ Tᵃ □ᵇ F □ᴿ` (T1); the values of `TT□ᵇFF` (T2); `Tᵃ□ᵇFᵃ = ∗`
for `a > b > 0`, `b ≠ 2` (T3); `Tᵃ□ᵇFᵃ ∈ {0, ∗}` for `b ≥ a > 0` (T4); and, for each `c ≥ 3`,
`Tᶜ□ᵇFᶜ = 0` for all large `b` (T5). The README's table of conjectures lists their status.

## What [T11b] adds

[T11b] is a manuscript of 30 pages, read in full in November 2026.

* **Proofs.** `Tᵃ□³Fᵇ = {a − b | a − b}` (`a, b ≥ 4`), Erickson's 7.1 and 7.3, by hand with computer
  help: case trees that compare positions with sums of known values, using the one-sided Death
  Leap Principle and a *Blocking Rule*, `X FF Y ≤ X + Y`.
* **A new conjecture: `Tᵃ□⁴Fᵇ = {a − b | a − b}` for `a, b ≥ 6`.** Its diagonal is our
  `start_four_value` (`∗` for `a ≥ 5`). By exact computation it holds for every `a, b` from 6
  to 9 (`START=G STARTONLY=1` of `tools/column/col_shapes.cpp`, which checks that the start padded
  with `|a − b|` free moves is `≤ ∗`, in both directions). The bound 6 is needed: with a 5 it
  holds at `(5, 6)`, `(6, 5)`, `(5, 7)`, `(7, 5)` but fails at `(8, 5)` and `(5, 8)`
  (`T⁸□⁴F⁵ ≤ {3 | 3}`, not equal; `tools/cgt_values.py`), and it fails when `a` or `b` is 4.
* **An open problem:** the values of `Tᵃ□ⁱFᵇ` for fixed `i ≥ 5`.
* **One-frog "library values"** quoted from *Library values for Toads and Frogs* (which we still
  have not seen): `Tᵃ□TᵇF□ = a`, `Tᵃ□□F = a − 1` and `Tᵃ□□TF = a`. The manuscript says the
  symbolic finite-state method of [TZ07] gave the values of the classes `□F` to `□⁵F`: a fixed
  number of empty squares, any number of toads, in any order. The first two values are cases of
  our `value_room_zero_even`; the third has `room = −2`, outside our theorem. So for at most five
  empty squares the one-frog values were known from that library; Conjecture T1 and our theorem
  concern any number of empty squares.

## Sources searched

* [E96] (paper, and Erickson's page for it, last updated 2000), [TZ07], [T11] (the arXiv preprint
  0804.0640v1 and the journal version, both in full), and [Th08] (the Toads and Frogs chapters in
  full).
* The "Unsolved problems in combinatorial games" lists in all six *Games of No Chance* volumes
  (1996, 2002, 2009, 2015, 2019, 2025): none mentions Toads and Frogs.
* Works citing [E96], [TZ07], [T11] and [Th08], from OpenAlex, Crossref, Semantic Scholar and
  zbMATH Open: eleven distinct citing works, none about the values of `Tᵃ□ᵇFᵃ` (game-playing
  programs, complexity surveys, bibliographies, the loopy variant *Backsliding Toads and Frogs*).
* arXiv (only [TZ07] and [T11] have Toads and Frogs in their metadata), Wikipedia (Conjecture 5
  "the last one still open"), GitHub (sen-ltd/toads-and-frogs [sen-ltd], which recomputes
  `a = 2` to `b = 70`, `a = 3` to `b = 29`, `a = 4` to `b = 13`, `a = 5` to `b = 6`; CGSuite;
  smaller engines), the OEIS, and the Lean Zulip.

## Not reached

* *Library values for Toads and Frogs*, a web page of Thanatipanonda cited by [T11] and [T11b]:
  its host no longer serves it. (The supplement *Three (More) Results of Combinatorial Game Toads
  and Frogs* cited by [T11] was not reached either; [T11b] is a later version of it, and [Th08]
  contains its proofs.)
* Siegel, *Combinatorial Game Theory* (AMS, 2013), and Albert, Nowakowski and Wolfe, *Lessons in
  Play*.
* Google Scholar, MathSciNet, and the Isabelle Archive of Formal Proofs index.

## References

* **[E96]** Jeff Erickson, *New Toads and Frogs Results*. *Games of No Chance*, MSRI Publications
  29, 1996, pp. 299–310.
* **[TZ07]** Thotsaporn Thanatipanonda and Doron Zeilberger, *A Symbolic Finite-State Approach for
  Automated Proving of Theorems in Combinatorial Game Theory*. arXiv:0710.4951; J. Difference
  Equations and Applications 15(2), 2009.
* **[T11]** Thotsaporn Thanatipanonda, *Further Hopping with Toads and Frogs*. Electronic Journal
  of Combinatorics 18(1), 2011, #P67; preprint arXiv:0804.0640 (2008).
* **[T11b]** Thotsaporn "Aek" Thanatipanonda, *Three Results of Combinatorial Game Toads and
  Frogs*. Manuscript dated 18 March 2011; private communication.
* **[Th08]** Thotsaporn Thanatipanonda, *Symbolic-computational methods in combinatorial game
  theory and Ramsey theory*. PhD thesis, Rutgers University, 2008. doi:10.7282/T30G3K3F.
* **[sen-ltd]** sen-ltd/toads-and-frogs, GitHub, 2026.
