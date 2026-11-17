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
| `TT□ᵇFF = 0` for every even `b ≥ 6` | **Conjectured only:** the even half of Conjecture T2 [T11] (`TT□ᵇFF = ∗` when `b = 7 + 6n`, otherwise `0`, for `b ≥ 7`), plus the table value at `b = 6`. The odd half is still open. |
| `T⁶□¹²F⁶` and `T⁷□¹⁰F⁷` are neither `0` nor `∗` | **Not reported anywhere.** They contradict Conjecture T4 of [T11] (`0` or `∗` whenever `b ≥ a > 0`; Conjecture 4 in the preprint and in [Th08]), which the journal version restates unchanged in 2011. Not to be confused with Erickson's Conjecture 4, which [T11] refutes. |
| Exact values beyond the published tables | **Not reported anywhere.** The largest published table is Figure 2 of the arXiv preprint of [T11] (= Figure 4.1 of [Th08]): `a ≤ 4` to `b = 20`, `a = 5` to `b = 12`, `a = 6` to `b = 8`, `a = 7` to `b = 7`, `a = 8` to `b = 5`, `a = 9, 10` to `b = 4`, and `a = 2` to `b = 103`, `a = 3` to `b = 53` in its notes. Its four "≠ 0" cells, `(5, 11)`, `(6, 8)`, `(7, 6)` and `(7, 7)`, are blank in the journal version; all four are `∗`. The table's entries come from a program that compares with `0` and `∗`, not from computed values. |
| A Lean formalisation of Toads and Frogs | **None found.** The only other formalisation is an unmerged Rocq pull request (bloomberg/game-trees #17, July 2026) for boards of at most four squares, including `T□F = ∗`. Nothing on Toads and Frogs in Mathlib, vihdzp/combinatorial-games, the Isabelle and Coq libraries we could search, or formal-conjectures. |

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

* Two preprints of Thanatipanonda cited by [T11], *Three (More) Results of Combinatorial Game
  Toads and Frogs* and *Library values for Toads and Frogs*: their hosts no longer serve them.
  [Th08] contains the proofs the first one announced.
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
* **[Th08]** Thotsaporn Thanatipanonda, *Symbolic-computational methods in combinatorial game
  theory and Ramsey theory*. PhD thesis, Rutgers University, 2008. doi:10.7282/T30G3K3F.
* **[sen-ltd]** sen-ltd/toads-and-frogs, GitHub, 2026.
