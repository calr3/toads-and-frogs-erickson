import Cgt.Col.Margin

/-!
# Mirror symmetry of the margin relation, and Right moves

Mirroring a run list reverses the order of its runs (index `i ↦ L - 1 - i`) and swaps toads and
frogs. Dead runs, entries and lengths correspond, so `Rel j` is preserved (`Rel.mirror`). Right
moves are mirrored Left moves, so the margin lemma for Right moves (`margin_right`) follows from
the one for Left moves.
-/

namespace Cgt
namespace Col
open Cell

theorem length_mirrorRL (R : RL) : (mirrorRL R).length = R.length := by simp [mirrorRL]

theorem runAt_mirrorRL {R : RL} {i : Nat} (h : i < R.length) :
    runAt (mirrorRL R) i = ((runAt R (R.length - 1 - i)).1.swap, (runAt R (R.length - 1 - i)).2) := by
  have h1 : i < (mirrorRL R).length := by rw [length_mirrorRL]; exact h
  have h2 : R.length - 1 - i < R.length := by omega
  rw [runAt_eq_getElem h1, runAt_eq_getElem h2]
  simp [mirrorRL, List.getElem_reverse]

theorem runAt_mirrorRL_ge {R : RL} {i : Nat} (h : R.length ≤ i) : runAt (mirrorRL R) i = (E, 0) :=
  runAt_of_ge (by rw [length_mirrorRL]; exact h)

theorem cellAt_mirrorRL {R : RL} {i : Nat} (h : i < R.length) :
    cellAt (mirrorRL R) i = (cellAt R (R.length - 1 - i)).swap := by
  rw [cellAt_def, runAt_mirrorRL h]; rfl

theorem lenAt_mirrorRL {R : RL} {i : Nat} (h : i < R.length) :
    lenAt (mirrorRL R) i = lenAt R (R.length - 1 - i) := by
  rw [lenAt_def, runAt_mirrorRL h]; rfl

theorem swap_eq_iff {c d : Cell} : c.swap = d ↔ c = d.swap := by
  cases c <;> cases d <;> simp [Cell.swap]

theorem deadP_mirror_of {R : RL} {i : Nat} (h : i < R.length) (hd : DeadP R (R.length - 1 - i)) :
    DeadP (mirrorRL R) i := by
  obtain ⟨s, e, hs, he, hel, hT, h2s, hF, h2e, hn⟩ := hd
  refine ⟨R.length - 1 - e, R.length - 1 - s, by omega, by omega, by rw [length_mirrorRL]; omega, ?_, ?_, ?_, ?_,
    fun k h1 h2 => ?_⟩
  · rw [cellAt_mirrorRL (by omega), show R.length - 1 - (R.length - 1 - e) = e by omega, hF]; rfl
  · rw [lenAt_mirrorRL (by omega), show R.length - 1 - (R.length - 1 - e) = e by omega]; exact h2e
  · rw [cellAt_mirrorRL (by omega), show R.length - 1 - (R.length - 1 - s) = s by omega, hT]; rfl
  · rw [lenAt_mirrorRL (by omega), show R.length - 1 - (R.length - 1 - s) = s by omega]; exact h2s
  · rw [cellAt_mirrorRL (by omega)]
    have := hn (R.length - 1 - k) (by omega) (by omega)
    intro hE; apply this; rw [swap_eq_iff] at hE; exact hE

theorem deadP_mirror {R : RL} {i : Nat} (h : i < R.length) :
    DeadP (mirrorRL R) i ↔ DeadP R (R.length - 1 - i) := by
  constructor
  · intro hd
    have h' : R.length - 1 - i < (mirrorRL R).length := by rw [length_mirrorRL]; omega
    have := deadP_mirror_of h' (by rw [length_mirrorRL, show R.length - 1 - (R.length - 1 - i) = i by omega]; exact hd)
    rwa [mirrorRL_mirrorRL] at this
  · exact deadP_mirror_of h

theorem isEntB_mirror {R : RL} {i : Nat} :
    isEntB (mirrorRL R) i = (decide (i < R.length) && isEntB R (R.length - 1 - i)) := by
  rcases Nat.lt_or_ge i R.length with h | h
  · simp only [h, decide_true, Bool.true_and]
    apply Bool.eq_iff_iff.2
    rw [isEntB_iff, isEntB_iff, length_mirrorRL, cellAt_mirrorRL h, lenAt_mirrorRL h, deadP_mirror h]
    constructor
    · rintro ⟨-, hE, h2, hd⟩
      exact ⟨by omega, fun h' => hE (by rw [h']; rfl), h2, hd⟩
    · rintro ⟨-, hE, h2, hd⟩
      exact ⟨h, fun h' => hE (by rw [swap_eq_iff] at h'; exact h'), h2, hd⟩
  · have : ¬ i < R.length := by omega
    simp only [this, decide_false, Bool.false_and]
    cases hb : isEntB (mirrorRL R) i
    · rfl
    · have := (isEntB_iff.1 hb).1; rw [length_mirrorRL] at this; omega

theorem Rel.mirror {j : Nat} {R R' : RL} (h : Rel j R R') : Rel j (mirrorRL R) (mirrorRL R') := by
  have hl := h.1.1
  refine ⟨⟨by rw [length_mirrorRL, length_mirrorRL, hl], fun i => ?_⟩, fun i hi => ?_, fun i k hi hk => ?_⟩
  · rcases Nat.lt_or_ge i R.length with hi | hi
    · obtain ⟨h1, h2, h3⟩ := h.1.2 (R.length - 1 - i)
      rw [cellAt_mirrorRL hi, cellAt_mirrorRL (by omega), lenAt_mirrorRL hi, lenAt_mirrorRL (by omega), ← hl, h1]
      refine ⟨rfl, h2, fun hE => h3 ?_⟩
      rw [swap_eq_iff] at hE; rw [h1]; exact hE
    · rw [cellAt_def, cellAt_def, lenAt_def, lenAt_def, runAt_mirrorRL_ge hi, runAt_mirrorRL_ge (by omega)]
      exact ⟨rfl, Or.inl rfl, fun _ => rfl⟩
  · rw [isEntB_mirror, Bool.and_eq_true, decide_eq_true_eq] at hi
    rw [lenAt_mirrorRL (R := R) hi.1, lenAt_mirrorRL (R := R') (i := i) (by omega), ← hl]
    exact h.2.1 _ hi.2
  · rw [isEntB_mirror, Bool.and_eq_true, decide_eq_true_eq] at hi hk
    rw [lenAt_mirrorRL (R := R) hi.1, lenAt_mirrorRL (R := R') (i := i) (by omega),
      lenAt_mirrorRL (R := R) hk.1, lenAt_mirrorRL (R := R') (i := k) (by omega), ← hl]
    exact h.2.2 _ _ hi.2 hk.2

/-- **The margin lemma for Right moves.** -/
theorem margin_right (j : Nat) (R R' Y : RL) (h : Rel (j + 2) R R') (hR : maxB R = true) (hR' : maxB R' = true)
    (hY : Y ∈ rmovesR R) : ∃ Y' ∈ rmovesR R', Rel j Y Y' := by
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
  obtain ⟨X', hX', hXX⟩ := margin_left j _ _ X h.mirror (maxB_mirrorRL hR) (maxB_mirrorRL hR') hX
  exact ⟨mirrorRL X', List.mem_map_of_mem hX', hXX.mirror⟩

end Col
end Cgt
