import Cgt.Col.Rel

/-!
# Dead runs

Characterisations of the computable tests of `Cgt/Col/Key.lean`: a run is dead (`deadB`) iff some
toad run of length `≥ 2` at `s` and some frog run of length `≥ 2` at `e` enclose it, with no empty
run in `s .. e` (`deadB_iff`). Dead toad runs cannot move (`moveAt_of_dead`).
-/

namespace Cgt
namespace Col
open Cell

/-! ### Runs of appended lists -/

theorem runAt_append_lt {A B : RL} {i : Nat} (h : i < A.length) : runAt (A ++ B) i = runAt A i := by
  simp [runAt, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem runAt_append_ge {A B : RL} {i : Nat} (h : A.length ≤ i) : runAt (A ++ B) i = runAt B (i - A.length) := by
  simp [runAt, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem runAt_cons_zero (x : Cell × Nat) (R : RL) : runAt (x :: R) 0 = x := rfl
theorem runAt_cons_succ (x : Cell × Nat) (R : RL) (i : Nat) : runAt (x :: R) (i + 1) = runAt R i := by
  simp [runAt, List.getD_eq_getElem?_getD]

theorem runAt_of_ge {R : RL} {i : Nat} (h : R.length ≤ i) : runAt R i = (E, 0) := by
  simp [runAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

/-! ### Characterisations -/

theorem noE_iff {R : RL} {i d : Nat} : noE R i d = true ↔ ∀ k, k ≤ d → cellAt R (i + k) ≠ E := by
  unfold noE
  simp only [List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  constructor
  · intro h k hk; exact h k (by omega)
  · intro h k hk; exact h k (by omega)

theorem leftDead_iff {R : RL} {i : Nat} : leftDead R i = true ↔
    ∃ s, s ≤ i ∧ cellAt R s = T ∧ 2 ≤ lenAt R s ∧ ∀ k, s ≤ k → k ≤ i → cellAt R k ≠ E := by
  unfold leftDead
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, noE_iff]
  constructor
  · rintro ⟨s, hs, ⟨hT, h2⟩, hn⟩
    refine ⟨s, by omega, hT, h2, fun k hk1 hk2 => ?_⟩
    have := hn (k - s) (by omega)
    rwa [show s + (k - s) = k by omega] at this
  · rintro ⟨s, hs, hT, h2, hn⟩
    exact ⟨s, by omega, ⟨hT, h2⟩, fun k hk => hn (s + k) (by omega) (by omega)⟩

theorem rightDead_iff {R : RL} {i : Nat} : rightDead R i = true ↔
    ∃ e, i ≤ e ∧ e < R.length ∧ cellAt R e = F ∧ 2 ≤ lenAt R e ∧ ∀ k, i ≤ k → k ≤ e → cellAt R k ≠ E := by
  unfold rightDead
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, noE_iff]
  constructor
  · rintro ⟨d, hd, ⟨hF, h2⟩, hn⟩
    refine ⟨i + d, by omega, by omega, hF, h2, fun k hk1 hk2 => ?_⟩
    have := hn (k - i) (by omega)
    rwa [show i + (k - i) = k by omega] at this
  · rintro ⟨e, he, hel, hF, h2, hn⟩
    refine ⟨e - i, by omega, ⟨?_, ?_⟩, fun k hk => hn (i + k) (by omega) (by omega)⟩
    · rwa [show i + (e - i) = e by omega]
    · rwa [show i + (e - i) = e by omega]

/-- Dead runs: enclosed by a toad run `≥ 2` and a frog run `≥ 2` with no empty run between. -/
def DeadP (R : RL) (i : Nat) : Prop :=
  ∃ s e, s ≤ i ∧ i ≤ e ∧ e < R.length ∧ cellAt R s = T ∧ 2 ≤ lenAt R s ∧ cellAt R e = F ∧ 2 ≤ lenAt R e ∧
    ∀ k, s ≤ k → k ≤ e → cellAt R k ≠ E

theorem deadB_iff {R : RL} {i : Nat} : deadB R i = true ↔ DeadP R i := by
  unfold deadB
  rw [Bool.and_eq_true, leftDead_iff, rightDead_iff]
  constructor
  · rintro ⟨⟨s, hs, hT, h2, hn⟩, ⟨e, he, hel, hF, h2', hn'⟩⟩
    refine ⟨s, e, hs, he, hel, hT, h2, hF, h2', fun k hk1 hk2 => ?_⟩
    rcases Nat.le_total k i with h | h
    · exact hn k hk1 h
    · exact hn' k h hk2
  · rintro ⟨s, e, hs, he, hel, hT, h2, hF, h2', hn⟩
    exact ⟨⟨s, hs, hT, h2, fun k h1 h2 => hn k h1 (by omega)⟩, ⟨e, he, hel, hF, h2', fun k h1 h2 => hn k (by omega) h2⟩⟩

theorem isEntB_iff {R : RL} {i : Nat} : isEntB R i = true ↔
    i < R.length ∧ cellAt R i ≠ E ∧ 2 ≤ lenAt R i ∧ ¬ DeadP R i := by
  unfold isEntB
  rw [← deadB_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨h1, h2, h3, by simp [h4]⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨⟨h1, h2⟩, h3⟩, by simpa using h4⟩

end Col
end Cgt
