import Cgt.Col.B4Checks
import Cgt.Basic
import Cgt.FamilyA1

/-!
# The column `b = 4`: `Tᵃ □⁴ Fᵃ` is infinitesimal for every `a`

The same argument as for `b = 3` (`Cgt/Col/B3.lean`), with the gap rule `ruleF`: gaps between
sorted lengths are exact up to 1 and above that only "far", without parity. The 32,853 + 200,234
keys of `Cgt/Col/B4Data.lean` pass the finite check (`hcU4`, `hcN4`), and the start `Tᵃ□⁴Fᵃ` has
its key in the Left-stop tree for every `a ≥ 2` (`key_s4`; from `a = 4` on the key is the same).

**Trust.** The finite check and the start keys are evaluated by `native_decide`, which trusts the
Lean compiler and runtime, not only the kernel: each use adds an axiom asserting the result of
the compiled evaluation. Everything else is checked by the kernel.
-/

namespace Cgt
namespace Col
open Cell TF Game

/-- `Tᵃ □⁴ Fᵃ` as a run list. -/
def s4 (a : Nat) : RL := [(T, a), (E, 4), (F, a)]

theorem expand_s4 (a : Nat) : expand (s4 a) = start a 4 := by
  simp [s4, start]

theorem maxB_s4 {a : Nat} (ha : 1 ≤ a) : maxB (s4 a) = true := by
  simp [s4, maxB, okFrom, ha]

theorem lenAt_s4 (a i : Nat) : lenAt (s4 a) i = if i = 0 ∨ i = 2 then a else if i = 1 then 4 else 0 := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | i + 3 => simp [lenAt, runAt, s4, List.getD]

theorem cellAt_s4 (a i : Nat) : cellAt (s4 a) i = cellAt (s4 (a + 1)) i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | i + 3 => simp [cellAt, runAt, s4, List.getD]

/-- The only entries of `Tᵃ □⁴ Fᵃ` are the toad run and the frog run. -/
theorem isEnt_s4 {a i : Nat} (h : isEntB (s4 a) i = true) : i = 0 ∨ i = 2 := by
  match i with
  | 0 => exact Or.inl rfl
  | 1 => simp [isEntB, cellAt, runAt, s4] at h
  | 2 => exact Or.inr rfl
  | i + 3 => simp [isEntB, s4] at h; exact absurd h.1.1.1 (by omega)

/-- From `a = 4` on, all start keys are equal (far gaps keep no parity). -/
theorem rel_s4 {a : Nat} (ha : 4 ≤ a) : Rel ruleF 0 (s4 a) (s4 (a + 1)) := by
  refine ⟨⟨rfl, fun i => ⟨cellAt_s4 a i, ?_, ?_⟩⟩, fun i _ => ?_, fun i k hi hk => ?_⟩
  · rw [lenAt_s4, lenAt_s4]; split <;> (try split) <;> omega
  · intro h; rw [lenAt_s4, lenAt_s4]
    match i with
    | 0 => simp [cellAt, runAt, s4] at h
    | 1 => rfl
    | 2 => simp [cellAt, runAt, s4] at h
    | i + 3 => simp
  · rw [lenAt_s4, lenAt_s4]; unfold close; simp only [ruleF, true_or, and_true]
    split <;> (try split) <;> omega
  · rcases isEnt_s4 hi with rfl | rfl <;> rcases isEnt_s4 hk with rfl | rfl <;>
      exact Or.inl (by simp [lenAt_s4])

theorem key_s4 : ∀ a, 2 ≤ a → colB4U.mem (keyOf ruleF (s4 a)) = true
  | 2, _ => by native_decide
  | 3, _ => by native_decide
  | 4, _ => by native_decide
  | a + 5, _ => by
    rw [← keyOf_eq_of_rel (rel_s4 (a := a + 4) (by omega))]
    exact key_s4 (a + 4) (by omega)

/-- **The column `b = 4`, given the margin lemmas.** -/
theorem infinitesimal_start_four_of (hm : Margin ruleF) (a : Nat) : Infinitesimal (tf (start a 4)) := by
  match a with
  | 0 => exact infinitesimal_start_a_zero 4
  | 1 => exact infinitesimal_start_one 4
  | a + 2 =>
    rw [infinitesimal_start_iff, ← expand_s4]
    exact (sound hm colB4U colB4N hcU4 hcN4 _ (s4 (a + 2)) (maxB_s4 (by omega)) (Nat.lt_succ_self _)).2
      (key_s4 (a + 2) (by omega))

end Col
end Cgt
