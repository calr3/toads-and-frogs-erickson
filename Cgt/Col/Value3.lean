import Cgt.Col.B3SBlocks
import Cgt.Col.Column3
import Cgt.Col.SoundStar

/-!
# The exact values of the column `b = 3`

**Theorem.** `Tᵃ □³ Fᵃ = ∗` for every `a ≥ 4` (`start_three_equiv_star`); with the small cases,
`Tᵃ □³ Fᵃ = 0` for `a = 0, 3` and `∗` otherwise (`start_three_value`). This is the case `b = 3` of
Thanatipanonda's conjecture that `Tᵃ □ᵇ Fᵃ = ∗` whenever `a > b`, `b ≠ 2` [T11].

The proof is that of the column `b = 3` (`Cgt/Col/Column3.lean`) with `≤ ∗` in place of "Left stop
`≤ 0`": the 55 + 1,208 keys of `Cgt/Col/B3SData.lean` pass the finite check (`hcS3`, `hcN3S`,
evaluated by the kernel in `Cgt/Col/B3SCheck*.lean`), so every run list with a key in the `≤ ∗`
tree is `≤ ∗` (`soundS`). The start `Tᵃ□³Fᵃ` has such a key for every `a ≥ 4` (`key_s3S`), and
since it is its own mirror image, `≤ ∗` means `= ∗` (`equiv_star_of_mirror`).
-/

namespace Cgt
namespace Col
open Cell TF Game

theorem hcS3 : ∀ k ∈ colB3SS.toList, ∀ W ∈ witOf ruleP k, chkS ruleP colB3SS colB3SN W = true := by
  have h : colB3SS.toList.all (fun k => (witOf ruleP k).all (chkS ruleP colB3SS colB3SN)) = true :=
    all_of_sizes _ [55] _ (by decide +kernel) fun i hi => by
      match i, hi with
      | 0, _ => exact blkB3SS_0
      | _ + 1, h => exact absurd h (by simp)
  simp only [List.all_eq_true] at h
  exact h

theorem hcN3S : ∀ k ∈ colB3SN.toList, ∀ W ∈ witOf ruleP k, chkN ruleP colB3SN W = true := by
  have h : colB3SN.toList.all (fun k => (witOf ruleP k).all (chkN ruleP colB3SN)) = true :=
    all_of_sizes _ [593, 316, 177, 45, 77] _ (by decide +kernel) fun i hi => by
      match i, hi with
      | 0, _ => exact blkB3SN_1
      | 1, _ => exact blkB3SN_2
      | 2, _ => exact blkB3SN_3
      | 3, _ => exact blkB3SN_4
      | 4, _ => exact blkB3SN_5
      | _ + 5, h => exact absurd h (by simp)
  simp only [List.all_eq_true] at h
  exact h

theorem key_s3S : ∀ a, 4 ≤ a → colB3SS.mem (keyOf ruleP (s3 a)) = true
  | 4, _ => by decide +kernel
  | 5, _ => by decide +kernel
  | 6, _ => by decide +kernel
  | 7, _ => by decide +kernel
  | a + 8, _ => by
    rw [← keyOf_eq_of_rel (rel_s3 (a := a + 6) (by omega))]
    exact key_s3S (a + 6) (by omega)

theorem start_three_le_star (a : Nat) (ha : 4 ≤ a) : le (tf (start a 3)) star := by
  rw [← expand_s3]
  exact soundS margin colB3SS colB3SN hcS3 hcN3S _ (s3 a) (maxB_s3 (by omega)) (Nat.lt_succ_self _)
    (key_s3S a ha)

end Col

open Cell TF Game

/-- **`Tᵃ □³ Fᵃ = ∗` for every `a ≥ 4`.** -/
theorem start_three_equiv_star (a : Nat) (ha : 4 ≤ a) : Equiv (tf (start a 3)) star :=
  equiv_star_of_mirror (mirror_start a 3) (Col.start_three_le_star a ha)

/-- The value of `Tᵃ □³ Fᵃ`: `0` for `a = 0, 3`, otherwise `∗`. -/
def valueB3 (a : Nat) : Game := if a = 0 ∨ a = 3 then zero else star

/-- **The exact values of the column `b = 3`.** -/
theorem start_three_value (a : Nat) : Equiv (tf (start a 3)) (valueB3 a) := by
  match a with
  | 0 => exact equiv_zero_of_mirror (mirror_start 0 3) (le_zero_of_leZeroB (by decide +kernel))
  | 1 =>
    refine equiv_star_of_mirror (mirror_start 1 3) (le_star_of (fun q hq => ?_) ?_)
    · have h : leftMoves (start 1 3) = [[Cell.E, Cell.T, Cell.E, Cell.E, Cell.F]] := by decide +kernel
      rw [h, List.mem_singleton] at hq
      subst hq
      exact not_star_le_of_le_zero (le_zero_of_leZeroB (by decide +kernel))
    · exact ⟨[Cell.T, Cell.E, Cell.E, Cell.F, Cell.E], by decide +kernel, le_zero_of_leZeroB (by decide +kernel)⟩
  | 2 =>
    have h := start_two_value 3 (Or.inr (by omega))
    simpa [valueA2, valueB3] using h
  | 3 => exact equiv_zero_of_mirror (mirror_start 3 3) (le_zero_of_leZeroB (by decide +kernel))
  | a + 4 =>
    have hv : valueB3 (a + 4) = star := by unfold valueB3; rw [if_neg (by omega)]
    rw [hv]; exact start_three_equiv_star (a + 4) (by omega)

end Cgt
