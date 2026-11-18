import Cgt.RowA2Zero
import Cgt.Decide

/-!
# Exact values in the row `a = 2`

Thanatipanonda's computations [T11] (for `b ≤ 103`) fit the pattern

  `TT□ᵇFF = ∗` if `2 ≤ b ≤ 4` or `b ≡ 1 (mod 6)`, and `TT□ᵇFF = 0` otherwise

(`valueA2 b`). This file proves the pattern for every even `b` and for every `b ≤ 30`
(`start_two_value`). The general statement `ExactValuesA2` is proved in `Cgt/RowA2Odd.lean`
(`exactValuesA2`), which handles the odd `b ≥ 31` with a linear invariant.

Both values reduce to a single normal-play claim, because `TT□ᵇFF` is symmetric and Left's
only move leads to `T□T□ᵇ⁻¹FF ≤ 0` (`q2_le_zero`):

* `TT□ᵇFF = 0` as soon as `T□T□ᵇ⁻²F□F ≤ 0` (`start_two_equiv_zero_of`);
* `TT□ᵇFF = ∗` as soon as `TT□ᵇ⁻¹F□F ≤ 0` (`start_two_equiv_star_of`): then the game is `≤ ∗`
  (`le_star_of`), and so `= ∗` by symmetry.

The even case is `start_two_equiv_zero` (`Cgt/RowA2Zero.lean`). The cases `b ≤ 30` with `b` odd,
or `b ∈ {2, 4}`, are settled one by one by the kernel (`leZeroB`).
-/

namespace Cgt
open Cell TF Game

namespace Game

theorem neg_star : neg star = star := by
  rw [star, neg_mk]; simp [neg_zero]

theorem not_star_le_zero : ¬ le star zero :=
  not_le_left (g := star) (x := zero) (by simp [star, left])

end Game

theorem not_star_le_of_le_zero {g : Game} (h : le g zero) : ¬ le star g :=
  fun h' => not_star_le_zero (le_trans _ _ _ h' h)

/-- `∗ ≤ X` fails if some Right option of `X` is `≤ ∗`. -/
theorem not_star_le_of_right {p : List Cell} (h : ∃ r ∈ rightMoves p, le (tf r) star) :
    ¬ le star (tf p) := by
  intro h'
  rw [le_iff] at h'
  obtain ⟨r, hr, hle⟩ := h
  exact h'.2 _ (mem_right_tf.2 ⟨r, hr, rfl⟩) hle

/-- `X ≤ ∗` if no Left option of `X` is `≥ ∗` and some Right option is `≤ 0`. -/
theorem le_star_of {p : List Cell} (hl : ∀ q ∈ leftMoves p, ¬ le star (tf q))
    (hr : ∃ r ∈ rightMoves p, le (tf r) zero) : le (tf p) star := by
  rw [le_iff]
  refine ⟨fun x hx hsx => ?_, fun y hy hyle => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := mem_left_tf.1 hx
    exact hl q hq hsx
  · have hy0 : y = zero := by simpa [star, right] using hy
    subst hy0
    obtain ⟨r, hr, hle⟩ := hr
    exact not_right_le (mem_right_tf.2 ⟨r, hr, rfl⟩) (le_trans _ _ _ hle hyle)

/-- A symmetric position that is `≤ ∗` is `∗`. -/
theorem equiv_star_of_mirror {p : List Cell} (hp : mirror p = p) (h : le (tf p) star) :
    Equiv (tf p) star := by
  refine ⟨h, ?_⟩
  have e := tf_mirror p
  rw [hp] at e
  have h' : le star (neg (tf p)) := by
    rw [← neg_star, neg_le_neg_iff]; exact h
  exact le_trans _ _ _ h' e.2

/-- `tf p ≤ 0`, decided by the kernel. -/
theorem le_zero_of_leZeroB {p : List Cell} (h : leZeroB (pot p + 1) p = true) :
    le (tf p) zero :=
  (leZeroB_iff _ p (Nat.lt_succ_self _)).1 h

/-! ### The two reductions -/

/-- `TT□ᵐF□F`: Right's only move from `TT□ᵐ⁺¹FF`. -/
def r2 (m : Nat) : P4 := ⟨true, true, false, false, 0, 0, m, 1, 0⟩

theorem r2_mem_rms_s2 (m : Nat) : r2 m ∈ (s2 m).rms := by
  simp [P4.rms, P4.rm1, P4.rm2, P4.rm3, P4.rm4, s2, r2]

/-- `TT□ᵐ⁺¹FF = ∗` as soon as `TT□ᵐF□F ≤ 0` (`m ≥ 1`). -/
theorem start_two_equiv_star_of (m : Nat) (hm : 1 ≤ m) (h : le (tf (r2 m).toList) zero) :
    Equiv (tf (start 2 (m + 1))) star := by
  refine equiv_star_of_mirror (mirror_start 2 (m + 1)) (le_star_of ?_ ?_)
  · rw [start_two_eq, leftMoves_toList, lms_s2]
    intro q hq
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
    subst hq
    exact not_star_le_of_le_zero (q2_le_zero m hm)
  · rw [start_two_eq]
    exact ⟨_, toList_mem_rightMoves (r2_mem_rms_s2 m), h⟩

/-- `TT□ᵏ⁺²FF = 0` as soon as `T□T□ᵏF□F ≤ 0`. -/
theorem start_two_equiv_zero_of (k : Nat) (h : le (tf (p0 k).toList) zero) :
    Equiv (tf (start 2 (k + 2))) zero := by
  refine equiv_zero_of_mirror (mirror_start 2 (k + 2)) ?_
  rw [le_zero_iff_tf, start_two_eq, leftMoves_toList, lms_s2]
  intro q hq
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at hq
  subst hq
  exact ⟨_, toList_mem_rightMoves (p0_mem_rms_q2 k), h⟩

/-! ### The conjectured values

`valueA2` and `ExactValuesA2` (Thanatipanonda's Conjecture T2) are defined in `Cgt/Statement.lean`;
`ExactValuesA2` is proved as `exactValuesA2` in `Cgt/RowA2Odd.lean`. -/

theorem start_two_value_of_even (b : Nat) (hb : 6 ≤ b) (he : b % 2 = 0) :
    Equiv (tf (start 2 b)) (valueA2 b) := by
  have hv : valueA2 b = zero := by
    unfold valueA2
    split
    · next h => exact absurd h (by omega)
    · rfl
  rw [hv]; exact start_two_equiv_zero b hb he

/-! ### Small cases, decided by the kernel -/

theorem value_0 : Equiv (tf (start 2 0)) (valueA2 0) :=
  equiv_zero_of_mirror (mirror_start 2 0) (le_zero_of_leZeroB (by decide +kernel))

/-- `TT□FF = ∗`. Here Left's option `T□TFF` is not `≤ 0`, but its Right option `TFT□F` is `≤ ∗`. -/
theorem value_1 : Equiv (tf (start 2 1)) (valueA2 1) := by
  have hY : le (tf [T, F, T, E, F]) star := by
    refine le_star_of ?_ ⟨[T, F, T, F, E], by decide, le_zero_of_leZeroB (by decide +kernel)⟩
    intro q hq
    rw [show leftMoves [T, F, T, E, F] = [[T, F, E, T, F]] from rfl, List.mem_singleton] at hq
    subst hq
    exact not_star_le_of_le_zero (le_zero_of_leZeroB (by decide +kernel))
  refine equiv_star_of_mirror (mirror_start 2 1) (le_star_of ?_ ⟨[T, T, F, E, F], by decide,
    le_zero_of_leZeroB (by decide +kernel)⟩)
  intro q hq
  rw [show leftMoves (start 2 1) = [[T, E, T, F, F]] from rfl, List.mem_singleton] at hq
  subst hq
  exact not_star_le_of_right ⟨_, by decide, hY⟩

/-- `∗` at `b = m + 1`, from `TT□ᵐF□F ≤ 0`. -/
local macro "star_case" m:num : term =>
  `(start_two_equiv_star_of $m (by decide) (le_zero_of_leZeroB (by decide +kernel)))

/-- `0` at `b = k + 2`, from `T□T□ᵏF□F ≤ 0`. -/
local macro "zero_case" k:num : term =>
  `(start_two_equiv_zero_of $k (le_zero_of_leZeroB (by decide +kernel)))

theorem value_2 : Equiv (tf (start 2 2)) (valueA2 2) := star_case 1
theorem value_3 : Equiv (tf (start 2 3)) (valueA2 3) := star_case 2
theorem value_4 : Equiv (tf (start 2 4)) (valueA2 4) := star_case 3
theorem value_5 : Equiv (tf (start 2 5)) (valueA2 5) := zero_case 3
theorem value_7 : Equiv (tf (start 2 7)) (valueA2 7) := star_case 6
theorem value_9 : Equiv (tf (start 2 9)) (valueA2 9) := zero_case 7
theorem value_11 : Equiv (tf (start 2 11)) (valueA2 11) := zero_case 9
theorem value_13 : Equiv (tf (start 2 13)) (valueA2 13) := star_case 12
theorem value_15 : Equiv (tf (start 2 15)) (valueA2 15) := zero_case 13
theorem value_17 : Equiv (tf (start 2 17)) (valueA2 17) := zero_case 15
theorem value_19 : Equiv (tf (start 2 19)) (valueA2 19) := star_case 18
theorem value_21 : Equiv (tf (start 2 21)) (valueA2 21) := zero_case 19
theorem value_23 : Equiv (tf (start 2 23)) (valueA2 23) := zero_case 21
theorem value_25 : Equiv (tf (start 2 25)) (valueA2 25) := star_case 24
theorem value_27 : Equiv (tf (start 2 27)) (valueA2 27) := zero_case 25
theorem value_29 : Equiv (tf (start 2 29)) (valueA2 29) := zero_case 27

/-- **Exact values of `TT□ᵇFF`** for every even `b` and every `b ≤ 30`. -/
theorem start_two_value (b : Nat) (hb : b % 2 = 0 ∨ b ≤ 30) :
    Equiv (tf (start 2 b)) (valueA2 b) := by
  by_cases h6 : 6 ≤ b ∧ b % 2 = 0
  · exact start_two_value_of_even b h6.1 h6.2
  match b, hb, h6 with
  | 0, _, _ => exact value_0
  | 1, _, _ => exact value_1
  | 2, _, _ => exact value_2
  | 3, _, _ => exact value_3
  | 4, _, _ => exact value_4
  | 5, _, _ => exact value_5
  | 7, _, _ => exact value_7
  | 9, _, _ => exact value_9
  | 11, _, _ => exact value_11
  | 13, _, _ => exact value_13
  | 15, _, _ => exact value_15
  | 17, _, _ => exact value_17
  | 19, _, _ => exact value_19
  | 21, _, _ => exact value_21
  | 23, _, _ => exact value_23
  | 25, _, _ => exact value_25
  | 27, _, _ => exact value_27
  | 29, _, _ => exact value_29
  | b + 30, hb, h6 => exfalso; omega

end Cgt
