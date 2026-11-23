import Cgt.ToadsFrogs
import Cgt.Sum.ZNum

/-!
# The Blocking Rule

Two adjacent frogs `FF` can never be passed by a toad, so Left's moves in `X FF Y` are exactly
his moves in `X` and in `Y`. Hence integer upper bounds add: `X ≤ m` and `Y ≤ m'` give
`X FF Y ≤ m + m'`.
-/

namespace Cgt
open Cell TF Game

/-- Where a toad sits relative to a frog in two decompositions of the same list. -/
private theorem split_F_T {X Y u v : List Cell} (h : X ++ F :: Y = u ++ T :: v) :
    (∃ w, u = X ++ F :: w ∧ Y = w ++ T :: v) ∨ (∃ w, X = u ++ T :: w ∧ v = w ++ F :: Y) := by
  induction X generalizing u with
  | nil =>
    cases u with
    | nil => simp at h
    | cons d u =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨u, rfl, rfl⟩
  | cons x X ih =>
    cases u with
    | nil =>
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨X, rfl, rfl⟩
    | cons d u =>
      simp at h
      obtain ⟨rfl, h⟩ := h
      rcases ih h with ⟨w, rfl, rfl⟩ | ⟨w, rfl, rfl⟩
      · exact Or.inl ⟨w, rfl, rfl⟩
      · exact Or.inr ⟨w, rfl, rfl⟩

/-- Left's moves in `X FF Y` are his moves in `X` and his moves in `Y`: no toad passes two frogs. -/
theorem mem_leftMoves_FF {X Y q : List Cell} :
    q ∈ leftMoves (X ++ F :: F :: Y) ↔
      (∃ X', X' ∈ leftMoves X ∧ q = X' ++ F :: F :: Y) ∨
      (∃ Y', Y' ∈ leftMoves Y ∧ q = X ++ F :: F :: Y') := by
  constructor
  · intro h
    rcases mem_leftMoves.1 h with ⟨u, r, hp, rfl⟩ | ⟨u, r, hp, rfl⟩
    · rcases split_F_T hp with ⟨w, rfl, hY⟩ | ⟨w, rfl, hr⟩
      · right
        cases w with
        | nil => simp at hY
        | cons d w =>
          simp at hY
          obtain ⟨rfl, rfl⟩ := hY
          exact ⟨w ++ E :: T :: r, mem_leftMoves.2 (Or.inl ⟨w, r, rfl, rfl⟩), by simp⟩
      · left
        cases w with
        | nil => simp at hr
        | cons d w =>
          simp at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨u ++ E :: T :: w, mem_leftMoves.2 (Or.inl ⟨u, w, rfl, rfl⟩), by simp⟩
    · rcases split_F_T hp with ⟨w, rfl, hY⟩ | ⟨w, rfl, hr⟩
      · right
        cases w with
        | nil => simp at hY
        | cons d w =>
          simp at hY
          obtain ⟨rfl, rfl⟩ := hY
          exact ⟨w ++ E :: F :: T :: r, mem_leftMoves.2 (Or.inr ⟨w, r, rfl, rfl⟩), by simp⟩
      · left
        cases w with
        | nil => simp at hr
        | cons d w =>
          cases w with
          | nil => simp at hr
          | cons e w =>
            simp at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨u ++ E :: F :: T :: w, mem_leftMoves.2 (Or.inr ⟨u, w, rfl, rfl⟩), by simp⟩
  · rintro (⟨X', hX, rfl⟩ | ⟨Y', hY, rfl⟩)
    · rcases mem_leftMoves.1 hX with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
      · exact mem_leftMoves.2 (Or.inl ⟨u, r ++ F :: F :: Y, by simp, by simp⟩)
      · exact mem_leftMoves.2 (Or.inr ⟨u, r ++ F :: F :: Y, by simp, by simp⟩)
    · rcases mem_leftMoves.1 hY with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
      · exact mem_leftMoves.2 (Or.inl ⟨X ++ F :: F :: u, r, by simp, by simp⟩)
      · exact mem_leftMoves.2 (Or.inr ⟨X ++ F :: F :: u, r, by simp, by simp⟩)

/-- Right's moves in `X` and in `Y` are still available in `X FF Y` (he has others too). -/
theorem rightMoves_FF_left {X X' : List Cell} (Y : List Cell) (h : X' ∈ rightMoves X) :
    X' ++ F :: F :: Y ∈ rightMoves (X ++ F :: F :: Y) := by
  rcases mem_rightMoves.1 h with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
  · exact mem_rightMoves.2 (Or.inl ⟨u, r ++ F :: F :: Y, by simp, by simp⟩)
  · exact mem_rightMoves.2 (Or.inr ⟨u, r ++ F :: F :: Y, by simp, by simp⟩)

theorem rightMoves_FF_right (X : List Cell) {Y Y' : List Cell} (h : Y' ∈ rightMoves Y) :
    X ++ F :: F :: Y' ∈ rightMoves (X ++ F :: F :: Y) := by
  rcases mem_rightMoves.1 h with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
  · exact mem_rightMoves.2 (Or.inl ⟨X ++ F :: F :: u, r, by simp, by simp⟩)
  · exact mem_rightMoves.2 (Or.inr ⟨X ++ F :: F :: u, r, by simp, by simp⟩)

private theorem blocking_rule_aux : ∀ (N : Nat) (X Y : List Cell) (m m' : Int),
    pot X + pot Y < N → le (tf X) (zint m) → le (tf Y) (zint m') →
      le (tf (X ++ F :: F :: Y)) (zint (m + m')) := by
  intro N
  induction N with
  | zero => intro X Y m m' h; omega
  | succ N ih =>
    intro X Y m m' hN hX hY
    have hX' := le_zint_iff.1 hX
    have hY' := le_zint_iff.1 hY
    refine le_zint_of (fun x hx => ?_) (fun hneg => ?_)
    · obtain ⟨q, hq, rfl⟩ := mem_left_tf.1 hx
      rcases mem_leftMoves_FF.1 hq with ⟨X', hX1, rfl⟩ | ⟨Y', hY1, rfl⟩
      · have hp := pot_lt_of_mem_leftMoves hX1
        rcases hX'.1 _ (mem_left_tf.2 ⟨X', hX1, rfl⟩) with ⟨_, hle⟩ | ⟨y, hy, hle⟩
        · left
          have := ih X' Y (m - 1) m' (by omega) hle hY
          have e : m - 1 + m' = m + m' - 1 := by omega
          rw [e] at this; exact this
        · right
          obtain ⟨X'', hX2, rfl⟩ := mem_right_tf.1 hy
          have hp2 := pot_lt_of_mem_rightMoves hX2
          exact ⟨_, mem_right_tf.2 ⟨_, rightMoves_FF_left Y hX2, rfl⟩,
            ih X'' Y m m' (by omega) hle hY⟩
      · have hp := pot_lt_of_mem_leftMoves hY1
        rcases hY'.1 _ (mem_left_tf.2 ⟨Y', hY1, rfl⟩) with ⟨_, hle⟩ | ⟨y, hy, hle⟩
        · left
          have := ih X Y' m (m' - 1) (by omega) hX hle
          have e : m + (m' - 1) = m + m' - 1 := by omega
          rw [e] at this; exact this
        · right
          obtain ⟨Y'', hY2, rfl⟩ := mem_right_tf.1 hy
          have hp2 := pot_lt_of_mem_rightMoves hY2
          exact ⟨_, mem_right_tf.2 ⟨_, rightMoves_FF_right X hY2, rfl⟩,
            ih X Y'' m m' (by omega) hX hle⟩
    · by_cases hm : m < 0
      · obtain ⟨y, hy, hle⟩ := hX'.2 hm
        obtain ⟨X'', hX2, rfl⟩ := mem_right_tf.1 hy
        have hp2 := pot_lt_of_mem_rightMoves hX2
        have := ih X'' Y (m + 1) m' (by omega) hle hY
        have e : m + 1 + m' = m + m' + 1 := by omega
        rw [e] at this
        exact ⟨_, mem_right_tf.2 ⟨_, rightMoves_FF_left Y hX2, rfl⟩, this⟩
      · obtain ⟨y, hy, hle⟩ := hY'.2 (by omega)
        obtain ⟨Y'', hY2, rfl⟩ := mem_right_tf.1 hy
        have hp2 := pot_lt_of_mem_rightMoves hY2
        have := ih X Y'' m (m' + 1) (by omega) hX hle
        have e : m + (m' + 1) = m + m' + 1 := by omega
        rw [e] at this
        exact ⟨_, mem_right_tf.2 ⟨_, rightMoves_FF_right X hY2, rfl⟩, this⟩

/-- **Blocking Rule** for integer bounds: if `X ≤ m` and `Y ≤ m'` then `X FF Y ≤ m + m'`. -/
theorem blocking_rule : ∀ (X Y : List Cell) (m m' : Int),
    le (tf X) (zint m) → le (tf Y) (zint m') → le (tf (X ++ F :: F :: Y)) (zint (m + m')) :=
  fun X Y m m' hX hY => blocking_rule_aux (pot X + pot Y + 1) X Y m m' (by omega) hX hY

end Cgt
