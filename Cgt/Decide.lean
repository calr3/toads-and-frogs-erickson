import Cgt.ToadsFrogs

/-!
# Deciding stops of concrete Toads and Frogs positions

Fuel-based (hence kernel-reducible) evaluators for

* `tf p ≤ 0`               (`leZeroB`),
* `Game.LfZero (tf p)`     (`lfZeroB`, Right stop `≤ 0`),
* `Game.UpperZero (tf p)`  (`upperZeroB`, Left stop `≤ 0`),

together with soundness theorems. These let `decide` settle individual positions.
-/

namespace Cgt
open Cell TF Game

/-- `leZeroB n p` decides `tf p ≤ 0` provided `pot p < n`. -/
def leZeroB : Nat → List Cell → Bool
  | 0, _ => false
  | n + 1, p => (leftMoves p).all fun q => (rightMoves q).any fun q' => leZeroB n q'

/-- `stopB n p = (u, r)` where `u` decides the Left stop `≤ 0` and `r` the Right stop `≤ 0`
predicate of `tf p`, provided `pot p < n`. Defined by structural recursion on the fuel. -/
def stopB : Nat → List Cell → Bool × Bool
  | 0, _ => (false, false)
  | n + 1, p =>
    let r := leZeroB (n + 1) p || (rightMoves p).any fun q => (stopB n q).1
    (r && (leftMoves p).all fun q => (stopB n q).2, r)

theorem le_zero_iff_tf (p : List Cell) :
    le (tf p) zero ↔ ∀ q ∈ leftMoves p, ∃ q' ∈ rightMoves q, le (tf q') zero := by
  rw [le_iff]
  simp only [zero, right_mk, List.not_mem_nil, false_implies, imp_false, implies_true, and_true]
  constructor
  · intro h q hq
    have := h (tf q) (mem_left_tf.2 ⟨q, hq, rfl⟩)
    rw [le_iff] at this
    apply Classical.byContradiction
    intro hne
    apply this
    refine ⟨fun x hx => by simp [zero] at hx, fun y hy hle => ?_⟩
    obtain ⟨q', hq', rfl⟩ := mem_right_tf.1 hy
    exact hne ⟨q', hq', hle⟩
  · intro h x hx hle
    obtain ⟨q, hq, rfl⟩ := mem_left_tf.1 hx
    obtain ⟨q', hq', hle'⟩ := h q hq
    rw [le_iff] at hle
    exact hle.2 (tf q') (mem_right_tf.2 ⟨q', hq', rfl⟩) hle'

theorem leZeroB_iff : ∀ (n : Nat) (p : List Cell), pot p < n → (leZeroB n p = true ↔ le (tf p) zero)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, p, h => by
    rw [le_zero_iff_tf, leZeroB]
    simp only [List.all_eq_true, List.any_eq_true]
    constructor
    · intro H q hq
      obtain ⟨q', hq', hb⟩ := H q hq
      have h1 := pot_lt_of_mem_leftMoves hq
      have h2 := pot_lt_of_mem_rightMoves hq'
      exact ⟨q', hq', (leZeroB_iff n q' (by omega)).1 hb⟩
    · intro H q hq
      obtain ⟨q', hq', hle⟩ := H q hq
      have h1 := pot_lt_of_mem_leftMoves hq
      have h2 := pot_lt_of_mem_rightMoves hq'
      exact ⟨q', hq', (leZeroB_iff n q' (by omega)).2 hle⟩

theorem upperZero_tf_iff (p : List Cell) :
    UpperZero (tf p) ↔ LfZero (tf p) ∧ ∀ q ∈ leftMoves p, LfZero (tf q) := by
  rw [upperZero_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun q hq => h2 _ (mem_left_tf.2 ⟨q, hq, rfl⟩)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun x hx => ?_⟩
    obtain ⟨q, hq, rfl⟩ := mem_left_tf.1 hx
    exact h2 q hq

theorem lfZero_tf_iff (p : List Cell) :
    LfZero (tf p) ↔ le (tf p) zero ∨ ∃ q ∈ rightMoves p, UpperZero (tf q) := by
  rw [lfZero_iff]
  constructor
  · rintro (h | ⟨y, hy, hu⟩)
    · exact Or.inl h
    · obtain ⟨q, hq, rfl⟩ := mem_right_tf.1 hy
      exact Or.inr ⟨q, hq, hu⟩
  · rintro (h | ⟨q, hq, hu⟩)
    · exact Or.inl h
    · exact Or.inr ⟨tf q, mem_right_tf.2 ⟨q, hq, rfl⟩, hu⟩

theorem stopB_iff : ∀ (n : Nat) (p : List Cell), pot p < n →
    ((stopB n p).1 = true ↔ UpperZero (tf p)) ∧ ((stopB n p).2 = true ↔ LfZero (tf p))
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, p, h => by
    have hr : (leZeroB (n + 1) p || (rightMoves p).any fun q => (stopB n q).1) = true ↔
        LfZero (tf p) := by
      simp only [Bool.or_eq_true, List.any_eq_true]
      rw [lfZero_tf_iff, leZeroB_iff (n + 1) p h]
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨q, hq, hb⟩
        have := pot_lt_of_mem_rightMoves hq
        exact ⟨q, hq, ((stopB_iff n q (by omega)).1).1 hb⟩
      · rintro ⟨q, hq, hu⟩
        have := pot_lt_of_mem_rightMoves hq
        exact ⟨q, hq, ((stopB_iff n q (by omega)).1).2 hu⟩
    refine ⟨?_, hr⟩
    simp only [stopB, Bool.and_eq_true, List.all_eq_true]
    rw [hr, upperZero_tf_iff]
    apply and_congr Iff.rfl
    constructor
    · intro H q hq
      have := pot_lt_of_mem_leftMoves hq
      exact ((stopB_iff n q (by omega)).2).1 (H q hq)
    · intro H q hq
      have := pot_lt_of_mem_leftMoves hq
      exact ((stopB_iff n q (by omega)).2).2 (H q hq)

/-- Decide whether the starting position `Tᵃ □ᵇ Fᵃ` is infinitesimal. -/
def startInfinitesimalB (a b : Nat) : Bool :=
  (stopB (pot (start a b) + 1) (start a b)).1

theorem infinitesimal_start_of_decide {a b : Nat} (h : startInfinitesimalB a b = true) :
    Infinitesimal (tf (start a b)) := by
  rw [infinitesimal_start_iff]
  exact ((stopB_iff _ (start a b) (Nat.lt_succ_self _)).1).1 h

theorem not_infinitesimal_start_of_decide {a b : Nat} (h : startInfinitesimalB a b = false) :
    ¬ Infinitesimal (tf (start a b)) := by
  rw [infinitesimal_start_iff]
  intro hu
  have := ((stopB_iff _ (start a b) (Nat.lt_succ_self _)).1).2 hu
  rw [startInfinitesimalB] at h
  rw [h] at this
  exact Bool.false_ne_true this

end Cgt
