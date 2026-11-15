import Cgt.Moves

/-!
# The family `T □ᵇ F` (`a = 1`)

Every position `T □ᵇ F` is infinitesimal (its value is `0` or `*`).
-/

namespace Cgt
open Cell TF Game

local notation "Es" => List.replicate

theorem replicate_append_cons_self {α : Type} (c : α) (y : Nat) (r : List α) :
    List.replicate y c ++ c :: r = c :: (List.replicate y c ++ r) := by
  induction y with
  | zero => rfl
  | succ y ih => simp [List.replicate_succ, ih]

/-- `□ⁱ T □ʲ F □ᵏ`. -/
def pos1 (i j k : Nat) : List Cell := Es i E ++ T :: Es j E ++ F :: Es k E

/-- `□ˣ F □ʸ T □ᶻ`: the toad and frog have crossed. -/
def cross1 (x y z : Nat) : List Cell := Es x E ++ F :: Es y E ++ T :: Es z E

theorem leftMoves_cross1_zero (x y : Nat) : leftMoves (cross1 x y 0) = [] := by
  simp [cross1, leftMoves_replicate_E_append, List.replicate_succ]

theorem leftMoves_cross1_succ (x y z : Nat) :
    leftMoves (cross1 x y (z + 1)) = [cross1 x (y + 1) z] := by
  simp [cross1, leftMoves_replicate_E_append, List.replicate_succ, leftMoves_replicate_E,
    replicate_append_cons_self]

theorem cross1_mem_rightMoves (x y z : Nat) :
    cross1 x (y + 1) z ∈ rightMoves (cross1 (x + 1) y z) := by
  rw [mem_rightMoves]
  left
  refine ⟨Es x E, Es y E ++ T :: Es z E, ?_, ?_⟩
  · simp [cross1, List.replicate_succ']
  · simp [cross1, List.replicate_succ]

/-- After crossing, the position is the integer `z - x`; in particular it is `≤ 0` if `z ≤ x`. -/
theorem cross1_le_zero : ∀ (z x y : Nat), z ≤ x → le (tf (cross1 x y z)) zero
  | 0, x, y, _ => by
    rw [le_zero_iff_tf, leftMoves_cross1_zero]
    simp
  | z + 1, x, y, h => by
    rw [le_zero_iff_tf, leftMoves_cross1_succ]
    simp only [List.mem_singleton, forall_eq]
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
    exact ⟨_, cross1_mem_rightMoves x' (y + 1) z, cross1_le_zero z x' (y + 2) (by omega)⟩

theorem leftMoves_pos1_succ (i j k : Nat) : leftMoves (pos1 i (j + 1) k) = [pos1 (i + 1) j k] := by
  simp [pos1, leftMoves_replicate_E_append, List.replicate_succ, leftMoves_replicate_E,
    replicate_append_cons_self]

theorem leftMoves_pos1_zero_zero (i : Nat) : leftMoves (pos1 i 0 0) = [] := by
  simp [pos1, leftMoves_replicate_E_append]

theorem leftMoves_pos1_zero_succ (i k : Nat) :
    leftMoves (pos1 i 0 (k + 1)) = [cross1 (i + 1) 0 k] := by
  simp [pos1, cross1, leftMoves_replicate_E_append, List.replicate_succ, leftMoves_replicate_E,
    replicate_append_cons_self]

theorem pos1_mem_rightMoves (i j k : Nat) : pos1 i j (k + 1) ∈ rightMoves (pos1 i (j + 1) k) := by
  rw [mem_rightMoves]
  left
  refine ⟨Es i E ++ T :: Es j E, Es k E, ?_, ?_⟩
  · simp [pos1, List.replicate_succ']
  · simp [pos1, List.replicate_succ]

theorem cross1_mem_rightMoves' (i k : Nat) :
    cross1 i 1 k ∈ rightMoves (cross1 (i + 1) 0 k) := cross1_mem_rightMoves i 0 k

theorem mirror_replicate_E (i : Nat) : mirror (Es i E) = Es i E := by
  simp [mirror, List.map_replicate, List.reverse_replicate]

theorem mirror_pos1 (i j : Nat) : mirror (pos1 i j i) = pos1 i j i := by
  simp [pos1, mirror_replicate_E, List.append_assoc]

/-- A mirror-symmetric position has Right stop `≤ 0`. -/
theorem lfZero_of_mirror {p : List Cell} (hp : mirror p = p) : LfZero (tf p) := by
  apply lfZero_of_equiv_neg
  have e := tf_mirror p
  rw [hp] at e
  exact e.symm

/-- `□ⁱ T □ʲ F □ⁱ` has Left stop `≤ 0`. -/
theorem upperZero_pos1 : ∀ (j i : Nat), UpperZero (tf (pos1 i j i))
  | 0, i => by
    rw [upperZero_tf_iff]
    refine ⟨lfZero_of_mirror (mirror_pos1 i 0), ?_⟩
    cases i with
    | zero => simp [leftMoves_pos1_zero_zero]
    | succ i =>
      rw [leftMoves_pos1_zero_succ]
      simp only [List.mem_singleton, forall_eq]
      rw [lfZero_tf_iff]
      exact Or.inl (cross1_le_zero _ _ _ (by omega))
  | 1, i => by
    rw [upperZero_tf_iff]
    refine ⟨lfZero_of_mirror (mirror_pos1 i 1), ?_⟩
    rw [leftMoves_pos1_succ]
    simp only [List.mem_singleton, forall_eq]
    rw [lfZero_tf_iff]
    left
    cases i with
    | zero =>
      rw [le_zero_iff_tf, leftMoves_pos1_zero_zero]; simp
    | succ i =>
      rw [le_zero_iff_tf, leftMoves_pos1_zero_succ]
      simp only [List.mem_singleton, forall_eq]
      exact ⟨_, cross1_mem_rightMoves' (i + 2) i, cross1_le_zero i (i + 2) 1 (by omega)⟩
  | j + 2, i => by
    rw [upperZero_tf_iff]
    refine ⟨lfZero_of_mirror (mirror_pos1 i (j + 2)), ?_⟩
    rw [leftMoves_pos1_succ]
    simp only [List.mem_singleton, forall_eq]
    rw [lfZero_tf_iff]
    exact Or.inr ⟨_, pos1_mem_rightMoves (i + 1) j i, upperZero_pos1 j (i + 1)⟩

theorem start_one (b : Nat) : start 1 b = pos1 0 b 0 := by
  simp [start, pos1]

/-- **The case `a = 1`**: `T □ᵇ F` is infinitesimal for every `b`. -/
theorem infinitesimal_start_one (b : Nat) : Infinitesimal (tf (start 1 b)) := by
  rw [infinitesimal_start_iff, start_one]
  exact upperZero_pos1 b 0

end Cgt
