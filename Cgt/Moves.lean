import Cgt.Decide

/-!
# Symbolic computation of moves

Simp lemmas computing `leftMoves` / `rightMoves` on positions given by explicit heads and
blocks of empty squares, for symbolic reasoning about infinite families of positions.
-/

namespace Cgt
namespace TF
open Cell

@[simp] theorem leftMoves_nil : leftMoves [] = [] := rfl
@[simp] theorem leftMoves_E (r : List Cell) : leftMoves (E :: r) = (leftMoves r).map (E :: ·) := by
  simp [leftMoves]
@[simp] theorem leftMoves_F (r : List Cell) : leftMoves (F :: r) = (leftMoves r).map (F :: ·) := by
  simp [leftMoves]
@[simp] theorem leftMoves_T_nil : leftMoves [T] = [] := rfl
@[simp] theorem leftMoves_T_E (r : List Cell) :
    leftMoves (T :: E :: r) = (E :: T :: r) :: (leftMoves (E :: r)).map (T :: ·) := by
  simp [leftMoves]
@[simp] theorem leftMoves_T_T (r : List Cell) :
    leftMoves (T :: T :: r) = (leftMoves (T :: r)).map (T :: ·) := by
  simp [leftMoves]
@[simp] theorem leftMoves_T_F_nil : leftMoves [T, F] = [] := rfl
@[simp] theorem leftMoves_T_F_E (r : List Cell) :
    leftMoves (T :: F :: E :: r) = (E :: F :: T :: r) :: (leftMoves (F :: E :: r)).map (T :: ·) := by
  simp [leftMoves]
@[simp] theorem leftMoves_T_F_T (r : List Cell) :
    leftMoves (T :: F :: T :: r) = (leftMoves (F :: T :: r)).map (T :: ·) := by
  simp [leftMoves]
@[simp] theorem leftMoves_T_F_F (r : List Cell) :
    leftMoves (T :: F :: F :: r) = (leftMoves (F :: F :: r)).map (T :: ·) := by
  simp [leftMoves]

@[simp] theorem rightMoves_nil : rightMoves [] = [] := rfl
@[simp] theorem rightMoves_T (r : List Cell) : rightMoves (T :: r) = (rightMoves r).map (T :: ·) := by
  simp [rightMoves]
@[simp] theorem rightMoves_F (r : List Cell) : rightMoves (F :: r) = (rightMoves r).map (F :: ·) := by
  simp [rightMoves]
@[simp] theorem rightMoves_E_nil : rightMoves [E] = [] := rfl
@[simp] theorem rightMoves_E_F (r : List Cell) :
    rightMoves (E :: F :: r) = (F :: E :: r) :: (rightMoves (F :: r)).map (E :: ·) := by
  simp [rightMoves]
@[simp] theorem rightMoves_E_E (r : List Cell) :
    rightMoves (E :: E :: r) = (rightMoves (E :: r)).map (E :: ·) := by
  simp [rightMoves]
@[simp] theorem rightMoves_E_T_nil : rightMoves [E, T] = [] := rfl
@[simp] theorem rightMoves_E_T_F (r : List Cell) :
    rightMoves (E :: T :: F :: r) = (F :: T :: E :: r) :: (rightMoves (T :: F :: r)).map (E :: ·) := by
  simp [rightMoves]
@[simp] theorem rightMoves_E_T_T (r : List Cell) :
    rightMoves (E :: T :: T :: r) = (rightMoves (T :: T :: r)).map (E :: ·) := by
  simp [rightMoves]
@[simp] theorem rightMoves_E_T_E (r : List Cell) :
    rightMoves (E :: T :: E :: r) = (rightMoves (T :: E :: r)).map (E :: ·) := by
  simp [rightMoves]

theorem leftMoves_replicate_E (i : Nat) : leftMoves (List.replicate i E) = [] := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, ih]

theorem leftMoves_replicate_E_append (i : Nat) (r : List Cell) :
    leftMoves (List.replicate i E ++ r) = (leftMoves r).map (List.replicate i E ++ ·) := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp [List.replicate_succ, ih, List.map_map, Function.comp_def]

theorem rightMoves_replicate_E (i : Nat) : rightMoves (List.replicate i E) = [] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.replicate_succ, List.replicate_succ, rightMoves_E_E, ← List.replicate_succ, ih]
      rfl

theorem rightMoves_replicate_T_append (i : Nat) (r : List Cell) :
    rightMoves (List.replicate i T ++ r) = (rightMoves r).map (List.replicate i T ++ ·) := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp [List.replicate_succ, ih, List.map_map, Function.comp_def]

theorem leftMoves_replicate_F_append (i : Nat) (r : List Cell) :
    leftMoves (List.replicate i F ++ r) = (leftMoves r).map (List.replicate i F ++ ·) := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp [List.replicate_succ, ih, List.map_map, Function.comp_def]

theorem rightMoves_replicate_F (i : Nat) : rightMoves (List.replicate i F) = [] := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, ih]

theorem leftMoves_replicate_T (i : Nat) : leftMoves (List.replicate i T) = [] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    cases i with
    | zero => rfl
    | succ i =>
      rw [List.replicate_succ, List.replicate_succ, leftMoves_T_T, ← List.replicate_succ, ih]
      rfl

end TF
end Cgt
