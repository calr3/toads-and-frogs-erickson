import Cgt.DLP

/-!
# The family `Tᵃ □ Fᵃ` (`b = 1`)

Left's only move is `Tᵃ⁻¹□TFᵃ`; Right answers with the jump `Tᵃ⁻¹FT□Fᵃ⁻¹`. From there every
continuation is settled by the one-sided Death Leap Principle.
-/

namespace Cgt
open Cell TF Game

local notation "rep" => List.replicate

theorem leftMoves_rep_T_append_T (k : Nat) (r : List Cell) :
    leftMoves (rep k T ++ T :: r) = (leftMoves (T :: r)).map (rep k T ++ ·) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : rep (k + 1) T ++ T :: r = T :: T :: (rep k T ++ r) := by
      rw [List.replicate_succ, List.cons_append, replicate_append_cons_self]
    rw [e, leftMoves_T_T, ← replicate_append_cons_self, ih, List.map_map]
    apply List.map_congr_left
    intro q _
    simp [List.replicate_succ]

theorem leftMoves_rep_F (k : Nat) : leftMoves (rep k F) = [] := by
  have := leftMoves_replicate_F_append k []
  simpa using this

/-! ### Adjacency helpers -/

theorem adjOK_rep (R : Cell → Cell → Prop) (x : Cell) (hxx : R x x) :
    ∀ k, AdjOK R (rep k x)
  | 0 => trivial
  | 1 => trivial
  | k + 2 => by
    show R x x ∧ AdjOK R (rep (k + 1) x)
    exact ⟨hxx, adjOK_rep R x hxx (k + 1)⟩

theorem adjOK_cons_rep (R : Cell → Cell → Prop) (x y : Cell) (hxy : R x y) (hyy : R y y) :
    ∀ k, AdjOK R (x :: rep k y)
  | 0 => trivial
  | k + 1 => by
    show R x y ∧ AdjOK R (y :: rep k y)
    exact ⟨hxy, by simpa [List.replicate_succ] using adjOK_rep R y hyy (k + 1)⟩

theorem adjOK_rep_append (R : Cell → Cell → Prop) (x y : Cell) (r : List Cell)
    (hxx : R x x) (hxy : R x y) (h : AdjOK R (y :: r)) : ∀ k, AdjOK R (rep k x ++ y :: r)
  | 0 => h
  | k + 1 => by
    rw [adjOK_append_cons]
    refine ⟨adjOK_rep R x hxx (k + 1), fun z hz => ?_, h⟩
    rw [List.getLast?_replicate] at hz
    simp at hz
    rw [← hz]; exact hxy

/-! ### The positions -/

/-- `Tᶜ⁺¹□TFᶜ⁺²`, Left's only move from `Tᶜ⁺²□Fᶜ⁺²`. -/
def b1Q (c : Nat) : List Cell := rep (c + 1) T ++ E :: T :: rep (c + 2) F
/-- `Tᶜ⁺¹FT□Fᶜ⁺¹`, after Right's jump. -/
def b1P (c : Nat) : List Cell := rep (c + 1) T ++ F :: T :: E :: rep (c + 1) F
/-- `Tᶜ⁺¹F□TFᶜ⁺¹`, Left's only move from `b1P`. -/
def b1P2 (c : Nat) : List Cell := rep (c + 1) T ++ F :: E :: T :: rep (c + 1) F
/-- `Tᶜ⁺¹FTF□Fᶜ`, Right's answer to a Left pass in `b1P`. -/
def b1P3 (c : Nat) : List Cell := rep (c + 1) T ++ F :: T :: F :: E :: rep c F

theorem leftMoves_start_b1 (c : Nat) : leftMoves (start (c + 2) 1) = [b1Q c] := by
  have e : start (c + 2) 1 = rep (c + 1) T ++ T :: E :: rep (c + 2) F := by
    simp [start, List.replicate_succ' (n := c + 1), List.append_assoc]
  rw [e, leftMoves_rep_T_append_T, leftMoves_T_E, leftMoves_E, leftMoves_rep_F]
  simp [b1Q]

theorem b1P_mem (c : Nat) : b1P c ∈ rightMoves (b1Q c) := by
  rw [mem_rightMoves]
  right
  refine ⟨rep (c + 1) T, rep (c + 1) F, ?_, ?_⟩
  · simp [b1Q, List.replicate_succ]
  · simp [b1P]

theorem leftMoves_b1P (c : Nat) : leftMoves (b1P c) = [b1P2 c] := by
  have e : b1P c = rep c T ++ T :: F :: T :: E :: rep (c + 1) F := by
    simp [b1P, List.replicate_succ', List.append_assoc]
  rw [e, leftMoves_rep_T_append_T, leftMoves_T_F_T, leftMoves_F, leftMoves_T_E, leftMoves_E,
    leftMoves_rep_F]
  simp [b1P2, List.replicate_succ', List.append_assoc]

theorem b1P3_mem (c : Nat) : b1P3 c ∈ rightMoves (b1P c) := by
  rw [mem_rightMoves]
  left
  refine ⟨rep (c + 1) T ++ [F, T], rep c F, ?_, ?_⟩
  · simp [b1P, List.replicate_succ, List.append_assoc]
  · simp [b1P3, List.append_assoc]

theorem dlp_b1P2 (c : Nat) : DLPCond (b1P2 c) := by
  constructor
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    show NoTE F E ∧ (NoTE E T ∧ AdjOK NoTE (T :: rep (c + 1) F))
    exact ⟨by decide, by decide, adjOK_cons_rep _ T F (by decide) (by decide) _⟩
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    show NoEE F E ∧ (NoEE E T ∧ AdjOK NoEE (T :: rep (c + 1) F))
    exact ⟨by decide, by decide, adjOK_cons_rep _ T F (by decide) (by decide) _⟩

theorem dlp_b1P3 (c : Nat) : DLPCond (b1P3 c) := by
  constructor
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    show NoTE F T ∧ (NoTE T F ∧ (NoTE F E ∧ AdjOK NoTE (E :: rep c F)))
    exact ⟨by decide, by decide, by decide, adjOK_cons_rep _ E F (by decide) (by decide) _⟩
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    show NoEE F T ∧ (NoEE T F ∧ (NoEE F E ∧ AdjOK NoEE (E :: rep c F)))
    exact ⟨by decide, by decide, by decide, adjOK_cons_rep _ E F (by decide) (by decide) _⟩

theorem upperZero_b1P (c : Nat) : UpperZero (tf (b1P c)) := by
  rw [upperZero_tf_iff, lfZero_tf_iff, leftMoves_b1P]
  refine ⟨Or.inr ⟨b1P3 c, b1P3_mem c, upperZero_of_le_zero (le_zero_of_dlp _ (dlp_b1P3 c))⟩, ?_⟩
  simp only [List.mem_singleton, forall_eq]
  rw [lfZero_tf_iff]
  exact Or.inl (le_zero_of_dlp _ (dlp_b1P2 c))

/-- **The case `b = 1`**: `Tᵃ □ Fᵃ` is infinitesimal for every `a`. -/
theorem infinitesimal_start_b_one (a : Nat) : Infinitesimal (tf (start a 1)) := by
  match a with
  | 0 => exact infinitesimal_start_a_zero 1
  | 1 => exact infinitesimal_start_one 1
  | c + 2 =>
    rw [infinitesimal_start_iff, upperZero_tf_iff, leftMoves_start_b1]
    refine ⟨lfZero_of_mirror (mirror_start _ _), ?_⟩
    simp only [List.mem_singleton, forall_eq]
    rw [lfZero_tf_iff]
    exact Or.inr ⟨b1P c, b1P_mem c, upperZero_b1P c⟩

end Cgt
