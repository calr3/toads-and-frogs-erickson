import Cgt.FamilyA1

/-!
# Strategy certificates

Helper lemmas for machine-generated proofs: a proof for a position is given by explicit
Right replies to each Left move, checked by `decide`, plus proofs for the replies.
-/

namespace Cgt
open Cell TF Game

/-- `AllL P l` : `P` holds for every element of `l` (unfolds to a chain of `∧`). -/
def AllL {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | x :: l => P x ∧ AllL P l

theorem AllL.mem {α : Type} {P : α → Prop} : ∀ {l : List α}, AllL P l → ∀ x ∈ l, P x
  | [], _, _, hx => by simp at hx
  | y :: l, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact AllL.mem h.2 x hx

/-- `tf p ≤ 0` from explicit replies `(q, r)` to every Left move `q`. -/
theorem le_zero_of_pairs (p : List Cell) (pairs : List (List Cell × List Cell))
    (hcov : ((leftMoves p).all fun q => pairs.any fun x => x.1 == q) = true)
    (hmove : (pairs.all fun x => (rightMoves x.1).contains x.2) = true)
    (hrec : AllL (fun x => le (tf x.2) zero) pairs) : le (tf p) zero := by
  rw [le_zero_iff_tf]
  intro q hq
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq] at hcov
  obtain ⟨x, hx, rfl⟩ := hcov q hq
  simp only [List.all_eq_true, List.contains_iff_mem] at hmove
  exact ⟨x.2, hmove x hx, AllL.mem hrec x hx⟩

/-- Left stop `≤ 0` from: a proof of `LfZero` for `p`, and for each Left move either a proof
that it is `≤ 0` (Right passes) or an explicit Right reply with Left stop `≤ 0`. -/
theorem upperZero_of_pairs (p : List Cell) (hlf : LfZero (tf p)) (passes : List (List Cell))
    (pairs : List (List Cell × List Cell))
    (hcov : ((leftMoves p).all fun q => passes.contains q || pairs.any fun x => x.1 == q) = true)
    (hmove : (pairs.all fun x => (rightMoves x.1).contains x.2) = true)
    (hpass : AllL (fun q => le (tf q) zero) passes)
    (hrec : AllL (fun x => UpperZero (tf x.2)) pairs) : UpperZero (tf p) := by
  rw [upperZero_tf_iff]
  refine ⟨hlf, fun q hq => ?_⟩
  simp only [List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
    beq_iff_eq] at hcov
  rw [lfZero_tf_iff]
  rcases hcov q hq with h | ⟨x, hx, rfl⟩
  · exact Or.inl (AllL.mem hpass q h)
  · simp only [List.all_eq_true, List.contains_iff_mem] at hmove
    exact Or.inr ⟨x.2, hmove x hx, AllL.mem hrec x hx⟩

/-- `LfZero` via an explicit Right move. -/
theorem lfZero_of_reply (p r : List Cell) (h : (rightMoves p).contains r = true)
    (hr : UpperZero (tf r)) : LfZero (tf p) := by
  rw [lfZero_tf_iff]
  exact Or.inr ⟨r, by simpa [List.contains_iff_mem] using h, hr⟩

/-- `LfZero` of a mirror-symmetric position, checked by `decide`. -/
theorem lfZero_of_mirror_dec (p : List Cell) (h : (mirror p == p) = true) : LfZero (tf p) :=
  lfZero_of_mirror (by simpa using h)

end Cgt
