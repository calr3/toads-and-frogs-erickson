import Cgt.Basic

/-!
# The one-sided Death Leap Principle

**Lemma (Thanatipanonda).** If no toad can slide (there is no `T□`) and there are no two
consecutive empty squares (no `□□`), then the position is `≤ 0`: Right, moving second, wins.

Indeed, every Left move is then a jump `TF□ → □FT`, which Right answers by sliding the jumped
frog into the vacated square, `□FT → F□T`; both properties are preserved.
-/

namespace Cgt
open Cell TF Game

/-- `AdjOK R p` : every pair of adjacent cells `(x, y)` of `p` satisfies `R x y`. -/
def AdjOK (R : Cell → Cell → Prop) : List Cell → Prop
  | [] => True
  | [_] => True
  | x :: y :: r => R x y ∧ AdjOK R (y :: r)

theorem AdjOK.tail {R : Cell → Cell → Prop} {x : Cell} {r : List Cell} (h : AdjOK R (x :: r)) :
    AdjOK R r := by
  cases r with
  | nil => trivial
  | cons y r => exact h.2

theorem adjOK_cons_cons {R : Cell → Cell → Prop} {x y : Cell} {r : List Cell} :
    AdjOK R (x :: y :: r) ↔ R x y ∧ AdjOK R (y :: r) := Iff.rfl

/-- Adjacency condition on `u ++ v` where `v = y :: r` is nonempty. -/
theorem adjOK_append_cons {R : Cell → Cell → Prop} :
    ∀ (u : List Cell) (y : Cell) (r : List Cell),
      AdjOK R (u ++ y :: r) ↔
        AdjOK R u ∧ (∀ x, u.getLast? = some x → R x y) ∧ AdjOK R (y :: r)
  | [], y, r => by simp [AdjOK]
  | [x], y, r => by simp [AdjOK]
  | x :: x' :: u, y, r => by
    have ih := adjOK_append_cons (R := R) (x' :: u) y r
    simp only [List.cons_append] at ih ⊢
    rw [adjOK_cons_cons, ih, adjOK_cons_cons]
    simp only [List.getLast?_cons_cons]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨h1, h2, h3, h4⟩

/-- No toad can slide. -/
def NoTE (x y : Cell) : Prop := ¬ (x = T ∧ y = E)
/-- No two consecutive empty squares. -/
def NoEE (x y : Cell) : Prop := ¬ (x = E ∧ y = E)

instance (x y : Cell) : Decidable (NoTE x y) := by unfold NoTE; infer_instance
instance (x y : Cell) : Decidable (NoEE x y) := by unfold NoEE; infer_instance

def DLPCond (p : List Cell) : Prop := AdjOK NoTE p ∧ AdjOK NoEE p

theorem dlp_no_slide {u r : List Cell} (h : AdjOK NoTE (u ++ T :: E :: r)) : False := by
  rw [adjOK_append_cons] at h
  exact h.2.2.1 ⟨rfl, rfl⟩

/-- Key step: after a jump answered by the refill, the conditions still hold. -/
theorem dlp_step {u r : List Cell} (h : DLPCond (u ++ T :: F :: E :: r)) :
    DLPCond (u ++ F :: E :: T :: r) := by
  obtain ⟨h1, h2⟩ := h
  rw [adjOK_append_cons] at h1 h2
  obtain ⟨h1u, -, h1r⟩ := h1
  obtain ⟨h2u, -, h2r⟩ := h2
  have h1r' : AdjOK NoTE (E :: r) := h1r.tail.tail
  have h2r' : AdjOK NoEE (E :: r) := h2r.tail.tail
  constructor
  · rw [adjOK_append_cons]
    refine ⟨h1u, (fun x _ hx => nomatch hx.2), ?_⟩
    show NoTE F E ∧ (NoTE E T ∧ AdjOK NoTE (T :: r))
    refine ⟨(fun hx => nomatch hx.1), (fun hx => nomatch hx.1), ?_⟩
    cases r with
    | nil => trivial
    | cons z r =>
      show NoTE T z ∧ AdjOK NoTE (z :: r)
      exact ⟨fun hz => h2r'.1 ⟨rfl, hz.2⟩, h1r'.tail⟩
  · rw [adjOK_append_cons]
    refine ⟨h2u, (fun x _ hx => nomatch hx.2), ?_⟩
    show NoEE F E ∧ (NoEE E T ∧ AdjOK NoEE (T :: r))
    refine ⟨(fun hx => nomatch hx.1), (fun hx => nomatch hx.2), ?_⟩
    cases r with
    | nil => trivial
    | cons z r =>
      show NoEE T z ∧ AdjOK NoEE (z :: r)
      exact ⟨(fun hz => nomatch hz.1), h2r'.tail⟩

theorem le_zero_of_dlp (p : List Cell) (h : DLPCond p) : le (tf p) zero := by
  induction hn : pot p using Nat.strongRecOn generalizing p with
  | _ n ih =>
  rw [le_zero_iff_tf]
  intro q hq
  rcases mem_leftMoves.1 hq with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩
  · exact (dlp_no_slide h.1).elim
  · refine ⟨u ++ F :: E :: T :: r, ?_, ?_⟩
    · rw [mem_rightMoves]
      left
      exact ⟨u, T :: r, by simp, by simp⟩
    · apply ih _ _ _ (dlp_step h) rfl
      have h1 := pot_lt_of_mem_leftMoves hq
      have h2 : pot (u ++ F :: E :: T :: r) < pot (u ++ E :: F :: T :: r) :=
        pot_lt_of_mem_rightMoves (mem_rightMoves.2 (Or.inl ⟨u, T :: r, by simp, by simp⟩))
      omega

/-- A position that is `≤ 0` has Left stop `≤ 0`. -/
theorem upperZero_of_le_zero {g : Game} (h : le g zero) : UpperZero g :=
  fun n => le_trans _ _ _ h (zero_le_powHalf n)

end Cgt
