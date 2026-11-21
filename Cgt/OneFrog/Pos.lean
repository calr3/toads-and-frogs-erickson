import Cgt.Moves

/-!
# One-frog positions

Positions with exactly one frog, written as a zipper around the frog, together with the
counting statistics used to evaluate them.
-/

namespace Cgt
namespace OneFrog

open Cell TF

def cell : Bool → Cell
  | true => T
  | false => E

/-- The position with squares `L` to the left of the frog (nearest first) and `B` to its right. -/
def pos (L B : List Bool) : List Cell := (L.map cell).reverse ++ F :: B.map cell

/-- Number of toads / of empty squares. -/
def cT : List Bool → Nat
  | [] => 0
  | true :: X => cT X + 1
  | false :: X => cT X
def cE : List Bool → Nat
  | [] => 0
  | true :: X => cE X
  | false :: X => cE X + 1

/-- For a left side: sum over toads of the empty squares between it and the frog. -/
def invL : List Bool → Nat
  | [] => 0
  | true :: X => invL X
  | false :: X => invL X + cT X
/-- For a right side: sum over toads of the empty squares to its right. -/
def invB : List Bool → Nat
  | [] => 0
  | true :: X => invB X + cE X
  | false :: X => invB X

/-- Left's moves minus Right's moves if every toad left of the frog jumps it. -/
def phi (L B : List Bool) : Int :=
  ((invL L + invB B + cT L * cE B : Nat) : Int) - ((cT L + cE L : Nat) : Int)

/-- Empty squares between the frog and the nearest toad on its left. -/
def gap : List Bool → Nat
  | false :: X => gap X + 1
  | _ => 0
/-- Empty squares to the left of the nearest toad on the frog's left (0 if there is none). -/
def behind : List Bool → Nat
  | false :: X => behind X
  | true :: X => cE X
  | [] => 0

@[simp] theorem gap_nil : gap [] = 0 := rfl
@[simp] theorem gap_true (X : List Bool) : gap (true :: X) = 0 := rfl
@[simp] theorem gap_false (X : List Bool) : gap (false :: X) = gap X + 1 := rfl

/-! ### Counting -/

theorem cT_append (X Y : List Bool) : cT (X ++ Y) = cT X + cT Y := by
  induction X with
  | nil => simp [cT]
  | cons a X ih => cases a <;> simp [cT, ih] <;> omega

theorem cE_append (X Y : List Bool) : cE (X ++ Y) = cE X + cE Y := by
  induction X with
  | nil => simp [cE]
  | cons a X ih => cases a <;> simp [cE, ih] <;> omega

theorem cT_replicate_true (i : Nat) : cT (List.replicate i true) = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, cT, ih]

theorem cT_replicate_false (i : Nat) : cT (List.replicate i false) = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, cT, ih]

theorem cE_replicate_true (i : Nat) : cE (List.replicate i true) = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, cE, ih]

theorem cE_replicate_false (i : Nat) : cE (List.replicate i false) = i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, cE, ih]

/-! ### Moves -/

@[simp] theorem cell_ne_F (a : Bool) : cell a ≠ F := by cases a <;> simp [cell]
@[simp] theorem cell_eq_T (a : Bool) : cell a = T ↔ a = true := by cases a <;> simp [cell]
@[simp] theorem cell_eq_E (a : Bool) : cell a = E ↔ a = false := by cases a <;> simp [cell]

theorem F_not_mem_map (L : List Bool) : F ∉ L.map cell := by
  simp

theorem F_not_mem_rev (L : List Bool) : F ∉ (L.map cell).reverse := by
  simp

theorem map_cell_cons {L : List Bool} {c : Cell} {Z : List Cell} (h : L.map cell = c :: Z) :
    ∃ a L', L = a :: L' ∧ cell a = c ∧ L'.map cell = Z := by
  cases L with
  | nil => simp at h
  | cons a L' =>
    simp only [List.map_cons, List.cons.injEq] at h
    exact ⟨a, L', rfl, h.1, h.2⟩

theorem map_cell_append {L : List Bool} {Z₁ Z₂ : List Cell} (h : L.map cell = Z₁ ++ Z₂) :
    ∃ a b, L = a ++ b ∧ a.map cell = Z₁ ∧ b.map cell = Z₂ :=
  List.map_eq_append_iff.1 h

theorem rev_map_eq {L : List Bool} {Z : List Cell} (h : (L.map cell).reverse = Z) :
    L.map cell = Z.reverse := by
  rw [← h, List.reverse_reverse]

/-- Locating a non-frog cell in a list with a distinguished frog. -/
theorem split_at_F {X Y u v : List Cell} {c : Cell} (hc : c ≠ F)
    (h : X ++ F :: Y = u ++ c :: v) :
    (∃ w, u = X ++ F :: w ∧ Y = w ++ c :: v) ∨ (∃ w, X = u ++ c :: w ∧ v = w ++ F :: Y) := by
  induction X generalizing u with
  | nil =>
    cases u with
    | nil => simp at h; exact absurd h.1.symm hc
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

theorem mem_leftMoves_pos {L B : List Bool} {q : List Cell} :
    q ∈ leftMoves (pos L B) ↔
      (∃ u r, L = u ++ false :: true :: r ∧ q = pos (u ++ true :: false :: r) B) ∨
      (∃ u r, B = u ++ true :: false :: r ∧ q = pos L (u ++ false :: true :: r)) ∨
      (∃ L' B', L = true :: L' ∧ B = false :: B' ∧ q = pos (false :: L') (true :: B')) := by
  rw [mem_leftMoves]
  constructor
  · rintro (⟨u, r, hp, rfl⟩ | ⟨u, r, hp, rfl⟩)
    · rcases split_at_F (by decide) hp with ⟨w, rfl, hY⟩ | ⟨w, hX, hr⟩
      · right; left
        obtain ⟨a, b, rfl, ha, hb⟩ := map_cell_append hY
        obtain ⟨x, b, rfl, hx, hb1⟩ := map_cell_cons hb
        obtain ⟨y, b, rfl, hy, hb2⟩ := map_cell_cons hb1
        simp at hx hy; subst hx hy ha hb2
        refine ⟨a, b, rfl, ?_⟩
        simp [pos, cell]
      · cases w with
        | nil => simp at hr
        | cons e w =>
          simp at hr
          obtain ⟨rfl, rfl⟩ := hr
          left
          have h := rev_map_eq hX
          simp at h
          obtain ⟨a, b, rfl, ha, hb⟩ := map_cell_append h
          obtain ⟨x, b, rfl, hx, hb1⟩ := map_cell_cons hb
          obtain ⟨y, b, rfl, hy, hb2⟩ := map_cell_cons hb1
          simp at hx hy; subst hx hy
          have ha' := congrArg List.reverse ha
          have hb' := congrArg List.reverse hb2
          simp only [List.reverse_reverse] at ha' hb'
          subst ha' hb'
          refine ⟨a, b, rfl, ?_⟩
          simp [pos, cell]
    · rcases split_at_F (by decide) hp with ⟨w, rfl, hY⟩ | ⟨w, hX, hr⟩
      · exfalso
        have : F ∈ B.map cell := by rw [hY]; simp
        exact F_not_mem_map B this
      · cases w with
        | nil =>
          simp at hr
          right; right
          have h := rev_map_eq hX
          simp at h
          obtain ⟨x, L', rfl, hx, hL⟩ := map_cell_cons h
          obtain ⟨y, B', rfl, hy, hB⟩ := map_cell_cons hr.symm
          simp at hx hy; subst hx hy hB
          have hL' := congrArg List.reverse hL
          simp only [List.reverse_reverse] at hL'
          subst hL'
          refine ⟨L', B', rfl, rfl, ?_⟩
          simp [pos, cell]
        | cons e w =>
          exfalso
          simp at hr
          obtain ⟨rfl, -⟩ := hr
          have : F ∈ (L.map cell).reverse := by rw [hX]; simp
          exact F_not_mem_rev L this
  · rintro (⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩ | ⟨L', B', rfl, rfl, rfl⟩)
    · left
      exact ⟨(r.map cell).reverse, (u.map cell).reverse ++ F :: B.map cell,
        by simp [pos, cell], by simp [pos, cell]⟩
    · left
      exact ⟨(L.map cell).reverse ++ F :: u.map cell, r.map cell,
        by simp [pos, cell], by simp [pos, cell]⟩
    · right
      exact ⟨(L'.map cell).reverse, B'.map cell, by simp [pos, cell], by simp [pos, cell]⟩

theorem mem_rightMoves_pos {L B : List Bool} {q : List Cell} :
    q ∈ rightMoves (pos L B) ↔
      (∃ L', L = false :: L' ∧ q = pos L' (false :: B)) ∨
      (∃ L', L = true :: false :: L' ∧ q = pos L' (true :: false :: B)) := by
  rw [mem_rightMoves]
  constructor
  · rintro (⟨u, r, hp, rfl⟩ | ⟨u, r, hp, rfl⟩)
    · rcases split_at_F (by decide) hp with ⟨w, rfl, hY⟩ | ⟨w, hX, hr⟩
      · exfalso
        have : F ∈ B.map cell := by rw [hY]; simp
        exact F_not_mem_map B this
      · cases w with
        | nil =>
          simp at hr; subst hr
          left
          have h := rev_map_eq hX
          simp at h
          obtain ⟨x, L', rfl, hx, hL⟩ := map_cell_cons h
          simp at hx; subst hx
          have hL' := congrArg List.reverse hL
          simp only [List.reverse_reverse] at hL'
          subst hL'
          refine ⟨L', rfl, ?_⟩
          simp [pos, cell]
        | cons e w =>
          exfalso
          simp at hr
          obtain ⟨rfl, -⟩ := hr
          have : F ∈ (L.map cell).reverse := by rw [hX]; simp
          exact F_not_mem_rev L this
    · rcases split_at_F (by decide) hp with ⟨w, rfl, hY⟩ | ⟨w, hX, hr⟩
      · exfalso
        have : F ∈ B.map cell := by rw [hY]; simp
        exact F_not_mem_map B this
      · cases w with
        | nil => simp at hr
        | cons e w =>
          simp at hr
          obtain ⟨rfl, hr⟩ := hr
          cases w with
          | nil =>
            simp at hr; subst hr
            right
            have h := rev_map_eq hX
            simp at h
            obtain ⟨x, L', rfl, hx, hL⟩ := map_cell_cons h
            obtain ⟨y, L', rfl, hy, hL2⟩ := map_cell_cons hL
            simp at hx hy; subst hx hy
            have hL' := congrArg List.reverse hL2
            simp only [List.reverse_reverse] at hL'
            subst hL'
            refine ⟨L', rfl, ?_⟩
            simp [pos, cell]
          | cons e w =>
            exfalso
            simp at hr
            obtain ⟨rfl, -⟩ := hr
            have : F ∈ (L.map cell).reverse := by rw [hX]; simp
            exact F_not_mem_rev L this
  · rintro (⟨L', rfl, rfl⟩ | ⟨L', rfl, rfl⟩)
    · left
      exact ⟨(L'.map cell).reverse, B.map cell, by simp [pos, cell], by simp [pos, cell]⟩
    · right
      exact ⟨(L'.map cell).reverse, B.map cell, by simp [pos, cell], by simp [pos, cell]⟩

/-! ### Effect of toad slides on the statistics -/

theorem cT_lmove (u r : List Bool) : cT (u ++ true :: false :: r) = cT (u ++ false :: true :: r) := by
  simp [cT_append, cT]

theorem cE_lmove (u r : List Bool) : cE (u ++ true :: false :: r) = cE (u ++ false :: true :: r) := by
  simp [cE_append, cE]

theorem invL_lmove (u r : List Bool) :
    invL (u ++ true :: false :: r) + 1 = invL (u ++ false :: true :: r) := by
  induction u with
  | nil => simp [invL, cT]; omega
  | cons a u ih =>
    cases a
    · simp only [List.cons_append, invL, cT_lmove]; omega
    · simpa [invL] using ih

/-- Either the nearest toad moved (then `u` is all empty), or gap and behind are unchanged. -/
theorem gap_behind_lmove (u r : List Bool) :
    (cT u = 0 ∧ gap (u ++ true :: false :: r) + 1 = gap (u ++ false :: true :: r) ∧
        behind (u ++ true :: false :: r) = behind (u ++ false :: true :: r) + 1) ∨
    (0 < cT u ∧ gap (u ++ true :: false :: r) = gap (u ++ false :: true :: r) ∧
        behind (u ++ true :: false :: r) = behind (u ++ false :: true :: r)) := by
  induction u with
  | nil => left; simp [gap, behind, cT, cE]
  | cons a u ih =>
    cases a
    · rcases ih with ⟨h0, hg, hb⟩ | ⟨h0, hg, hb⟩
      · left; simp only [List.cons_append, gap, behind, cT]
        refine ⟨h0, ?_, hb⟩; omega
      · right; simp only [List.cons_append, gap, behind, cT]
        refine ⟨h0, ?_, hb⟩; omega
    · right
      simp only [List.cons_append, gap_true, behind, cT, cE_lmove]
      exact ⟨Nat.succ_pos _, trivial, trivial⟩

theorem cT_bmove (u r : List Bool) : cT (u ++ false :: true :: r) = cT (u ++ true :: false :: r) :=
  (cT_lmove u r).symm

theorem cE_bmove (u r : List Bool) : cE (u ++ false :: true :: r) = cE (u ++ true :: false :: r) :=
  (cE_lmove u r).symm

theorem invB_bmove (u r : List Bool) :
    invB (u ++ false :: true :: r) + 1 = invB (u ++ true :: false :: r) := by
  induction u with
  | nil => simp [invB, cE]; omega
  | cons a u ih =>
    cases a
    · simpa [invB] using ih
    · simp only [List.cons_append, invB, cE_bmove]; omega

/-! ### Effect of each move on `phi` -/

theorem phi_lmove (u r B : List Bool) :
    phi (u ++ true :: false :: r) B = phi (u ++ false :: true :: r) B - 1 := by
  have h := invL_lmove u r
  simp only [phi, cT_lmove, cE_lmove]
  generalize cT (u ++ false :: true :: r) * cE B = m
  omega

theorem phi_bmove (L u r : List Bool) :
    phi L (u ++ false :: true :: r) = phi L (u ++ true :: false :: r) - 1 := by
  have h := invB_bmove u r
  simp only [phi, cE_bmove]
  generalize cT L * cE (u ++ true :: false :: r) = m
  omega

theorem phi_jump (L' B' : List Bool) :
    phi (false :: L') (true :: B') = phi (true :: L') (false :: B') - 1 := by
  simp only [phi, invL, invB, cT, cE, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  generalize cT L' * cE B' = m
  omega

theorem phi_slide (L' B : List Bool) : phi L' (false :: B) = phi (false :: L') B + 1 := by
  simp only [phi, invL, invB, cT, cE, Nat.mul_add, Nat.mul_one]
  generalize cT L' * cE B = m
  omega

theorem phi_fjump (L' B : List Bool) :
    phi L' (true :: false :: B) = phi (true :: false :: L') B + 3 := by
  simp only [phi, invL, invB, cT, cE, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  generalize cT L' * cE B = m
  omega

/-! ### Structure -/

theorem cE_eq_gap_add_behind {L : List Bool} (h : 0 < cT L) : cE L = gap L + behind L := by
  induction L with
  | nil => simp [cT] at h
  | cons a L ih =>
    cases a
    · simp only [cT] at h
      simp only [cE, gap, behind, ih h]; omega
    · simp [cE, gap, behind]

theorem gap_eq_cE_of_cT_zero {L : List Bool} (h : cT L = 0) : gap L = cE L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases a
    · simp only [cT] at h
      simp only [cE, gap, ih h]
    · simp [cT] at h

theorem behind_eq_zero_of_cT_zero {L : List Bool} (h : cT L = 0) : behind L = 0 := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    cases a
    · simp only [cT] at h
      simp only [behind, ih h]
    · simp [cT] at h

theorem eq_replicate_of_cT_zero {X : List Bool} (h : cT X = 0) :
    X = List.replicate (cE X) false := by
  induction X with
  | nil => rfl
  | cons a X ih =>
    cases a
    · simp only [cT] at h
      simp only [cE, List.replicate_succ, List.cons.injEq, true_and]
      exact ih h
    · simp [cT] at h

theorem eq_replicate_of_cE_zero {X : List Bool} (h : cE X = 0) :
    X = List.replicate (cT X) true := by
  induction X with
  | nil => rfl
  | cons a X ih =>
    cases a
    · simp [cE] at h
    · simp only [cE] at h
      simp only [cT, List.replicate_succ, List.cons.injEq, true_and]
      exact ih h

/-- A left side with no toad slide available is `T^i` then `E^j` (reading away from the frog). -/
theorem lmove_or_packed (X : List Bool) :
    (∃ u r, X = u ++ false :: true :: r) ∨
      X = List.replicate (cT X) true ++ List.replicate (cE X) false := by
  induction X with
  | nil => right; rfl
  | cons a X ih =>
    rcases ih with ⟨u, r, rfl⟩ | ih
    · exact Or.inl ⟨a :: u, r, rfl⟩
    · cases a
      · cases X with
        | nil => right; rfl
        | cons b X =>
          cases b
          · right
            simp only [cT, cE] at ih ⊢
            generalize cT X = n at ih ⊢
            cases n with
            | zero =>
              simp only [List.replicate_zero, List.nil_append] at ih ⊢
              rw [List.replicate_succ, ← ih]
            | succ n => simp [List.replicate_succ] at ih
          · exact Or.inl ⟨[], X, rfl⟩
      · right
        simp only [cT, cE, List.replicate_succ, List.cons_append, List.cons.injEq, true_and]
        exact ih

/-- A right side with no toad slide available is `E^j` then `T^i`. -/
theorem bmove_or_packed (X : List Bool) :
    (∃ u r, X = u ++ true :: false :: r) ∨
      X = List.replicate (cE X) false ++ List.replicate (cT X) true := by
  induction X with
  | nil => right; rfl
  | cons a X ih =>
    rcases ih with ⟨u, r, rfl⟩ | ih
    · exact Or.inl ⟨a :: u, r, rfl⟩
    · cases a
      · right
        simp only [cT, cE, List.replicate_succ, List.cons_append, List.cons.injEq, true_and]
        exact ih
      · cases X with
        | nil => right; rfl
        | cons b X =>
          cases b
          · exact Or.inl ⟨[], X, rfl⟩
          · right
            simp only [cT, cE] at ih ⊢
            generalize cE X = n at ih ⊢
            cases n with
            | zero =>
              simp only [List.replicate_zero, List.nil_append] at ih ⊢
              rw [List.replicate_succ, ← ih]
            | succ n => simp [List.replicate_succ] at ih

theorem invL_replicate_false_append (d : Nat) (X : List Bool) :
    invL (List.replicate d false ++ X) = invL X + d * cT X := by
  induction d with
  | zero => simp
  | succ d ih =>
    simp only [List.replicate_succ, List.cons_append, invL, ih, cT_append, cT_replicate_false,
      Nat.succ_mul]
    omega

theorem invL_packed (i j : Nat) : invL (List.replicate i true ++ List.replicate j false) = 0 := by
  induction i with
  | zero =>
    have h := invL_replicate_false_append j []
    simpa [invL, cT] using h
  | succ i ih => simpa [List.replicate_succ, invL] using ih

theorem invB_packed (i j : Nat) : invB (List.replicate j false ++ List.replicate i true) = 0 := by
  induction j with
  | zero =>
    induction i with
    | zero => rfl
    | succ i ih =>
      simp only [List.replicate_zero, List.nil_append] at ih
      simp [List.replicate_succ, invB, ih, cE_replicate_true]
  | succ j ih => simpa [List.replicate_succ, invB] using ih

end OneFrog
end Cgt
