import Cgt.OneFrog.Rules

/-!
# One-frog positions: lower bounds

* `lower0`: the value is at least `phi` whenever `phi ≥ 0`, for every one-frog position. Left is
  never stuck while `phi` is positive.
* `lowerK` (`k = 1, 2`): the value is at least `phi + k` when `room ≤ -k`, or `room = 1 - k` and
  the gap between the nearest toad and the frog is even.
* `lower_half`, `lower_star`: the lower bounds `phi + 1/2` and `(phi + 1)∗` for an odd gap.
-/

namespace Cgt
namespace OneFrog

open Cell TF Game

theorem lower0 : ∀ (N : Nat) (L B : List Bool) (n : Nat), mu L B < N → (n : Int) ≤ phi L B →
    le (int n) (V L B) := by
  intro N
  induction N with
  | zero => intro L B n h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
    intro L B n hmu hn
    apply int_le_V
    · by_cases h0 : n = 0
      · exact Or.inl h0
      · right
        obtain ⟨L₁, B₁, hm⟩ := exists_LM_of_phi_pos (L := L) (B := B) (by omega)
        have hp := phi_LM hm
        have := mu_LM hm
        exact ⟨L₁, B₁, hm, ih L₁ B₁ (n - 1) (by omega) (by omega)⟩
    · rintro L₂ rfl
      have hs := phi_slide L₂ B
      have hmu2 := mu_slide L₂ B
      obtain ⟨L₃, B₃, hm⟩ := exists_LM_of_phi_pos (L := L₂) (B := false :: B) (by omega)
      have hp := phi_LM hm
      have := mu_LM hm
      exact ⟨L₃, B₃, hm, ih L₃ B₃ n (by omega) (by omega)⟩
    · rintro L₂ rfl
      have hs := phi_fjump L₂ B
      have hmu2 := mu_fjump L₂ B
      obtain ⟨L₃, B₃, hm⟩ := exists_LM_of_phi_pos (L := L₂) (B := true :: false :: B) (by omega)
      have hp := phi_LM hm
      have := mu_LM hm
      exact ⟨L₃, B₃, hm, ih L₃ B₃ n (by omega) (by omega)⟩

/-- The value is at least `phi` when `phi ≥ 0`. -/
theorem int_le_V_of_le_phi {L B : List Bool} {n : Nat} (h : (n : Int) ≤ phi L B) :
    le (int n) (V L B) :=
  lower0 (mu L B + 1) L B n (Nat.lt_succ_self _) h

theorem lowerK (k : Nat) (hk : k = 1 ∨ k = 2) : ∀ (N : Nat) (L B : List Bool) (n : Nat),
    mu L B < N → 0 < cT L →
    (room L B ≤ -(k : Int) ∨ (room L B = 1 - (k : Int) ∧ gap L % 2 = 0)) →
    (n : Int) ≤ phi L B + k → le (int n) (V L B) := by
  intro N
  induction N with
  | zero => intro L B n h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
    intro L B n hmu hT hroom hn
    apply int_le_V
    · -- Left has a move that keeps the bound
      by_cases h0 : n = 0
      · exact Or.inl h0
      right
      by_cases hg : 0 < gap L
      · obtain ⟨L₁, hm, c1, g1, b1⟩ := exists_front_slide B hg hT
        have hp := phi_LM hm
        have := mu_LM hm
        refine ⟨L₁, B, hm, ih L₁ B (n - 1) (by omega) (by omega) (Or.inl ?_) (by omega)⟩
        unfold room at hroom ⊢
        omega
      · obtain ⟨L', rfl, hb, hc⟩ := exists_contact (L := L) (by omega) hT
        rcases slide_or_packed (true :: L') B with
          ⟨L₁, B₁, hm, c1, e1, ⟨g1, b1⟩ | ⟨g1, b1, -⟩⟩ | ⟨hL, hB⟩
        · have hp := phi_LM hm
          have := mu_LM hm
          refine ⟨L₁, B₁, hm, ih L₁ B₁ (n - 1) (by omega) (by omega) ?_ (by omega)⟩
          unfold room at hroom ⊢
          rw [g1, b1, e1]
          exact hroom
        · simp [gap] at g1
        · cases hi : cT L' with
          | zero =>
            exfalso
            rw [hL, hB, phi_packed] at hn
            simp only [cT, cE, hi] at hn
            unfold room at hroom
            simp only [behind] at hroom
            simp at hn
            omega
          | succ i =>
            cases hj : cE B with
            | zero =>
              exfalso
              rw [hL, hB, phi_packed] at hn
              simp only [cT, cE, hi, hj] at hn
              simp at hn
              omega
            | succ j =>
              simp only [cT, cE, hi] at hL
              rw [List.replicate_succ, List.replicate_succ, List.cons_append,
                List.cons_append] at hL
              injection hL with _ hL'
              rw [hj, List.replicate_succ, List.cons_append] at hB
              generalize hB' : List.replicate j false ++ List.replicate (cT B) true = B' at hB
              generalize hL'' : List.replicate i true ++ List.replicate (cE L') false = L'' at hL'
              subst hB
              subst hL'
              have hm : LM (true :: true :: L'') (false :: B') (false :: true :: L'') (true :: B') :=
                Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl, rfl⟩)
              have hp := phi_LM hm
              have := mu_LM hm
              refine ⟨_, _, hm, ih _ _ (n - 1) (by omega) (by simp [cT]) (Or.inl ?_) (by omega)⟩
              unfold room at hroom ⊢
              simp only [behind, cE] at hroom ⊢
              omega
    · -- the frog slides
      rintro L₂ rfl
      have hs := phi_slide L₂ B
      have hmu2 := mu_slide L₂ B
      have hT2 : 0 < cT L₂ := by simpa [cT] using hT
      have hroom2 : room L₂ (false :: B) = room (false :: L₂) B + 1 := by
        unfold room; simp only [behind, cE]; omega
      by_cases hg : 0 < gap L₂
      · obtain ⟨L₃, hm, c1, g1, b1⟩ := exists_front_slide (false :: B) hg hT2
        have hp := phi_LM hm
        have := mu_LM hm
        refine ⟨L₃, _, hm, ih L₃ _ n (by omega) (by omega) ?_ (by omega)⟩
        have hr3 : room L₃ (false :: B) = room (false :: L₂) B := by
          unfold room at hroom2 ⊢; omega
        rw [hr3]
        simp only [gap] at hroom
        rcases hroom with h | ⟨h, hpar⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, by omega⟩
      · have hroomk : room (false :: L₂) B ≤ -(k : Int) := by
          simp only [gap] at hroom
          rcases hroom with h | ⟨-, hpar⟩
          · exact h
          · omega
        obtain ⟨L', rfl, hb, hc⟩ := exists_contact (L := L₂) (by omega) hT2
        rcases slide_or_packed (true :: L') (false :: B) with
          ⟨L₁, B₁, hm, c1, e1, ⟨g1, b1⟩ | ⟨g1, b1, -⟩⟩ | ⟨hL, hB⟩
        · have hp := phi_LM hm
          have := mu_LM hm
          refine ⟨L₁, B₁, hm, ih L₁ B₁ n (by omega) (by omega) ?_ (by omega)⟩
          have hr1 : room L₁ B₁ = room (false :: true :: L') B + 1 := by
            unfold room at hroom2 ⊢
            rw [b1, e1]; exact hroom2
          have hg1 : gap L₁ = 0 := by rw [g1]; rfl
          by_cases hlt : room (false :: true :: L') B + 1 ≤ -(k : Int)
          · exact Or.inl (by omega)
          · exact Or.inr ⟨by omega, by omega⟩
        · simp [gap] at g1
        · cases hi : cT L' with
          | zero =>
            exfalso
            have hphi : phi (true :: L') (false :: B) =
                ((cE B + 1 : Nat) : Int) - ((1 + cE L' : Nat) : Int) := by
              rw [hL, hB, phi_packed]
              simp only [cT, cE, hi]
              simp
            unfold room at hroomk
            simp only [behind] at hroomk
            omega
          | succ i =>
            have hm : LM (true :: L') (false :: B) (false :: L') (true :: B) :=
              Or.inr (Or.inr ⟨_, _, rfl, rfl, rfl, rfl⟩)
            have hp := phi_LM hm
            have := mu_LM hm
            refine ⟨_, _, hm, ih _ _ n (by omega) (by simp [cT]; omega) (Or.inl ?_) (by omega)⟩
            have hbe : behind L' = cE L' := by
              have h1 := cE_eq_gap_add_behind (L := L') (by omega)
              have h2 : gap L' = 0 := by
                simp only [cT, cE, hi] at hL
                rw [List.replicate_succ, List.replicate_succ, List.cons_append,
                  List.cons_append] at hL
                injection hL with _ hL'
                rw [hL']; rfl
              omega
            unfold room at hroomk ⊢
            simp only [behind, cE] at hroomk ⊢
            omega
    · -- the frog jumps
      rintro L₂ rfl
      have hs := phi_fjump L₂ B
      have hmu2 := mu_fjump L₂ B
      have hk2 : (k : Int) ≤ 2 := by omega
      obtain ⟨L₃, B₃, hm⟩ := exists_LM_of_phi_pos (L := L₂) (B := true :: false :: B) (by omega)
      have hp := phi_LM hm
      exact ⟨L₃, B₃, hm, int_le_V_of_le_phi (by omega)⟩

/-- `phi + 1 ≤ V` when `room ≤ -1`, or `room = 0` and the gap is even. -/
theorem lower1 {L B : List Bool} {n : Nat} (hT : 0 < cT L)
    (hroom : room L B ≤ -1 ∨ (room L B = 0 ∧ gap L % 2 = 0)) (hn : (n : Int) ≤ phi L B + 1) :
    le (int n) (V L B) := by
  refine lowerK 1 (Or.inl rfl) (mu L B + 1) L B n (Nat.lt_succ_self _) hT ?_ (by simpa using hn)
  rcases hroom with h | ⟨h, hp⟩
  · exact Or.inl (by simpa using h)
  · exact Or.inr ⟨by simpa using h, hp⟩

/-- `phi + 2 ≤ V` when `room ≤ -2`, or `room = -1` and the gap is even. -/
theorem lower2 {L B : List Bool} {n : Nat} (hT : 0 < cT L)
    (hroom : room L B ≤ -2 ∨ (room L B = -1 ∧ gap L % 2 = 0)) (hn : (n : Int) ≤ phi L B + 2) :
    le (int n) (V L B) := by
  refine lowerK 2 (Or.inr rfl) (mu L B + 1) L B n (Nat.lt_succ_self _) hT ?_ (by simpa using hn)
  rcases hroom with h | ⟨h, hp⟩
  · exact Or.inl (by simpa using h)
  · exact Or.inr ⟨by simpa using h, hp⟩

theorem half_le_V {L₂ B : List Bool} {n : Nat} (h1 : le (int (n + 1)) (V L₂ (false :: B)))
    (h2 : ∃ L₁ B₁, LM (false :: L₂) B L₁ B₁ ∧ le (int n) (V L₁ B₁)) :
    le (half n) (V (false :: L₂) B) := by
  apply half_le_of
  · intro y hy
    rcases mem_right_V.1 hy with ⟨L₃, h, rfl⟩ | ⟨L₃, h, rfl⟩
    · injection h with _ h; subst h; exact Or.inl h1
    · simp at h
  · obtain ⟨L₁, B₁, hm, h⟩ := h2
    exact ⟨_, mem_left_V.2 ⟨L₁, B₁, hm, rfl⟩, h⟩

theorem starN_le_V {L₂ B : List Bool} {n : Nat} (h1 : le (int n) (V L₂ (false :: B)))
    (h2 : ∃ L₁ B₁, LM (false :: L₂) B L₁ B₁ ∧ le (int n) (V L₁ B₁)) :
    le (starN n) (V (false :: L₂) B) := by
  apply starN_le_of
  · intro y hy
    rcases mem_right_V.1 hy with ⟨L₃, h, rfl⟩ | ⟨L₃, h, rfl⟩
    · injection h with _ h; subst h; exact Or.inl h1
    · simp at h
  · obtain ⟨L₁, B₁, hm, h⟩ := h2
    exact ⟨_, mem_left_V.2 ⟨L₁, B₁, hm, rfl⟩, h⟩

/-- `phi + 1/2 ≤ V` when `room = 1` and the gap is odd. -/
theorem lower_half {L B : List Bool} {n : Nat} (hT : 0 < cT L) (hroom : room L B = 1)
    (hg : gap L % 2 = 1) (hn : (n : Int) = phi L B) : le (half n) (V L B) := by
  obtain ⟨L₂, rfl, g2, b2, c2⟩ := exists_slide (L := L) (by omega)
  have hs := phi_slide L₂ B
  apply half_le_V
  · exact int_le_V_of_le_phi (by push_cast; omega)
  · obtain ⟨L₁, hm, c1, g1, b1⟩ := exists_front_slide B (L := false :: L₂) (by omega) hT
    have hp := phi_LM hm
    refine ⟨L₁, B, hm, lower1 (by omega) (Or.inr ⟨?_, by omega⟩) (by omega)⟩
    unfold room at hroom ⊢
    omega

/-- `(phi + 1)∗ ≤ V` when `room = 0` and the gap is odd. -/
theorem lower_star {L B : List Bool} {n : Nat} (hT : 0 < cT L) (hroom : room L B = 0)
    (hg : gap L % 2 = 1) (hn : (n : Int) = phi L B + 1) : le (starN n) (V L B) := by
  obtain ⟨L₂, rfl, g2, b2, c2⟩ := exists_slide (L := L) (by omega)
  have hs := phi_slide L₂ B
  apply starN_le_V
  · exact int_le_V_of_le_phi (by omega)
  · obtain ⟨L₁, hm, c1, g1, b1⟩ := exists_front_slide B (L := false :: L₂) (by omega) hT
    have hp := phi_LM hm
    refine ⟨L₁, B, hm, lower2 (by omega) (Or.inr ⟨?_, by omega⟩) (by omega)⟩
    unfold room at hroom ⊢
    omega

end OneFrog
end Cgt
