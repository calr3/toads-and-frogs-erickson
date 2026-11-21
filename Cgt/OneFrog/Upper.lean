import Cgt.OneFrog.Rules

/-!
# One-frog positions: upper bounds

The upper bounds are proved together, by induction on the position (`upper`):

* no toad left of the frog: `V ≤ max(phi, 0)`;
* `room ≥ 2`, or `room = 1` and the gap is even: `V ≤ phi`;
* `room = 1`, gap odd: `V ≤ phi + 1/2`;
* `room = 0`, gap even: `V ≤ max(phi + 1, 0)`;
* `room = 0`, gap odd, `phi ≥ 0`: `V ≤ (phi + 1)∗`;
* `room = -1`, no gap, `phi ≥ -1`: `V ≤ phi + 2`;
* two degenerate families with `phi < 0` (`u6z`, `u5z`).

Right never needs to jump: he answers a Left move with a slide of the frog, or not at all.
-/

namespace Cgt
namespace OneFrog

open Cell TF Game

/-! ### Inequalities for `phi` -/

theorem invL_ge (L : List Bool) : gap L * cT L ≤ invL L := by
  induction L with
  | nil => simp [invL]
  | cons c X ih =>
    cases c with
    | true => simp [invL]
    | false =>
      simp only [gap_false, cT, invL, Nat.succ_mul]
      omega

theorem invL_le (X : List Bool) : invL X ≤ cE X * cT X := by
  induction X with
  | nil => simp [invL]
  | cons c X ih =>
    cases c with
    | true => simp only [invL, cE, cT, Nat.mul_succ]; omega
    | false => simp only [invL, cE, cT, Nat.succ_mul]; omega

theorem invB_eq_zero_of_cE_zero {B : List Bool} (h : cE B = 0) : invB B = 0 := by
  rw [eq_replicate_of_cE_zero h]
  have := invB_packed (cT B) 0
  simpa using this

private theorem add_le_mul_succ {t r : Nat} (ht : 1 ≤ t) (hr : 1 ≤ r) : t + r ≤ t * r + 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, t = a + 1 := ⟨t - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.succ_mul, Nat.mul_succ]
  omega

theorem phi_ge {L B : List Bool} (hT : 0 < cT L) (hB : 1 ≤ cE B) : room L B - 1 ≤ phi L B := by
  have h1 := invL_ge L
  have h2 := cE_eq_gap_add_behind hT
  have h3 : gap L ≤ gap L * cT L := Nat.le_mul_of_pos_right _ hT
  have h4 := add_le_mul_succ hT hB
  unfold phi room
  omega

theorem phi_ge_b {L B : List Bool} (hT : 0 < cT L) (hB : cE B = 0) (hg : 1 ≤ gap L) :
    -1 - (behind L : Int) ≤ phi L B := by
  have h1 := invL_ge L
  have h2 := cE_eq_gap_add_behind hT
  have h4 := add_le_mul_succ hg hT
  unfold phi
  rw [hB]
  simp only [Nat.mul_zero]
  omega

theorem phi_ge_c {L B : List Bool} (hT : cT L = 1) : room L B - 1 ≤ phi L B := by
  have h1 := invL_ge L
  have h2 := cE_eq_gap_add_behind (L := L) (by omega)
  unfold phi room
  rw [hT] at h1 ⊢
  simp only [Nat.mul_one, Nat.one_mul] at h1 ⊢
  omega

/-- The nearest toad is next to the frog and there is a second toad `gap L'` squares behind it. -/
theorem phi_ge_contact {L' B : List Bool} (hT : 0 < cT L') (hB : 1 ≤ cE B) :
    room (true :: L') B + gap L' - 1 ≤ phi (true :: L') B ∧
    (1 ≤ gap L' → room (true :: L') B + cT L' - 1 ≤ phi (true :: L') B) := by
  have h1 := invL_ge L'
  have h3 : gap L' ≤ gap L' * cT L' := Nat.le_mul_of_pos_right _ hT
  have h4 : cT L' ≤ cT L' * cE B := Nat.le_mul_of_pos_right _ hB
  have h5 : (cT L' + 1) * cE B = cT L' * cE B + cE B := by rw [Nat.succ_mul]
  constructor
  · unfold phi room
    simp only [invL, cT, cE, behind]
    rw [h5]
    omega
  · intro hg
    have h6 : cT L' ≤ gap L' * cT L' := Nat.le_mul_of_pos_left _ hg
    unfold phi room
    simp only [invL, cT, cE, behind]
    rw [h5]
    omega

theorem phi_le_d {L' B : List Bool} (hB : cE B = 0) (hL : cE L' = 1) :
    phi (true :: L') B ≤ -2 := by
  have h1 := invL_le L'
  have h2 := invB_eq_zero_of_cE_zero hB
  unfold phi
  simp only [invL, cT, cE]
  rw [hB, h2]
  rw [hL] at h1 ⊢
  simp only [Nat.mul_zero, Nat.one_mul] at h1 ⊢
  omega

theorem no_LM_of_cE_zero {L B L₁ B₁ : List Bool} (hL : cE L = 0) (hB : cE B = 0) :
    ¬ LM L B L₁ B₁ := by
  rintro (⟨u, r, rfl, -, -⟩ | ⟨u, r, rfl, -, -⟩ | ⟨L', B', -, rfl, -, -⟩)
  · rw [cE_append] at hL; simp [cE] at hL
  · rw [cE_append] at hB; simp [cE] at hB
  · simp [cE] at hB

theorem phi_nonneg_of_empty {L B : List Bool} (hT : cT L = 0) (hE : cE L = 0) : 0 ≤ phi L B := by
  unfold phi
  rw [hT, hE]
  omega

/-! ### Features after a move -/

theorem room_slide (L₂ B : List Bool) : room L₂ (false :: B) = room (false :: L₂) B + 1 := by
  unfold room; simp only [behind, cE]; omega

theorem room_jump {L' : List Bool} (B' : List Bool) (hT : 0 < cT L') :
    room L' (false :: true :: B') = room (true :: L') (false :: B') + gap L' := by
  have := cE_eq_gap_add_behind hT
  unfold room; simp only [behind, cE]; omega

theorem int_le_of_le {g : Game} {a n : Nat} (h : le g (int a)) (han : a ≤ n) : le g (int n) :=
  le_trans _ _ _ h (int_le_int han)

/-! ### The claims -/

/-- The upper bounds for the position `pos L B`. -/
structure UC (L B : List Bool) : Prop where
  u0 : cT L = 0 → le (V L B) (int (phi L B).toNat)
  u1 : 0 < cT L → (2 ≤ room L B ∨ (room L B = 1 ∧ gap L % 2 = 0)) →
    le (V L B) (int (phi L B).toNat)
  u3 : 0 < cT L → room L B = 1 → gap L % 2 = 1 → le (V L B) (half (phi L B).toNat)
  u4 : 0 < cT L → room L B = 0 → gap L % 2 = 0 → le (V L B) (int (phi L B + 1).toNat)
  u5 : 0 < cT L → room L B = 0 → gap L % 2 = 1 → 0 ≤ phi L B →
    le (V L B) (starN (phi L B + 1).toNat)
  u6 : 0 < cT L → room L B = -1 → gap L = 0 → -1 ≤ phi L B →
    le (V L B) (int (phi L B + 2).toNat)
  u6z : 0 < cT L → room L B = -1 → gap L = 0 → phi L B = -2 → (1 ≤ cE B ∨ cT L = 1) →
    le (V L B) (int 0)
  u5z : cT L = 1 → room L B = 0 → gap L % 2 = 1 → phi L B = -1 → le (V L B) (starN 0)

theorem upper : ∀ (N : Nat) (L B : List Bool), mu L B < N → UC L B := by
  intro N
  induction N with
  | zero => intro L B h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
    intro L B hmu
    -- induction hypothesis after a Left move, and after a Left move and a slide
    have ih1 : ∀ {L₁ B₁}, LM L B L₁ B₁ → UC L₁ B₁ := fun hm =>
      ih _ _ (by have := mu_LM hm; omega)
    have ih2 : ∀ {L₂ B₁}, LM L B (false :: L₂) B₁ → UC L₂ (false :: B₁) := fun {L₂ B₁} hm =>
      ih _ _ (by have := mu_LM hm; have := mu_slide L₂ B₁; omega)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- u0: no toad left of the frog
      intro hT
      apply V_le_int
      intro L₁ B₁ hm
      have hp := phi_LM hm
      have hT1 : cT L₁ = 0 := by
        rcases LM_cases hm with ⟨c, -⟩ | ⟨c, -⟩ | ⟨L', B', rfl, -⟩
        · omega
        · omega
        · simp [cT] at hT
      by_cases hpos : 0 < phi L B
      · left
        refine ⟨by omega, ?_⟩
        have := (ih1 hm).u0 hT1
        rwa [show (phi L₁ B₁).toNat = (phi L B).toNat - 1 by omega] at this
      · right
        have hg : 0 < gap L₁ := by
          rw [gap_eq_cE_of_cT_zero hT1]
          rcases Nat.eq_zero_or_pos (cE L₁) with h0 | h0
          · have := phi_nonneg_of_empty (B := B₁) hT1 h0; omega
          · exact h0
        obtain ⟨L₂, rfl, -, -, c2⟩ := exists_slide hg
        have hs := phi_slide L₂ B₁
        have := (ih2 hm).u0 (by omega)
        refine ⟨L₂, rfl, ?_⟩
        rwa [show (phi L₂ (false :: B₁)).toNat = (phi L B).toNat by omega] at this
    · -- u1: room ≥ 2, or room = 1 and an even gap
      intro hT hroom
      have hB : 1 ≤ cE B := by unfold room at hroom; omega
      apply V_le_int
      intro L₁ B₁ hm
      have hp := phi_LM hm
      rcases LM_cases hm with ⟨c1, g1, b1, e1⟩ | ⟨c1, g1, b1, rfl⟩ | ⟨L', B', rfl, rfl, rfl, rfl⟩
      · left
        have hr : room L₁ B₁ = room L B := by unfold room; rw [b1, e1]
        have hge := phi_ge (L := L₁) (B := B₁) (by omega) (by omega)
        refine ⟨by omega, ?_⟩
        have := (ih1 hm).u1 (by omega) (by rw [hr, g1]; exact hroom)
        rwa [show (phi L₁ B₁).toNat = (phi L B).toNat - 1 by omega] at this
      · have hr : room L₁ B = room L B - 1 := by unfold room; omega
        by_cases hin : 2 ≤ room L₁ B ∨ (room L₁ B = 1 ∧ gap L₁ % 2 = 0)
        · left
          have hge := phi_ge (L := L₁) (B := B) (by omega) hB
          refine ⟨by omega, ?_⟩
          have := (ih1 hm).u1 (by omega) hin
          rwa [show (phi L₁ B).toNat = (phi L B).toNat - 1 by omega] at this
        · right
          obtain ⟨L₂, rfl, g2, b2, c2⟩ := exists_slide (L := L₁) (by omega)
          have hs := phi_slide L₂ B
          have hr2 := room_slide L₂ B
          have := (ih2 hm).u1 (by omega) (by omega)
          refine ⟨L₂, rfl, ?_⟩
          rwa [show (phi L₂ (false :: B)).toNat = (phi (false :: L₂) B + 1).toNat by omega,
            show (phi (false :: L₂) B + 1).toNat = (phi L B).toNat by omega] at this
      · right
        refine ⟨L', rfl, ?_⟩
        have hs := phi_slide L' (true :: B')
        by_cases hT' : cT L' = 0
        · have := (ih2 hm).u0 hT'
          rwa [show (phi L' (false :: true :: B')).toNat =
            (phi (true :: L') (false :: B')).toNat by omega] at this
        · have hrj := room_jump B' (L' := L') (by omega)
          simp only [gap_true] at hroom
          have := (ih2 hm).u1 (by omega) (by omega)
          rwa [show (phi L' (false :: true :: B')).toNat =
            (phi (true :: L') (false :: B')).toNat by omega] at this
    · -- u3: room = 1 and an odd gap
      intro hT hroom hg
      have hB : 1 ≤ cE B := by unfold room at hroom; omega
      obtain ⟨L₂, rfl, g2, b2, c2⟩ := exists_slide (L := L) (by omega)
      have hs0 := phi_slide L₂ B
      have hr0 := room_slide L₂ B
      have hge0 := phi_ge hT hB
      apply V_le_half
      · intro L₁ B₁ hm
        have hp := phi_LM hm
        rcases LM_cases hm with ⟨c1, g1, b1, e1⟩ | ⟨c1, g1, b1, rfl⟩ | ⟨L', B', h, -⟩
        · left
          have hr : room L₁ B₁ = room (false :: L₂) B := by unfold room; rw [b1, e1]
          have hge := phi_ge (L := L₁) (B := B₁) (by omega) (by omega)
          have := (ih1 hm).u3 (by omega) (by omega) (by omega)
          have h2 := le_trans _ _ _ this (half_le_int_succ _)
          rwa [show (phi L₁ B₁).toNat + 1 = (phi (false :: L₂) B).toNat by omega] at h2
        · left
          have hr : room L₁ B = room (false :: L₂) B - 1 := by unfold room; omega
          have := (ih1 hm).u4 (by omega) (by omega) (by omega)
          rwa [show (phi L₁ B + 1).toNat = (phi (false :: L₂) B).toNat by omega] at this
        · simp at h
      · have := (ih L₂ (false :: B) (by have := mu_slide L₂ B; omega)).u1 (by omega) (Or.inl (by omega))
        rwa [show (phi L₂ (false :: B)).toNat = (phi (false :: L₂) B).toNat + 1 by omega] at this
    · -- u4: room = 0 and an even gap
      intro hT hroom hg
      apply V_le_int
      intro L₁ B₁ hm
      have hp := phi_LM hm
      rcases LM_cases hm with ⟨c1, g1, b1, e1⟩ | ⟨c1, g1, b1, rfl⟩ | ⟨L', B', rfl, rfl, rfl, rfl⟩
      · left
        have hr : room L₁ B₁ = room L B := by unfold room; rw [b1, e1]
        have hnn : 0 ≤ phi L B := by
          rcases Nat.eq_zero_or_pos (cE B) with hB | hB
          · have hbe : behind L = 0 := by unfold room at hroom; omega
            rcases Nat.eq_zero_or_pos (gap L) with hg0 | hg0
            · have := cE_eq_gap_add_behind hT
              exact absurd hm (no_LM_of_cE_zero (by omega) hB)
            · have := phi_ge_b (L := L₁) (B := B₁) (by omega) (by omega) (by omega)
              omega
          · have := phi_ge (L := L₁) (B := B₁) (by omega) (by omega)
            omega
        refine ⟨by omega, ?_⟩
        have := (ih1 hm).u4 (by omega) (by omega) (by omega)
        rwa [show (phi L₁ B₁ + 1).toNat = (phi L B + 1).toNat - 1 by omega] at this
      · right
        have hr : room L₁ B = room L B - 1 := by unfold room; omega
        obtain ⟨L₂, rfl, g2, b2, c2⟩ := exists_slide (L := L₁) (by omega)
        have hs := phi_slide L₂ B
        have hr2 := room_slide L₂ B
        have := (ih2 hm).u4 (by omega) (by omega) (by omega)
        refine ⟨L₂, rfl, ?_⟩
        rwa [show (phi L₂ (false :: B) + 1).toNat = (phi L B + 1).toNat by omega] at this
      · have hs := phi_slide L' (true :: B')
        by_cases hT' : cT L' = 0
        · right
          refine ⟨L', rfl, ?_⟩
          exact int_le_of_le ((ih2 hm).u0 hT') (by omega)
        · have hrj := room_jump B' (L' := L') (by omega)
          have hcon := phi_ge_contact (L' := L') (B := false :: B') (by omega) (by simp [cE])
          rcases Nat.lt_trichotomy (gap L') 1 with hg' | hg' | hg'
          · right
            refine ⟨L', rfl, ?_⟩
            have := (ih2 hm).u4 (by omega) (by omega) (by omega)
            rwa [show (phi L' (false :: true :: B') + 1).toNat =
              (phi (true :: L') (false :: B') + 1).toNat by omega] at this
          · left
            have hr1 : room (false :: L') (true :: B') = 0 := by
              have := room_slide L' (true :: B'); omega
            refine ⟨by omega, ?_⟩
            have := (ih1 hm).u4 (by simp [cT]; omega) hr1 (by simp; omega)
            rwa [show (phi (false :: L') (true :: B') + 1).toNat =
              (phi (true :: L') (false :: B') + 1).toNat - 1 by omega] at this
          · right
            refine ⟨L', rfl, ?_⟩
            exact int_le_of_le ((ih2 hm).u1 (by omega) (Or.inl (by omega))) (by omega)
    · -- u5: room = 0, an odd gap and phi ≥ 0
      intro hT hroom hg hphi
      obtain ⟨L₂, rfl, g2, b2, c2⟩ := exists_slide (L := L) (by omega)
      have hs0 := phi_slide L₂ B
      have hr0 := room_slide L₂ B
      apply V_le_starN
      · intro L₁ B₁ hm
        have hp := phi_LM hm
        rcases LM_cases hm with ⟨c1, g1, b1, e1⟩ | ⟨c1, g1, b1, rfl⟩ | ⟨L', B', h, -⟩
        · right
          have hr : room L₁ B₁ = room (false :: L₂) B := by unfold room; rw [b1, e1]
          obtain ⟨L₃, rfl, g3, b3, c3⟩ := exists_slide (L := L₁) (by omega)
          have hs := phi_slide L₃ B₁
          have hr3 := room_slide L₃ B₁
          have := (ih2 hm).u1 (by omega) (Or.inr ⟨by omega, by omega⟩)
          refine ⟨L₃, rfl, ?_⟩
          have h2 := le_trans _ _ _ this (int_le_starN_succ _)
          rwa [show (phi L₃ (false :: B₁)).toNat + 1 = (phi (false :: L₂) B + 1).toNat by omega]
            at h2
        · have hr : room L₁ B = room (false :: L₂) B - 1 := by unfold room; omega
          rcases Nat.eq_zero_or_pos (gap L₁) with hg1 | hg1
          · left
            have := (ih1 hm).u6 (by omega) (by omega) hg1 (by omega)
            rwa [show (phi L₁ B + 2).toNat = (phi (false :: L₂) B + 1).toNat by omega] at this
          · right
            obtain ⟨L₃, rfl, g3, b3, c3⟩ := exists_slide hg1
            have hs := phi_slide L₃ B
            have hr3 := room_slide L₃ B
            have := (ih2 hm).u5 (by omega) (by omega) (by omega) (by omega)
            refine ⟨L₃, rfl, ?_⟩
            rwa [show (phi L₃ (false :: B) + 1).toNat = (phi (false :: L₂) B + 1).toNat by omega]
              at this
        · simp at h
      · have := (ih L₂ (false :: B) (by have := mu_slide L₂ B; omega)).u1 (by omega)
          (Or.inr ⟨by omega, by simp only [gap_false] at hg; omega⟩)
        rwa [show (phi L₂ (false :: B)).toNat = (phi (false :: L₂) B + 1).toNat by omega] at this
    · -- u6: room = -1, no gap and phi ≥ -1
      intro hT hroom hg hphi
      obtain ⟨L', rfl, hb, hc⟩ := exists_contact hg hT
      apply V_le_int
      intro L₁ B₁ hm
      have hp := phi_LM hm
      rcases LM_cases hm with ⟨c1, g1, b1, e1⟩ | ⟨c1, g1, b1, rfl⟩ | ⟨L'', B', h, rfl, rfl, rfl⟩
      · left
        have hr : room L₁ B₁ = room (true :: L') B := by unfold room; rw [b1, e1]
        refine ⟨by omega, ?_⟩
        by_cases h0 : 0 ≤ phi (true :: L') B
        · have := (ih1 hm).u6 (by omega) (by omega) (by omega) (by omega)
          rwa [show (phi L₁ B₁ + 2).toNat = (phi (true :: L') B + 2).toNat - 1 by omega] at this
        · have hside : 1 ≤ cE B₁ ∨ cT L₁ = 1 := by
            rcases Nat.eq_zero_or_pos (cE B) with hB | hB
            · right
              have hL' : cE L' = 1 := by unfold room at hroom; omega
              have := phi_le_d (L' := L') hB hL'
              omega
            · left; omega
          have := (ih1 hm).u6z (by omega) (by omega) (by omega) (by omega) hside
          rwa [show (0 : Nat) = (phi (true :: L') B + 2).toNat - 1 by omega] at this
      · simp at g1
      · injection h with _ h; subst h
        right
        refine ⟨L', rfl, ?_⟩
        have hs := phi_slide L' (true :: B')
        by_cases hT' : cT L' = 0
        · exact int_le_of_le ((ih2 hm).u0 hT') (by omega)
        · have hrj := room_jump B' (L' := L') (by omega)
          have hcon := phi_ge_contact (L' := L') (B := false :: B') (by omega) (by simp [cE])
          rcases Nat.lt_trichotomy (gap L') 1 with hg' | hg' | hg'
          · have := (ih2 hm).u6 (by omega) (by omega) (by omega) (by omega)
            rwa [show (phi L' (false :: true :: B') + 2).toNat =
              (phi (true :: L') (false :: B') + 2).toNat by omega] at this
          · by_cases h0 : 0 ≤ phi (true :: L') (false :: B')
            · have := (ih2 hm).u5 (by omega) (by omega) (by omega) (by omega)
              have h2 := le_trans _ _ _ this (starN_le_int_succ _)
              rwa [show (phi L' (false :: true :: B') + 1).toNat + 1 =
                (phi (true :: L') (false :: B') + 2).toNat by omega] at h2
            · have h1 := hcon.2 (by omega)
              have := (ih2 hm).u5z (by omega) (by omega) (by omega) (by omega)
              have h2 := le_trans _ _ _ this (starN_le_int_succ _)
              rwa [show (0 : Nat) + 1 = (phi (true :: L') (false :: B') + 2).toNat by omega] at h2
          · exact int_le_of_le ((ih2 hm).u1 (by omega) (by omega)) (by omega)
    · -- u6z: room = -1, no gap, phi = -2
      intro hT hroom hg hphi hside
      obtain ⟨L', rfl, hb, hc⟩ := exists_contact hg hT
      apply V_le_int_zero
      intro L₁ B₁ hm
      have hp := phi_LM hm
      rcases LM_cases hm with ⟨c1, g1, b1, e1⟩ | ⟨c1, g1, b1, rfl⟩ | ⟨L'', B', h, rfl, rfl, rfl⟩
      · exfalso
        have hr : room L₁ B₁ = room (true :: L') B := by unfold room; rw [b1, e1]
        rcases hside with hB | hone
        · have := phi_ge (L := L₁) (B := B₁) (by omega) (by omega); omega
        · have := phi_ge_c (L := L₁) (B := B₁) (by omega); omega
      · simp at g1
      · injection h with _ h; subst h
        refine ⟨L', rfl, ?_⟩
        have hs := phi_slide L' (true :: B')
        by_cases hT' : cT L' = 0
        · have := (ih2 hm).u0 hT'
          rwa [show (phi L' (false :: true :: B')).toNat = 0 by omega] at this
        · have hrj := room_jump B' (L' := L') (by omega)
          have hcon := phi_ge_contact (L' := L') (B := false :: B') (by omega) (by simp [cE])
          exact (ih2 hm).u6z (by omega) (by omega) (by omega) (by omega) (Or.inl (by simp [cE]))
    · -- u5z: one toad, room = 0, an odd gap, phi = -1
      intro hT hroom hg hphi
      obtain ⟨L₂, rfl, g2, b2, c2⟩ := exists_slide (L := L) (by omega)
      have hs0 := phi_slide L₂ B
      have hr0 := room_slide L₂ B
      apply V_le_starN
      · intro L₁ B₁ hm
        have hp := phi_LM hm
        rcases LM_cases hm with ⟨c1, g1, b1, e1⟩ | ⟨c1, g1, b1, rfl⟩ | ⟨L', B', h, -⟩
        · exfalso
          have hr : room L₁ B₁ = room (false :: L₂) B := by unfold room; rw [b1, e1]
          have := phi_ge_c (L := L₁) (B := B₁) (by omega); omega
        · have hr : room L₁ B = room (false :: L₂) B - 1 := by unfold room; omega
          rcases Nat.eq_zero_or_pos (gap L₁) with hg1 | hg1
          · left
            exact (ih1 hm).u6z (by omega) (by omega) hg1 (by omega) (Or.inr (by omega))
          · right
            obtain ⟨L₃, rfl, g3, b3, c3⟩ := exists_slide hg1
            have hs := phi_slide L₃ B
            have hr3 := room_slide L₃ B
            exact ⟨L₃, rfl, (ih2 hm).u5z (by omega) (by omega) (by omega) (by omega)⟩
        · simp at h
      · have := (ih L₂ (false :: B) (by have := mu_slide L₂ B; omega)).u1 (by omega)
          (Or.inr ⟨by omega, by simp only [gap_false] at hg; omega⟩)
        rwa [show (phi L₂ (false :: B)).toNat = 0 by omega] at this

/-- The upper bounds hold for every one-frog position. -/
theorem upper_all (L B : List Bool) : UC L B := upper (mu L B + 1) L B (Nat.lt_succ_self _)

end OneFrog
end Cgt
