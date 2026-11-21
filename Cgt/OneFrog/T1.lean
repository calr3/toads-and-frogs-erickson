import Cgt.OneFrog.Lower
import Cgt.OneFrog.Upper

/-!
# Positions with one frog: Thanatipanonda's Conjecture T1

For a one-frog position with at least one toad left of the frog, let `phi` be Left's moves minus
Right's moves if every such toad jumps the frog, `room` the number of empty squares right of the
frog minus the number left of the nearest toad, and `gap` the number of empty squares between that
toad and the frog. Then (`value_*` below):

* `room ≥ 2`: the value is `phi`;
* `room = 1`: `phi` for an even gap, `phi + 1/2` for an odd gap;
* `room = 0`: `phi + 1` for an even gap, `(phi + 1)∗` for an odd gap (if these are not negative).

The toads may be anywhere. For the positions `□ˡ Tᵃ □ᵇ F □ʳ` this gives Conjecture 1 of
Thanatipanonda, *Further Hopping with Toads and Frogs* (`t1_*`).
-/

namespace Cgt
namespace OneFrog

open Cell TF Game

/-! ### The general theorem -/

theorem value_room_ge_two {L B : List Bool} (hT : 0 < cT L) (h : 2 ≤ room L B) :
    Equiv (V L B) (int (phi L B).toNat) := by
  have hB : 1 ≤ cE B := by unfold room at h; omega
  have hge := phi_ge (L := L) (B := B) hT hB
  exact ⟨(upper_all L B).u1 hT (Or.inl h), int_le_V_of_le_phi (by omega)⟩

theorem value_room_one_even {L B : List Bool} (hT : 0 < cT L) (h : room L B = 1)
    (hg : gap L % 2 = 0) : Equiv (V L B) (int (phi L B).toNat) := by
  have hB : 1 ≤ cE B := by unfold room at h; omega
  have hge := phi_ge (L := L) (B := B) hT hB
  exact ⟨(upper_all L B).u1 hT (Or.inr ⟨h, hg⟩), int_le_V_of_le_phi (by omega)⟩

theorem value_room_one_odd {L B : List Bool} (hT : 0 < cT L) (h : room L B = 1)
    (hg : gap L % 2 = 1) : Equiv (V L B) (half (phi L B).toNat) := by
  have hB : 1 ≤ cE B := by unfold room at h; omega
  have hge := phi_ge (L := L) (B := B) hT hB
  exact ⟨(upper_all L B).u3 hT h hg, lower_half hT h hg (by omega)⟩

theorem value_room_zero_even {L B : List Bool} (hT : 0 < cT L) (h : room L B = 0)
    (hg : gap L % 2 = 0) (hphi : -1 ≤ phi L B) : Equiv (V L B) (int (phi L B + 1).toNat) :=
  ⟨(upper_all L B).u4 hT h hg, lower1 hT (Or.inr ⟨h, hg⟩) (by omega)⟩

theorem value_room_zero_odd {L B : List Bool} (hT : 0 < cT L) (h : room L B = 0)
    (hg : gap L % 2 = 1) (hphi : 0 ≤ phi L B) : Equiv (V L B) (starN (phi L B + 1).toNat) :=
  ⟨(upper_all L B).u5 hT h hg hphi, lower_star hT h hg (by omega)⟩

/-- One toad, `room = 0`, an odd gap, and the toads right of the frog cannot move. -/
theorem value_one_toad_odd {L B : List Bool} (hT : cT L = 1) (h : room L B = 0)
    (hg : gap L % 2 = 1) (hphi : phi L B = -1) : Equiv (V L B) (starN 0) :=
  ⟨(upper_all L B).u5z hT h hg hphi, lower_star (by omega) h hg (by omega)⟩

/-! ### The positions `□ˡ Tᵃ □ᵇ F □ʳ` -/

/-- The left side of `□ˡ Tᵃ □ᵇ F □ʳ`, read from the frog. -/
def side (l a b : Nat) : List Bool :=
  List.replicate b false ++ (List.replicate a true ++ List.replicate l false)

theorem oneFrog_eq (l a b r : Nat) : oneFrog l a b r = pos (side l a b) (List.replicate r false) := by
  simp [oneFrog, pos, side, cell, List.map_append, List.map_replicate, List.reverse_append,
    List.reverse_replicate]

theorem gap_replicate_false_append (b : Nat) (X : List Bool) :
    gap (List.replicate b false ++ X) = b + gap X := by
  induction b with
  | zero => simp
  | succ b ih => rw [List.replicate_succ, List.cons_append, gap_false, ih]; omega

theorem behind_replicate_false_append (b : Nat) (X : List Bool) :
    behind (List.replicate b false ++ X) = behind X := by
  induction b with
  | zero => simp
  | succ b ih => rw [List.replicate_succ, List.cons_append]; simpa [behind] using ih

theorem cT_side (l a b : Nat) : cT (side l a b) = a := by
  simp [side, cT_append, cT_replicate_true, cT_replicate_false]

theorem cE_side (l a b : Nat) : cE (side l a b) = b + l := by
  simp [side, cE_append, cE_replicate_true, cE_replicate_false]

theorem gap_side (l a b : Nat) : gap (side l (a + 1) b) = b := by
  rw [side, gap_replicate_false_append, List.replicate_succ, List.cons_append, gap_true]; rfl

theorem behind_side (l a b : Nat) : behind (side l (a + 1) b) = l := by
  rw [side, behind_replicate_false_append, List.replicate_succ, List.cons_append]
  simp [behind, cE_append, cE_replicate_true, cE_replicate_false]

theorem room_side (l a b r : Nat) :
    room (side l (a + 1) b) (List.replicate r false) = (r : Int) - l := by
  unfold room; rw [behind_side, cE_replicate_false]

/-- `phi (□ˡ Tᵃ⁺¹ □ᵇ F □ʳ) = a (b + r - 1) + r - l - 1`. -/
theorem phi_side (l a b r : Nat) :
    phi (side l (a + 1) b) (List.replicate r false) =
      ((a * b + a * r + r : Nat) : Int) - ((a + l + 1 : Nat) : Int) := by
  have h1 : invL (side l (a + 1) b) = b * (a + 1) := by
    rw [side, invL_replicate_false_append, invL_packed, cT_append, cT_replicate_true,
      cT_replicate_false]
    simp
  have h2 : invB (List.replicate r false) = 0 := by
    have := invB_packed 0 r; simpa using this
  unfold phi
  rw [h1, h2, cT_side, cE_side, cE_replicate_false]
  simp only [Nat.mul_succ, Nat.succ_mul, Nat.mul_comm b a]
  omega

/-- The number `(a - 1)(b - 1 + r)` of the conjecture, for `a + 1` toads. -/
theorem mul_pred (a b r : Nat) (h : 1 ≤ b + r) : a * (b + r - 1) + a = a * b + a * r := by
  obtain ⟨c, hc⟩ : ∃ c, b + r = c + 1 := ⟨b + r - 1, by omega⟩
  rw [← Nat.mul_add, hc, Nat.add_sub_cancel, Nat.mul_succ]

/-- **Conjecture T1, case `r - l ≥ 2`**: `□ˡ Tᵃ □ᵇ F □ʳ = (r - l - 1) + (a - 1)(b - 1 + r)`. -/
theorem t1_far (l a b r : Nat) (h : l + 2 ≤ r) :
    Equiv (tf (oneFrog l (a + 1) b r)) (int (r - l - 1 + a * (b + r - 1))) := by
  have hv := value_room_ge_two (L := side l (a + 1) b) (B := List.replicate r false)
    (by rw [cT_side]; omega) (by rw [room_side]; omega)
  have hm := mul_pred a b r (by omega)
  rw [oneFrog_eq]
  rwa [show (phi (side l (a + 1) b) (List.replicate r false)).toNat = r - l - 1 + a * (b + r - 1)
    by rw [phi_side]; omega] at hv

/-- **Conjecture T1, case `l = r - 1`, `b` even**: `□ʳ⁻¹ Tᵃ □ᵇ F □ʳ = (a - 1)(b - 1 + r)`. -/
theorem t1_near_even (a b r : Nat) (hb : b % 2 = 0) :
    Equiv (tf (oneFrog r (a + 1) b (r + 1))) (int (a * (b + (r + 1) - 1))) := by
  have hv := value_room_one_even (L := side r (a + 1) b) (B := List.replicate (r + 1) false)
    (by rw [cT_side]; omega) (by rw [room_side]; omega) (by rw [gap_side]; exact hb)
  have hm := mul_pred a b (r + 1) (by omega)
  rw [oneFrog_eq]
  rwa [show (phi (side r (a + 1) b) (List.replicate (r + 1) false)).toNat = a * (b + (r + 1) - 1)
    by rw [phi_side]; omega] at hv

/-- **Conjecture T1, case `l = r - 1`, `b` odd**: `□ʳ⁻¹ Tᵃ □ᵇ F □ʳ = (a - 1)(b - 1 + r) + 1/2`. -/
theorem t1_near_odd (a b r : Nat) (hb : b % 2 = 1) :
    Equiv (tf (oneFrog r (a + 1) b (r + 1))) (half (a * (b + (r + 1) - 1))) := by
  have hv := value_room_one_odd (L := side r (a + 1) b) (B := List.replicate (r + 1) false)
    (by rw [cT_side]; omega) (by rw [room_side]; omega) (by rw [gap_side]; exact hb)
  have hm := mul_pred a b (r + 1) (by omega)
  rw [oneFrog_eq]
  rwa [show (phi (side r (a + 1) b) (List.replicate (r + 1) false)).toNat = a * (b + (r + 1) - 1)
    by rw [phi_side]; omega] at hv

/-- **Conjecture T1, case `l = r`, `b` even**: `□ʳ Tᵃ □ᵇ F □ʳ = (a - 1)(b - 1 + r)`, if `b + r ≥ 1`.
(For `b = r = 0` and `a ≥ 2` the formula is negative, and `Tᵃ F = 0`.) -/
theorem t1_equal_even (a b r : Nat) (hb : b % 2 = 0) (hbr : 1 ≤ b + r) :
    Equiv (tf (oneFrog r (a + 1) b r)) (int (a * (b + r - 1))) := by
  have hm := mul_pred a b r hbr
  have hphi : phi (side r (a + 1) b) (List.replicate r false) = ((a * (b + r - 1) : Nat) : Int) - 1 := by
    rw [phi_side]; omega
  have hv := value_room_zero_even (L := side r (a + 1) b) (B := List.replicate r false)
    (by rw [cT_side]; omega) (by rw [room_side]; omega) (by rw [gap_side]; exact hb)
    (by rw [hphi]; omega)
  rw [oneFrog_eq]
  rwa [show (phi (side r (a + 1) b) (List.replicate r false) + 1).toNat = a * (b + r - 1)
    by rw [hphi]; omega] at hv

/-- **Conjecture T1, case `l = r`, `b` odd**: `□ʳ Tᵃ □ᵇ F □ʳ = ((a - 1)(b - 1 + r))∗`, unless
`r = 0`, `b = 1` and `a ≥ 2` (the conjecture's exception `Tᵃ □ F`). -/
theorem t1_equal_odd (a b r : Nat) (hb : b % 2 = 1) (hex : a = 0 ∨ 2 ≤ b + r) :
    Equiv (tf (oneFrog r (a + 1) b r)) (starN (a * (b + r - 1))) := by
  have hm := mul_pred a b r (by omega)
  have hphi : phi (side r (a + 1) b) (List.replicate r false) = ((a * (b + r - 1) : Nat) : Int) - 1 := by
    rw [phi_side]; omega
  rw [oneFrog_eq]
  rcases Nat.eq_zero_or_pos (a * (b + r - 1)) with h0 | h0
  · rcases hex with ha | hbr
    · subst ha
      have hv := value_one_toad_odd (L := side r 1 b) (B := List.replicate r false)
        (by rw [cT_side]) (by rw [room_side]; omega) (by rw [gap_side]; exact hb)
        (by rw [hphi]; omega)
      rw [Nat.zero_mul]
      exact hv
    · have ha : a = 0 := by
        rcases Nat.eq_zero_or_pos a with ha | ha
        · exact ha
        · have : 1 ≤ a * (b + r - 1) := Nat.mul_pos ha (by omega)
          omega
      subst ha
      have hv := value_one_toad_odd (L := side r 1 b) (B := List.replicate r false)
        (by rw [cT_side]) (by rw [room_side]; omega) (by rw [gap_side]; exact hb)
        (by rw [hphi]; omega)
      rw [Nat.zero_mul]
      exact hv
  · have hv := value_room_zero_odd (L := side r (a + 1) b) (B := List.replicate r false)
      (by rw [cT_side]; omega) (by rw [room_side]; omega) (by rw [gap_side]; exact hb)
      (by rw [hphi]; omega)
    rwa [show (phi (side r (a + 1) b) (List.replicate r false) + 1).toNat = a * (b + r - 1)
      by rw [hphi]; omega] at hv

end OneFrog
end Cgt
