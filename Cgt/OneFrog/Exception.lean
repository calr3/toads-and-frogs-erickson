import Cgt.OneFrog.T1

/-!
# The exception of Conjecture T1: `Tᵃ □ F = {{a - 2 | 1} | 0}` for `a ≥ 2`

Here `l = r = 0` and `b = 1`. Left's only move is to `Tᵃ⁻¹ □ T F`, whose options are
`Tᵃ⁻² □ T T F = a - 2` (the frog can never move) and, after the frog's jump, `Tᵃ⁻¹ F T □ = 1`.
Right's only move is to `Tᵃ F □ = 0`.
-/

namespace Cgt
namespace OneFrog

open Cell TF Game

theorem equiv_of_options' {g h : Game}
    (hl1 : ∀ x ∈ g.left, ∃ x' ∈ h.left, Equiv x x') (hl2 : ∀ x' ∈ h.left, ∃ x ∈ g.left, Equiv x' x)
    (hr1 : ∀ y ∈ g.right, ∃ y' ∈ h.right, Equiv y y')
    (hr2 : ∀ y' ∈ h.right, ∃ y ∈ g.right, Equiv y' y) : Equiv g h := by
  cases g; cases h; exact equiv_of_options hl1 hl2 hr1 hr2

theorem not_replicate_true_eq (i : Nat) (u r : List Bool) :
    List.replicate i true ≠ u ++ false :: r := by
  intro h
  have := congrArg cE h
  rw [cE_replicate_true, cE_append] at this
  simp [cE] at this

/-! ### A frog behind two toads never moves -/

theorem dead_frog : ∀ (N : Nat) (L' : List Bool), invL L' < N →
    Equiv (V (true :: true :: L') []) (int (invL L')) := by
  intro N
  induction N with
  | zero => intro L' h; exact absurd h (Nat.not_lt_zero _)
  | succ N ih =>
    intro L' hN
    constructor
    · apply V_le_int
      intro L₁ B₁ hm
      rcases hm with ⟨u, r, hu, rfl, rfl⟩ | ⟨u, r, hu, -, -⟩ | ⟨L'', B', -, hB, -, -⟩
      · left
        match u, hu with
        | true :: true :: u', hu =>
          simp only [List.cons_append, List.cons.injEq, true_and] at hu
          subst hu
          have h1 := invL_lmove u' r
          refine ⟨by omega, ?_⟩
          have := (ih (u' ++ true :: false :: r) (by omega)).1
          rwa [show invL (u' ++ true :: false :: r) = invL (u' ++ false :: true :: r) - 1 by omega]
            at this
        | [true], hu => simp at hu
        | [], hu => simp at hu
      · simp at hu
      · simp at hB
    · apply int_le_V
      · rcases lmove_or_packed L' with ⟨u, r, rfl⟩ | hL
        · right
          have h1 := invL_lmove u r
          refine ⟨true :: true :: (u ++ true :: false :: r), [],
            Or.inl ⟨true :: true :: u, r, rfl, rfl, rfl⟩, ?_⟩
          have := (ih (u ++ true :: false :: r) (by omega)).2
          rwa [show invL (u ++ true :: false :: r) = invL (u ++ false :: true :: r) - 1 by omega]
            at this
        · left; rw [hL]; exact invL_packed _ _
      · intro L₂ h; simp at h
      · intro L₂ h; simp at h

theorem invL_replicate_true (i : Nat) : invL (List.replicate i true) = 0 := by
  have := invL_packed i 0; simpa using this

/-- `Tᵃ □ T T F = a`. -/
theorem dead_frog_value (a : Nat) :
    Equiv (V (true :: true :: false :: List.replicate a true) []) (int a) := by
  have := dead_frog _ (false :: List.replicate a true) (Nat.lt_succ_self _)
  simpa [invL, invL_replicate_true, cT_replicate_true] using this

/-! ### The two positions with `room = 1` -/

theorem behind_replicate_true (i : Nat) : behind (List.replicate i true) = 0 := by
  cases i with
  | zero => rfl
  | succ i => rw [List.replicate_succ]; simp [behind, cE_replicate_true]

theorem gap_replicate_true (i : Nat) : gap (List.replicate i true) = 0 := by
  cases i with
  | zero => rfl
  | succ i => rw [List.replicate_succ]; rfl

/-- `Tᵃ F □ = 0`. -/
theorem value_block_one (a : Nat) : Equiv (V (List.replicate (a + 1) true) [false]) (int 0) := by
  have hv := value_room_one_even (L := List.replicate (a + 1) true) (B := [false])
    (by rw [cT_replicate_true]; omega)
    (by unfold room; rw [behind_replicate_true]; simp [cE])
    (by rw [gap_replicate_true])
  rwa [show (phi (List.replicate (a + 1) true) [false]).toNat = 0 by
    unfold phi; rw [invL_replicate_true, cT_replicate_true, cE_replicate_true]; simp [invB, cE]]
    at hv

/-- `Tᵃ F T □ = 1`. -/
theorem value_block_jumped (a : Nat) :
    Equiv (V (List.replicate (a + 1) true) [true, false]) (int 1) := by
  have hv := value_room_one_even (L := List.replicate (a + 1) true) (B := [true, false])
    (by rw [cT_replicate_true]; omega)
    (by unfold room; rw [behind_replicate_true]; simp [cE])
    (by rw [gap_replicate_true])
  rwa [show (phi (List.replicate (a + 1) true) [true, false]).toNat = 1 by
    unfold phi; rw [invL_replicate_true, cT_replicate_true, cE_replicate_true]; simp [invB, cE]]
    at hv

/-! ### The exception -/

/-- `Tᵃ⁺¹ □ T F = {a | 1}`. -/
theorem value_exception_left (a : Nat) :
    Equiv (V (true :: false :: List.replicate (a + 1) true) []) (mk [int a] [int 1]) := by
  have hm : LM (true :: false :: List.replicate (a + 1) true) []
      (true :: true :: false :: List.replicate a true) [] :=
    Or.inl ⟨[true], List.replicate a true, by simp [List.replicate_succ], rfl, rfl⟩
  apply equiv_of_options'
  · intro x hx
    obtain ⟨L₁, B₁, h, rfl⟩ := mem_left_V.1 hx
    refine ⟨int a, by simp, ?_⟩
    rcases h with ⟨u, r, hu, rfl, rfl⟩ | ⟨u, r, hu, -, -⟩ | ⟨L'', B', -, hB, -, -⟩
    · match u, hu with
      | [], hu => simp at hu
      | [c], hu =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and,
          List.replicate_succ] at hu
        obtain ⟨rfl, rfl⟩ := hu
        exact dead_frog_value a
      | c :: d :: u', hu =>
        simp only [List.cons_append, List.cons.injEq] at hu
        exact absurd hu.2.2 (not_replicate_true_eq _ _ _)
    · simp at hu
    · simp at hB
  · intro x' hx'
    simp only [left_mk, List.mem_singleton] at hx'
    subst hx'
    exact ⟨_, mem_left_V.2 ⟨_, _, hm, rfl⟩, (dead_frog_value a).symm⟩
  · intro y hy
    refine ⟨int 1, by simp, ?_⟩
    rcases mem_right_V.1 hy with ⟨L₂, h, rfl⟩ | ⟨L₂, h, rfl⟩
    · simp at h
    · simp only [List.cons.injEq, true_and] at h
      subst h
      exact value_block_jumped a
  · intro y' hy'
    simp only [right_mk, List.mem_singleton] at hy'
    subst hy'
    exact ⟨_, mem_right_V.2 (Or.inr ⟨_, rfl, rfl⟩), (value_block_jumped a).symm⟩

/-- `Tᵃ⁺² □ F = {{a | 1} | 0}`. -/
theorem value_exception (a : Nat) :
    Equiv (V (false :: List.replicate (a + 2) true) []) (mk [mk [int a] [int 1]] [int 0]) := by
  have hm : LM (false :: List.replicate (a + 2) true) []
      (true :: false :: List.replicate (a + 1) true) [] :=
    Or.inl ⟨[], List.replicate (a + 1) true, by simp [List.replicate_succ], rfl, rfl⟩
  apply equiv_of_options'
  · intro x hx
    obtain ⟨L₁, B₁, h, rfl⟩ := mem_left_V.1 hx
    refine ⟨mk [int a] [int 1], by simp, ?_⟩
    rcases h with ⟨u, r, hu, rfl, rfl⟩ | ⟨u, r, hu, -, -⟩ | ⟨L'', B', hL, -, -, -⟩
    · match u, hu with
      | [], hu =>
        simp only [List.nil_append, List.cons.injEq, true_and] at hu
        rw [List.replicate_succ] at hu
        simp only [List.cons.injEq, true_and] at hu
        subst hu
        exact value_exception_left a
      | c :: u', hu =>
        simp only [List.cons_append, List.cons.injEq] at hu
        exact absurd hu.2 (not_replicate_true_eq _ _ _)
    · simp at hu
    · simp at hL
  · intro x' hx'
    simp only [left_mk, List.mem_singleton] at hx'
    subst hx'
    exact ⟨_, mem_left_V.2 ⟨_, _, hm, rfl⟩, (value_exception_left a).symm⟩
  · intro y hy
    refine ⟨int 0, by simp, ?_⟩
    rcases mem_right_V.1 hy with ⟨L₂, h, rfl⟩ | ⟨L₂, h, rfl⟩
    · simp only [List.cons.injEq, true_and] at h
      subst h
      exact value_block_one (a + 1)
    · simp at h
  · intro y' hy'
    simp only [right_mk, List.mem_singleton] at hy'
    subst hy'
    exact ⟨_, mem_right_V.2 (Or.inl ⟨_, rfl, rfl⟩), (value_block_one (a + 1)).symm⟩

/-- **Conjecture T1, the exception**: `Tᵃ □ F = {{a - 2 | 1} | 0}` for `a ≥ 2`. -/
theorem t1_exception (a : Nat) :
    Equiv (tf (oneFrog 0 (a + 2) 1 0)) (mk [mk [int a] [int 1]] [int 0]) := by
  have h : side 0 (a + 2) 1 = false :: List.replicate (a + 2) true := by simp [side]
  rw [oneFrog_eq, h]
  exact value_exception a

end OneFrog
end Cgt
