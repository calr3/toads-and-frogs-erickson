import Cgt.ToadsFrogs
import Cgt.OneFrog.Num
import Cgt.OneFrog.Pos

/-!
# One-frog positions: moves and comparison rules

`V L B` is the game value of the one-frog position `pos L B`. `LM L B L₁ B₁` says that Left can
move from `pos L B` to `pos L₁ B₁`. The frog has at most one move: a slide when `L = false :: _`,
a jump when `L = true :: false :: _`.

The comparison rules of `Cgt/OneFrog/Num.lean` are restated for `V`, and each Left move is sorted
into one of three kinds (`LM_cases`): a move that leaves the nearest toad alone, a slide of the
nearest toad, or a jump over the frog.
-/

namespace Cgt
namespace OneFrog

open Cell TF Game

/-- The value of the one-frog position `pos L B`. -/
def V (L B : List Bool) : Game := tf (pos L B)

/-- `room L B = D`: empty squares right of the frog minus empty squares left of the nearest toad. -/
def room (L B : List Bool) : Int := (cE B : Int) - (behind L : Int)

/-- Left can move from `pos L B` to `pos L₁ B₁`. -/
def LM (L B L₁ B₁ : List Bool) : Prop :=
  (∃ u r, L = u ++ false :: true :: r ∧ L₁ = u ++ true :: false :: r ∧ B₁ = B) ∨
  (∃ u r, B = u ++ true :: false :: r ∧ L₁ = L ∧ B₁ = u ++ false :: true :: r) ∨
  (∃ L' B', L = true :: L' ∧ B = false :: B' ∧ L₁ = false :: L' ∧ B₁ = true :: B')

theorem mem_left_V {L B : List Bool} {x : Game} :
    x ∈ (V L B).left ↔ ∃ L₁ B₁, LM L B L₁ B₁ ∧ x = V L₁ B₁ := by
  unfold V
  rw [mem_left_tf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases mem_leftMoves_pos.1 hq with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, rfl⟩ | ⟨L', B', rfl, rfl, rfl⟩
    · exact ⟨_, _, Or.inl ⟨u, r, rfl, rfl, rfl⟩, rfl⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨u, r, rfl, rfl, rfl⟩), rfl⟩
    · exact ⟨_, _, Or.inr (Or.inr ⟨L', B', rfl, rfl, rfl, rfl⟩), rfl⟩
  · rintro ⟨L₁, B₁, h, rfl⟩
    refine ⟨_, mem_leftMoves_pos.2 ?_, rfl⟩
    rcases h with ⟨u, r, rfl, rfl, rfl⟩ | ⟨u, r, rfl, rfl, rfl⟩ | ⟨L', B', rfl, rfl, rfl, rfl⟩
    · exact Or.inl ⟨u, r, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨u, r, rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨L', B', rfl, rfl, rfl⟩)

theorem mem_right_V {L B : List Bool} {y : Game} :
    y ∈ (V L B).right ↔
      (∃ L₂, L = false :: L₂ ∧ y = V L₂ (false :: B)) ∨
      (∃ L₂, L = true :: false :: L₂ ∧ y = V L₂ (true :: false :: B)) := by
  unfold V
  rw [mem_right_tf]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases mem_rightMoves_pos.1 hq with ⟨L₂, rfl, rfl⟩ | ⟨L₂, rfl, rfl⟩
    · exact Or.inl ⟨L₂, rfl, rfl⟩
    · exact Or.inr ⟨L₂, rfl, rfl⟩
  · rintro (⟨L₂, rfl, rfl⟩ | ⟨L₂, rfl, rfl⟩)
    · exact ⟨_, mem_rightMoves_pos.2 (Or.inl ⟨L₂, rfl, rfl⟩), rfl⟩
    · exact ⟨_, mem_rightMoves_pos.2 (Or.inr ⟨L₂, rfl, rfl⟩), rfl⟩

theorem slide_mem_right (L₂ B : List Bool) : V L₂ (false :: B) ∈ (V (false :: L₂) B).right :=
  mem_right_V.2 (Or.inl ⟨L₂, rfl, rfl⟩)

/-! ### Termination measure -/

/-- The measure of `Cgt/Statement.lean` on a one-frog position. -/
def mu (L B : List Bool) : Nat := pot (pos L B)

theorem mu_LM {L B L₁ B₁ : List Bool} (h : LM L B L₁ B₁) : mu L₁ B₁ < mu L B := by
  apply pot_lt_of_mem_leftMoves
  apply mem_leftMoves_pos.2
  rcases h with ⟨u, r, rfl, rfl, rfl⟩ | ⟨u, r, rfl, rfl, rfl⟩ | ⟨L', B', rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨u, r, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨u, r, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨L', B', rfl, rfl, rfl⟩)

theorem mu_slide (L₂ B : List Bool) : mu L₂ (false :: B) < mu (false :: L₂) B :=
  pot_lt_of_mem_rightMoves (mem_rightMoves_pos.2 (Or.inl ⟨L₂, rfl, rfl⟩))

theorem mu_fjump (L₂ B : List Bool) : mu L₂ (true :: false :: B) < mu (true :: false :: L₂) B :=
  pot_lt_of_mem_rightMoves (mem_rightMoves_pos.2 (Or.inr ⟨L₂, rfl, rfl⟩))

/-! ### Comparison rules for `V` -/

theorem V_le_int_zero {L B : List Bool}
    (h : ∀ L₁ B₁, LM L B L₁ B₁ → ∃ L₂, L₁ = false :: L₂ ∧ le (V L₂ (false :: B₁)) (int 0)) :
    le (V L B) (int 0) := by
  apply le_int_zero_of
  intro x hx
  obtain ⟨L₁, B₁, hm, rfl⟩ := mem_left_V.1 hx
  obtain ⟨L₂, rfl, h2⟩ := h L₁ B₁ hm
  exact ⟨_, slide_mem_right L₂ B₁, h2⟩

theorem V_le_int_succ {L B : List Bool} {n : Nat}
    (h : ∀ L₁ B₁, LM L B L₁ B₁ → le (V L₁ B₁) (int n) ∨
      ∃ L₂, L₁ = false :: L₂ ∧ le (V L₂ (false :: B₁)) (int (n + 1))) :
    le (V L B) (int (n + 1)) := by
  apply le_int_succ_of
  intro x hx
  obtain ⟨L₁, B₁, hm, rfl⟩ := mem_left_V.1 hx
  rcases h L₁ B₁ hm with h1 | ⟨L₂, rfl, h2⟩
  · exact Or.inl h1
  · exact Or.inr ⟨_, slide_mem_right L₂ B₁, h2⟩

/-- Both integer rules at once: a Left move either costs Left a move, or is answered by a slide. -/
theorem V_le_int {L B : List Bool} {n : Nat}
    (h : ∀ L₁ B₁, LM L B L₁ B₁ → (0 < n ∧ le (V L₁ B₁) (int (n - 1))) ∨
      ∃ L₂, L₁ = false :: L₂ ∧ le (V L₂ (false :: B₁)) (int n)) :
    le (V L B) (int n) := by
  cases n with
  | zero =>
    apply V_le_int_zero
    intro L₁ B₁ hm
    rcases h L₁ B₁ hm with ⟨h0, -⟩ | h2
    · exact absurd h0 (Nat.lt_irrefl 0)
    · exact h2
  | succ n =>
    apply V_le_int_succ
    intro L₁ B₁ hm
    rcases h L₁ B₁ hm with ⟨-, h1⟩ | h2
    · exact Or.inl h1
    · exact Or.inr h2

theorem V_le_half {L₂ B : List Bool} {n : Nat}
    (h1 : ∀ L₁ B₁, LM (false :: L₂) B L₁ B₁ → le (V L₁ B₁) (int n) ∨
      ∃ L₃, L₁ = false :: L₃ ∧ le (V L₃ (false :: B₁)) (half n))
    (h2 : le (V L₂ (false :: B)) (int (n + 1))) :
    le (V (false :: L₂) B) (half n) := by
  apply le_half_of
  · intro x hx
    obtain ⟨L₁, B₁, hm, rfl⟩ := mem_left_V.1 hx
    rcases h1 L₁ B₁ hm with h | ⟨L₃, rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, slide_mem_right L₃ B₁, h⟩
  · exact ⟨_, slide_mem_right L₂ B, h2⟩

theorem V_le_starN {L₂ B : List Bool} {n : Nat}
    (h1 : ∀ L₁ B₁, LM (false :: L₂) B L₁ B₁ → le (V L₁ B₁) (int n) ∨
      ∃ L₃, L₁ = false :: L₃ ∧ le (V L₃ (false :: B₁)) (starN n))
    (h2 : le (V L₂ (false :: B)) (int n)) :
    le (V (false :: L₂) B) (starN n) := by
  apply le_starN_of
  · intro x hx
    obtain ⟨L₁, B₁, hm, rfl⟩ := mem_left_V.1 hx
    rcases h1 L₁ B₁ hm with h | ⟨L₃, rfl, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, slide_mem_right L₃ B₁, h⟩
  · exact ⟨_, slide_mem_right L₂ B, h2⟩

theorem int_le_V {L B : List Bool} {n : Nat}
    (h1 : n = 0 ∨ ∃ L₁ B₁, LM L B L₁ B₁ ∧ le (int (n - 1)) (V L₁ B₁))
    (h2 : ∀ L₂, L = false :: L₂ → ∃ L₃ B₃, LM L₂ (false :: B) L₃ B₃ ∧ le (int n) (V L₃ B₃))
    (h3 : ∀ L₂, L = true :: false :: L₂ →
      ∃ L₃ B₃, LM L₂ (true :: false :: B) L₃ B₃ ∧ le (int n) (V L₃ B₃)) :
    le (int n) (V L B) := by
  apply int_le_of
  · rcases h1 with h | ⟨L₁, B₁, hm, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, mem_left_V.2 ⟨L₁, B₁, hm, rfl⟩, h⟩
  · intro y hy
    rcases mem_right_V.1 hy with ⟨L₂, rfl, rfl⟩ | ⟨L₂, rfl, rfl⟩
    · obtain ⟨L₃, B₃, hm, h⟩ := h2 L₂ rfl
      exact ⟨_, mem_left_V.2 ⟨L₃, B₃, hm, rfl⟩, h⟩
    · obtain ⟨L₃, B₃, hm, h⟩ := h3 L₂ rfl
      exact ⟨_, mem_left_V.2 ⟨L₃, B₃, hm, rfl⟩, h⟩

/-! ### Kinds of Left move -/

theorem phi_LM {L B L₁ B₁ : List Bool} (h : LM L B L₁ B₁) : phi L₁ B₁ = phi L B - 1 := by
  rcases h with ⟨u, r, rfl, rfl, rfl⟩ | ⟨u, r, rfl, rfl, rfl⟩ | ⟨L', B', rfl, rfl, rfl, rfl⟩
  · exact phi_lmove u r _
  · exact phi_bmove _ u r
  · exact phi_jump L' B'

/-- A Left move is of one of three kinds: it leaves the nearest toad alone; it slides the nearest
toad; or the nearest toad jumps the frog. -/
theorem LM_cases {L B L₁ B₁ : List Bool} (h : LM L B L₁ B₁) :
    (cT L₁ = cT L ∧ gap L₁ = gap L ∧ behind L₁ = behind L ∧ cE B₁ = cE B) ∨
    (cT L₁ = cT L ∧ gap L₁ + 1 = gap L ∧ behind L₁ = behind L + 1 ∧ B = B₁) ∨
    (∃ L' B', L = true :: L' ∧ B = false :: B' ∧ L₁ = false :: L' ∧ B₁ = true :: B') := by
  rcases h with ⟨u, r, rfl, rfl, rfl⟩ | ⟨u, r, rfl, rfl, rfl⟩ | ⟨L', B', rfl, rfl, rfl, rfl⟩
  · rcases gap_behind_lmove u r with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · exact Or.inr (Or.inl ⟨cT_lmove u r, h1, h2, rfl⟩)
    · exact Or.inl ⟨cT_lmove u r, h1, h2, rfl⟩
  · exact Or.inl ⟨rfl, rfl, rfl, cE_bmove u r⟩
  · exact Or.inr (Or.inr ⟨L', B', rfl, rfl, rfl, rfl⟩)

/-- With a positive gap the frog can slide. -/
theorem exists_slide {L : List Bool} (h : 0 < gap L) :
    ∃ L₂, L = false :: L₂ ∧ gap L₂ + 1 = gap L ∧ behind L₂ = behind L ∧ cT L₂ = cT L := by
  match L, h with
  | false :: L₂, _ => exact ⟨L₂, rfl, rfl, rfl, rfl⟩

/-- With no gap and a toad, the nearest toad is next to the frog. -/
theorem exists_contact {L : List Bool} (h : gap L = 0) (hT : 0 < cT L) :
    ∃ L', L = true :: L' ∧ behind L = cE L' ∧ cT L' + 1 = cT L := by
  match L, h, hT with
  | true :: L', _, _ => exact ⟨L', rfl, rfl, rfl⟩

theorem front_shape {L : List Bool} (h : 0 < gap L) (hT : 0 < cT L) :
    ∃ u r, L = u ++ false :: true :: r ∧ cT u = 0 := by
  induction L with
  | nil => simp at h
  | cons c X ih =>
    match c, X, h, hT with
    | false, true :: r, _, _ => exact ⟨[], r, rfl, rfl⟩
    | false, false :: r, _, hT =>
      obtain ⟨u, r', hu, hc⟩ := ih (by simp) (by simpa [cT] using hT)
      exact ⟨false :: u, r', by simp [hu], by simpa [cT] using hc⟩
    | false, [], _, hT => simp [cT] at hT

/-- With a positive gap and a toad, the nearest toad can slide. -/
theorem exists_front_slide {L : List Bool} (B : List Bool) (h : 0 < gap L) (hT : 0 < cT L) :
    ∃ L₁, LM L B L₁ B ∧ cT L₁ = cT L ∧ gap L₁ + 1 = gap L ∧ behind L₁ = behind L + 1 := by
  obtain ⟨u, r, rfl, hc⟩ := front_shape h hT
  refine ⟨_, Or.inl ⟨u, r, rfl, rfl, rfl⟩, cT_lmove u r, ?_⟩
  rcases gap_behind_lmove u r with ⟨-, h1, h2⟩ | ⟨h0, -, -⟩
  · exact ⟨h1, h2⟩
  · omega

/-- A position in which no toad can slide: `E^j T^i F E^j' T^i'`. -/
theorem phi_packed (i j j' i' : Nat) :
    phi (List.replicate i true ++ List.replicate j false)
        (List.replicate j' false ++ List.replicate i' true) =
      ((i * j' : Nat) : Int) - ((i + j : Nat) : Int) := by
  unfold phi
  rw [invL_packed, invB_packed, cT_append, cE_append, cE_append, cT_replicate_true,
    cT_replicate_false, cE_replicate_true, cE_replicate_false, cE_replicate_true,
    cE_replicate_false]
  simp

/-- Either Left has a move that is not a jump, or no toad can slide. -/
theorem slide_or_packed (L B : List Bool) :
    (∃ L₁ B₁, LM L B L₁ B₁ ∧ cT L₁ = cT L ∧ cE B₁ = cE B ∧
      ((gap L₁ = gap L ∧ behind L₁ = behind L) ∨ (gap L₁ + 1 = gap L ∧ behind L₁ = behind L + 1 ∧ B₁ = B))) ∨
    (L = List.replicate (cT L) true ++ List.replicate (cE L) false ∧
      B = List.replicate (cE B) false ++ List.replicate (cT B) true) := by
  rcases lmove_or_packed L with ⟨u, r, rfl⟩ | hL
  · left
    refine ⟨_, _, Or.inl ⟨u, r, rfl, rfl, rfl⟩, cT_lmove u r, rfl, ?_⟩
    rcases gap_behind_lmove u r with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
    · exact Or.inr ⟨h1, h2, rfl⟩
    · exact Or.inl ⟨h1, h2⟩
  rcases bmove_or_packed B with ⟨u, r, rfl⟩ | hB
  · left
    exact ⟨_, _, Or.inr (Or.inl ⟨u, r, rfl, rfl, rfl⟩), rfl, cE_bmove u r, Or.inl ⟨rfl, rfl⟩⟩
  · exact Or.inr ⟨hL, hB⟩

/-- If `phi` is positive, Left has a move. -/
theorem exists_LM_of_phi_pos {L B : List Bool} (h : 0 < phi L B) : ∃ L₁ B₁, LM L B L₁ B₁ := by
  rcases slide_or_packed L B with ⟨L₁, B₁, hm, -⟩ | ⟨hL, hB⟩
  · exact ⟨L₁, B₁, hm⟩
  rw [hL, hB, phi_packed] at h
  cases hi : cT L with
  | zero => rw [hi] at h; simp at h; omega
  | succ i =>
    cases hj : cE B with
    | zero => rw [hi, hj] at h; simp at h; omega
    | succ j =>
      rw [hi] at hL; rw [hj] at hB
      rw [List.replicate_succ, List.cons_append] at hL hB
      exact ⟨_, _, Or.inr (Or.inr ⟨_, _, hL, hB, rfl, rfl⟩)⟩

end OneFrog
end Cgt
