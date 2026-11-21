import Cgt.Game

/-!
# Integers, half-integers and `n∗` as games

The games `n`, `n + 1/2` and `n∗` for `n : Nat`, with one-step sufficient conditions for
comparing an arbitrary game against them and the basic order facts between them.
-/

namespace Cgt

namespace Game

/-- The integer `n ≥ 0` as a game: `0 = { | }`, `n + 1 = {n | }`. -/
def int : Nat → Game
  | 0 => zero
  | n + 1 => mk [int n] []

/-- `n + 1/2 = {n | n + 1}`. -/
def half (n : Nat) : Game := mk [int n] [int (n + 1)]

/-- `n∗ = {n | n}`. -/
def starN (n : Nat) : Game := mk [int n] [int n]

private theorem int_zero_left : (int 0).left = [] := rfl
private theorem int_succ_left (n : Nat) : (int (n + 1)).left = [int n] := rfl
private theorem int_right : ∀ n : Nat, (int n).right = []
  | 0 => rfl
  | _ + 1 => rfl
private theorem half_left (n : Nat) : (half n).left = [int n] := rfl
private theorem half_right (n : Nat) : (half n).right = [int (n + 1)] := rfl
private theorem starN_left (n : Nat) : (starN n).left = [int n] := rfl
private theorem starN_right (n : Nat) : (starN n).right = [int n] := rfl

private theorem mem_int_succ_left (n : Nat) : int n ∈ (int (n + 1)).left := by
  rw [int_succ_left]; exact List.mem_singleton.2 rfl

theorem le_int_zero_of {g : Game} (h : ∀ x ∈ g.left, ∃ y ∈ x.right, le y (int 0)) :
    le g (int 0) := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy => by rw [int_right] at hy; cases hy⟩
  obtain ⟨y, hy, hy'⟩ := h x hx
  rw [le_iff] at hle
  exact hle.2 y hy hy'

theorem le_int_succ_of {g : Game} {n : Nat}
    (h : ∀ x ∈ g.left, le x (int n) ∨ ∃ y ∈ x.right, le y (int (n + 1))) :
    le g (int (n + 1)) := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy => by rw [int_right] at hy; cases hy⟩
  rw [le_iff] at hle
  rcases h x hx with h' | ⟨y, hy, hy'⟩
  · exact hle.1 (int n) (mem_int_succ_left n) h'
  · exact hle.2 y hy hy'

theorem int_le_of {g : Game} {n : Nat} (h1 : n = 0 ∨ ∃ x ∈ g.left, le (int (n - 1)) x)
    (h2 : ∀ y ∈ g.right, ∃ x ∈ y.left, le (int n) x) : le (int n) g := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
  · cases n with
    | zero => rw [int_zero_left] at hx; cases hx
    | succ k =>
      rw [int_succ_left] at hx
      obtain rfl := List.mem_singleton.1 hx
      rcases h1 with h0 | ⟨x', hx', hle'⟩
      · omega
      · rw [le_iff] at hle
        exact hle.1 x' hx' hle'
  · obtain ⟨x, hx, hx'⟩ := h2 y hy
    rw [le_iff] at hle
    exact hle.1 x hx hx'

theorem le_half_of {g : Game} {n : Nat}
    (h1 : ∀ x ∈ g.left, le x (int n) ∨ ∃ y ∈ x.right, le y (half n))
    (h2 : ∃ y ∈ g.right, le y (int (n + 1))) : le g (half n) := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
  · rw [le_iff] at hle
    rcases h1 x hx with h' | ⟨y, hy, hy'⟩
    · exact hle.1 (int n) (by rw [half_left]; exact List.mem_singleton.2 rfl) h'
    · exact hle.2 y hy hy'
  · rw [half_right] at hy
    obtain rfl := List.mem_singleton.1 hy
    obtain ⟨z, hz, hz'⟩ := h2
    rw [le_iff] at hle
    exact hle.2 z hz hz'

theorem half_le_of {g : Game} {n : Nat}
    (h1 : ∀ y ∈ g.right, le (int (n + 1)) y ∨ ∃ x ∈ y.left, le (half n) x)
    (h2 : ∃ x ∈ g.left, le (int n) x) : le (half n) g := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
  · rw [half_left] at hx
    obtain rfl := List.mem_singleton.1 hx
    obtain ⟨z, hz, hz'⟩ := h2
    rw [le_iff] at hle
    exact hle.1 z hz hz'
  · rw [le_iff] at hle
    rcases h1 y hy with h' | ⟨x, hx, hx'⟩
    · exact hle.2 (int (n + 1)) (by rw [half_right]; exact List.mem_singleton.2 rfl) h'
    · exact hle.1 x hx hx'

theorem le_starN_of {g : Game} {n : Nat}
    (h1 : ∀ x ∈ g.left, le x (int n) ∨ ∃ y ∈ x.right, le y (starN n))
    (h2 : ∃ y ∈ g.right, le y (int n)) : le g (starN n) := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
  · rw [le_iff] at hle
    rcases h1 x hx with h' | ⟨y, hy, hy'⟩
    · exact hle.1 (int n) (by rw [starN_left]; exact List.mem_singleton.2 rfl) h'
    · exact hle.2 y hy hy'
  · rw [starN_right] at hy
    obtain rfl := List.mem_singleton.1 hy
    obtain ⟨z, hz, hz'⟩ := h2
    rw [le_iff] at hle
    exact hle.2 z hz hz'

theorem starN_le_of {g : Game} {n : Nat}
    (h1 : ∀ y ∈ g.right, le (int n) y ∨ ∃ x ∈ y.left, le (starN n) x)
    (h2 : ∃ x ∈ g.left, le (int n) x) : le (starN n) g := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
  · rw [starN_left] at hx
    obtain rfl := List.mem_singleton.1 hx
    obtain ⟨z, hz, hz'⟩ := h2
    rw [le_iff] at hle
    exact hle.1 z hz hz'
  · rw [le_iff] at hle
    rcases h1 y hy with h' | ⟨x, hx, hx'⟩
    · exact hle.2 (int n) (by rw [starN_right]; exact List.mem_singleton.2 rfl) h'
    · exact hle.1 x hx hx'

private theorem int_le_int_succ : ∀ n : Nat, le (int n) (int (n + 1))
  | 0 => int_le_of (Or.inl rfl) (fun y hy => by rw [int_right] at hy; cases hy)
  | n + 1 =>
    int_le_of (Or.inr ⟨int (n + 1), mem_int_succ_left (n + 1), int_le_int_succ n⟩)
      (fun y hy => by rw [int_right] at hy; cases hy)

theorem int_le_int {m n : Nat} (h : m ≤ n) : le (int m) (int n) := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans _ _ _ ih (int_le_int_succ _)

theorem int_le_half (n : Nat) : le (int n) (half n) := by
  refine int_le_of (Or.inr ⟨int n, by rw [half_left]; exact List.mem_singleton.2 rfl,
    int_le_int (Nat.sub_le n 1)⟩) (fun y hy => ?_)
  rw [half_right] at hy
  obtain rfl := List.mem_singleton.1 hy
  exact ⟨int n, mem_int_succ_left n, le_refl _⟩

theorem half_le_int_succ (n : Nat) : le (half n) (int (n + 1)) := by
  refine le_int_succ_of (fun x hx => ?_)
  rw [half_left] at hx
  obtain rfl := List.mem_singleton.1 hx
  exact Or.inl (le_refl _)

theorem int_le_starN_succ (n : Nat) : le (int n) (starN (n + 1)) := by
  refine int_le_of (Or.inr ⟨int (n + 1), by rw [starN_left]; exact List.mem_singleton.2 rfl,
    int_le_int (by omega)⟩) (fun y hy => ?_)
  rw [starN_right] at hy
  obtain rfl := List.mem_singleton.1 hy
  exact ⟨int n, mem_int_succ_left n, le_refl _⟩

theorem starN_le_int_succ (n : Nat) : le (starN n) (int (n + 1)) := by
  refine le_int_succ_of (fun x hx => ?_)
  rw [starN_left] at hx
  obtain rfl := List.mem_singleton.1 hx
  exact Or.inl (le_refl _)

theorem not_int_succ_le_int (n : Nat) : ¬ le (int (n + 1)) (int n) :=
  not_le_left (mem_int_succ_left n)

end Game
end Cgt
