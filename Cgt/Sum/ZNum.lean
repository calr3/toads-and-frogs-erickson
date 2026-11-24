import Cgt.OneFrog.Num

/-!
# Integers of either sign as games

`zint n` for `n : Int`, exact one-step characterisations of `G ≤ n` and `n ≤ G`, the order
between integers, and comparison with `{c | c}`.
-/

namespace Cgt

namespace Game

theorem zint_natCast (n : Nat) : zint (n : Int) = int n := rfl

/-- Negation without `attach`. -/
theorem neg_mk_map (l r : List Game) : neg (mk l r) = mk (r.map neg) (l.map neg) := by
  rw [neg_mk, List.attach_map_val, List.attach_map_val]

theorem neg_neg (g : Game) : neg (neg g) = g := by
  induction hn : sizeOf g using Nat.strongRecOn generalizing g with
  | _ n ih =>
  cases g with
  | mk l r =>
    have hl : ∀ x ∈ l, neg (neg x) = x := fun x hx =>
      ih _ (by have := sizeOf_lt_of_mem_left (r := r) hx; omega) x rfl
    have hr : ∀ y ∈ r, neg (neg y) = y := fun y hy =>
      ih _ (by have := sizeOf_lt_of_mem_right (l := l) hy; omega) y rfl
    have el : l.map (fun x => neg (neg x)) = l := by
      rw [List.map_congr_left hl, List.map_id']
    have er : r.map (fun x => neg (neg x)) = r := by
      rw [List.map_congr_left hr, List.map_id']
    rw [neg_mk_map, neg_mk_map, List.map_map, List.map_map]
    show mk (l.map (fun x => neg (neg x))) (r.map (fun x => neg (neg x))) = mk l r
    rw [el, er]

private theorem neg_zero' : neg zero = zero := by
  rw [zero, neg_mk_map]; rfl

theorem zint_neg_natCast (k : Nat) : zint (-(k : Int)) = neg (int k) := by
  cases k with
  | zero => exact neg_zero'.symm
  | succ k => rfl

theorem neg_zint (n : Int) : neg (zint n) = zint (-n) := by
  rcases Int.eq_nat_or_neg n with ⟨a, rfl | rfl⟩
  · rw [zint_natCast, zint_neg_natCast]
  · rw [zint_neg_natCast, neg_neg, Int.neg_neg, zint_natCast]

/-! ### Options of `zint n` -/

theorem zint_left_of_pos {n : Int} (h : 0 < n) : (zint n).left = [zint (n - 1)] := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, n = ((k + 1 : Nat) : Int) := ⟨(n - 1).toNat, by omega⟩
  have e : ((k + 1 : Nat) : Int) - 1 = (k : Int) := by omega
  rw [e, zint_natCast, zint_natCast]
  rfl

theorem zint_left_of_nonpos {n : Int} (h : n ≤ 0) : (zint n).left = [] := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, n = -(k : Int) := ⟨n.natAbs, by omega⟩
  rw [zint_neg_natCast]
  cases k with
  | zero => show (neg zero).left = []; rw [neg_zero']; rfl
  | succ k => show (neg (mk [int k] [])).left = []; rw [neg_mk_map]; rfl

theorem zint_right_of_nonneg {n : Int} (h : 0 ≤ n) : (zint n).right = [] := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, n = (k : Int) := ⟨n.toNat, by omega⟩
  rw [zint_natCast]
  cases k <;> rfl

theorem zint_right_of_neg {n : Int} (h : n < 0) : (zint n).right = [zint (n + 1)] := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, n = -((k + 1 : Nat) : Int) := ⟨(-n - 1).toNat, by omega⟩
  have e : -((k + 1 : Nat) : Int) + 1 = -(k : Int) := by omega
  rw [e, zint_neg_natCast, zint_neg_natCast]
  show (neg (mk [int k] [])).right = [neg (int k)]
  rw [neg_mk_map]; rfl

/-- `n ≰ x` in one step, exactly. -/
theorem not_zint_le_iff {x : Game} {n : Int} :
    ¬ le (zint n) x ↔ (0 < n ∧ le x (zint (n - 1))) ∨ ∃ y ∈ x.right, le y (zint n) := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hc
    apply h
    rw [le_iff]
    refine ⟨fun z hz hle => ?_, fun y hy hle => hc (Or.inr ⟨y, hy, hle⟩)⟩
    by_cases hn : 0 < n
    · rw [zint_left_of_pos hn] at hz
      obtain rfl := List.mem_singleton.1 hz
      exact hc (Or.inl ⟨hn, hle⟩)
    · rw [zint_left_of_nonpos (by omega)] at hz; cases hz
  · rintro (⟨hn, h⟩ | ⟨y, hy, h⟩) hle <;> rw [le_iff] at hle
    · exact hle.1 _ (by rw [zint_left_of_pos hn]; exact List.mem_singleton.2 rfl) h
    · exact hle.2 y hy h

/-- `x ≰ n` in one step, exactly. -/
theorem not_le_zint_iff {x : Game} {n : Int} :
    ¬ le x (zint n) ↔ (n < 0 ∧ le (zint (n + 1)) x) ∨ ∃ z ∈ x.left, le (zint n) z := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hc
    apply h
    rw [le_iff]
    refine ⟨fun z hz hle => hc (Or.inr ⟨z, hz, hle⟩), fun y hy hle => ?_⟩
    by_cases hn : n < 0
    · rw [zint_right_of_neg hn] at hy
      obtain rfl := List.mem_singleton.1 hy
      exact hc (Or.inl ⟨hn, hle⟩)
    · rw [zint_right_of_nonneg (by omega)] at hy; cases hy
  · rintro (⟨hn, h⟩ | ⟨z, hz, h⟩) hle <;> rw [le_iff] at hle
    · exact hle.2 _ (by rw [zint_right_of_neg hn]; exact List.mem_singleton.2 rfl) h
    · exact hle.1 z hz h

/-- `G ≤ n` in one step, exactly. -/
theorem le_zint_iff {g : Game} {n : Int} :
    le g (zint n) ↔
      (∀ x ∈ g.left, (0 < n ∧ le x (zint (n - 1))) ∨ ∃ y ∈ x.right, le y (zint n)) ∧
      (n < 0 → ∃ y ∈ g.right, le y (zint (n + 1))) := by
  rw [le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => not_zint_le_iff.1 (h1 x hx), fun hn => ?_⟩
    have h := h2 (zint (n + 1)) (by rw [zint_right_of_neg hn]; exact List.mem_singleton.2 rfl)
    rcases not_zint_le_iff.1 h with ⟨h0, _⟩ | h'
    · omega
    · exact h'
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => not_zint_le_iff.2 (h1 x hx), fun y hy => ?_⟩
    by_cases hn : n < 0
    · rw [zint_right_of_neg hn] at hy
      obtain rfl := List.mem_singleton.1 hy
      exact not_zint_le_iff.2 (Or.inr (h2 hn))
    · rw [zint_right_of_nonneg (by omega)] at hy; cases hy

/-- `n ≤ G` in one step, exactly. -/
theorem zint_le_iff {g : Game} {n : Int} :
    le (zint n) g ↔
      (∀ y ∈ g.right, (n < 0 ∧ le (zint (n + 1)) y) ∨ ∃ x ∈ y.left, le (zint n) x) ∧
      (0 < n → ∃ x ∈ g.left, le (zint (n - 1)) x) := by
  rw [le_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => not_le_zint_iff.1 (h2 y hy), fun hn => ?_⟩
    have h := h1 (zint (n - 1)) (by rw [zint_left_of_pos hn]; exact List.mem_singleton.2 rfl)
    rcases not_le_zint_iff.1 h with ⟨h0, _⟩ | h'
    · omega
    · exact h'
  · rintro ⟨h1, h2⟩
    refine ⟨fun x hx => ?_, fun y hy => not_le_zint_iff.2 (h1 y hy)⟩
    by_cases hn : 0 < n
    · rw [zint_left_of_pos hn] at hx
      obtain rfl := List.mem_singleton.1 hx
      exact not_le_zint_iff.2 (Or.inr (h2 hn))
    · rw [zint_left_of_nonpos (by omega)] at hx; cases hx

theorem zint_le_zint {m n : Int} (h : m ≤ n) : le (zint m) (zint n) := by
  rcases Int.eq_nat_or_neg m with ⟨a, rfl | rfl⟩ <;>
    rcases Int.eq_nat_or_neg n with ⟨b, rfl | rfl⟩
  · rw [zint_natCast, zint_natCast]; exact int_le_int (by omega)
  · have e : -(b : Int) = (a : Int) := by omega
    rw [e]; exact le_refl _
  · rw [zint_neg_natCast, zint_natCast]
    refine le_trans _ (int 0) _ ?_ (int_le_int (Nat.zero_le b))
    have h0 : int 0 = neg (int 0) := neg_zero'.symm
    rw [h0, neg_le_neg_iff]
    exact int_le_int (Nat.zero_le a)
  · rw [zint_neg_natCast, zint_neg_natCast, neg_le_neg_iff]
    exact int_le_int (by omega)

private theorem not_zint_le_pred (n : Int) : ¬ le (zint n) (zint (n - 1)) := by
  by_cases hn : 0 < n
  · exact not_le_left (by rw [zint_left_of_pos hn]; exact List.mem_singleton.2 rfl)
  · refine not_right_le ?_
    rw [zint_right_of_neg (by omega)]
    have e : n - 1 + 1 = n := by omega
    rw [e]; exact List.mem_singleton.2 rfl

theorem not_zint_le_zint {m n : Int} (h : m < n) : ¬ le (zint n) (zint m) := fun hle =>
  not_zint_le_pred n (le_trans _ _ _ hle (zint_le_zint (by omega)))

/-- Sufficient condition for `G ≤ n`: a Left option may be `≤ n - 1` whatever the sign of `n`. -/
theorem le_zint_of {g : Game} {n : Int}
    (h1 : ∀ x ∈ g.left, le x (zint (n - 1)) ∨ ∃ y ∈ x.right, le y (zint n))
    (h2 : n < 0 → ∃ y ∈ g.right, le y (zint (n + 1))) : le g (zint n) := by
  refine le_zint_iff.2 ⟨fun x hx => ?_, h2⟩
  rcases h1 x hx with h | h
  · exact not_zint_le_iff.1 fun hle => not_zint_le_pred n (le_trans _ _ _ hle h)
  · exact Or.inr h

theorem zint_le_of {g : Game} {n : Int}
    (h1 : ∀ y ∈ g.right, le (zint (n + 1)) y ∨ ∃ x ∈ y.left, le (zint n) x)
    (h2 : 0 < n → ∃ x ∈ g.left, le (zint (n - 1)) x) : le (zint n) g := by
  refine zint_le_iff.2 ⟨fun y hy => ?_, h2⟩
  rcases h1 y hy with h | h
  · refine not_le_zint_iff.1 fun hle => ?_
    have := not_zint_le_pred (n + 1)
    have e : n + 1 - 1 = n := by omega
    rw [e] at this
    exact this (le_trans _ _ _ h hle)
  · exact Or.inr h

/-- Comparison with `{c | c}` for any game `c`. -/
theorem le_star_of {g c : Game}
    (h1 : ∀ x ∈ g.left, le x c ∨ ∃ y ∈ x.right, le y (mk [c] [c]))
    (h2 : ∃ y ∈ g.right, le y c) : le g (mk [c] [c]) := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
  · rw [le_iff] at hle
    rcases h1 x hx with h' | ⟨y, hy, hy'⟩
    · exact hle.1 c (List.mem_singleton.2 rfl) h'
    · exact hle.2 y hy hy'
  · obtain rfl := List.mem_singleton.1 hy
    obtain ⟨z, hz, hz'⟩ := h2
    rw [le_iff] at hle
    exact hle.2 z hz hz'

theorem star_le_of {g c : Game}
    (h1 : ∀ y ∈ g.right, le c y ∨ ∃ x ∈ y.left, le (mk [c] [c]) x)
    (h2 : ∃ x ∈ g.left, le c x) : le (mk [c] [c]) g := by
  rw [le_iff]
  refine ⟨fun x hx hle => ?_, fun y hy hle => ?_⟩
  · obtain rfl := List.mem_singleton.1 hx
    obtain ⟨z, hz, hz'⟩ := h2
    rw [le_iff] at hle
    exact hle.1 z hz hz'
  · rw [le_iff] at hle
    rcases h1 y hy with h' | ⟨x, hx, hx'⟩
    · exact hle.2 c (List.mem_singleton.2 rfl) h'
    · exact hle.1 x hx hx'


theorem neg_starZ (n : Int) : neg (starZ n) = starZ (-n) := by
  rw [starZ, neg_mk_map, starZ, ← neg_zint]; rfl

end Game
end Cgt
