import Cgt.ToadsFrogs
import Cgt.Sum.ZNum

/-!
# Positions with only toads or only frogs

A position without frogs is the integer counting Left's remaining moves, and a position without
toads is minus the number of Right's remaining moves.
-/

namespace Cgt
open Cell TF Game

/-- Number of empty squares. -/
def countE : List Cell → Nat
  | [] => 0
  | E :: r => countE r + 1
  | _ :: r => countE r

/-- Sum over the toads of the number of empty squares to their right: the number of moves Left
has in a position without frogs. -/
def toadMoves : List Cell → Nat
  | [] => 0
  | T :: r => countE r + toadMoves r
  | _ :: r => toadMoves r

theorem countE_append (u v : List Cell) : countE (u ++ v) = countE u + countE v := by
  induction u with
  | nil => simp [countE]
  | cons c u ih => cases c <;> simp [countE, ih] <;> omega

theorem toadMoves_append (u v : List Cell) :
    toadMoves (u ++ v) = toadMoves u + toadMoves v + TF.countT u * countE v := by
  induction u with
  | nil => simp [toadMoves, countT]
  | cons c u ih =>
    cases c <;> simp [toadMoves, countT, ih, countE_append, Nat.add_mul] <;> omega

theorem countE_replicate_E (n : Nat) : countE (List.replicate n E) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countE, ih]

theorem countE_replicate_T (n : Nat) : countE (List.replicate n T) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countE, ih]

theorem countE_replicate_F (n : Nat) : countE (List.replicate n F) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countE, ih]

theorem toadMoves_replicate_T (n : Nat) : toadMoves (List.replicate n T) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, toadMoves, ih, countE_replicate_T]

theorem toadMoves_replicate_E (n : Nat) : toadMoves (List.replicate n E) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, toadMoves, ih]

theorem countT_replicate_T (n : Nat) : TF.countT (List.replicate n T) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countT, ih]; omega

theorem countT_replicate_E (n : Nat) : TF.countT (List.replicate n E) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, countT, ih]

/-- A slide uses up exactly one of Left's moves. -/
theorem toadMoves_slide (u r : List Cell) :
    toadMoves (u ++ E :: T :: r) + 1 = toadMoves (u ++ T :: E :: r) := by
  rw [toadMoves_append, toadMoves_append]
  simp only [toadMoves, countE]
  omega

/-- A position without frogs has no Right move. -/
theorem rightMoves_noF {p : List Cell} (h : F ∉ p) : rightMoves p = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro q hq
  rcases mem_rightMoves.1 hq with ⟨u, r, rfl, -⟩ | ⟨u, r, rfl, -⟩ <;> simp at h

theorem tf_right_noF {p : List Cell} (h : F ∉ p) : (tf p).right = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro x hx
  obtain ⟨q, hq, -⟩ := mem_right_tf.1 hx
  rw [rightMoves_noF h] at hq
  cases hq

/-- The Left moves of a position without frogs are slides. -/
theorem leftMoves_noF {p q : List Cell} (h : F ∉ p) (hq : q ∈ leftMoves p) :
    F ∉ q ∧ toadMoves q + 1 = toadMoves p := by
  rcases mem_leftMoves.1 hq with ⟨u, r, rfl, rfl⟩ | ⟨u, r, rfl, -⟩
  · refine ⟨?_, toadMoves_slide u r⟩
    simp at h ⊢
    exact h
  · simp at h

private theorem exists_TE_of_countE_pos :
    ∀ r : List Cell, F ∉ r → 0 < countE r → ∃ u s, T :: r = u ++ T :: E :: s
  | [], _, h => by simp [countE] at h
  | E :: r, _, _ => ⟨[], r, rfl⟩
  | F :: r, h, _ => by simp at h
  | T :: r, h, hc => by
    obtain ⟨u, s, hu⟩ := exists_TE_of_countE_pos r (by simp at h ⊢; exact h)
      (by simpa [countE] using hc)
    exact ⟨T :: u, s, by rw [hu]; rfl⟩

/-- A position without frogs in which Left still has a move to make contains `T□`. -/
theorem exists_TE_of_toadMoves_pos :
    ∀ p : List Cell, F ∉ p → 0 < toadMoves p → ∃ u r, p = u ++ T :: E :: r
  | [], _, h => by simp [toadMoves] at h
  | F :: r, h, _ => by simp at h
  | E :: r, h, hc => by
    obtain ⟨u, s, hu⟩ := exists_TE_of_toadMoves_pos r (by simp at h ⊢; exact h)
      (by simpa [toadMoves] using hc)
    exact ⟨E :: u, s, by rw [hu]; rfl⟩
  | T :: r, h, hc => by
    have hr : F ∉ r := by simp at h ⊢; exact h
    simp only [toadMoves] at hc
    rcases Nat.eq_zero_or_pos (countE r) with h0 | h0
    · obtain ⟨u, s, hu⟩ := exists_TE_of_toadMoves_pos r hr (by omega)
      exact ⟨T :: u, s, by rw [hu]; rfl⟩
    · exact exists_TE_of_countE_pos r hr h0

private theorem tf_noF_int :
    ∀ (n : Nat) (p : List Cell), F ∉ p → toadMoves p = n → Equiv (tf p) (int n) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro p h hn
  refine ⟨?_, ?_⟩
  · cases n with
    | zero =>
      apply le_int_zero_of
      intro x hx
      obtain ⟨q, hq, -⟩ := mem_left_tf.1 hx
      have := (leftMoves_noF h hq).2
      omega
    | succ k =>
      apply le_int_succ_of
      intro x hx
      obtain ⟨q, hq, rfl⟩ := mem_left_tf.1 hx
      obtain ⟨hF, hm⟩ := leftMoves_noF h hq
      exact Or.inl (ih k (by omega) q hF (by omega)).1
  · apply int_le_of
    · cases n with
      | zero => exact Or.inl rfl
      | succ k =>
        right
        obtain ⟨u, r, rfl⟩ := exists_TE_of_toadMoves_pos p h (by omega)
        have hq : u ++ E :: T :: r ∈ leftMoves (u ++ T :: E :: r) :=
          mem_leftMoves.2 (Or.inl ⟨u, r, rfl, rfl⟩)
        obtain ⟨hF, hm⟩ := leftMoves_noF h hq
        exact ⟨_, mem_left_tf.2 ⟨_, hq, rfl⟩, (ih k (by omega) _ hF (by omega)).2⟩
    · intro y hy
      rw [tf_right_noF h] at hy
      cases hy

/-- A position with no frog is the integer `toadMoves p`. -/
theorem tf_noF {p : List Cell} (h : F ∉ p) : Equiv (tf p) (zint (toadMoves p)) := by
  rw [zint_natCast]
  exact tf_noF_int _ p h rfl

/-- A position with no toad is minus the number of moves Right has. -/
theorem tf_noT {p : List Cell} (h : T ∉ p) :
    Equiv (tf p) (zint (-(toadMoves (mirror p) : Int))) := by
  have hF : F ∉ mirror p := by
    intro hm
    apply h
    simp only [mirror, List.mem_reverse, List.mem_map] at hm
    obtain ⟨c, hc, hs⟩ := hm
    cases c <;> simp at hs
    exact hc
  have h1 := tf_noF hF
  have h2 := tf_mirror (mirror p)
  rw [mirror_mirror] at h2
  rw [← neg_zint]
  refine ⟨le_trans _ _ _ h2.1 ((neg_le_neg_iff _ _).2 h1.2),
    le_trans _ _ _ ((neg_le_neg_iff _ _).2 h1.1) h2.2⟩

end Cgt
