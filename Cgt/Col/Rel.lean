import Cgt.Col.Check

/-!
# The margin relation between run lists

`Rel r j R R'`: the two run lists have the same skeleton (`Skel`: same cells, lengths equal or
both at least 2, empty runs exact), and every difference between the lengths of two entries, or
between an entry and the anchor 2, agrees in both or is at least `r.m + 1 + j` in both with the
same sign, and the same parity unless `r.par = 0` (`close r j`).

`Rel r 0` determines the key `keyOf r` (`keyOf_eq_of_rel`).
-/

namespace Cgt
namespace Col
open Cell

/-! ### Closeness of differences -/

def close (r : GapRule) (j : Nat) (x y : Int) : Prop :=
  x = y ∨ ((r.m + 1 + j : Int) ≤ x ∧ (r.m + 1 + j : Int) ≤ y ∧ (r.par = 0 ∨ (x - y) % 2 = 0)) ∨
    (x ≤ -(r.m + 1 + j : Int) ∧ y ≤ -(r.m + 1 + j : Int) ∧ (r.par = 0 ∨ (x - y) % 2 = 0))

theorem close.mono {r : GapRule} {j : Nat} {x y : Int} (h : close r (j + 1) x y) : close r j x y := by
  unfold close at *; omega

theorem close.mono' {r : GapRule} {j k : Nat} {x y : Int} (hjk : k ≤ j) (h : close r j x y) : close r k x y := by
  unfold close at *; omega

theorem close.symm {r : GapRule} {j : Nat} {x y : Int} (h : close r j x y) : close r j y x := by
  unfold close at *; omega

theorem close.trans {r : GapRule} {j : Nat} {x y z : Int} (h1 : close r j x y) (h2 : close r j y z) : close r j x z := by
  unfold close at *; omega

theorem close.refl (r : GapRule) (j : Nat) (x : Int) : close r j x x := Or.inl rfl

theorem close.shift {r : GapRule} {j : Nat} {x y d : Int} (hd : -2 ≤ d ∧ d ≤ 2) (h : close r (j + 2) x y) :
    close r j (x + d) (y + d) := by
  unfold close at *; omega

theorem close.neg {r : GapRule} {j : Nat} {x y : Int} (h : close r j x y) : close r j (-x) (-y) := by
  unfold close at *; omega

/-! ### Skeletons -/

/-- Same cells; lengths equal or both at least 2; empty runs exact. -/
def Skel (R R' : RL) : Prop :=
  R.length = R'.length ∧ ∀ i, cellAt R i = cellAt R' i ∧
    (lenAt R i = lenAt R' i ∨ (2 ≤ lenAt R i ∧ 2 ≤ lenAt R' i)) ∧ (cellAt R i = E → lenAt R i = lenAt R' i)

theorem Skel.symm {R R' : RL} (h : Skel R R') : Skel R' R := by
  refine ⟨h.1.symm, fun i => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 i
  refine ⟨h1.symm, ?_, fun hE => (h3 (h1 ▸ hE)).symm⟩
  rcases h2 with h2 | h2
  · exact Or.inl h2.symm
  · exact Or.inr ⟨h2.2, h2.1⟩

theorem Skel.trans {R R' R'' : RL} (h : Skel R R') (h' : Skel R' R'') : Skel R R'' := by
  refine ⟨h.1.trans h'.1, fun i => ?_⟩
  obtain ⟨a1, a2, a3⟩ := h.2 i
  obtain ⟨b1, b2, b3⟩ := h'.2 i
  refine ⟨a1.trans b1, ?_, fun hE => (a3 hE).trans (b3 (a1 ▸ hE))⟩
  omega

theorem Skel.two_le {R R' : RL} (h : Skel R R') (i : Nat) : (2 ≤ lenAt R i) = (2 ≤ lenAt R' i) := by
  have := (h.2 i).2.1
  apply propext; omega

theorem Skel.dtwo {R R' : RL} (h : Skel R R') (i : Nat) :
    decide (2 ≤ lenAt R i) = decide (2 ≤ lenAt R' i) := by
  have := (h.2 i).2.1
  by_cases h2 : 2 ≤ lenAt R i
  · have : 2 ≤ lenAt R' i := by omega
    simp [*]
  · have : ¬ 2 ≤ lenAt R' i := by omega
    simp [*]

theorem Skel.noE {R R' : RL} (h : Skel R R') (i d : Nat) : Col.noE R i d = Col.noE R' i d := by
  unfold Col.noE; congr 1; funext k; rw [(h.2 (i + k)).1]

theorem Skel.leftDead {R R' : RL} (h : Skel R R') (i : Nat) : Col.leftDead R i = Col.leftDead R' i := by
  unfold Col.leftDead; congr 1; funext s
  rw [(h.2 s).1, h.dtwo s, h.noE]

theorem Skel.rightDead {R R' : RL} (h : Skel R R') (i : Nat) : Col.rightDead R i = Col.rightDead R' i := by
  unfold Col.rightDead; rw [h.1]; congr 1; funext d
  rw [(h.2 (i + d)).1, h.dtwo (i + d), h.noE]

theorem Skel.deadB {R R' : RL} (h : Skel R R') (i : Nat) : Col.deadB R i = Col.deadB R' i := by
  unfold Col.deadB; rw [h.leftDead, h.rightDead]

theorem Skel.isEntB {R R' : RL} (h : Skel R R') (i : Nat) : Col.isEntB R i = Col.isEntB R' i := by
  unfold Col.isEntB; rw [h.1, (h.2 i).1, h.dtwo i, h.deadB]

/-! ### The relation -/

def Rel (r : GapRule) (j : Nat) (R R' : RL) : Prop :=
  Skel R R' ∧
  (∀ i, isEntB R i = true → close r j ((lenAt R i : Int) - 2) ((lenAt R' i : Int) - 2)) ∧
  (∀ i k, isEntB R i = true → isEntB R k = true →
    close r j ((lenAt R i : Int) - lenAt R k) ((lenAt R' i : Int) - lenAt R' k))

theorem Rel.mono {r : GapRule} {j : Nat} {R R' : RL} (h : Rel r (j + 1) R R') : Rel r j R R' :=
  ⟨h.1, fun i hi => (h.2.1 i hi).mono, fun i k hi hk => (h.2.2 i k hi hk).mono⟩

theorem Rel.mono' {r : GapRule} {j k : Nat} {R R' : RL} (hjk : k ≤ j) (h : Rel r j R R') : Rel r k R R' :=
  ⟨h.1, fun i hi => (h.2.1 i hi).mono' hjk, fun i l hi hl => (h.2.2 i l hi hl).mono' hjk⟩

theorem Rel.symm {r : GapRule} {j : Nat} {R R' : RL} (h : Rel r j R R') : Rel r j R' R := by
  refine ⟨h.1.symm, fun i hi => ?_, fun i k hi hk => ?_⟩
  · rw [← h.1.isEntB] at hi; exact (h.2.1 i hi).symm
  · rw [← h.1.isEntB] at hi hk; exact (h.2.2 i k hi hk).symm

theorem Rel.trans {r : GapRule} {j : Nat} {R R' R'' : RL} (h : Rel r j R R') (h' : Rel r j R' R'') : Rel r j R R'' := by
  refine ⟨h.1.trans h'.1, fun i hi => ?_, fun i k hi hk => ?_⟩
  · have hi' : isEntB R' i = true := by rwa [← h.1.isEntB]
    exact (h.2.1 i hi).trans (h'.2.1 i hi')
  · have hi' : isEntB R' i = true := by rwa [← h.1.isEntB]
    have hk' : isEntB R' k = true := by rwa [← h.1.isEntB]
    exact (h.2.2 i k hi hk).trans (h'.2.2 i k hi' hk')

theorem Rel.refl (r : GapRule) (j : Nat) (R : RL) : Rel r j R R :=
  ⟨⟨rfl, fun _ => ⟨rfl, Or.inl rfl, fun _ => rfl⟩⟩, fun _ _ => close.refl _ _ _, fun _ _ _ _ => close.refl _ _ _⟩

/-! ### `Rel 0` determines the key -/

theorem mem_insertE {x y : Nat × Nat} : ∀ {l : List (Nat × Nat)}, y ∈ insertE x l ↔ y = x ∨ y ∈ l
  | [] => by simp [insertE]
  | z :: l => by
    unfold insertE
    split
    · simp
    · simp only [List.mem_cons, mem_insertE]; exact or_left_comm

theorem mem_sortE {y : Nat × Nat} : ∀ {l : List (Nat × Nat)}, y ∈ sortE l ↔ y ∈ l
  | [] => by simp [sortE]
  | x :: l => by simp [sortE, mem_insertE, mem_sortE]

theorem insertE_map (f : Nat × Nat → Nat × Nat) {x : Nat × Nat} :
    ∀ {l : List (Nat × Nat)}, (∀ y ∈ l, ltE (f x) (f y) = ltE x y) →
      insertE (f x) (l.map f) = (insertE x l).map f
  | [], _ => by simp [insertE]
  | y :: l, h => by
    simp only [List.map_cons, insertE]
    rw [h y (by simp)]
    split
    · simp
    · simp only [List.map_cons, List.cons.injEq, true_and]
      exact insertE_map f fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem sortE_map (f : Nat × Nat → Nat × Nat) :
    ∀ {l : List (Nat × Nat)}, (∀ x ∈ l, ∀ y ∈ l, ltE (f x) (f y) = ltE x y) →
      sortE (l.map f) = (sortE l).map f
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, sortE]
    rw [sortE_map f fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)]
    exact insertE_map f fun y hy => h x (by simp) y (List.mem_cons_of_mem _ (mem_sortE.1 hy))

/-- Comparisons agree when differences are close. -/
theorem ltE_eq_of_close {r : GapRule} {a b a' b' i k : Nat} (h : close r 0 ((a : Int) - b) ((a' : Int) - b')) :
    ltE (a', i) (b', k) = ltE (a, i) (b, k) := by
  have e1 : decide (a' < b') = decide (a < b) := by
    unfold close at h
    by_cases h1 : a < b
    · have : a' < b' := by omega
      simp [h1, this]
    · have : ¬ a' < b' := by omega
      simp [h1, this]
  have e2 : (a' == b') = (a == b) := by
    unfold close at h
    by_cases h1 : a = b
    · have : a' = b' := by omega
      simp [h1, this]
    · have : a' ≠ b' := by omega
      rw [beq_eq_false_iff_ne.2 h1, beq_eq_false_iff_ne.2 this]
  simp only [ltE]
  rw [e1, e2]

theorem capG_eq_of_close {r : GapRule} {x y x' y' : Nat} (h : close r 0 ((x : Int) - y) ((x' : Int) - y')) :
    capG r (x - y) = capG r (x' - y') := by
  unfold capG close at *
  by_cases h1 : x - y ≤ r.m <;> by_cases h2 : x' - y' ≤ r.m <;> by_cases hp : r.par = 0 <;>
    simp only [h1, h2, hp, ite_true, ite_false] <;> omega

/-- The entries of `R`, before sorting. -/
def entL (R : RL) : List (Nat × Nat) :=
  (List.range R.length).filterMap fun i => if isEntB R i then some (lenAt R i, i) else none

theorem mem_entL {R : RL} {x : Nat × Nat} : x ∈ entL R ↔ isEntB R x.2 = true ∧ x.1 = lenAt R x.2 := by
  unfold entL
  simp only [List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨i, hi, h⟩
    split at h
    · next he => simp only [Option.some.injEq] at h; subst h; exact ⟨he, rfl⟩
    · simp at h
  · rintro ⟨he, hx⟩
    have hlt : x.2 < R.length := by
      unfold isEntB at he; simp only [Bool.and_eq_true, decide_eq_true_eq] at he; exact he.1.1.1
    refine ⟨x.2, hlt, ?_⟩
    simp only [he, ite_true, Option.some.injEq]
    exact Prod.ext hx.symm rfl

theorem entL_eq_map {r : GapRule} {j : Nat} {R R' : RL} (h : Rel r j R R') :
    entL R' = (entL R).map fun x => (lenAt R' x.2, x.2) := by
  unfold entL
  rw [h.1.1, List.map_filterMap]
  congr 1; funext i
  rw [h.1.isEntB]
  split <;> rfl

theorem gaps_map {r : GapRule} {R R' : RL} (h : Rel r 0 R R') :
    ∀ (l : List (Nat × Nat)) (p p' : Nat), (∀ x ∈ l, isEntB R x.2 = true ∧ x.1 = lenAt R x.2) →
      (∀ x ∈ l, capG r (x.1 - p) = capG r (lenAt R' x.2 - p')) →
      (∀ x ∈ l, ∀ y ∈ l, capG r (y.1 - x.1) = capG r (lenAt R' y.2 - lenAt R' x.2)) →
      (gapsFrom p l).map (capG r) = (gapsFrom p' (l.map fun x => (lenAt R' x.2, x.2))).map (capG r)
  | [], _, _, _, _, _ => rfl
  | x :: l, p, p', he, h0, hp => by
    simp only [gapsFrom, List.map_cons, List.cons.injEq]
    refine ⟨h0 x (by simp), gaps_map h l x.1 (lenAt R' x.2) (fun y hy => he y (List.mem_cons_of_mem _ hy))
      (fun y hy => hp x (by simp) y (List.mem_cons_of_mem _ hy))
      (fun a ha b hb => hp a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩

theorem lenAt_of_ge {R : RL} {i : Nat} (h : R.length ≤ i) : lenAt R i = 0 := by
  simp [lenAt, runAt, List.getD, h]

theorem keyOf_def (r : GapRule) (R : RL) : keyOf r R = [R.length] ++ ((List.range R.length).flatMap fun i => [cellCode (cellAt R i), clsAt R i]) ++
    [(entries R).length] ++ (entries R).map Prod.snd ++ (gapsFrom 2 (entries R)).map (capG r) := rfl

theorem clsAt_eq_of_skel {R R' : RL} (hs : Skel R R') (i : Nat) : clsAt R i = clsAt R' i := by
  obtain ⟨hc, hl, hE⟩ := hs.2 i
  unfold clsAt
  rw [hs.isEntB, hs.deadB, hs.dtwo, hc]
  by_cases e1 : isEntB R' i = true
  · rw [if_pos e1, if_pos e1]
  rw [if_neg e1, if_neg e1]
  by_cases e2 : (deadB R' i && decide (2 ≤ lenAt R' i) && cellAt R' i != E) = true
  · rw [if_pos e2, if_pos e2]
  rw [if_neg e2, if_neg e2]
  congr 1
  by_cases he : cellAt R' i = E
  · exact hE (hc ▸ he)
  by_cases h2 : 2 ≤ lenAt R i
  · exfalso
    have h2' : 2 ≤ lenAt R' i := by omega
    have hd : deadB R' i = false := by
      cases hd : deadB R' i
      · rfl
      · exfalso; apply e2
        simp only [hd, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
        exact ⟨h2', he⟩
    have hlen : ¬ i < R'.length := by
      intro hi; apply e1
      unfold isEntB
      simp only [hd, Bool.not_false, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      exact ⟨⟨hi, he⟩, h2'⟩
    rw [lenAt_of_ge (by omega)] at h2'
    omega
  · omega

theorem keyOf_eq_of_rel {r : GapRule} {R R' : RL} (h : Rel r 0 R R') : keyOf r R = keyOf r R' := by
  have hs := h.1
  have hcmp : ∀ x ∈ entL R, ∀ y ∈ entL R,
      ltE (lenAt R' x.2, x.2) (lenAt R' y.2, y.2) = ltE x y := by
    intro x hx y hy
    obtain ⟨hxe, hx1⟩ := mem_entL.1 hx
    obtain ⟨hye, hy1⟩ := mem_entL.1 hy
    have := h.2.2 x.2 y.2 hxe hye
    rw [← hx1, ← hy1] at this
    obtain ⟨x1, x2⟩ := x; obtain ⟨y1, y2⟩ := y
    exact ltE_eq_of_close this
  have hes : entries R' = (entries R).map fun x => (lenAt R' x.2, x.2) := by
    show sortE (entL R') = (sortE (entL R)).map _
    rw [entL_eq_map h, sortE_map _ hcmp]
  have hmem : ∀ x ∈ entries R, isEntB R x.2 = true ∧ x.1 = lenAt R x.2 := fun x hx =>
    mem_entL.1 (mem_sortE.1 hx)
  have htok : ((List.range R.length).flatMap fun i => [cellCode (cellAt R i), clsAt R i]) =
      (List.range R'.length).flatMap fun i => [cellCode (cellAt R' i), clsAt R' i] := by
    have hf : (fun i => [cellCode (cellAt R i), clsAt R i]) = (fun i => [cellCode (cellAt R' i), clsAt R' i]) := by
      funext i; rw [(hs.2 i).1, clsAt_eq_of_skel hs]
    rw [hs.1, hf]
  have hgaps : (gapsFrom 2 (entries R)).map (capG r) = (gapsFrom 2 (entries R')).map (capG r) := by
    rw [hes]
    refine gaps_map h _ 2 2 hmem (fun x hx => ?_) (fun x hx y hy => ?_)
    · obtain ⟨hxe, hx1⟩ := hmem x hx
      have := h.2.1 x.2 hxe
      rw [← hx1] at this
      exact capG_eq_of_close (y := 2) (y' := 2) (by simpa using this)
    · obtain ⟨hxe, hx1⟩ := hmem x hx
      obtain ⟨hye, hy1⟩ := hmem y hy
      have := h.2.2 y.2 x.2 hye hxe
      rw [← hx1, ← hy1] at this
      exact capG_eq_of_close this
  rw [keyOf_def, keyOf_def, htok, hgaps, hs.1, hes]
  simp [List.map_map, Function.comp_def]

end Col
end Cgt
