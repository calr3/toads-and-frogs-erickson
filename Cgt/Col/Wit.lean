import Cgt.Col.Mirror

/-!
# Every run list has a witness of its key within margin 4

For a maximal run list `R`, take the sorted entries, their gaps from the anchor 2, and compress every
gap above 8 to 7 or 8 (keeping its parity). `build (keyOf R)` of these gaps is a witness of the key
of `R` (`witOf`), and it is related to `R` with margin 4 (`wit_complete`).
-/

namespace Cgt
namespace Col
open Cell

/-! ### Reading the key back -/

theorem length_toks (R : RL) :
    ((List.range R.length).flatMap fun i => [cellCode (cellAt R i), clsAt R i]).length = 2 * R.length := by
  induction R.length with
  | zero => rfl
  | succ L ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega

theorem getD_toks (a b : Nat → Nat) : ∀ (L i : Nat), i < L →
    ((List.range L).flatMap fun j => [a j, b j]).getD (2 * i) 0 = a i ∧
    ((List.range L).flatMap fun j => [a j, b j]).getD (2 * i + 1) 0 = b i
  | 0, i, h => by omega
  | L + 1, i, h => by
    have hlen : ((List.range L).flatMap fun j => [a j, b j]).length = 2 * L := by
      clear h; induction L with
      | zero => rfl
      | succ L ih => rw [List.range_succ, List.flatMap_append, List.length_append, ih]; simp; omega
    rw [List.range_succ, List.flatMap_append]
    simp only [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge i L with hi | hi
    · rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
      have := getD_toks a b L i hi
      simp only [List.getD_eq_getElem?_getD] at this
      exact this
    · have : i = L := by omega
      subst this
      rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), hlen]
      simp

theorem take_app {α : Type} : ∀ (l₁ l₂ : List α), (l₁ ++ l₂).take l₁.length = l₁
  | [], _ => by simp
  | x :: l₁, l₂ => by simp [take_app l₁ l₂]

theorem drop_app {α : Type} : ∀ (l₁ l₂ : List α), (l₁ ++ l₂).drop l₁.length = l₂
  | [], _ => by simp
  | x :: l₁, l₂ => by simp [drop_app l₁ l₂]

theorem length_gapsFrom : ∀ (p : Nat) (es : List (Nat × Nat)), (gapsFrom p es).length = es.length
  | _, [] => rfl
  | p, x :: es => by simp [gapsFrom, length_gapsFrom x.1 es]

theorem keyOf_parts (R : RL) :
    (keyOf R).headD 0 = R.length ∧
    ((keyOf R).drop 1).take (2 * R.length) = (List.range R.length).flatMap (fun i => [cellCode (cellAt R i), clsAt R i]) ∧
    ((keyOf R).drop (1 + 2 * R.length)).headD 0 = (entries R).length ∧
    ((keyOf R).drop (2 + 2 * R.length)).take (entries R).length = (entries R).map Prod.snd ∧
    ((keyOf R).drop (2 + 2 * R.length + (entries R).length)).take (entries R).length =
      (gapsFrom 2 (entries R)).map capG := by
  have ht := length_toks R
  generalize hT : (List.range R.length).flatMap (fun i => [cellCode (cellAt R i), clsAt R i]) = toks at ht
  have hk : keyOf R = [R.length] ++ toks ++ [(entries R).length] ++ (entries R).map Prod.snd ++
      (gapsFrom 2 (entries R)).map capG := by rw [keyOf_def, hT]
  have hg : ((gapsFrom 2 (entries R)).map capG).length = (entries R).length := by
    rw [List.length_map, length_gapsFrom]
  rw [hk]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [show [R.length] ++ toks ++ [(entries R).length] ++ (entries R).map Prod.snd ++ (gapsFrom 2 (entries R)).map capG
        = R.length :: (toks ++ ([(entries R).length] ++ (entries R).map Prod.snd ++ (gapsFrom 2 (entries R)).map capG)) by
        simp [List.append_assoc]]
    rw [List.drop_one, List.tail_cons, ← ht, take_app]
  · rw [show 1 + 2 * R.length = ([R.length] ++ toks).length by simp [ht]; omega,
      show [R.length] ++ toks ++ [(entries R).length] ++ (entries R).map Prod.snd ++ (gapsFrom 2 (entries R)).map capG =
        ([R.length] ++ toks) ++ ((entries R).length :: ((entries R).map Prod.snd ++ (gapsFrom 2 (entries R)).map capG)) by
        simp [List.append_assoc], drop_app]
    rfl
  · rw [show 2 + 2 * R.length = ([R.length] ++ toks ++ [(entries R).length]).length by simp [ht]; omega,
      show [R.length] ++ toks ++ [(entries R).length] ++ (entries R).map Prod.snd ++ (gapsFrom 2 (entries R)).map capG =
        ([R.length] ++ toks ++ [(entries R).length]) ++ ((entries R).map Prod.snd ++ (gapsFrom 2 (entries R)).map capG) by
        simp [List.append_assoc], drop_app]
    have := take_app ((entries R).map Prod.snd) ((gapsFrom 2 (entries R)).map capG)
    rwa [List.length_map] at this
  · rw [show 2 + 2 * R.length + (entries R).length =
        ([R.length] ++ toks ++ [(entries R).length] ++ (entries R).map Prod.snd).length by simp [ht]; omega, drop_app]
    rw [← hg, List.take_length]

/-! ### Sorted entries and prefix sums -/

/-- Values non-decreasing, starting from at least `p`. -/
def VS : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | p, x :: l => p ≤ x.1 ∧ VS x.1 l

theorem VS_insertE {x : Nat × Nat} : ∀ {p : Nat} {l : List (Nat × Nat)}, VS p l → p ≤ x.1 → VS p (insertE x l)
  | p, [], _, hx => ⟨hx, trivial⟩
  | p, y :: l, ⟨hy, hl⟩, hx => by
    unfold insertE
    by_cases h : ltE x y = true
    · rw [if_pos h]
      refine ⟨hx, ?_, hl⟩
      simp only [ltE, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
      omega
    · rw [if_neg h]
      refine ⟨hy, VS_insertE hl ?_⟩
      simp only [ltE, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq, not_or, not_and] at h
      omega

theorem VS_sortE {p : Nat} : ∀ {l : List (Nat × Nat)}, (∀ x ∈ l, p ≤ x.1) → VS p (sortE l)
  | [], _ => trivial
  | x :: l, h => VS_insertE (VS_sortE fun y hy => h y (List.mem_cons_of_mem _ hy)) (h x (by simp))

theorem prefix_gaps : ∀ {p : Nat} {es : List (Nat × Nat)}, VS p es → prefixVals p (gapsFrom p es) = es.map Prod.fst
  | _, [], _ => rfl
  | p, x :: es, ⟨hx, hs⟩ => by
    simp only [gapsFrom, prefixVals, List.map_cons, List.cons.injEq]
    refine ⟨by omega, ?_⟩
    rw [show p + (x.1 - p) = x.1 by omega]
    exact prefix_gaps hs

theorem VS_entries (R : RL) : VS 2 (entries R) :=
  VS_sortE fun x hx => by
    obtain ⟨he, hx1⟩ := mem_entL.1 hx
    rw [hx1]; exact (isEntB_iff.1 he).2.2.1

/-! ### Compressing gaps -/

/-- Gaps above 8 become 7 or 8, keeping their parity. -/
def comp (g : Nat) : Nat := if g ≤ 8 then g else 7 + (g - 7) % 2

/-- Equal, or both at least 7 with the same parity. -/
def Cl (x y : Nat) : Prop := x = y ∨ (7 ≤ x ∧ 7 ≤ y ∧ x % 2 = y % 2)

theorem Cl_step {x y : Nat} (g : Nat) (h : Cl x y) : Cl (x + g) (y + comp g) := by
  unfold Cl comp at *
  by_cases hg : g ≤ 8 <;> simp only [hg, ite_true, ite_false] <;> omega

theorem comp_mem_choices (g : Nat) : comp g ∈ gapChoices (capG g) := by
  unfold comp gapChoices capG M
  by_cases hg : g ≤ 2
  · simp [hg, show g ≤ 8 by omega]
  · simp only [hg, ite_false, show ¬ (2 + 1 + (g - 2 - 1) % 2 ≤ 2) by omega, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false]
    by_cases h8 : g ≤ 8 <;> simp only [h8, ite_true, ite_false] <;> omega

theorem comp_mem_choicesAll : ∀ (gs : List Nat), gs.map comp ∈ choicesAll (gs.map capG)
  | [] => by simp [choicesAll]
  | g :: gs => by
    simp only [List.map_cons, choicesAll, List.mem_flatMap, List.mem_map]
    exact ⟨comp g, comp_mem_choices g, gs.map comp, comp_mem_choicesAll gs, rfl⟩

/-- The value at position `a` of the prefix sums. -/
def PV (p : Nat) (gs : List Nat) (a : Nat) : Nat := (prefixVals p gs).getD a 0

theorem PV_cons_zero (p g : Nat) (gs : List Nat) : PV p (g :: gs) 0 = p + g := rfl
theorem PV_cons_succ (p g : Nat) (gs : List Nat) (a : Nat) : PV p (g :: gs) (a + 1) = PV (p + g) gs a := by
  simp [PV, prefixVals, List.getD_eq_getElem?_getD]

theorem PV_ge : ∀ (p : Nat) (gs : List Nat) (a : Nat), a < gs.length → p ≤ PV p gs a
  | _, [], _, h => by simp at h
  | p, g :: gs, 0, _ => by rw [PV_cons_zero]; omega
  | p, g :: gs, a + 1, h => by
    rw [PV_cons_succ]; have := PV_ge (p + g) gs a (by simp at h; omega); omega

theorem PV_close : ∀ (p p' : Nat) (gs : List Nat) (a : Nat), a < gs.length →
    Cl (PV p gs a - p) (PV p' (gs.map comp) a - p')
  | _, _, [], _, h => by simp at h
  | p, p', g :: gs, 0, _ => by
    rw [List.map_cons, PV_cons_zero, PV_cons_zero, show p + g - p = 0 + g by omega,
      show p' + comp g - p' = 0 + comp g by omega]
    exact Cl_step g (Or.inl rfl)
  | p, p', g :: gs, a + 1, h => by
    rw [List.map_cons, PV_cons_succ, PV_cons_succ]
    have h1 := PV_close (p + g) (p' + comp g) gs a (by simp at h; omega)
    have h2 := PV_ge (p + g) gs a (by simp at h; omega)
    have h3 := PV_ge (p' + comp g) (gs.map comp) a (by simp at h ⊢; omega)
    have := Cl_step g h1
    rw [show PV (p + g) gs a - p = PV (p + g) gs a - (p + g) + g by omega,
      show PV (p' + comp g) (gs.map comp) a - p' = PV (p' + comp g) (gs.map comp) a - (p' + comp g) + comp g by omega]
    exact this

theorem PV_drop : ∀ (p : Nat) (gs : List Nat) (b a : Nat), b < a →
    PV p gs a = PV (PV p gs b) (gs.drop (b + 1)) (a - b - 1)
  | _, [], _, _, _ => by simp [PV, prefixVals]
  | p, g :: gs, 0, a + 1, _ => by rw [PV_cons_succ, PV_cons_zero]; simp
  | p, g :: gs, b + 1, a + 1, h => by
    rw [PV_cons_succ, PV_cons_succ, PV_drop (p + g) gs b a (by omega)]
    simp [show a + 1 - (b + 1) - 1 = a - b - 1 by omega]

theorem PV_close_pair (p p' : Nat) (gs : List Nat) {a b : Nat} (hba : b < a) (ha : a < gs.length) :
    Cl (PV p gs a - PV p gs b) (PV p' (gs.map comp) a - PV p' (gs.map comp) b) := by
  rw [PV_drop p gs b a hba, PV_drop p' (gs.map comp) b a hba, ← List.map_drop]
  exact PV_close _ _ _ _ (by simp; omega)

theorem close_of_Cl {x y : Nat} (h : Cl x y) : close 4 (x : Int) (y : Int) := by
  unfold Cl close at *; omega

/-! ### The witness -/

theorem prefixVals_length : ∀ (p : Nat) (gs : List Nat), (prefixVals p gs).length = gs.length
  | _, [] => rfl
  | p, g :: gs => by simp [prefixVals, prefixVals_length (p + g) gs]

theorem lenFor_one (idx vals : List Nat) (i : Nat) :
    lenFor 1 idx vals i = ((idx.zip vals).find? (fun x => x.1 == i)).elim 0 Prod.snd := rfl

theorem lenFor_entry : ∀ (idx vals : List Nat) (i : Nat), i ∈ idx → idx.length ≤ vals.length →
    ∃ a, a < idx.length ∧ idx.getD a 0 = i ∧ lenFor 1 idx vals i = vals.getD a 0
  | [], _, _, h, _ => by simp at h
  | x :: idx, [], _, _, h => by simp at h
  | x :: idx, v :: vals, i, h, hl => by
    rw [lenFor_one]
    by_cases hx : x = i
    · subst hx; exact ⟨0, by simp, rfl, by simp⟩
    · have hi : i ∈ idx := by
        rcases List.mem_cons.1 h with h | h
        · exact absurd h.symm hx
        · exact h
      obtain ⟨a, ha, hia, hv⟩ := lenFor_entry idx vals i hi (by simp at hl; omega)
      refine ⟨a + 1, by simp; omega, by simpa [List.getD_eq_getElem?_getD] using hia, ?_⟩
      rw [lenFor_one] at hv
      have hxi : (x == i) = false := by simp [hx]
      simp only [List.zip_cons_cons, List.find?_cons, hxi]
      simpa [List.getD_eq_getElem?_getD] using hv

theorem runAt_map_range {f : Nat → Cell × Nat} {L i : Nat} (h : i < L) :
    runAt ((List.range L).map f) i = f i := by
  simp [runAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

theorem codeCell_cellCode (c : Cell) : codeCell (cellCode c) = c := by cases c <;> rfl

theorem length_build (R : RL) (gs : List Nat) : (build (keyOf R) gs).length = R.length := by
  unfold build; simp only [List.length_map, List.length_range]; exact (keyOf_parts R).1

theorem runAt_build (R : RL) (gs : List Nat) {i : Nat} (hi : i < R.length) :
    runAt (build (keyOf R) gs) i = (cellAt R i, lenFor (clsAt R i) ((entries R).map Prod.snd) (prefixVals 2 gs) i) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := keyOf_parts R
  unfold build
  simp only [h1, h2, h3, h4]
  rw [runAt_map_range hi]
  obtain ⟨g1, g2⟩ := getD_toks (fun j => cellCode (cellAt R j)) (fun j => clsAt R j) R.length i hi
  rw [g1, g2, codeCell_cellCode]

theorem maxB_of_cells : ∀ (p : Option Cell) (R W : RL), R.length = W.length → (∀ i, cellAt R i = cellAt W i) →
    PosR W → okFrom p R = true → okFrom p W = true
  | _, [], [], _, _, _, _ => rfl
  | p, x :: R, y :: W, hl, hc, hW, h => by
    have h0 : x.1 = y.1 := hc 0
    rw [okFrom_cons] at h ⊢
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h ⊢
    refine ⟨⟨hW y (by simp), by rw [← h0]; exact h.1.2⟩, ?_⟩
    rw [← h0]
    exact maxB_of_cells _ R W (by simpa using hl) (fun i => by simpa [cellAt, runAt_cons_succ] using hc (i + 1))
      hW.tail h.2
  | _, [], _ :: _, hl, _, _, _ => by simp at hl
  | _, _ :: _, [], hl, _, _, _ => by simp at hl

theorem PV_mono (p : Nat) (gs : List Nat) {a b : Nat} (hba : b ≤ a) (ha : a < gs.length) : PV p gs b ≤ PV p gs a := by
  rcases Nat.lt_or_eq_of_le hba with h | h
  · rw [PV_drop p gs b a h]; exact PV_ge _ _ _ (by simp; omega)
  · subst h; exact Nat.le_refl _

/-- **Witness completeness.** -/
theorem wit_complete (R : RL) (hR : maxB R = true) : ∃ W ∈ witOf (keyOf R), Rel 4 R W ∧ maxB W = true := by
  have hpos := posR_of_maxB hR
  -- the data of the key
  have hVS := VS_entries R
  have hpg := prefix_gaps hVS
  have hlg := length_gapsFrom 2 (entries R)
  obtain ⟨k1, -, k3, -, k5⟩ := keyOf_parts R
  refine ⟨build (keyOf R) ((gapsFrom 2 (entries R)).map comp), ?_, ?_⟩
  · unfold witOf
    simp only [k1, k3, k5]
    exact List.mem_map_of_mem (comp_mem_choicesAll _)
  -- positions of entries in the sorted order
  have hpos_e : ∀ i, isEntB R i = true → ∃ a, a < (entries R).length ∧
      lenAt R i = PV 2 (gapsFrom 2 (entries R)) a ∧
      lenFor (clsAt R i) ((entries R).map Prod.snd) (prefixVals 2 ((gapsFrom 2 (entries R)).map comp)) i =
        PV 2 ((gapsFrom 2 (entries R)).map comp) a := by
    intro i hi
    have hmem : i ∈ (entries R).map Prod.snd := by
      rw [List.mem_map]
      exact ⟨(lenAt R i, i), mem_sortE.2 (mem_entL.2 ⟨hi, rfl⟩), rfl⟩
    obtain ⟨a, ha, hia, hv⟩ := lenFor_entry _ (prefixVals 2 ((gapsFrom 2 (entries R)).map comp)) i hmem
      (by simp [prefixVals_length, hlg])
    have hcls : clsAt R i = 1 := by simp [clsAt, hi]
    refine ⟨a, by simpa using ha, ?_, by rw [hcls, hv]; rfl⟩
    have ha' : a < (entries R).length := by simpa using ha
    have hx : (entries R)[a] ∈ entries R := List.getElem_mem ha'
    obtain ⟨-, hx1⟩ := mem_entL.1 (mem_sortE.1 hx)
    have hi2 : (entries R)[a].2 = i := by
      have := hia; simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ha'] at this
      simpa using this
    unfold PV; rw [hpg]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem ha', Option.map_some,
      Option.getD_some]
    rw [hx1, hi2]
  -- the runs of the witness
  generalize hgs : gapsFrom 2 (entries R) = gs at hpos_e hlg hpg
  have hW : ∀ i, i < R.length → runAt (build (keyOf R) (gs.map comp)) i =
      (cellAt R i, lenFor (clsAt R i) ((entries R).map Prod.snd) (prefixVals 2 (gs.map comp)) i) :=
    fun i hi => runAt_build R _ hi
  have hlW := length_build R (gs.map comp)
  generalize hWd : build (keyOf R) (gs.map comp) = W at hW hlW
  have hcell : ∀ i, cellAt W i = cellAt R i := by
    intro i
    rcases Nat.lt_or_ge i R.length with hi | hi
    · rw [cellAt_def, hW i hi]
    · rw [cellAt_def, cellAt_def, runAt_of_ge (by omega), runAt_of_ge hi]
  -- lengths: an entry, a dead long run, or exact
  have hlen : ∀ i, i < R.length →
      (isEntB R i = true ∨ (2 ≤ lenAt R i ∧ cellAt R i ≠ E ∧ lenAt W i = 2) ∨ lenAt W i = lenAt R i) := by
    intro i hi
    by_cases he : isEntB R i = true
    · exact Or.inl he
    right
    have hl : lenAt W i = lenFor (clsAt R i) ((entries R).map Prod.snd) (prefixVals 2 (gs.map comp)) i := by
      rw [lenAt_def, hW i hi]
    unfold clsAt at hl
    rw [if_neg he] at hl
    by_cases hd : (deadB R i && decide (2 ≤ lenAt R i) && cellAt R i != E) = true
    · rw [if_pos hd] at hl
      left
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hd
      exact ⟨hd.1.2, hd.2, by rw [hl]; rfl⟩
    · rw [if_neg hd] at hl
      right
      rw [hl]; unfold lenFor; simp
  have hEW : ∀ i, i < R.length → isEntB R i = true → 2 ≤ lenAt W i := by
    intro i hi he
    obtain ⟨a, ha, -, hv⟩ := hpos_e i he
    have hl : lenAt W i = lenFor (clsAt R i) ((entries R).map Prod.snd) (prefixVals 2 (gs.map comp)) i := by
      rw [lenAt_def, hW i hi]
    rw [hl, hv]; exact PV_ge 2 (gs.map comp) a (by simp; omega)
  have hskel : Skel R W := by
    refine ⟨hlW.symm, fun i => ⟨(hcell i).symm, ?_, ?_⟩⟩
    · rcases Nat.lt_or_ge i R.length with hi | hi
      · rcases hlen i hi with he | ⟨h2, -, h⟩ | h
        · exact Or.inr ⟨(isEntB_iff.1 he).2.2.1, hEW i hi he⟩
        · exact Or.inr ⟨h2, by omega⟩
        · exact Or.inl h.symm
      · left; rw [lenAt_def R, lenAt_def W, runAt_of_ge (R := R) hi, runAt_of_ge (R := W) (by omega)]
    · intro hE
      rcases Nat.lt_or_ge i R.length with hi | hi
      · rcases hlen i hi with he | ⟨-, hne, -⟩ | h
        · exact absurd hE (isEntB_iff.1 he).2.1
        · exact absurd hE hne
        · exact h.symm
      · rw [lenAt_def R, lenAt_def W, runAt_of_ge (R := R) hi, runAt_of_ge (R := W) (by omega)]
  refine ⟨⟨hskel, fun i hi => ?_, fun i k hi hk => ?_⟩, ?_⟩
  · -- the anchor
    have hil := (isEntB_iff.1 hi).1
    obtain ⟨a, ha, hRa, hv⟩ := hpos_e i hi
    have hWa : lenAt W i = PV 2 (gs.map comp) a := by rw [lenAt_def, hW i hil, ← hv]
    have h1 := PV_ge 2 gs a (by omega)
    have h2 := PV_ge 2 (gs.map comp) a (by simp; omega)
    have := close_of_Cl (PV_close 2 2 gs a (by omega))
    rw [hRa, hWa]
    have e1 : ((PV 2 gs a - 2 : Nat) : Int) = (PV 2 gs a : Int) - 2 := by omega
    have e2 : ((PV 2 (gs.map comp) a - 2 : Nat) : Int) = (PV 2 (gs.map comp) a : Int) - 2 := by omega
    rwa [e1, e2] at this
  · -- pairs of entries
    have hil := (isEntB_iff.1 hi).1
    have hkl := (isEntB_iff.1 hk).1
    obtain ⟨a, ha, hRa, hva⟩ := hpos_e i hi
    obtain ⟨b, hb, hRb, hvb⟩ := hpos_e k hk
    have hWa : lenAt W i = PV 2 (gs.map comp) a := by rw [lenAt_def, hW i hil, ← hva]
    have hWb : lenAt W k = PV 2 (gs.map comp) b := by rw [lenAt_def, hW k hkl, ← hvb]
    rw [hRa, hRb, hWa, hWb]
    rcases Nat.lt_trichotomy a b with hab | rfl | hab
    · have h1 := PV_mono 2 gs (Nat.le_of_lt hab) (by omega)
      have h2 := PV_mono 2 (gs.map comp) (Nat.le_of_lt hab) (by simp; omega)
      have := (close_of_Cl (PV_close_pair 2 2 gs hab (by omega))).neg
      have c1 : ((PV 2 gs b - PV 2 gs a : Nat) : Int) = (PV 2 gs b : Int) - PV 2 gs a := by omega
      have c2 : ((PV 2 (gs.map comp) b - PV 2 (gs.map comp) a : Nat) : Int) =
          (PV 2 (gs.map comp) b : Int) - PV 2 (gs.map comp) a := by omega
      rw [c1, c2] at this
      have e1 : ((PV 2 gs a : Nat) : Int) - (PV 2 gs b : Nat) = -(((PV 2 gs b : Nat) : Int) - (PV 2 gs a : Nat)) := by omega
      have e2 : ((PV 2 (gs.map comp) a : Nat) : Int) - (PV 2 (gs.map comp) b : Nat) =
          -(((PV 2 (gs.map comp) b : Nat) : Int) - (PV 2 (gs.map comp) a : Nat)) := by omega
      rw [e1, e2]; exact this
    · simp only [Int.sub_self]; exact close.refl _ _
    · have h1 := PV_mono 2 gs (Nat.le_of_lt hab) (by omega)
      have h2 := PV_mono 2 (gs.map comp) (Nat.le_of_lt hab) (by simp; omega)
      have := close_of_Cl (PV_close_pair 2 2 gs hab (by omega))
      have c1 : ((PV 2 gs a - PV 2 gs b : Nat) : Int) = (PV 2 gs a : Int) - PV 2 gs b := by omega
      have c2 : ((PV 2 (gs.map comp) a - PV 2 (gs.map comp) b : Nat) : Int) =
          (PV 2 (gs.map comp) a : Int) - PV 2 (gs.map comp) b := by omega
      rwa [c1, c2] at this
  · -- the witness is maximal
    have hposW : PosR W := by
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hiR : i < R.length := by omega
      rw [← runAt_eq_getElem hi, ← lenAt_def]
      rcases hlen i hiR with he | ⟨-, -, h⟩ | h
      · have := hEW i hiR he; omega
      · omega
      · rw [h, lenAt_def]
        exact hpos _ (by rw [runAt_eq_getElem hiR]; exact List.getElem_mem hiR)
    exact maxB_of_cells none R W hlW.symm (fun i => (hcell i).symm) hposW hR

end Col
end Cgt
