import Cgt.FamilyB1

/-!
# The family `Tᵃ □□ Fᵃ` (`b = 2`), following Thanatipanonda

`Tᵃ □□ Fᵃ` is infinitesimal for `a ≥ 4` (Thanatipanonda, *Further hopping with toads and
frogs*, Theorem C.1). The proof uses the one-sided Death Leap Principle and Lemma C.1 below.
-/

namespace Cgt
open Cell TF Game

local notation "rep" => List.replicate

/-- A prefix consisting of toads and frogs only, ending in a frog (or empty). Such a prefix
never produces moves of its own when followed by a toad or a frog. -/
def Inert (L : List Cell) : Prop := E ∉ L ∧ (L = [] ∨ L.getLast? = some F)

theorem leftMoves_T_cons_of {r : List Cell} (h1 : r.head? ≠ some E)
    (h2 : ∀ s, r ≠ F :: E :: s) : leftMoves (T :: r) = (leftMoves r).map (T :: ·) := by
  match r, h1, h2 with
  | [], _, _ => rfl
  | E :: s, h1, _ => simp at h1
  | T :: s, _, _ => simp [leftMoves]
  | F :: [], _, _ => rfl
  | F :: E :: s, _, h2 => exact absurd rfl (h2 s)
  | F :: T :: s, _, _ => simp [leftMoves]
  | F :: F :: s, _, _ => simp [leftMoves]

theorem leftMoves_inert_append : ∀ (L B : List Cell), Inert L → B.head? ≠ some E →
    leftMoves (L ++ B) = (leftMoves B).map (L ++ ·)
  | [], B, _, _ => by simp
  | c :: L', B, ⟨hE, hlast⟩, hB => by
    have hc : c ≠ E := fun h => hE (h ▸ List.mem_cons_self ..)
    have hE' : E ∉ L' := fun h => hE (List.mem_cons_of_mem _ h)
    -- the tail is inert too, or empty
    have hL' : Inert L' ∨ L' = [] := by
      rcases L' with _ | ⟨d, L''⟩
      · exact Or.inr rfl
      · left
        refine ⟨hE', Or.inr ?_⟩
        rcases hlast with h | h
        · simp at h
        · simpa [List.getLast?_cons_cons] using h
    have ih : leftMoves (L' ++ B) = (leftMoves B).map (L' ++ ·) := by
      rcases hL' with hL' | rfl
      · exact leftMoves_inert_append L' B hL' hB
      · simp
    cases c with
    | E => exact absurd rfl hc
    | F =>
      simp only [List.cons_append, leftMoves_F, ih, List.map_map]
      rfl
    | T =>
      -- `L'` is nonempty (otherwise `L = [T]` would not end with `F`)
      rcases L' with _ | ⟨d, L''⟩
      · rcases hlast with h | h <;> simp at h
      · rw [List.cons_append, leftMoves_T_cons_of, ih, List.map_map]
        · rfl
        · have : d ≠ E := fun h => hE' (h ▸ List.mem_cons_self ..)
          simpa using this
        · intro s hs
          simp only [List.cons_append, List.cons.injEq] at hs
          obtain ⟨rfl, hs⟩ := hs
          rcases L'' with _ | ⟨e, L'''⟩
          · simp at hs; rw [hs] at hB; simp at hB
          · simp at hs
            exact hE' (by simp [hs.1])

/-! ### Lemma C.1 -/

theorem rep_succ_append {α : Type} (c : α) (k : Nat) (r : List α) :
    rep (k + 1) c ++ r = rep k c ++ c :: r := by
  rw [List.replicate_succ', List.append_assoc]; rfl

/-- `L Tᵃ F□ Tᵏ FT□ Fᵇ⁺¹`. -/
def c1pos (L : List Cell) (a k b : Nat) : List Cell :=
  L ++ (rep a T ++ F :: E :: (rep k T ++ F :: T :: E :: rep (b + 1) F))

theorem lm_c1_tail (k b : Nat) :
    leftMoves (rep k T ++ F :: T :: E :: rep (b + 1) F) =
      [rep k T ++ F :: E :: T :: rep (b + 1) F] := by
  cases k with
  | zero => simp [leftMoves_rep_F]
  | succ k =>
    rw [rep_succ_append, leftMoves_rep_T_append_T, leftMoves_T_F_T, leftMoves_F, leftMoves_T_E,
      leftMoves_E, leftMoves_rep_F]
    simp [rep_succ_append]

theorem lm_c1_B (a k b : Nat) :
    ∀ q ∈ leftMoves (rep a T ++ F :: E :: (rep k T ++ F :: T :: E :: rep (b + 1) F)),
      q = rep a T ++ F :: E :: (rep k T ++ F :: E :: T :: rep (b + 1) F) ∨
      ∃ a', a = a' + 1 ∧ q = rep a' T ++ E :: F :: T :: (rep k T ++ F :: T :: E :: rep (b + 1) F) := by
  cases a with
  | zero =>
    simp [lm_c1_tail]
  | succ a =>
    rw [rep_succ_append, leftMoves_rep_T_append_T, leftMoves_T_F_E, leftMoves_F, leftMoves_E,
      lm_c1_tail]
    intro q hq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · right; exact ⟨a, rfl, rfl⟩
    · left
      rw [rep_succ_append]

/-! ### Death Leap conditions with an inert prefix -/

theorem adjOK_of_noE {R : Cell → Cell → Prop} (hR : ∀ x y, x ≠ E → y ≠ E → R x y) :
    ∀ L : List Cell, E ∉ L → AdjOK R L
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: r, h => by
    refine ⟨hR x y (fun hx => h (hx ▸ List.mem_cons_self ..)) (fun hy => h ?_),
      adjOK_of_noE hR (y :: r) (fun hm => h (List.mem_cons_of_mem _ hm))⟩
    rw [hy]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem noTE_of_ne {x y : Cell} (_ : x ≠ E) (hy : y ≠ E) : NoTE x y := fun h => hy h.2
theorem noEE_of_ne {x y : Cell} (hx : x ≠ E) (_ : y ≠ E) : NoEE x y := fun h => hx h.1

theorem dlp_inert_append {L B : List Cell} (hL : Inert L) (hB : DLPCond B) :
    DLPCond (L ++ B) := by
  rcases B with _ | ⟨y, r⟩
  · simp only [List.append_nil]
    exact ⟨adjOK_of_noE (fun _ _ => noTE_of_ne) L hL.1, adjOK_of_noE (fun _ _ => noEE_of_ne) L hL.1⟩
  · obtain ⟨hE, hlast⟩ := hL
    constructor
    · rw [adjOK_append_cons]
      refine ⟨adjOK_of_noE (fun _ _ => noTE_of_ne) L hE, fun x hx hT => ?_, hB.1⟩
      rcases hlast with rfl | h
      · simp at hx
      · rw [h] at hx; cases hx; cases hT.1
    · rw [adjOK_append_cons]
      refine ⟨adjOK_of_noE (fun _ _ => noEE_of_ne) L hE, fun x hx hT => ?_, hB.2⟩
      rcases hlast with rfl | h
      · simp at hx
      · rw [h] at hx; cases hx; cases hT.1

/-- `x :: (cᵏ ++ y :: r)` satisfies an adjacency condition. -/
theorem adjOK_cons_rep_append (R : Cell → Cell → Prop) (x c y : Cell) (r : List Cell)
    (hxc : R x c) (hxy : R x y) (hcc : R c c) (hcy : R c y) (h : AdjOK R (y :: r)) :
    ∀ k, AdjOK R (x :: (rep k c ++ y :: r))
  | 0 => ⟨hxy, h⟩
  | k + 1 => by
    show R x c ∧ AdjOK R (rep (k + 1) c ++ y :: r)
    exact ⟨hxc, adjOK_rep_append R c y r hcc hcy h (k + 1)⟩

theorem inert_head {a : Nat} {X : List Cell} :
    (rep a T ++ F :: X).head? ≠ some E := by
  cases a <;> simp [List.replicate_succ]

/-- Right's answer to a Left pass in `c1pos`. -/
def c1pass (L : List Cell) (a k b : Nat) : List Cell :=
  L ++ (rep a T ++ F :: E :: (rep k T ++ F :: T :: F :: E :: rep b F))

theorem c1pass_mem (L : List Cell) (a k b : Nat) : c1pass L a k b ∈ rightMoves (c1pos L a k b) := by
  rw [mem_rightMoves]
  left
  refine ⟨L ++ (rep a T ++ F :: E :: (rep k T ++ [F, T])), rep b F, ?_, ?_⟩
  · simp [c1pos, List.replicate_succ, List.append_assoc]
  · simp [c1pass, List.append_assoc]

theorem dlpB_c1pass (a k b : Nat) :
    DLPCond (rep a T ++ F :: E :: (rep k T ++ F :: T :: F :: E :: rep b F)) := by
  have tailOK : ∀ R : Cell → Cell → Prop, R F T → R T F → R F E → R E F → R F F →
      AdjOK R (F :: T :: F :: E :: rep b F) := by
    intro R h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, adjOK_cons_rep R E F h4 h5 b⟩
  constructor
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    exact ⟨by decide, adjOK_cons_rep_append _ E T F _ (by decide) (by decide) (by decide)
      (by decide) (tailOK _ (by decide) (by decide) (by decide) (by decide) (by decide)) k⟩
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    exact ⟨by decide, adjOK_cons_rep_append _ E T F _ (by decide) (by decide) (by decide)
      (by decide) (tailOK _ (by decide) (by decide) (by decide) (by decide) (by decide)) k⟩

theorem dlpB_c1slide (a k b : Nat) :
    DLPCond (rep a T ++ F :: E :: (rep k T ++ F :: E :: T :: rep (b + 1) F)) := by
  have tailOK : ∀ R : Cell → Cell → Prop, R F E → R E T → R T F → R F F →
      AdjOK R (F :: E :: T :: rep (b + 1) F) := by
    intro R h1 h2 h3 h4
    exact ⟨h1, h2, adjOK_cons_rep R T F h3 h4 (b + 1)⟩
  constructor
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    exact ⟨by decide, adjOK_cons_rep_append _ E T F _ (by decide) (by decide) (by decide)
      (by decide) (tailOK _ (by decide) (by decide) (by decide) (by decide)) k⟩
  · apply adjOK_rep_append _ T F _ (by decide) (by decide)
    exact ⟨by decide, adjOK_cons_rep_append _ E T F _ (by decide) (by decide) (by decide)
      (by decide) (tailOK _ (by decide) (by decide) (by decide) (by decide)) k⟩

/-- **Lemma C.1** (Thanatipanonda): `L Tᵃ F□ Tᵏ FT□ Fᵇ⁺¹` has Left stop `≤ 0` for every inert
prefix `L`. -/
theorem upperZero_c1 : ∀ (a : Nat) (L : List Cell) (k b : Nat), Inert L →
    UpperZero (tf (c1pos L a k b))
  | a, L, k, b, hL => by
    rw [upperZero_tf_iff]
    refine ⟨?_, ?_⟩
    · rw [lfZero_tf_iff]
      exact Or.inr ⟨_, c1pass_mem L a k b,
        upperZero_of_le_zero (le_zero_of_dlp _ (dlp_inert_append hL (dlpB_c1pass a k b)))⟩
    · intro q hq
      rw [c1pos, leftMoves_inert_append L _ hL inert_head] at hq
      simp only [List.mem_map] at hq
      obtain ⟨q', hq', rfl⟩ := hq
      rcases lm_c1_B a k b q' hq' with rfl | ⟨a', rfl, rfl⟩
      · rw [lfZero_tf_iff]
        exact Or.inl (le_zero_of_dlp _ (dlp_inert_append hL (dlpB_c1slide a k b)))
      · rw [lfZero_tf_iff]
        right
        refine ⟨c1pos L a' (k + 1) b, ?_, upperZero_c1 a' L (k + 1) b hL⟩
        rw [mem_rightMoves]
        left
        refine ⟨L ++ rep a' T, T :: (rep k T ++ F :: T :: E :: rep (b + 1) F), ?_, ?_⟩
        · simp [List.append_assoc]
        · simp [c1pos, List.replicate_succ, List.append_assoc]

/-! ### Move enumeration helpers -/

/-- A `simp` set that computes Left moves of positions built from blocks. -/
theorem lm_helper_TFT (k : Nat) (r : List Cell) :
    leftMoves (rep (k + 1) T ++ F :: T :: r) = (leftMoves (F :: T :: r)).map (rep (k + 1) T ++ ·) := by
  rw [rep_succ_append, leftMoves_rep_T_append_T, leftMoves_T_F_T, List.map_map]
  apply List.map_congr_left; intro q _; simp [rep_succ_append]

theorem lm_helper_TFF (k : Nat) (r : List Cell) :
    leftMoves (rep (k + 1) T ++ F :: F :: r) = (leftMoves (F :: F :: r)).map (rep (k + 1) T ++ ·) := by
  rw [rep_succ_append, leftMoves_rep_T_append_T, leftMoves_T_F_F, List.map_map]
  apply List.map_congr_left; intro q _; simp [rep_succ_append]

theorem lm_helper_TE (k : Nat) (r : List Cell) :
    leftMoves (rep (k + 1) T ++ E :: r) =
      (rep k T ++ E :: T :: r) :: (leftMoves (E :: r)).map (rep (k + 1) T ++ ·) := by
  rw [rep_succ_append, leftMoves_rep_T_append_T, leftMoves_T_E]
  simp only [List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left; intro q _; simp [rep_succ_append]

theorem lm_helper_TFE (k : Nat) (r : List Cell) :
    leftMoves (rep (k + 1) T ++ F :: E :: r) =
      (rep k T ++ E :: F :: T :: r) :: (leftMoves (F :: E :: r)).map (rep (k + 1) T ++ ·) := by
  rw [rep_succ_append, leftMoves_rep_T_append_T, leftMoves_T_F_E]
  simp only [List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left; intro q _; simp [rep_succ_append]

theorem leftMoves_T_rep_F (k : Nat) : leftMoves (T :: rep (k + 2) F) = [] := by
  simp [List.replicate_succ, leftMoves_rep_F]

/-! ### The jammed chain `Tᵖ □ Tʳ⁺² Fʳ⁺² □ Fᵖ` -/

def chainM (p r : Nat) : List Cell := rep p T ++ E :: (rep (r + 2) T ++ (rep (r + 2) F ++ E :: rep p F))

theorem mirror_rep_T (k : Nat) : mirror (rep k T) = rep k F := by
  simp [mirror, List.map_replicate, List.reverse_replicate]

theorem mirror_rep_F (k : Nat) : mirror (rep k F) = rep k T := by
  simp [mirror, List.map_replicate, List.reverse_replicate]

theorem mirror_chainM (p r : Nat) : mirror (chainM p r) = chainM p r := by
  simp [chainM, mirror_rep_T, mirror_rep_F, List.append_assoc]

theorem lm_chain_tail (r : Nat) (X : List Cell) (hX : leftMoves X = []) :
    leftMoves (rep (r + 2) T ++ (rep (r + 2) F ++ X)) = [] := by
  have e : rep (r + 2) T ++ (rep (r + 2) F ++ X) = rep (r + 2) T ++ F :: F :: (rep r F ++ X) := by
    simp [List.replicate_succ]
  rw [e, lm_helper_TFF, leftMoves_F, leftMoves_F, leftMoves_replicate_F_append, hX]
  simp

theorem lm_E_rep_F (p : Nat) : leftMoves (E :: rep p F) = [] := by
  simp [leftMoves_rep_F]

theorem leftMoves_chainM_zero (r : Nat) : leftMoves (chainM 0 r) = [] := by
  rw [chainM, List.replicate_zero, List.nil_append, leftMoves_E, lm_chain_tail r _ (lm_E_rep_F 0)]
  rfl

theorem leftMoves_chainM_succ (p r : Nat) :
    leftMoves (chainM (p + 1) r) =
      [rep p T ++ E :: (rep (r + 3) T ++ (rep (r + 2) F ++ E :: rep (p + 1) F))] := by
  rw [chainM, lm_helper_TE, leftMoves_E, lm_chain_tail r _ (lm_E_rep_F _)]
  simp [List.replicate_succ]

theorem chainM_mem (p r : Nat) :
    chainM p (r + 1) ∈ rightMoves (rep p T ++ E :: (rep (r + 3) T ++ (rep (r + 2) F ++ E :: rep (p + 1) F))) := by
  rw [mem_rightMoves]
  left
  refine ⟨rep p T ++ E :: (rep (r + 3) T ++ rep (r + 2) F), rep p F, ?_, ?_⟩
  · simp [List.replicate_succ, List.append_assoc]
  · simp [chainM, List.append_assoc, List.replicate_succ']

theorem upperZero_chainM : ∀ (p r : Nat), UpperZero (tf (chainM p r))
  | 0, r => by
    rw [upperZero_tf_iff, leftMoves_chainM_zero]
    exact ⟨lfZero_of_mirror (mirror_chainM 0 r), by simp⟩
  | p + 1, r => by
    rw [upperZero_tf_iff, leftMoves_chainM_succ]
    refine ⟨lfZero_of_mirror (mirror_chainM (p + 1) r), ?_⟩
    simp only [List.mem_singleton, forall_eq]
    rw [lfZero_tf_iff]
    exact Or.inr ⟨_, chainM_mem p r, upperZero_chainM p (r + 1)⟩

/-! ### The asymmetric nodes (with `a = c + 4`) -/

/-- Proves `DLPCond` for positions `Tᵏ x₁ … xₙ Fᵐ`. -/
macro "dlp_tac" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩ <;>
  (apply adjOK_rep_append _ T _ _ (by decide) (by decide)) <;>
  (repeat (first
    | exact adjOK_cons_rep _ _ F (by decide) (by decide) _
    | refine adjOK_cons_cons.2 ⟨by decide, ?_⟩))))

def nH1 (c : Nat) : List Cell := rep (c + 3) T ++ E :: F :: E :: T :: rep (c + 3) F
def nH2 (c : Nat) : List Cell := rep (c + 3) T ++ E :: F :: F :: T :: E :: rep (c + 2) F
def nK1 (c : Nat) : List Cell := rep (c + 2) T ++ F :: T :: E :: E :: T :: rep (c + 3) F
def nK2 (c : Nat) : List Cell := rep (c + 2) T ++ F :: T :: E :: F :: T :: E :: rep (c + 2) F
def nK3 (c : Nat) : List Cell := rep (c + 2) T ++ F :: T :: F :: E :: T :: E :: rep (c + 2) F
def nK4 (c : Nat) : List Cell := rep (c + 2) T ++ F :: T :: E :: F :: F :: T :: E :: rep (c + 1) F

theorem inert_TF (k : Nat) : Inert (rep k T ++ [F]) := by
  refine ⟨by simp [List.mem_replicate], Or.inr (by simp)⟩

theorem inert_nil : Inert [] := ⟨by simp, Or.inl rfl⟩

/-- Membership of a slide `□F → F□` given explicitly. -/
theorem slide_mem (u r : List Cell) : u ++ F :: E :: r ∈ rightMoves (u ++ E :: F :: r) :=
  mem_rightMoves.2 (Or.inl ⟨u, r, rfl, rfl⟩)

/-- Membership of a jump `□TF → FT□` given explicitly. -/
theorem jump_mem (u r : List Cell) : u ++ F :: T :: E :: r ∈ rightMoves (u ++ E :: T :: F :: r) :=
  mem_rightMoves.2 (Or.inr ⟨u, r, rfl, rfl⟩)

theorem upperZero_K3 (c : Nat) : UpperZero (tf (nK3 c)) := by
  rw [upperZero_tf_iff]
  refine ⟨?_, ?_⟩
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨rep (c + 2) T ++ F :: T :: F :: E :: T :: F :: E :: rep (c + 1) F, ?_,
      upperZero_of_le_zero (le_zero_of_dlp _ (by dlp_tac))⟩
    have := slide_mem (rep (c + 2) T ++ [F, T, F, E, T]) (rep (c + 1) F)
    simpa [nK3, List.replicate_succ, List.append_assoc] using this
  · intro q hq
    rw [nK3, lm_helper_TFT, leftMoves_F, leftMoves_T_F_E, leftMoves_F, leftMoves_E,
      leftMoves_T_E, leftMoves_E, leftMoves_rep_F] at hq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.map_map] at hq
    rcases hq with rfl | rfl
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨rep (c + 2) T ++ F :: E :: F :: T :: T :: F :: E :: rep (c + 1) F, ?_,
        upperZero_of_le_zero (le_zero_of_dlp _ (by dlp_tac))⟩
      have := slide_mem (rep (c + 2) T ++ [F, E, F, T, T]) (rep (c + 1) F)
      simpa [List.replicate_succ, List.append_assoc] using this
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨c1pos (rep (c + 2) T ++ [F]) 1 0 c, ?_, upperZero_c1 1 _ 0 c (inert_TF _)⟩
      have := jump_mem (rep (c + 2) T ++ [F, T, F, E]) (rep (c + 1) F)
      simpa [c1pos, List.replicate_succ, List.append_assoc] using this

theorem upperZero_K4 (c : Nat) : UpperZero (tf (nK4 c)) := by
  rw [upperZero_tf_iff]
  refine ⟨?_, ?_⟩
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨c1pos (rep (c + 2) T ++ [F]) 1 0 c, ?_, upperZero_c1 1 _ 0 c (inert_TF _)⟩
    have := slide_mem (rep (c + 2) T ++ [F, T]) (F :: T :: E :: rep (c + 1) F)
    simpa [nK4, c1pos, List.replicate_succ, List.append_assoc] using this
  · intro q hq
    rw [nK4, lm_helper_TFT, leftMoves_F, leftMoves_T_E, leftMoves_E, leftMoves_F, leftMoves_F,
      leftMoves_T_E, leftMoves_E, leftMoves_rep_F] at hq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.map_map] at hq
    rcases hq with rfl | rfl
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨rep (c + 2) T ++ F :: E :: T :: F :: F :: T :: F :: E :: rep c F, ?_,
        upperZero_of_le_zero (le_zero_of_dlp _ (by dlp_tac))⟩
      have := slide_mem (rep (c + 2) T ++ [F, E, T, F, F, T]) (rep c F)
      simpa [List.replicate_succ, List.append_assoc] using this
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨rep (c + 2) T ++ F :: T :: F :: E :: F :: E :: T :: rep (c + 1) F, ?_,
        upperZero_of_le_zero (le_zero_of_dlp _ (by dlp_tac))⟩
      have := slide_mem (rep (c + 2) T ++ [F, T]) (F :: E :: T :: rep (c + 1) F)
      simpa [List.append_assoc] using this

theorem upperZero_K2 (c : Nat) : UpperZero (tf (nK2 c)) := by
  rw [upperZero_tf_iff]
  refine ⟨?_, ?_⟩
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨nK3 c, ?_, upperZero_K3 c⟩
    have := slide_mem (rep (c + 2) T ++ [F, T]) (T :: E :: rep (c + 2) F)
    simpa [nK2, nK3, List.append_assoc] using this
  · intro q hq
    rw [nK2, lm_helper_TFT, leftMoves_F, leftMoves_T_E, leftMoves_E, leftMoves_F,
      leftMoves_T_E, leftMoves_E, leftMoves_rep_F] at hq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.map_map] at hq
    rcases hq with rfl | rfl
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨rep (c + 2) T ++ F :: E :: T :: F :: T :: F :: E :: rep (c + 1) F, ?_,
        upperZero_of_le_zero (le_zero_of_dlp _ (by dlp_tac))⟩
      have := slide_mem (rep (c + 2) T ++ [F, E, T, F, T]) (rep (c + 1) F)
      simpa [List.replicate_succ, List.append_assoc] using this
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨nK4 c, ?_, upperZero_K4 c⟩
      have := jump_mem (rep (c + 2) T ++ [F, T, E, F]) (rep (c + 1) F)
      simpa [nK4, List.replicate_succ, List.append_assoc] using this

theorem upperZero_K1 (c : Nat) : UpperZero (tf (nK1 c)) := by
  rw [upperZero_tf_iff]
  refine ⟨?_, ?_⟩
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨nK2 c, ?_, upperZero_K2 c⟩
    have := jump_mem (rep (c + 2) T ++ [F, T, E]) (rep (c + 2) F)
    simpa [nK1, nK2, List.replicate_succ, List.append_assoc] using this
  · intro q hq
    rw [nK1, lm_helper_TFT, leftMoves_F, leftMoves_T_E, leftMoves_E, leftMoves_E,
      leftMoves_T_rep_F (c + 1)] at hq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.map_map] at hq
    subst hq
    rw [lfZero_tf_iff]
    refine Or.inr ⟨c1pos [] (c + 2) 1 (c + 1), ?_, upperZero_c1 (c + 2) [] 1 (c + 1) inert_nil⟩
    have := jump_mem (rep (c + 2) T ++ [F, E, T]) (rep (c + 2) F)
    simpa [c1pos, List.replicate_succ, List.append_assoc] using this

theorem upperZero_H2 (c : Nat) : UpperZero (tf (nH2 c)) := by
  rw [upperZero_tf_iff]
  refine ⟨?_, ?_⟩
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨c1pos [] (c + 3) 0 (c + 1), ?_, upperZero_c1 (c + 3) [] 0 (c + 1) inert_nil⟩
    have := slide_mem (rep (c + 3) T) (F :: T :: E :: rep (c + 2) F)
    simpa [nH2, c1pos, List.append_assoc] using this
  · intro q hq
    rw [nH2, lm_helper_TE, leftMoves_E, leftMoves_F, leftMoves_F, leftMoves_T_E, leftMoves_E,
      leftMoves_rep_F] at hq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.map_map] at hq
    rcases hq with rfl | rfl
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨nK2 c, ?_, upperZero_K2 c⟩
      have := jump_mem (rep (c + 2) T) (F :: T :: E :: rep (c + 2) F)
      simpa [nK2, List.append_assoc] using this
    · rw [lfZero_tf_iff]
      refine Or.inr ⟨rep (c + 3) T ++ F :: E :: F :: E :: T :: rep (c + 2) F, ?_,
        upperZero_of_le_zero (le_zero_of_dlp _ (by dlp_tac))⟩
      have := slide_mem (rep (c + 3) T) (F :: E :: T :: rep (c + 2) F)
      simpa [List.append_assoc] using this

theorem upperZero_H1 (c : Nat) : UpperZero (tf (nH1 c)) := by
  rw [upperZero_tf_iff]
  refine ⟨?_, ?_⟩
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨nH2 c, ?_, upperZero_H2 c⟩
    have := jump_mem (rep (c + 3) T ++ [E, F]) (rep (c + 2) F)
    simpa [nH1, nH2, List.replicate_succ, List.append_assoc] using this
  · intro q hq
    rw [nH1, lm_helper_TE, leftMoves_E, leftMoves_F, leftMoves_E, leftMoves_T_rep_F (c + 1)] at hq
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      List.map_map] at hq
    subst hq
    rw [lfZero_tf_iff]
    refine Or.inr ⟨nK1 c, ?_, upperZero_K1 c⟩
    have := jump_mem (rep (c + 2) T) (E :: T :: rep (c + 3) F)
    simpa [nK1, List.append_assoc] using this

/-- `Tᶜ⁺³ □ TF □ Fᶜ⁺³` (symmetric). -/
def nG1 (c : Nat) : List Cell := rep (c + 3) T ++ E :: T :: F :: E :: rep (c + 3) F

theorem mirror_nG1 (c : Nat) : mirror (nG1 c) = nG1 c := by
  simp [nG1, mirror_rep_T, mirror_rep_F, List.append_assoc]

theorem upperZero_G1 (c : Nat) : UpperZero (tf (nG1 c)) := by
  rw [upperZero_tf_iff]
  refine ⟨lfZero_of_mirror (mirror_nG1 c), ?_⟩
  intro q hq
  rw [nG1, lm_helper_TE, leftMoves_E, leftMoves_T_F_E, leftMoves_F, leftMoves_E,
    leftMoves_rep_F] at hq
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    List.map_map] at hq
  rcases hq with rfl | rfl
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨chainM (c + 2) 0, ?_, upperZero_chainM (c + 2) 0⟩
    have := slide_mem (rep (c + 2) T ++ [E, T, T, F]) (rep (c + 2) F)
    simpa [chainM, List.replicate_succ, List.append_assoc] using this
  · rw [lfZero_tf_iff]
    refine Or.inr ⟨nH1 c, ?_, upperZero_H1 c⟩
    have := slide_mem (rep (c + 3) T ++ [E]) (T :: rep (c + 3) F)
    simpa [nH1, List.append_assoc] using this

theorem leftMoves_start_b2 (c : Nat) :
    leftMoves (start (c + 4) 2) = [rep (c + 3) T ++ E :: T :: E :: rep (c + 4) F] := by
  have e : start (c + 4) 2 = rep (c + 4) T ++ E :: E :: rep (c + 4) F := by
    simp [start, List.append_assoc]
  rw [e, lm_helper_TE, leftMoves_E, leftMoves_E, leftMoves_rep_F]
  rfl

/-- **The case `b = 2`, `a ≥ 4`** (Thanatipanonda's Theorem C.1). -/
theorem infinitesimal_start_b_two (c : Nat) : Infinitesimal (tf (start (c + 4) 2)) := by
  rw [infinitesimal_start_iff, upperZero_tf_iff, leftMoves_start_b2]
  refine ⟨lfZero_of_mirror (mirror_start _ _), ?_⟩
  simp only [List.mem_singleton, forall_eq]
  rw [lfZero_tf_iff]
  refine Or.inr ⟨nG1 c, ?_, upperZero_G1 c⟩
  have := slide_mem (rep (c + 3) T ++ [E, T]) (rep (c + 3) F)
  simpa [nG1, List.replicate_succ, List.append_assoc] using this

end Cgt
