import Cgt.Four

/-!
# Shapes of four-piece positions

The *shape* of a four-piece position records its pieces, the differences `g₄ - g₀` and
`g₃ - g₁` of mirrored gaps, and the smaller gap of each mirrored pair and the centre gap,
capped at `K = 4` (above the cap only the parity is kept).

`Rel j p q` says that `p` and `q` have the same shape with a margin of `j`: capped values are
at least `K + j` on both sides. One move turns `Rel (j + 1)` into `Rel j`
(`lm_rel`, `rm_rel`), and `Rel 0` positions have equal shapes. Every position is related with
margin `2` to its normal form `norm`, one of finitely many witnesses of its shape. So "every
Left move from a shape can be answered by a Right move into a given set of shapes" is a finite
check on witnesses (`Inv4.step`).
-/

namespace Cgt
open Cell TF Game

def K4 : Nat := 4

def cap (x : Nat) : Nat := if x < K4 then x else K4 + x % 2

/-- Code of a piece: `1` for a toad, `2` for a frog. -/
def cellCode (b : Bool) : Nat := if b then 1 else 2

def codeCell (n : Nat) : Bool := n == 1

structure Shape where
  code : Nat
  d0 : Int
  d1 : Int
  m0 : Nat
  m1 : Nat
  m2 : Nat
  deriving DecidableEq, Repr

namespace P4

def code (p : P4) : Nat := 27 * cellCode p.c1 + 9 * cellCode p.c2 + 3 * cellCode p.c3 + cellCode p.c4

def shape (p : P4) : Shape :=
  ⟨p.code, (p.g4 : Int) - p.g0, (p.g3 : Int) - p.g1, cap (min p.g0 p.g4), cap (min p.g1 p.g3), cap p.g2⟩

end P4

/-! ### Closeness with a margin -/

def close (j x y : Nat) : Prop := x = y ∨ (K4 + j ≤ x ∧ K4 + j ≤ y ∧ x % 2 = y % 2)

/-- A mirrored pair of gaps `(x, y)` and `(x', y')`: same difference, close minima. -/
def PR (j x y x' y' : Nat) : Prop := y + x' = y' + x ∧ close j (min x y) (min x' y')

def Rel (j : Nat) (p q : P4) : Prop :=
  p.c1 = q.c1 ∧ p.c2 = q.c2 ∧ p.c3 = q.c3 ∧ p.c4 = q.c4 ∧
  PR j p.g0 p.g4 q.g0 q.g4 ∧ PR j p.g1 p.g3 q.g1 q.g3 ∧ close j p.g2 q.g2

def ORel {α : Type} (R : α → α → Prop) : Option α → Option α → Prop
  | none, none => True
  | some x, some y => R x y
  | _, _ => False

theorem cap_eq {x y : Nat} (h : x = y ∨ (4 + 0 ≤ x ∧ 4 + 0 ≤ y ∧ x % 2 = y % 2)) : cap x = cap y := by
  unfold cap K4
  by_cases hx : x < 4 <;> by_cases hy : y < 4 <;> simp only [hx, hy, ite_true, ite_false] <;> omega

theorem shape_eq_of_rel {p q : P4} (h : Rel 0 p q) : p.shape = q.shape := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel, PR] at h
  obtain ⟨rfl, rfl, rfl, rfl, ⟨h5, h7⟩, ⟨h6, h8⟩, h9⟩ := h
  simp only [close, K4] at h7 h8 h9
  simp only [P4.shape, P4.code, Shape.mk.injEq, true_and]
  refine ⟨by omega, by omega, cap_eq h7, cap_eq h8, cap_eq h9⟩

-- Close a goal about one part (a pair or the centre) from the hypothesis about that part,
-- with the other parts' hypotheses removed so that `omega` stays fast.
set_option hygiene false in
macro "part_tac" : tactic => `(tactic| first
  | (clear hB hC; simp only [PR, close, K4, true_or, or_true, true_and, and_true] at * <;> omega)
  | (clear hA hC; simp only [PR, close, K4, true_or, or_true, true_and, and_true] at * <;> omega)
  | (clear hA hB; simp only [PR, close, K4, true_or, or_true, true_and, and_true] at * <;> omega))

set_option hygiene false in
macro "rel_parts" : tactic => `(tactic| first
  | trivial
  | (refine ⟨?_, ?_, ?_⟩ <;> part_tac)
  | (refine ⟨?_, ?_⟩ <;> part_tac)
  | part_tac)

section
variable {j : Nat} {p q : P4} (h : Rel (j + 1) p q)
include h

set_option maxHeartbeats 4000000 in
theorem lm1_rel : ORel (Rel j) p.lm1 q.lm1 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.lm1
  by_cases a0 : c1 = true <;> by_cases a1 : c2 = false <;> by_cases zg1 : g1 = 0 <;> by_cases zg1' : g1' = 0 <;> by_cases zg2 : g2 = 0 <;> by_cases zg2' : g2' = 0 <;>
    simp only [a0, a1, zg1, zg1', zg2, zg2', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

set_option maxHeartbeats 4000000 in
theorem lm2_rel : ORel (Rel j) p.lm2 q.lm2 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.lm2
  by_cases a0 : c2 = true <;> by_cases a1 : c3 = false <;> by_cases zg2 : g2 = 0 <;> by_cases zg2' : g2' = 0 <;> by_cases zg3 : g3 = 0 <;> by_cases zg3' : g3' = 0 <;>
    simp only [a0, a1, zg2, zg2', zg3, zg3', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

set_option maxHeartbeats 4000000 in
theorem lm3_rel : ORel (Rel j) p.lm3 q.lm3 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.lm3
  by_cases a0 : c3 = true <;> by_cases a1 : c4 = false <;> by_cases zg3 : g3 = 0 <;> by_cases zg3' : g3' = 0 <;> by_cases zg4 : g4 = 0 <;> by_cases zg4' : g4' = 0 <;>
    simp only [a0, a1, zg3, zg3', zg4, zg4', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

set_option maxHeartbeats 4000000 in
theorem lm4_rel : ORel (Rel j) p.lm4 q.lm4 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.lm4
  by_cases a0 : c4 = true <;> by_cases zg4 : g4 = 0 <;> by_cases zg4' : g4' = 0 <;>
    simp only [a0, zg4, zg4', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

set_option maxHeartbeats 4000000 in
theorem rm1_rel : ORel (Rel j) p.rm1 q.rm1 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.rm1
  by_cases a0 : c1 = false <;> by_cases zg0 : g0 = 0 <;> by_cases zg0' : g0' = 0 <;>
    simp only [a0, zg0, zg0', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

set_option maxHeartbeats 4000000 in
theorem rm2_rel : ORel (Rel j) p.rm2 q.rm2 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.rm2
  by_cases a0 : c2 = false <;> by_cases a1 : c1 = true <;> by_cases zg1 : g1 = 0 <;> by_cases zg1' : g1' = 0 <;> by_cases zg0 : g0 = 0 <;> by_cases zg0' : g0' = 0 <;>
    simp only [a0, a1, zg1, zg1', zg0, zg0', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

set_option maxHeartbeats 4000000 in
theorem rm3_rel : ORel (Rel j) p.rm3 q.rm3 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.rm3
  by_cases a0 : c3 = false <;> by_cases a1 : c2 = true <;> by_cases zg2 : g2 = 0 <;> by_cases zg2' : g2' = 0 <;> by_cases zg1 : g1 = 0 <;> by_cases zg1' : g1' = 0 <;>
    simp only [a0, a1, zg2, zg2', zg1, zg1', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

set_option maxHeartbeats 4000000 in
theorem rm4_rel : ORel (Rel j) p.rm4 q.rm4 := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  obtain ⟨c1', c2', c3', c4', g0', g1', g2', g3', g4'⟩ := q
  dsimp only [Rel] at h
  obtain ⟨rfl, rfl, rfl, rfl, hA, hB, hC⟩ := h
  unfold P4.rm4
  by_cases a0 : c4 = false <;> by_cases a1 : c3 = true <;> by_cases zg3 : g3 = 0 <;> by_cases zg3' : g3' = 0 <;> by_cases zg2 : g2 = 0 <;> by_cases zg2' : g2' = 0 <;>
    simp only [a0, a1, zg3, zg3', zg2, zg2', ne_eq, not_true_eq_false, not_false_eq_true, and_true, true_and,
      and_false, false_and, ite_true, ite_false, ORel, Rel] <;>
    rel_parts

end

/-! ### Validity is preserved by moves -/

theorem mem_lms {p q : P4} : q ∈ p.lms ↔ p.lm1 = some q ∨ p.lm2 = some q ∨ p.lm3 = some q ∨ p.lm4 = some q := by
  simp [P4.lms, Option.mem_toList, Option.mem_def, or_assoc, eq_comm]

theorem mem_rms {p q : P4} : q ∈ p.rms ↔ p.rm1 = some q ∨ p.rm2 = some q ∨ p.rm3 = some q ∨ p.rm4 = some q := by
  simp [P4.rms, Option.mem_toList, Option.mem_def, or_assoc, eq_comm]

/-! ### Transfer of moves between related positions -/

theorem ORel.some_left {α : Type} {R : α → α → Prop} {a : Option α} {x : α} :
    ORel R (some x) a → ∃ y, a = some y ∧ R x y := by
  cases a <;> simp [ORel]

theorem ORel.some_right {α : Type} {R : α → α → Prop} {a : Option α} {y : α} :
    ORel R a (some y) → ∃ x, a = some x ∧ R x y := by
  cases a <;> simp [ORel]

theorem lms_rel {j : Nat} {p w q : P4} (h : Rel (j + 1) p w) (hq : q ∈ p.lms) :
    ∃ qw ∈ w.lms, Rel j q qw := by
  rcases mem_lms.1 hq with e | e | e | e
  · have := lm1_rel h; rw [e] at this; obtain ⟨y, hy, hr⟩ := ORel.some_left this
    exact ⟨y, mem_lms.2 (Or.inl hy), hr⟩
  · have := lm2_rel h; rw [e] at this; obtain ⟨y, hy, hr⟩ := ORel.some_left this
    exact ⟨y, mem_lms.2 (Or.inr (Or.inl hy)), hr⟩
  · have := lm3_rel h; rw [e] at this; obtain ⟨y, hy, hr⟩ := ORel.some_left this
    exact ⟨y, mem_lms.2 (Or.inr (Or.inr (Or.inl hy))), hr⟩
  · have := lm4_rel h; rw [e] at this; obtain ⟨y, hy, hr⟩ := ORel.some_left this
    exact ⟨y, mem_lms.2 (Or.inr (Or.inr (Or.inr hy))), hr⟩

theorem rms_rel {j : Nat} {q qw rw : P4} (h : Rel (j + 1) q qw) (hr : rw ∈ qw.rms) :
    ∃ r ∈ q.rms, Rel j r rw := by
  rcases mem_rms.1 hr with e | e | e | e
  · have := rm1_rel h; rw [e] at this; obtain ⟨x, hx, hr⟩ := ORel.some_right this
    exact ⟨x, mem_rms.2 (Or.inl hx), hr⟩
  · have := rm2_rel h; rw [e] at this; obtain ⟨x, hx, hr⟩ := ORel.some_right this
    exact ⟨x, mem_rms.2 (Or.inr (Or.inl hx)), hr⟩
  · have := rm3_rel h; rw [e] at this; obtain ⟨x, hx, hr⟩ := ORel.some_right this
    exact ⟨x, mem_rms.2 (Or.inr (Or.inr (Or.inl hx))), hr⟩
  · have := rm4_rel h; rw [e] at this; obtain ⟨x, hx, hr⟩ := ORel.some_right this
    exact ⟨x, mem_rms.2 (Or.inr (Or.inr (Or.inr hx))), hr⟩

/-! ### Normal forms and witnesses -/

/-- Values `≥ K + 2` are lowered by an even amount to `K + 2` or `K + 3`. -/
def nrm (m : Nat) : Nat := if m < K4 + 2 then m else K4 + 2 + (m - K4) % 2

theorem nrm_spec (m : Nat) : nrm m ≤ m ∧ close 2 m (nrm m) := by
  unfold nrm close K4
  by_cases h : m < 4 + 2 <;> simp only [h, ite_true, ite_false, true_or, and_true] <;> omega

/-- The normal form: each mirrored pair is shifted down by the same even amount. -/
def P4.norm (p : P4) : P4 :=
  { p with
    g0 := p.g0 - (min p.g0 p.g4 - nrm (min p.g0 p.g4)),
    g4 := p.g4 - (min p.g0 p.g4 - nrm (min p.g0 p.g4)),
    g1 := p.g1 - (min p.g1 p.g3 - nrm (min p.g1 p.g3)),
    g3 := p.g3 - (min p.g1 p.g3 - nrm (min p.g1 p.g3)),
    g2 := nrm p.g2 }

theorem rel_norm (p : P4) : Rel 2 p p.norm := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  have h0 := nrm_spec (min g0 g4)
  have h1 := nrm_spec (min g1 g3)
  have h2 := nrm_spec g2
  simp only [Rel, PR, P4.norm, true_and]
  simp only [close] at h0 h1 h2 ⊢
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, by omega⟩

/-- Candidate values of a minimum with capped value `c` in a normal form (`K` is even). -/
def capVals (c : Nat) : List Nat := if c < K4 then [c] else [c, c + 2]

def gapsOf (m : Nat) (d : Int) : Nat × Nat :=
  if 0 ≤ d then (m, m + d.toNat) else (m + (-d).toNat, m)

def mkP (s : Shape) (a b c : Nat) : P4 :=
  ⟨codeCell (s.code / 27 % 3), codeCell (s.code / 9 % 3), codeCell (s.code / 3 % 3),
    codeCell (s.code % 3), (gapsOf a s.d0).1, (gapsOf b s.d1).1, c, (gapsOf b s.d1).2,
    (gapsOf a s.d0).2⟩

/-- The witnesses of a shape: every normal form with that shape is one of them. -/
def wit (s : Shape) : List P4 :=
  (capVals s.m0).flatMap fun a => (capVals s.m1).flatMap fun b => (capVals s.m2).map fun c => mkP s a b c

theorem nrm_mem_capVals (m : Nat) : nrm m ∈ capVals (cap m) := by
  unfold nrm capVals cap K4
  by_cases h : m < 4 <;> by_cases h' : m < 4 + 2 <;>
    simp only [h, h', ite_true, ite_false, List.mem_cons, List.mem_singleton, List.not_mem_nil] <;>
    (first | omega | (by_cases h'' : 4 + m % 2 < 4 <;> simp only [h'', ite_true, ite_false,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] <;> omega))

theorem codeCell_cellCode (c : Bool) : codeCell (cellCode c) = c := by
  cases c <;> rfl

theorem norm_mem_wit (p : P4) : p.norm ∈ wit p.shape := by
  obtain ⟨c1, c2, c3, c4, g0, g1, g2, g3, g4⟩ := p
  simp only [wit, List.mem_flatMap, List.mem_map]
  refine ⟨nrm (min g0 g4), nrm_mem_capVals _, nrm (min g1 g3), nrm_mem_capVals _, nrm g2,
    nrm_mem_capVals _, ?_⟩
  have e1 : (27 * cellCode c1 + 9 * cellCode c2 + 3 * cellCode c3 + cellCode c4) / 27 % 3 = cellCode c1 := by
    cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp [cellCode]
  have e2 : (27 * cellCode c1 + 9 * cellCode c2 + 3 * cellCode c3 + cellCode c4) / 9 % 3 = cellCode c2 := by
    cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp [cellCode]
  have e3 : (27 * cellCode c1 + 9 * cellCode c2 + 3 * cellCode c3 + cellCode c4) / 3 % 3 = cellCode c3 := by
    cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp [cellCode]
  have e4 : (27 * cellCode c1 + 9 * cellCode c2 + 3 * cellCode c3 + cellCode c4) % 3 = cellCode c4 := by
    cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp [cellCode]
  have n0 := (nrm_spec (min g0 g4)).1
  have n1 := (nrm_spec (min g1 g3)).1
  simp only [mkP, P4.shape, P4.code, e1, e2, e3, e4, codeCell_cellCode, P4.norm, gapsOf, P4.mk.injEq, true_and]
  by_cases d0 : (0 : Int) ≤ (g4 : Int) - g0 <;> by_cases d1 : (0 : Int) ≤ (g3 : Int) - g1 <;>
    simp only [d0, d1, ite_true, ite_false] <;> omega

/-! ### Keys and the finite check -/

def Shape.inRange (s : Shape) : Bool :=
  s.code < 81 && -32 ≤ s.d0 && s.d0 < 32 && -32 ≤ s.d1 && s.d1 < 32 && s.m0 < 8 && s.m1 < 8 && s.m2 < 8

def Shape.key (s : Shape) : Nat :=
  s.code * 2097152 + (s.d0 + 32).toNat * 32768 + (s.d1 + 32).toNat * 512 + s.m0 * 64 + s.m1 * 8 + s.m2

def decodeKey (k : Nat) : Shape :=
  ⟨k / 2097152, ((k / 32768 % 64 : Nat) : Int) - 32, ((k / 512 % 64 : Nat) : Int) - 32, k / 64 % 8,
    k / 8 % 8, k % 8⟩

theorem decodeKey_key (s : Shape) (h : s.inRange = true) : decodeKey s.key = s := by
  obtain ⟨c, d0, d1, m0, m1, m2⟩ := s
  simp only [Shape.inRange, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [decodeKey, Shape.key, Shape.mk.injEq]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

inductive KTree where
  | leaf : KTree
  | node : KTree → Nat → KTree → KTree

def KTree.mem : KTree → Nat → Bool
  | leaf, _ => false
  | node l k r, x => if x < k then l.mem x else if k < x then r.mem x else true

def KTree.toList : KTree → List Nat
  | leaf => []
  | node l k r => l.toList ++ k :: r.toList

theorem KTree.mem_toList : ∀ {t : KTree} {x : Nat}, t.mem x = true → x ∈ t.toList
  | leaf, _, h => by simp [KTree.mem] at h
  | node l k r, x, h => by
    simp only [KTree.mem] at h
    simp only [KTree.toList, List.mem_append, List.mem_cons]
    by_cases h1 : x < k
    · simp only [h1, ite_true] at h; exact Or.inl (KTree.mem_toList h)
    · by_cases h2 : k < x
      · simp only [h1, h2, ite_true, ite_false] at h; exact Or.inr (Or.inr (KTree.mem_toList h))
      · exact Or.inr (Or.inl (by omega))

/-- `r`'s shape is one of the shapes in `t`. -/
def good (t : KTree) (r : P4) : Bool := r.shape.inRange && t.mem r.shape.key

/-- Every Left move from `w` has a Right reply whose shape is in `t`. -/
def stepOK (t : KTree) (w : P4) : Bool := w.lms.all fun q => q.rms.any (good t)

/-- The finite check: `stepOK` for every witness of every shape in `t`. -/
def checkAll (t : KTree) : Bool := t.toList.all fun k => (wit (decodeKey k)).all (stepOK t)

/-- If the finite check passes, every position whose shape is in `t` is `≤ 0`. -/
theorem le_zero_of_good (t : KTree) (ht : checkAll t = true) :
    ∀ (n : Nat) (p : P4), pot p.toList < n → good t p = true → le (tf p.toList) zero := by
  intro n
  induction n with
  | zero => intro p h; omega
  | succ n ih =>
    intro p hn hg
    rw [le_zero_iff_tf, leftMoves_toList p]
    intro q hq
    obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
    simp only [good, Bool.and_eq_true] at hg
    have hk := KTree.mem_toList hg.2
    simp only [checkAll, List.all_eq_true] at ht
    have hw := ht _ hk p.norm (by rw [decodeKey_key _ hg.1]; exact norm_mem_wit p)
    obtain ⟨qw, hqw, hrel⟩ := lms_rel (rel_norm p) hq'
    simp only [stepOK, List.all_eq_true, List.any_eq_true] at hw
    obtain ⟨rw, hrw, hgood⟩ := hw qw hqw
    obtain ⟨r, hr, hrel'⟩ := rms_rel hrel hrw
    have hmem := toList_mem_rightMoves hr
    refine ⟨r.toList, hmem, ih r ?_ ?_⟩
    · have h1 := pot_lt_of_mem_leftMoves (leftMoves_toList p ▸ hq)
      have h2 := pot_lt_of_mem_rightMoves hmem
      omega
    · simp only [good] at hgood ⊢
      rw [shape_eq_of_rel hrel']; exact hgood

end Cgt
