import Cgt.Moves
import Cgt.Four

/-!
# Positions as lists of runs

A run list `R : RL` is a list of pairs `(c, n)`: `n` copies of the cell `c`. `expand R` is the
position. A run list is *maximal* (`maxB`) if every run is nonempty and adjacent runs have
different cells; every position has exactly one maximal run list.

`lmovesR R` lists the Left moves of a maximal run list explicitly: the last toad of a toad run
slides into the empty run after it, or jumps the single frog after it. The runs on either side are
merged where needed, so the results are again maximal. `mem_leftMoves_expand` shows that these are
exactly the Left moves of `expand R`. Right moves are obtained by mirroring (`rmovesR`).
-/

namespace Cgt
namespace Col
open Cell TF

local notation "rep" => List.replicate

abbrev RL := List (Cell × Nat)

def expand : RL → List Cell
  | [] => []
  | (c, n) :: R => rep n c ++ expand R

@[simp] theorem expand_nil : expand [] = [] := rfl
@[simp] theorem expand_cons (c : Cell) (n : Nat) (R : RL) :
    expand ((c, n) :: R) = rep n c ++ expand R := rfl

@[simp] theorem expand_append (R S : RL) : expand (R ++ S) = expand R ++ expand S := by
  induction R with
  | nil => rfl
  | cons x R ih => obtain ⟨c, n⟩ := x; simp [ih]

/-! ### Maximal run lists -/

/-- Scan for maximality: every run nonempty and with a cell different from the previous one. -/
def okFrom : Option Cell → RL → Bool
  | _, [] => true
  | p, x :: R => decide (1 ≤ x.2) && (p != some x.1) && okFrom (some x.1) R

/-- The cell of the last run (or `p` if there is none). -/
def lastC : Option Cell → RL → Option Cell
  | p, [] => p
  | _, x :: R => lastC (some x.1) R

/-- Maximal run lists: every run nonempty, adjacent runs with different cells. -/
def maxB (R : RL) : Bool := okFrom none R

theorem okFrom_append (p : Option Cell) (L M : RL) :
    okFrom p (L ++ M) = (okFrom p L && okFrom (lastC p L) M) := by
  induction L generalizing p with
  | nil => simp [okFrom, lastC]
  | cons x L ih => simp [okFrom, lastC, ih, Bool.and_assoc]

@[simp] theorem okFrom_nil (p : Option Cell) : okFrom p [] = true := rfl
@[simp] theorem okFrom_cons (p : Option Cell) (x : Cell × Nat) (R : RL) :
    okFrom p (x :: R) = (decide (1 ≤ x.2) && (p != some x.1) && okFrom (some x.1) R) := rfl
@[simp] theorem lastC_nil (p : Option Cell) : lastC p [] = p := rfl
@[simp] theorem lastC_cons (p : Option Cell) (x : Cell × Nat) (R : RL) : lastC p (x :: R) = lastC (some x.1) R := rfl

theorem lastC_append (p : Option Cell) (L M : RL) : lastC p (L ++ M) = lastC (lastC p L) M := by
  induction L generalizing p with
  | nil => rfl
  | cons x L ih => simp [ih]

/-- Every run is nonempty. -/
def PosR (R : RL) : Prop := ∀ x ∈ R, 1 ≤ x.2

theorem posR_of_okFrom : ∀ {p : Option Cell} {R : RL}, okFrom p R = true → PosR R
  | _, [], _ => by simp [PosR]
  | _, x :: R, h => by
    simp only [okFrom_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1.1
    · exact posR_of_okFrom h.2 y hy

theorem posR_of_maxB {R : RL} (h : maxB R = true) : PosR R := posR_of_okFrom h

theorem PosR.tail {x : Cell × Nat} {R : RL} (h : PosR (x :: R)) : PosR R :=
  fun y hy => h y (List.mem_cons_of_mem _ hy)

theorem PosR.append {R S : RL} (hR : PosR R) (hS : PosR S) : PosR (R ++ S) := by
  intro y hy
  rcases List.mem_append.1 hy with h | h
  · exact hR y h
  · exact hS y h

theorem PosR.left {R S : RL} (h : PosR (R ++ S)) : PosR R :=
  fun y hy => h y (List.mem_append_left _ hy)

theorem PosR.right {R S : RL} (h : PosR (R ++ S)) : PosR S :=
  fun y hy => h y (List.mem_append_right _ hy)

/-! ### Explicit Left moves -/

/-- The cells before the moved toad, read backwards: `Arev` is the reversed prefix, `n` the
length of the toad's run. The toad leaves one empty square behind, merged into an empty run just
before if its run disappears. -/
def leftPartRev (Arev : RL) (n : Nat) : RL :=
  if n = 1 then
    match Arev with
    | (E, p) :: Ar => (E, p + 1) :: Ar
    | _ => (E, 1) :: Arev
  else (E, 1) :: (T, n - 1) :: Arev

/-- The toad arrives in front of the rest `C` of an empty run of length `m`, merging into a toad
run just after if the empty run disappears. -/
def rightPart (m : Nat) (C : RL) : RL :=
  if m = 1 then
    match C with
    | (T, q) :: C' => (T, q + 1) :: C'
    | _ => (T, 1) :: C
  else (T, 1) :: (E, m - 1) :: C

/-- The move of the last toad of the run `(T, n)`, preceded by the reversed prefix `Arev` and
followed by `B`. -/
def moveAt (Arev : RL) (n : Nat) : RL → Option RL
  | (E, m) :: C => some ((leftPartRev Arev n).reverse ++ rightPart m C)
  | (F, 1) :: (E, m) :: C => some ((leftPartRev Arev n).reverse ++ (F, 1) :: rightPart m C)
  | _ => none

def lmovesAux : RL → RL → List RL
  | _, [] => []
  | Arev, (c, n) :: B => (if c = T then (moveAt Arev n B).toList else []) ++ lmovesAux ((c, n) :: Arev) B

/-- All Left moves of a maximal run list. -/
def lmovesR (R : RL) : List RL := lmovesAux [] R

theorem expand_leftPartRev (Arev : RL) (n : Nat) (hn : 1 ≤ n) :
    expand (leftPartRev Arev n).reverse = expand Arev.reverse ++ rep (n - 1) T ++ [E] := by
  unfold leftPartRev
  by_cases h1 : n = 1
  · subst h1
    simp only [ite_true]
    split
    · next p Ar =>
      simp [List.replicate_succ', List.append_assoc]
    · simp
  · simp only [h1, ite_false, List.reverse_cons, expand_append, expand_cons, List.append_assoc]
    simp

theorem expand_rightPart (m : Nat) (C : RL) (hm : 1 ≤ m) :
    expand (rightPart m C) = T :: (rep (m - 1) E ++ expand C) := by
  unfold rightPart
  by_cases h1 : m = 1
  · subst h1
    simp only [ite_true]
    split
    · next q C' => simp [List.replicate_succ]
    · simp
  · simp [h1]

/-- `lmovesAux Pre B` contains the move of every toad run of `B`. -/
theorem mem_lmovesAux_of {X : RL} :
    ∀ (Pre A : RL) (n : Nat) (B : RL), moveAt (A.reverse ++ Pre) n B = some X →
      X ∈ lmovesAux Pre (A ++ (T, n) :: B)
  | Pre, [], n, B, h => by
    simp only [List.reverse_nil, List.nil_append] at h
    simp [lmovesAux, h]
  | Pre, (c, k) :: A, n, B, h => by
    simp only [List.cons_append, lmovesAux, List.mem_append]
    right
    exact mem_lmovesAux_of ((c, k) :: Pre) A n B (by simpa [List.reverse_cons, List.append_assoc] using h)

/-- Every element of `lmovesAux Pre B` is a move of a toad run of `B`. -/
theorem exists_of_mem_lmovesAux {X : RL} :
    ∀ (Pre B : RL), X ∈ lmovesAux Pre B →
      ∃ A n B', B = A ++ (T, n) :: B' ∧ moveAt (A.reverse ++ Pre) n B' = some X
  | _, [], h => by simp [lmovesAux] at h
  | Pre, (c, k) :: B, h => by
    simp only [lmovesAux, List.mem_append] at h
    rcases h with h | h
    · by_cases hc : c = T
      · subst hc
        simp only [ite_true, Option.mem_toList] at h
        exact ⟨[], k, B, rfl, by simpa using h⟩
      · simp [hc] at h
    · obtain ⟨A, n, B', rfl, hm⟩ := exists_of_mem_lmovesAux ((c, k) :: Pre) B h
      exact ⟨(c, k) :: A, n, B', rfl, by simpa [List.reverse_cons, List.append_assoc] using hm⟩

/-! ### Parsing a cell-level move back into runs -/

theorem rep_eq_append_cons {k : Nat} {c d : Cell} {u v : List Cell} (h : rep k c = u ++ d :: v) :
    d = c := by
  have : d ∈ rep k c := by rw [h]; simp
  exact (List.eq_of_mem_replicate this)

/-- The first cell of a nonempty expanded run list is the cell of its first run. -/
theorem expand_eq_cons {R : RL} (hR : PosR R) {d : Cell} {r : List Cell} (h : expand R = d :: r) :
    ∃ m C, R = (d, m) :: C ∧ 1 ≤ m ∧ r = rep (m - 1) d ++ expand C := by
  match R, hR, h with
  | (c, k) :: C, hR, h =>
    have hk : 1 ≤ k := hR _ (List.mem_cons_self ..)
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [expand_cons, List.replicate_succ, List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨k + 1, C, rfl, hk, by simp⟩

/-- A slide in `expand R`: the toad is the last of its run and the empty square starts the next. -/
theorem parse_slide : ∀ {R : RL}, PosR R → ∀ {u r : List Cell}, expand R = u ++ T :: E :: r →
    ∃ A n m C, R = A ++ (T, n) :: (E, m) :: C ∧ 1 ≤ n ∧ 1 ≤ m ∧
      u = expand A ++ rep (n - 1) T ∧ r = rep (m - 1) E ++ expand C
  | [], _, u, r, h => by cases u <;> simp at h
  | (c, k) :: R, hR, u, r, h => by
    have hk : 1 ≤ k := hR _ (List.mem_cons_self ..)
    simp only [expand_cons] at h
    rcases List.append_eq_append_iff.1 h with ⟨as, rfl, h2⟩ | ⟨bs, h1, h2⟩
    · obtain ⟨A, n, m, C, rfl, hn, hm, rfl, rfl⟩ := parse_slide hR.tail h2
      exact ⟨(c, k) :: A, n, m, C, rfl, hn, hm, by simp, rfl⟩
    · match bs, h1, h2 with
      | [], h1, h2 =>
        simp only [List.append_nil, List.nil_append] at h1 h2
        obtain ⟨A, n, m, C, rfl, hn, hm, hu, rfl⟩ := parse_slide (u := []) hR.tail (by simpa using h2.symm)
        subst h1
        exact ⟨(c, k) :: A, n, m, C, rfl, hn, hm, by rw [expand_cons, List.append_assoc, ← hu, List.append_nil], rfl⟩
      | [x], h1, h2 =>
        simp only [List.singleton_append, List.cons.injEq] at h2
        obtain ⟨rfl, h2⟩ := h2
        have hc : c = T := (rep_eq_append_cons (v := []) h1).symm
        subst hc
        obtain ⟨m, C, rfl, hm, rfl⟩ := expand_eq_cons hR.tail h2.symm
        refine ⟨[], k, m, C, rfl, hk, hm, ?_, rfl⟩
        have : rep k T = rep (k - 1) T ++ [T] := by
          rw [← List.replicate_succ']; congr 1; omega
        rw [this] at h1
        simpa using (List.append_inj_left' h1 rfl).symm
      | x :: y :: bs, h1, h2 =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl, -⟩ := h2
        have e1 := rep_eq_append_cons h1
        have e2 := rep_eq_append_cons (u := u ++ [T]) (by simpa using h1)
        rw [← e1] at e2; exact absurd e2 (by decide)

/-- A jump in `expand R`: the toad is the last of its run, the frog a run of its own. -/
theorem parse_jump : ∀ {R : RL}, PosR R → ∀ {u r : List Cell}, expand R = u ++ T :: F :: E :: r →
    ∃ A n m C, R = A ++ (T, n) :: (F, 1) :: (E, m) :: C ∧ 1 ≤ n ∧ 1 ≤ m ∧
      u = expand A ++ rep (n - 1) T ∧ r = rep (m - 1) E ++ expand C
  | [], _, u, r, h => by cases u <;> simp at h
  | (c, k) :: R, hR, u, r, h => by
    have hk : 1 ≤ k := hR _ (List.mem_cons_self ..)
    simp only [expand_cons] at h
    rcases List.append_eq_append_iff.1 h with ⟨as, rfl, h2⟩ | ⟨bs, h1, h2⟩
    · obtain ⟨A, n, m, C, rfl, hn, hm, rfl, rfl⟩ := parse_jump hR.tail h2
      exact ⟨(c, k) :: A, n, m, C, rfl, hn, hm, by simp, rfl⟩
    · match bs, h1, h2 with
      | [], h1, h2 =>
        simp only [List.append_nil, List.nil_append] at h1 h2
        obtain ⟨A, n, m, C, rfl, hn, hm, hu, rfl⟩ := parse_jump (u := []) hR.tail (by simpa using h2.symm)
        subst h1
        exact ⟨(c, k) :: A, n, m, C, rfl, hn, hm, by rw [expand_cons, List.append_assoc, ← hu, List.append_nil], rfl⟩
      | [x], h1, h2 =>
        simp only [List.singleton_append, List.cons.injEq] at h2
        obtain ⟨rfl, h2⟩ := h2
        have hc : c = T := (rep_eq_append_cons (v := []) h1).symm
        subst hc
        obtain ⟨j, D, rfl, hj, hr⟩ := expand_eq_cons hR.tail h2.symm
        -- the frog run has length one: the next cell is empty
        have hj1 : j = 1 := by
          rcases Nat.lt_or_ge j 2 with h | h
          · omega
          · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 2 := ⟨j - 2, by omega⟩
            simp [List.replicate_succ] at hr
        subst hj1
        simp only [Nat.sub_self, List.replicate_zero, List.nil_append] at hr
        obtain ⟨m, C, rfl, hm, rfl⟩ := expand_eq_cons hR.tail.tail hr.symm
        refine ⟨[], k, m, C, rfl, hk, hm, ?_, rfl⟩
        have : rep k T = rep (k - 1) T ++ [T] := by
          rw [← List.replicate_succ']; congr 1; omega
        rw [this] at h1
        simpa using (List.append_inj_left' h1 rfl).symm
      | x :: y :: bs, h1, h2 =>
        simp only [List.cons_append, List.cons.injEq] at h2
        obtain ⟨rfl, rfl, -⟩ := h2
        have e1 := rep_eq_append_cons h1
        have e2 := rep_eq_append_cons (u := u ++ [T]) (by simpa using h1)
        rw [← e1] at e2; exact absurd e2 (by decide)

theorem rep_append_cons (n : Nat) (c : Cell) (X : List Cell) : rep n c ++ c :: X = c :: (rep n c ++ X) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-! ### The Left moves of `expand R` -/

theorem expand_moveAt {Arev : RL} {n : Nat} {B X : RL} (hn : 1 ≤ n) (hB : PosR B)
    (h : moveAt Arev n B = some X) :
    expand X ∈ leftMoves (expand Arev.reverse ++ rep n T ++ expand B) := by
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  match B, hB, h with
  | (E, m) :: C, hB, h =>
    simp only [moveAt, Option.some.injEq] at h; subst h
    have hm : 1 ≤ m := hB _ (List.mem_cons_self ..)
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [mem_leftMoves]; left
    refine ⟨expand Arev.reverse ++ rep n T, rep m E ++ expand C, ?_, ?_⟩
    · simp [List.replicate_succ', List.append_assoc, rep_append_cons]
    · rw [expand_append, expand_leftPartRev _ _ (by omega), expand_rightPart _ _ (by omega)]
      simp [List.append_assoc]
  | (F, 1) :: (E, m) :: C, hB, h =>
    simp only [moveAt, Option.some.injEq] at h; subst h
    have hm : 1 ≤ m := hB (E, m) (by simp)
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [mem_leftMoves]; right
    refine ⟨expand Arev.reverse ++ rep n T, rep m E ++ expand C, ?_, ?_⟩
    · simp [List.replicate_succ', List.append_assoc, rep_append_cons]
    · rw [expand_append, expand_leftPartRev _ _ (by omega)]
      simp [expand_rightPart _ _ (show 1 ≤ m + 1 by omega), List.append_assoc]

theorem mem_leftMoves_expand {R : RL} (hR : PosR R) {q : List Cell} :
    q ∈ leftMoves (expand R) ↔ ∃ X ∈ lmovesR R, q = expand X := by
  constructor
  · intro hq
    rcases mem_leftMoves.1 hq with ⟨u, r, h, rfl⟩ | ⟨u, r, h, rfl⟩
    · obtain ⟨A, n, m, C, rfl, hn, hm, rfl, rfl⟩ := parse_slide hR h
      refine ⟨_, mem_lmovesAux_of [] A n ((E, m) :: C) (by simp [moveAt]; rfl), ?_⟩
      rw [expand_append, expand_leftPartRev _ _ hn, expand_rightPart _ _ hm]
      simp [List.append_assoc]
    · obtain ⟨A, n, m, C, rfl, hn, hm, rfl, rfl⟩ := parse_jump hR h
      refine ⟨_, mem_lmovesAux_of [] A n ((F, 1) :: (E, m) :: C) (by simp [moveAt]; rfl), ?_⟩
      rw [expand_append, expand_leftPartRev _ _ hn]
      simp [expand_rightPart _ _ hm, List.append_assoc]
  · rintro ⟨X, hX, rfl⟩
    obtain ⟨A, n, B, rfl, hm⟩ := exists_of_mem_lmovesAux [] R hX
    have hn : 1 ≤ n := hR (T, n) (by simp)
    have := expand_moveAt (Arev := A.reverse ++ []) hn (hR.right.tail) hm
    simpa [List.append_assoc] using this

/-! ### Moves keep run lists maximal -/

theorem okFrom_reverse_cases (A : RL) : A = [] ∨ ∃ Ar x, A = Ar.reverse ++ [x] ∧ A.reverse = x :: Ar := by
  cases h : A.reverse with
  | nil => left; simpa using congrArg List.reverse h
  | cons x Ar =>
    right
    refine ⟨Ar, x, ?_, rfl⟩
    have := congrArg List.reverse h
    simpa using this

theorem left_ok {A : RL} {n : Nat} (hA : okFrom none A = true) (hT : lastC none A ≠ some T) (hn : 1 ≤ n) :
    okFrom none (leftPartRev A.reverse n).reverse = true ∧ lastC none (leftPartRev A.reverse n).reverse = some E := by
  unfold leftPartRev
  by_cases h1 : n = 1
  · subst h1
    simp only [ite_true]
    rcases okFrom_reverse_cases A with rfl | ⟨Ar, x, rfl, hx⟩
    · simp
    · rw [hx]
      obtain ⟨c, q⟩ := x
      rw [okFrom_append] at hA
      cases c with
      | E =>
        simp only [List.reverse_cons, okFrom_append, lastC_append, Bool.and_eq_true] at hA ⊢
        simp_all
      | T => simp [lastC_append] at hT
      | F =>
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append, okFrom_append,
          lastC_append, Bool.and_eq_true] at hA ⊢
        simp_all
  · simp only [h1, ite_false, List.reverse_cons, List.reverse_reverse, List.append_assoc, List.singleton_append,
      okFrom_append, lastC_append, Bool.and_eq_true]
    simp_all
    omega

theorem right_ok {m : Nat} {C : RL} (hm : 1 ≤ m) (hC : okFrom (some E) C = true) (p : Option Cell)
    (hp : p ≠ some T) : okFrom p (rightPart m C) = true := by
  unfold rightPart
  by_cases h1 : m = 1
  · simp only [h1, ite_true]
    match C, hC with
    | [], _ => simpa using hp
    | (T, q) :: C', hC =>
      simp only [okFrom_cons, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hC ⊢
      exact ⟨⟨by omega, hp⟩, hC.2⟩
    | (E, q) :: C', hC => simp at hC
    | (F, q) :: C', hC =>
      simp only [okFrom_cons, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hC ⊢
      simp only [Option.some.injEq, reduceCtorEq, not_false_eq_true, and_true] at hC ⊢
      exact ⟨⟨Nat.le_refl _, hp⟩, hC.1, hC.2⟩
  · simp only [h1, ite_false, okFrom_cons, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      Option.some.injEq, reduceCtorEq, not_false_eq_true, and_true]
    exact ⟨⟨Nat.le_refl _, hp⟩, by omega, hC⟩

theorem maxB_moveAt {A : RL} {n : Nat} {B X : RL} (hR : maxB (A ++ (T, n) :: B) = true)
    (h : moveAt A.reverse n B = some X) : maxB X = true := by
  unfold maxB at hR ⊢
  rw [okFrom_append] at hR
  simp only [Bool.and_eq_true, okFrom_cons, decide_eq_true_eq, bne_iff_ne, ne_eq] at hR
  obtain ⟨hA, ⟨hn, hT⟩, hB⟩ := hR
  obtain ⟨hl, hlE⟩ := left_ok hA hT hn
  match B, hB, h with
  | (E, m) :: C, hB, h =>
    simp only [moveAt, Option.some.injEq] at h; subst h
    simp only [okFrom_cons, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB
    rw [okFrom_append, hl, hlE]
    simpa using right_ok hB.1.1 hB.2 (some E) (by simp)
  | (F, 1) :: (E, m) :: C, hB, h =>
    simp only [moveAt, Option.some.injEq] at h; subst h
    simp only [okFrom_cons, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hB
    rw [okFrom_append, hl, hlE]
    rw [okFrom_cons, right_ok hB.2.1.1 hB.2.2 (some F) (by simp)]
    simp

theorem maxB_of_mem_lmovesR {R X : RL} (hR : maxB R = true) (hX : X ∈ lmovesR R) : maxB X = true := by
  obtain ⟨A, n, B, rfl, hm⟩ := exists_of_mem_lmovesAux [] R hX
  exact maxB_moveAt hR (by simpa using hm)

/-! ### Mirror image and Right moves -/

def mirrorRL (R : RL) : RL := (R.map fun x => (x.1.swap, x.2)).reverse

@[simp] theorem mirrorRL_nil : mirrorRL [] = [] := rfl

theorem mirrorRL_cons (x : Cell × Nat) (R : RL) : mirrorRL (x :: R) = mirrorRL R ++ [(x.1.swap, x.2)] := by
  simp [mirrorRL]

theorem mirror_replicate (n : Nat) (c : Cell) : mirror (rep n c) = rep n c.swap := by
  simp [mirror, List.map_replicate, List.reverse_replicate]

theorem expand_mirrorRL (R : RL) : expand (mirrorRL R) = mirror (expand R) := by
  induction R with
  | nil => rfl
  | cons x R ih =>
    obtain ⟨c, n⟩ := x
    rw [mirrorRL_cons, expand_append, ih]
    simp [mirror_append, mirror_replicate]

theorem mirrorRL_mirrorRL (R : RL) : mirrorRL (mirrorRL R) = R := by
  simp [mirrorRL, List.map_reverse, List.map_map, Function.comp_def]

theorem PosR.mirror {R : RL} (h : PosR R) : PosR (mirrorRL R) := by
  intro y hy
  simp only [mirrorRL, List.mem_reverse, List.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact h x hx

theorem mirrorRL_append (L M : RL) : mirrorRL (L ++ M) = mirrorRL M ++ mirrorRL L := by
  simp [mirrorRL]

/-- Adjacent runs have different cells. -/
def AdjD (R : RL) : Prop := ∀ u x y v, R = u ++ x :: y :: v → x.1 ≠ y.1

theorem adjD_cons {x : Cell × Nat} {R : RL} :
    AdjD (x :: R) ↔ (∀ y R', R = y :: R' → x.1 ≠ y.1) ∧ AdjD R := by
  constructor
  · intro h
    refine ⟨fun y R' hR => h [] x y R' (by simp [hR]), fun u a b v hR => h (x :: u) a b v (by simp [hR])⟩
  · rintro ⟨h1, h2⟩ u a b v hR
    cases u with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hR
      obtain ⟨rfl, rfl⟩ := hR
      exact h1 b v rfl
    | cons c u =>
      simp only [List.cons_append, List.cons.injEq] at hR
      exact h2 u a b v hR.2

theorem okFrom_iff : ∀ (p : Option Cell) (R : RL),
    okFrom p R = true ↔ PosR R ∧ AdjD R ∧ ∀ y R', R = y :: R' → p ≠ some y.1
  | p, [] => by
    simp only [okFrom_nil, true_iff]
    refine ⟨by simp [PosR], fun u x y v h => by cases u <;> simp at h, fun y R' h => by simp at h⟩
  | p, x :: R => by
    rw [okFrom_cons, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, okFrom_iff, adjD_cons]
    constructor
    · rintro ⟨⟨hx, hp⟩, hR, hadj, hne⟩
      refine ⟨fun z hz => ?_, ⟨fun y R' h => ?_, hadj⟩, fun y R' h => ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact hx
        · exact hR z hz
      · have := hne y R' h; simpa using this
      · simp only [List.cons.injEq] at h; obtain ⟨rfl, rfl⟩ := h; exact hp
    · rintro ⟨hpos, ⟨h1, hadj⟩, hp⟩
      refine ⟨⟨hpos x (by simp), hp x R rfl⟩, hpos.tail, hadj, fun y R' h => ?_⟩
      have := h1 y R' h; simpa using this

theorem maxB_iff (R : RL) : maxB R = true ↔ PosR R ∧ AdjD R := by
  rw [maxB, okFrom_iff]; simp

theorem adjD_mirror {R : RL} (h : AdjD R) : AdjD (mirrorRL R) := by
  intro u x y v hR
  have := congrArg mirrorRL hR
  rw [mirrorRL_mirrorRL, mirrorRL_append, mirrorRL_cons, mirrorRL_cons] at this
  have h' := h (mirrorRL v) (y.1.swap, y.2) (x.1.swap, x.2) (mirrorRL u) (by simpa [List.append_assoc] using this)
  intro hxy; apply h'; simp [hxy]

theorem maxB_mirrorRL {R : RL} (h : maxB R = true) : maxB (mirrorRL R) = true := by
  rw [maxB_iff] at h ⊢
  exact ⟨h.1.mirror, adjD_mirror h.2⟩

/-- All Right moves of a maximal run list, by mirroring. -/
def rmovesR (R : RL) : List RL := (lmovesR (mirrorRL R)).map mirrorRL

theorem mem_rightMoves_iff_mirror {p q : List Cell} : q ∈ rightMoves p ↔ mirror q ∈ leftMoves (mirror p) := by
  rw [mem_leftMoves_mirror]
  constructor
  · intro h; exact ⟨q, h, rfl⟩
  · rintro ⟨q', hq', h⟩; rwa [mirror_injective h]

theorem mem_rightMoves_expand {R : RL} (hR : PosR R) {q : List Cell} :
    q ∈ rightMoves (expand R) ↔ ∃ Y ∈ rmovesR R, q = expand Y := by
  rw [mem_rightMoves_iff_mirror, ← expand_mirrorRL, mem_leftMoves_expand hR.mirror]
  constructor
  · rintro ⟨X, hX, h⟩
    refine ⟨mirrorRL X, List.mem_map_of_mem hX, ?_⟩
    rw [expand_mirrorRL, ← h, mirror_mirror]
  · rintro ⟨Y, hY, rfl⟩
    obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
    exact ⟨X, hX, by rw [expand_mirrorRL, mirror_mirror]⟩

theorem maxB_of_mem_rmovesR {R Y : RL} (hR : maxB R = true) (hY : Y ∈ rmovesR R) : maxB Y = true := by
  obtain ⟨X, hX, rfl⟩ := List.mem_map.1 hY
  exact maxB_mirrorRL (maxB_of_mem_lmovesR (maxB_mirrorRL hR) hX)

end Col
end Cgt
