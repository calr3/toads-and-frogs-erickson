import Cgt.Col.Dead

/-!
# The structure of a Left move

Every Left move of a maximal run list `A ++ (T, n) :: J ++ (E, m) :: C` (`J = []` for a slide,
`J = [(F, 1)]` for a jump) is `moveX A n J m C`:

* the prefix `A`, whose last run (an empty run) is lengthened by one if the toad run disappears;
* the toad run `(T, n - 1)` (absent if `n = 1`) and a short middle part `midR`, which depends only
  on `n = 1`, on whether `A` ends with an empty run, on `J`, on `m` and on whether `C` starts with a
  toad run;
* the suffix `C`, whose first run (a toad run) is lengthened by one if the empty run disappears.
-/

namespace Cgt
namespace Col
open Cell

def endsE (A : RL) : Bool :=
  match A.getLast? with
  | some (E, _) => true
  | _ => false

def startsT (C : RL) : Bool :=
  match C with
  | (T, _) :: _ => true
  | _ => false

/-- `A` with its last run lengthened by one (if `f`). -/
def modLast (A : RL) (f : Bool) : RL :=
  if f then A.dropLast ++ [(E, (A.getLastD (E, 0)).2 + 1)] else A

/-- `C` with its first run, a toad run, lengthened by one (if `f`). -/
def modHead (C : RL) (f : Bool) : RL :=
  if f then (T, (C.headD (E, 0)).2 + 1) :: C.tail else C

def mT (n : Nat) : RL := if n = 1 then [] else [(T, n - 1)]

def midR (n1 eA : Bool) (J : RL) (m : Nat) (tC : Bool) : RL :=
  (if n1 && eA then [] else [(E, 1)]) ++ J ++
    (if m = 1 then (if tC then [] else [(T, 1)]) else [(T, 1), (E, m - 1)])

def moveX (A : RL) (n : Nat) (J : RL) (m : Nat) (C : RL) : RL :=
  modLast A (decide (n = 1) && endsE A) ++ (mT n ++ midR (decide (n = 1)) (endsE A) J m (startsT C)) ++
    modHead C (decide (m = 1) && startsT C)

theorem endsE_of_reverse {A : RL} {p : Nat} {Ar : RL} (h : A.reverse = (E, p) :: Ar) :
    endsE A = true ∧ A = Ar.reverse ++ [(E, p)] := by
  have hA : A = Ar.reverse ++ [(E, p)] := by
    have := congrArg List.reverse h; simpa using this
  subst hA; simp [endsE]

theorem leftPart_eq (A : RL) (n : Nat) (hn : 1 ≤ n) :
    (leftPartRev A.reverse n).reverse = modLast A (decide (n = 1) && endsE A) ++ mT n ++
      (if decide (n = 1) && endsE A then [] else [(E, 1)]) := by
  unfold leftPartRev
  by_cases h1 : n = 1
  · subst h1
    simp only [ite_true, mT, decide_true, Bool.true_and]
    rcases hA : A.reverse with _ | ⟨⟨c, p⟩, Ar⟩
    · have : A = [] := by simpa using congrArg List.reverse hA
      subst this; simp [endsE, modLast]
    · cases c with
      | E =>
        obtain ⟨he, rfl⟩ := endsE_of_reverse hA
        simp [modLast, he]
      | T =>
        have hA' : A = Ar.reverse ++ [(T, p)] := by simpa using congrArg List.reverse hA
        subst hA'; simp [endsE, modLast]
      | F =>
        have hA' : A = Ar.reverse ++ [(F, p)] := by simpa using congrArg List.reverse hA
        subst hA'; simp [endsE, modLast]
  · simp [h1, mT, modLast]

theorem rightPart_eq (m : Nat) (C : RL) :
    rightPart m C = (if m = 1 then (if startsT C then [] else [(T, 1)]) else [(T, 1), (E, m - 1)]) ++
      modHead C (decide (m = 1) && startsT C) := by
  unfold rightPart
  by_cases h1 : m = 1
  · subst h1
    match C with
    | [] => simp [startsT, modHead]
    | (T, q) :: C' => simp [startsT, modHead]
    | (E, q) :: C' => simp [startsT, modHead]
    | (F, q) :: C' => simp [startsT, modHead]
  · simp [h1, modHead]

theorem moveAt_slide (A : RL) (n m : Nat) (C : RL) (hn : 1 ≤ n) :
    moveAt A.reverse n ((E, m) :: C) = some (moveX A n [] m C) := by
  simp only [moveAt, Option.some.injEq]
  rw [leftPart_eq A n hn, rightPart_eq]
  simp [moveX, midR, List.append_assoc]

theorem moveAt_jump (A : RL) (n m : Nat) (C : RL) (hn : 1 ≤ n) :
    moveAt A.reverse n ((F, 1) :: (E, m) :: C) = some (moveX A n [(F, 1)] m C) := by
  simp only [moveAt, Option.some.injEq]
  rw [leftPart_eq A n hn, rightPart_eq]
  simp [moveX, midR, List.append_assoc]

/-- Every Left move of a maximal run list has the form `moveX`. -/
theorem lmovesR_struct {R X : RL} (hR : maxB R = true) (hX : X ∈ lmovesR R) :
    ∃ A n J m C, R = A ++ (T, n) :: (J ++ (E, m) :: C) ∧ (J = [] ∨ J = [(F, 1)]) ∧ 1 ≤ n ∧ 1 ≤ m ∧
      X = moveX A n J m C := by
  obtain ⟨A, n, B, rfl, hm⟩ := exists_of_mem_lmovesAux [] _ hX
  have hpos := posR_of_maxB hR
  have hn : 1 ≤ n := hpos (T, n) (by simp)
  simp only [List.append_nil] at hm
  match B, hm with
  | (E, m) :: C, hm =>
    rw [moveAt_slide A n m C hn, Option.some.injEq] at hm
    exact ⟨A, n, [], m, C, rfl, Or.inl rfl, hn, hpos (E, m) (by simp), hm.symm⟩
  | (F, 1) :: (E, m) :: C, hm =>
    rw [moveAt_jump A n m C hn, Option.some.injEq] at hm
    exact ⟨A, n, [(F, 1)], m, C, rfl, Or.inr rfl, hn, hpos (E, m) (by simp), hm.symm⟩

theorem moveX_mem {A : RL} {n : Nat} {J : RL} {m : Nat} {C : RL} (hJ : J = [] ∨ J = [(F, 1)]) (hn : 1 ≤ n) :
    moveX A n J m C ∈ lmovesR (A ++ (T, n) :: (J ++ (E, m) :: C)) := by
  apply mem_lmovesAux_of [] A n
  simp only [List.append_nil]
  rcases hJ with rfl | rfl
  · exact moveAt_slide A n m C hn
  · exact moveAt_jump A n m C hn

/-! ### Where the runs are -/

theorem cellAt_def (R : RL) (i : Nat) : cellAt R i = (runAt R i).1 := rfl
theorem lenAt_def (R : RL) (i : Nat) : lenAt R i = (runAt R i).2 := rfl

theorem endsE_spec : ∀ {A : RL}, endsE A = true → ∃ A₀ p, A = A₀ ++ [(E, p)]
  | [], h => by simp [endsE] at h
  | [(c, p)], h => by
    cases c
    · exact ⟨[], p, rfl⟩
    · simp [endsE] at h
    · simp [endsE] at h
  | x :: y :: R, h => by
    have : endsE (y :: R) = true := by simpa [endsE] using h
    obtain ⟨A₀, p, hA⟩ := endsE_spec this
    exact ⟨x :: A₀, p, by rw [hA]; rfl⟩

theorem startsT_spec {C : RL} (h : startsT C = true) : ∃ q C', C = (T, q) :: C' := by
  match C, h with
  | (T, q) :: C', _ => exact ⟨q, C', rfl⟩

theorem length_modLast {A : RL} {f : Bool} (hf : f = true → endsE A = true) : (modLast A f).length = A.length := by
  unfold modLast
  cases f
  · rfl
  · obtain ⟨A₀, p, rfl⟩ := endsE_spec (hf rfl); simp

theorem length_modHead (C : RL) (f : Bool) (hf : f = true → startsT C = true) : (modHead C f).length = C.length := by
  unfold modHead
  cases f
  · rfl
  · obtain ⟨q, C', rfl⟩ := startsT_spec (hf rfl); simp

theorem runAt_modLast {A : RL} {f : Bool} (hf : f = true → endsE A = true) {i : Nat} (hi : i < A.length) :
    cellAt (modLast A f) i = cellAt A i ∧
      lenAt (modLast A f) i = lenAt A i + (if f = true ∧ i + 1 = A.length then 1 else 0) := by
  unfold modLast
  cases f
  · simp
  · obtain ⟨A₀, p, rfl⟩ := endsE_spec (hf rfl)
    simp only [List.length_append, List.length_singleton] at hi
    simp only [ite_true, List.dropLast_concat, List.getLastD_concat, cellAt, lenAt, true_and,
      List.length_append, List.length_singleton]
    by_cases h : i < A₀.length
    · rw [runAt_append_lt h, runAt_append_lt h]; simp; omega
    · have : i = A₀.length := by omega
      subst this
      rw [runAt_append_ge (Nat.le_refl _), runAt_append_ge (Nat.le_refl _)]
      simp [runAt_cons_zero]

theorem runAt_modHead {C : RL} {f : Bool} (hf : f = true → startsT C = true) (j : Nat) :
    cellAt (modHead C f) j = cellAt C j ∧ lenAt (modHead C f) j = lenAt C j + (if f = true ∧ j = 0 then 1 else 0) := by
  unfold modHead
  cases f
  · simp
  · obtain ⟨q, C', rfl⟩ := startsT_spec (hf rfl)
    cases j with
    | zero => simp [cellAt, lenAt, runAt_cons_zero]
    | succ j => simp [cellAt, lenAt, runAt_cons_succ]

/-! ### Dead intervals avoid the moving runs -/

section Struct
variable {A : RL} {n : Nat} {J : RL} {m : Nat} {C : RL}

theorem runAt_R_A {i : Nat} (h : i < A.length) : runAt (A ++ (T, n) :: (J ++ (E, m) :: C)) i = runAt A i :=
  runAt_append_lt h

theorem runAt_R_T : runAt (A ++ (T, n) :: (J ++ (E, m) :: C)) A.length = (T, n) := by
  rw [runAt_append_ge (Nat.le_refl _), Nat.sub_self, runAt_cons_zero]

theorem runAt_R_J {k : Nat} (h : k < J.length) :
    runAt (A ++ (T, n) :: (J ++ (E, m) :: C)) (A.length + 1 + k) = runAt J k := by
  rw [runAt_append_ge (by omega), show A.length + 1 + k - A.length = k + 1 by omega, runAt_cons_succ,
    runAt_append_lt h]

theorem runAt_R_E : runAt (A ++ (T, n) :: (J ++ (E, m) :: C)) (A.length + 1 + J.length) = (E, m) := by
  rw [runAt_append_ge (by omega), show A.length + 1 + J.length - A.length = J.length + 1 by omega,
    runAt_cons_succ, runAt_append_ge (Nat.le_refl _), Nat.sub_self, runAt_cons_zero]

theorem runAt_R_C {i : Nat} (h : A.length + 2 + J.length ≤ i) :
    runAt (A ++ (T, n) :: (J ++ (E, m) :: C)) i = runAt C (i - (A.length + 2 + J.length)) := by
  rw [runAt_append_ge (by omega), show i - A.length = (i - A.length - 1) + 1 by omega, runAt_cons_succ,
    runAt_append_ge (by omega), show i - A.length - 1 - J.length = (i - (A.length + 2 + J.length)) + 1 by omega,
    runAt_cons_succ]

theorem length_R : (A ++ (T, n) :: (J ++ (E, m) :: C)).length = A.length + 2 + J.length + C.length := by
  simp; omega

/-- A dead interval of `R` lies before the toad run or after the empty run. -/
theorem dead_interval {s e : Nat} (hJ : J = [] ∨ J = [(F, 1)])
    (hs : cellAt (A ++ (T, n) :: (J ++ (E, m) :: C)) s = T)
    (he : cellAt (A ++ (T, n) :: (J ++ (E, m) :: C)) e = F ∧ 2 ≤ lenAt (A ++ (T, n) :: (J ++ (E, m) :: C)) e)
    (hse : s ≤ e) (hn : ∀ k, s ≤ k → k ≤ e → cellAt (A ++ (T, n) :: (J ++ (E, m) :: C)) k ≠ E) :
    e < A.length ∨ A.length + 2 + J.length ≤ s := by
  rcases Nat.lt_or_ge e A.length with h | hea
  · exact Or.inl h
  rcases Nat.lt_or_ge s (A.length + 2 + J.length) with hsc | h
  · exfalso
    -- the empty run is not in [s, e]
    have hE := hn (A.length + 1 + J.length)
    rw [cellAt_def, runAt_R_E] at hE
    have h1 : e < A.length + 1 + J.length := Nat.lt_of_not_le fun hle => hE (by omega) hle rfl
    -- so e is the toad run or the frog of a jump
    rcases hJ with rfl | rfl
    · have : e = A.length := by simp at h1; omega
      subst this
      rw [cellAt_def, runAt_R_T] at he; exact absurd he.1 (by simp)
    · simp at h1
      rcases (show e = A.length ∨ e = A.length + 1 by omega) with rfl | rfl
      · rw [cellAt_def, runAt_R_T] at he; exact absurd he.1 (by simp)
      · have := he.2
        rw [lenAt_def, show A.length + 1 = A.length + 1 + 0 by rfl, runAt_R_J (by simp)] at this
        simp [runAt] at this
  · exact Or.inr h

/-- The moving toad run is not dead. -/
theorem not_dead_T (hJ : J = [] ∨ J = [(F, 1)]) : ¬ DeadP (A ++ (T, n) :: (J ++ (E, m) :: C)) A.length := by
  rintro ⟨s, e, hs, he, -, hT, -, hF, h2, hn⟩
  rcases dead_interval hJ hT ⟨hF, h2⟩ (by omega) hn with h | h <;> omega

/-! ### Where the runs of the move are -/

/-- The middle part of the move. -/
def Mx (A : RL) (n : Nat) (J : RL) (m : Nat) (C : RL) : RL :=
  mT n ++ midR (decide (n = 1)) (endsE A) J m (startsT C)

theorem f1_spec : (decide (n = 1) && endsE A) = true → endsE A = true := by
  simp only [Bool.and_eq_true]; exact fun h => h.2

theorem f2_spec : (decide (m = 1) && startsT C) = true → startsT C = true := by
  simp only [Bool.and_eq_true]; exact fun h => h.2

theorem moveX_def : moveX A n J m C =
    modLast A (decide (n = 1) && endsE A) ++ Mx A n J m C ++ modHead C (decide (m = 1) && startsT C) := rfl

theorem length_moveX : (moveX A n J m C).length = A.length + (Mx A n J m C).length + C.length := by
  rw [moveX_def, List.length_append, List.length_append, length_modLast f1_spec, length_modHead _ _ f2_spec]

theorem runAt_X_A {i : Nat} (h : i < A.length) :
    cellAt (moveX A n J m C) i = cellAt A i ∧
      lenAt (moveX A n J m C) i = lenAt A i + (if (decide (n = 1) && endsE A) = true ∧ i + 1 = A.length then 1 else 0) := by
  have hl := length_modLast (A := A) (f := decide (n = 1) && endsE A) f1_spec
  have := runAt_modLast (A := A) (f := decide (n = 1) && endsE A) f1_spec h
  rw [moveX_def, cellAt, lenAt, List.append_assoc, runAt_append_lt (by omega)]
  exact this

theorem runAt_X_M {i : Nat} (h1 : A.length ≤ i) (h2 : i < A.length + (Mx A n J m C).length) :
    runAt (moveX A n J m C) i = runAt (Mx A n J m C) (i - A.length) := by
  have hl := length_modLast (A := A) (f := decide (n = 1) && endsE A) f1_spec
  rw [moveX_def, List.append_assoc, runAt_append_ge (by omega), hl, runAt_append_lt (by omega)]

theorem runAt_X_C {i : Nat} (h : A.length + (Mx A n J m C).length ≤ i) :
    cellAt (moveX A n J m C) i = cellAt C (i - (A.length + (Mx A n J m C).length)) ∧
      lenAt (moveX A n J m C) i = lenAt C (i - (A.length + (Mx A n J m C).length)) +
        (if (decide (m = 1) && startsT C) = true ∧ i = A.length + (Mx A n J m C).length then 1 else 0) := by
  have hl := length_modLast (A := A) (f := decide (n = 1) && endsE A) f1_spec
  have hlen : (modLast A (decide (n = 1) && endsE A) ++ Mx A n J m C).length = A.length + (Mx A n J m C).length := by
    rw [List.length_append, hl]
  have := runAt_modHead (C := C) (f := decide (m = 1) && startsT C) f2_spec (i - (A.length + (Mx A n J m C).length))
  rw [moveX_def, cellAt, lenAt, runAt_append_ge (by rw [hlen]; exact h), hlen]
  refine ⟨this.1, ?_⟩
  rw [show (runAt (modHead C (decide (m = 1) && startsT C)) (i - (A.length + (Mx A n J m C).length))).2 =
    lenAt (modHead C (decide (m = 1) && startsT C)) (i - (A.length + (Mx A n J m C).length)) from rfl, this.2]
  congr 1
  by_cases hf : (decide (m = 1) && startsT C) = true
  · by_cases hi : i = A.length + (Mx A n J m C).length
    · simp [hf, hi]
    · have : ¬ (i - (A.length + (Mx A n J m C).length) = 0) := by omega
      simp [hf, hi, this]
  · simp [hf]

/-- The runs of the middle part: only `(T, n - 1)` can be long and not empty. -/
theorem midR_short {n1 eA : Bool} {tC : Bool} (hJ : J = [] ∨ J = [(F, 1)]) :
    ∀ x ∈ midR n1 eA J m tC, x.1 ≠ E → x.2 ≤ 1 := by
  have h1 : ∀ x ∈ (if n1 && eA then ([] : RL) else [(E, 1)]), x = (E, 1) := by
    split <;> simp
  have h2 : ∀ x ∈ J, x = (F, 1) := by rcases hJ with rfl | rfl <;> simp
  have h3 : ∀ x ∈ (if m = 1 then (if tC then ([] : RL) else [(T, 1)]) else [(T, 1), (E, m - 1)]),
      x = (T, 1) ∨ x.1 = E := by
    split
    · split <;> simp
    · intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> simp
  intro x hx hE
  unfold midR at hx
  simp only [List.mem_append] at hx
  rcases hx with (h | h) | h
  · rw [h1 x h] at hE; exact absurd rfl hE
  · rw [h2 x h]; exact Nat.le_refl _
  · rcases h3 x h with rfl | h
    · exact Nat.le_refl _
    · exact absurd h hE

theorem runAt_mem_or (l : RL) (k : Nat) : runAt l k ∈ l ∨ runAt l k = (E, 0) := by
  rcases Nat.lt_or_ge k l.length with h | h
  · left; simp [runAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  · right; exact runAt_of_ge h

theorem Mx_long (hJ : J = [] ∨ J = [(F, 1)]) {k : Nat} (hE : cellAt (Mx A n J m C) k ≠ E)
    (h2 : 2 ≤ lenAt (Mx A n J m C) k) : k = 0 ∧ 2 ≤ n ∧ runAt (Mx A n J m C) 0 = (T, n - 1) := by
  by_cases hn : n = 1
  · exfalso
    have hM : Mx A n J m C = midR (decide (n = 1)) (endsE A) J m (startsT C) := by simp [Mx, mT, hn]
    rw [hM] at hE h2
    rcases runAt_mem_or (midR (decide (n = 1)) (endsE A) J m (startsT C)) k with h | h
    · have := midR_short hJ _ h hE; simp only [lenAt] at h2; omega
    · simp [cellAt, h] at hE
  · have hM : Mx A n J m C = (T, n - 1) :: midR (decide (n = 1)) (endsE A) J m (startsT C) := by simp [Mx, mT, hn]
    rw [hM] at hE h2 ⊢
    cases k with
    | zero => simp only [lenAt, runAt_cons_zero] at h2; exact ⟨rfl, by omega, rfl⟩
    | succ k =>
      exfalso
      simp only [cellAt, lenAt, runAt_cons_succ] at hE h2
      rcases runAt_mem_or (midR (decide (n = 1)) (endsE A) J m (startsT C)) k with h | h
      · have := midR_short hJ _ h hE; omega
      · simp [h] at hE

/-! ### Dead intervals survive the move -/

theorem dead_transfer (hJ : J = [] ∨ J = [(F, 1)]) {i : Nat}
    (hd : DeadP (A ++ (T, n) :: (J ++ (E, m) :: C)) i) :
    (i < A.length → DeadP (moveX A n J m C) i) ∧
    (A.length + 2 + J.length ≤ i → DeadP (moveX A n J m C) (i - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length))) := by
  obtain ⟨s, e, hs, he, hel, hT, h2s, hF, h2e, hn⟩ := hd
  have hX := length_moveX (A := A) (n := n) (J := J) (m := m) (C := C)
  have hR := length_R (A := A) (n := n) (J := J) (m := m) (C := C)
  rcases dead_interval hJ hT ⟨hF, h2e⟩ (by omega) hn with hea | hcs
  · refine ⟨fun _ => ⟨s, e, hs, he, by omega, ?_, ?_, ?_, ?_, fun k h1 h2 => ?_⟩, fun h => by omega⟩
    · rw [(runAt_X_A (by omega)).1]; rw [cellAt_def, runAt_R_A (by omega)] at hT; exact hT
    · rw [(runAt_X_A (by omega)).2]; rw [lenAt_def, runAt_R_A (by omega)] at h2s; simp only [lenAt]; omega
    · rw [(runAt_X_A (by omega)).1]; rw [cellAt_def, runAt_R_A (by omega)] at hF; exact hF
    · rw [(runAt_X_A (by omega)).2]; rw [lenAt_def, runAt_R_A (by omega)] at h2e; simp only [lenAt]; omega
    · rw [(runAt_X_A (by omega)).1]; have := hn k h1 h2; rwa [cellAt_def, runAt_R_A (by omega)] at this
  · refine ⟨fun h => by omega, fun _ => ⟨s - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length),
      e - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length), by omega, by omega, by omega,
      ?_, ?_, ?_, ?_, fun k h1 h2 => ?_⟩⟩
    · rw [(runAt_X_C (by omega)).1, show s - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length) -
          (A.length + (Mx A n J m C).length) = s - (A.length + 2 + J.length) by omega]
      rwa [cellAt_def, runAt_R_C (by omega)] at hT
    · rw [(runAt_X_C (by omega)).2, show s - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length) -
          (A.length + (Mx A n J m C).length) = s - (A.length + 2 + J.length) by omega]
      rw [lenAt_def, runAt_R_C (by omega)] at h2s; simp only [lenAt]; omega
    · rw [(runAt_X_C (by omega)).1, show e - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length) -
          (A.length + (Mx A n J m C).length) = e - (A.length + 2 + J.length) by omega]
      rwa [cellAt_def, runAt_R_C (by omega)] at hF
    · rw [(runAt_X_C (by omega)).2, show e - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length) -
          (A.length + (Mx A n J m C).length) = e - (A.length + 2 + J.length) by omega]
      rw [lenAt_def, runAt_R_C (by omega)] at h2e; simp only [lenAt]; omega
    · rw [(runAt_X_C (by omega)).1]
      have := hn (k - (A.length + (Mx A n J m C).length) + (A.length + 2 + J.length)) (by omega) (by omega)
      rw [cellAt_def, runAt_R_C (by omega)] at this
      rwa [show k - (A.length + (Mx A n J m C).length) + (A.length + 2 + J.length) - (A.length + 2 + J.length) =
        k - (A.length + (Mx A n J m C).length) by omega] at this

end Struct

/-! ### Origins of entries, and the arithmetic of the margin -/

/-- An entry of `X` either comes from an entry of `R` shifted by at most one (the same shift in `X'`
and `R'`), or is a new run of length at most 3, the same in `X` and `X'`. -/
def Orig (R R' X X' : RL) (i : Nat) : Prop :=
  (∃ (i₀ : Nat) (δ : Int), isEntB R i₀ = true ∧ -1 ≤ δ ∧ δ ≤ 1 ∧ (lenAt X i : Int) = lenAt R i₀ + δ ∧
      (lenAt X' i : Int) = lenAt R' i₀ + δ) ∨
    (lenAt X i = lenAt X' i ∧ lenAt X i ≤ 3)

theorem pc_anchor_of_orig {j : Nat} {R R' X X' : RL} (h : Rel (j + 2) R R') {i : Nat} (hi : Orig R R' X X' i) :
    close j ((lenAt X i : Int) - 2) ((lenAt X' i : Int) - 2) := by
  rcases hi with ⟨i₀, δ, he, hd1, hd2, h1, h2⟩ | ⟨h1, -⟩
  · have := (h.2.1 i₀ he).shift (d := δ) ⟨by omega, by omega⟩
    have e1 : (lenAt X i : Int) - 2 = (lenAt R i₀ : Int) - 2 + δ := by omega
    have e2 : (lenAt X' i : Int) - 2 = (lenAt R' i₀ : Int) - 2 + δ := by omega
    rw [e1, e2]; exact this
  · rw [h1]; exact close.refl _ _

theorem pc_pair_of_orig {j : Nat} {R R' X X' : RL} (h : Rel (j + 2) R R') {i k : Nat}
    (hi : Orig R R' X X' i) (hk : Orig R R' X X' k) (hi2 : 2 ≤ lenAt X i) (hk2 : 2 ≤ lenAt X k) :
    close j ((lenAt X i : Int) - lenAt X k) ((lenAt X' i : Int) - lenAt X' k) := by
  rcases hi with ⟨i₀, δ, he, hd1, hd2, h1, h2⟩ | ⟨h1, h3⟩ <;>
    rcases hk with ⟨k₀, ε, he', he1, he2, h1', h2'⟩ | ⟨h1', h3'⟩
  · have := (h.2.2 i₀ k₀ he he').shift (d := δ - ε) ⟨by omega, by omega⟩
    have e1 : (lenAt X i : Int) - lenAt X k = ((lenAt R i₀ : Int) - lenAt R k₀) + (δ - ε) := by omega
    have e2 : (lenAt X' i : Int) - lenAt X' k = ((lenAt R' i₀ : Int) - lenAt R' k₀) + (δ - ε) := by omega
    rw [e1, e2]; exact this
  · -- `k` is new: compare with the anchor
    have := (h.2.1 i₀ he).shift (d := δ + 2 - lenAt X k) ⟨by omega, by omega⟩
    have e1 : (lenAt X i : Int) - lenAt X k = ((lenAt R i₀ : Int) - 2) + (δ + 2 - lenAt X k) := by omega
    have e2 : (lenAt X' i : Int) - lenAt X' k = ((lenAt R' i₀ : Int) - 2) + (δ + 2 - lenAt X k) := by omega
    rw [e1, e2]; exact this
  · have := ((h.2.1 k₀ he').shift (d := ε + 2 - lenAt X i) ⟨by omega, by omega⟩).neg
    have e1 : (lenAt X i : Int) - lenAt X k = -(((lenAt R k₀ : Int) - 2) + (ε + 2 - lenAt X i)) := by omega
    have e2 : (lenAt X' i : Int) - lenAt X' k = -(((lenAt R' k₀ : Int) - 2) + (ε + 2 - lenAt X i)) := by omega
    rw [e1, e2]; exact this
  · rw [h1, h1']; exact close.refl _ _

/-! ### Decomposing the related run list -/

theorem runAt_eq_getElem {R : RL} {i : Nat} (h : i < R.length) : runAt R i = R[i] := by
  simp [runAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getElem_eq_of_runAt {R : RL} {i : Nat} (h : i < R.length) {c : Cell} (hc : cellAt R i = c) :
    R[i] = (c, lenAt R i) := by
  rw [← runAt_eq_getElem h]; exact Prod.ext hc rfl

theorem decomp_rel {R' A J C : RL} {n m : Nat} (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) R')
    (hJ : J = [] ∨ J = [(F, 1)]) :
    ∃ A' n' C', R' = A' ++ (T, n') :: (J ++ (E, m) :: C') ∧ A'.length = A.length ∧ C'.length = C.length := by
  have hl : R'.length = A.length + 2 + J.length + C.length := by rw [← hs.1, length_R]
  have cT : cellAt R' A.length = T := by rw [← (hs.2 _).1, cellAt_def, runAt_R_T]
  have cE : cellAt R' (A.length + 1 + J.length) = E := by rw [← (hs.2 _).1, cellAt_def, runAt_R_E]
  have lE : lenAt R' (A.length + 1 + J.length) = m := by
    rw [← (hs.2 _).2.2 (by rw [cellAt_def, runAt_R_E]), lenAt_def, runAt_R_E]
  have h0 : A.length < R'.length := by omega
  rw [← List.take_append_drop A.length R', List.drop_eq_getElem_cons h0, getElem_eq_of_runAt h0 cT]
  rcases hJ with rfl | rfl
  · have h1 : A.length + 1 < R'.length := by simp at hl; omega
    simp only [List.length_nil, Nat.add_zero] at cE lE
    rw [List.drop_eq_getElem_cons h1, getElem_eq_of_runAt h1 cE, lE]
    refine ⟨R'.take A.length, lenAt R' A.length, R'.drop (A.length + 1 + 1), rfl, by simp; omega, by simp at hl ⊢; omega⟩
  · have h1 : A.length + 1 < R'.length := by simp at hl; omega
    have h2 : A.length + 1 + 1 < R'.length := by simp at hl; omega
    have cF : cellAt R' (A.length + 1) = F := by
      rw [← (hs.2 _).1, cellAt_def, show A.length + 1 = A.length + 1 + 0 by rfl, runAt_R_J (by simp)]; rfl
    have lF : lenAt R' (A.length + 1) = 1 := by
      have := (hs.2 (A.length + 1)).2.1
      rw [lenAt_def, show A.length + 1 = A.length + 1 + 0 by rfl, runAt_R_J (by simp)] at this
      simp [runAt] at this; omega
    simp only [List.length_singleton] at cE lE
    rw [List.drop_eq_getElem_cons h1, getElem_eq_of_runAt h1 cF, lF, List.drop_eq_getElem_cons h2,
      getElem_eq_of_runAt h2 cE, lE]
    refine ⟨R'.take A.length, lenAt R' A.length, R'.drop (A.length + 1 + 1 + 1), rfl, by simp; omega,
      by simp at hl ⊢; omega⟩

/-! ### The flags of the move agree -/

theorem endsE_iff {A : RL} : endsE A = true ↔ 0 < A.length ∧ cellAt A (A.length - 1) = E := by
  constructor
  · intro h
    obtain ⟨A₀, p, rfl⟩ := endsE_spec h
    refine ⟨by simp, ?_⟩
    rw [cellAt_def, List.length_append, List.length_singleton, Nat.add_sub_cancel, runAt_append_ge (Nat.le_refl _),
      Nat.sub_self, runAt_cons_zero]
  · rintro ⟨h0, hE⟩
    obtain ⟨A₀, x, rfl⟩ : ∃ A₀ x, A = A₀ ++ [x] := ⟨A.dropLast, A.getLast (by intro h; simp [h] at h0),
      (List.dropLast_concat_getLast _).symm⟩
    rw [cellAt_def, List.length_append, List.length_singleton, Nat.add_sub_cancel, runAt_append_ge (Nat.le_refl _),
      Nat.sub_self, runAt_cons_zero] at hE
    obtain ⟨c, p⟩ := x
    simp only at hE; subst hE
    simp [endsE]

theorem startsT_iff {C : RL} : startsT C = true ↔ 0 < C.length ∧ cellAt C 0 = T := by
  match C with
  | [] => simp [startsT]
  | (c, q) :: C => cases c <;> simp [startsT, cellAt, runAt_cons_zero]

section Pair
variable {A A' : RL} {n n' : Nat} {J : RL} {m : Nat} {C C' : RL}

theorem cells_A (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) {i : Nat} (hi : i < A.length) :
    cellAt A i = cellAt A' i ∧ (lenAt A i = lenAt A' i ∨ (2 ≤ lenAt A i ∧ 2 ≤ lenAt A' i)) ∧
      (cellAt A i = E → lenAt A i = lenAt A' i) := by
  have := hs.2 i
  rw [cellAt_def, cellAt_def, lenAt_def, lenAt_def, runAt_R_A hi, runAt_R_A (by omega)] at this
  exact this

theorem cells_C (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) (c : Nat) :
    cellAt C c = cellAt C' c ∧ (lenAt C c = lenAt C' c ∨ (2 ≤ lenAt C c ∧ 2 ≤ lenAt C' c)) ∧
      (cellAt C c = E → lenAt C c = lenAt C' c) := by
  have := hs.2 (A.length + 2 + J.length + c)
  rw [cellAt_def, cellAt_def, lenAt_def, lenAt_def, runAt_R_C (by omega), runAt_R_C (by omega)] at this
  rw [hA, show A.length + 2 + J.length + c - (A.length + 2 + J.length) = c by omega] at this
  exact this

theorem n_rel (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) : n = n' ∨ (2 ≤ n ∧ 2 ≤ n') := by
  have := (hs.2 A.length).2.1
  rw [lenAt_def, lenAt_def, runAt_R_T, ← hA, runAt_R_T] at this
  exact this

theorem flags_eq (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) (hC : C'.length = C.length) :
    endsE A' = endsE A ∧ startsT C' = startsT C ∧ decide (n' = 1) = decide (n = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Bool.eq_iff_iff.2
    rw [endsE_iff, endsE_iff, hA]
    constructor
    · rintro ⟨h0, h⟩; exact ⟨h0, by rw [(cells_A hs hA (by omega)).1]; exact h⟩
    · rintro ⟨h0, h⟩; exact ⟨h0, by rw [← (cells_A hs hA (by omega)).1]; exact h⟩
  · apply Bool.eq_iff_iff.2
    rw [startsT_iff, startsT_iff, hC, (cells_C hs hA 0).1]
  · have := n_rel hs hA
    by_cases h : n = 1 <;> by_cases h' : n' = 1 <;> simp [h, h'] <;> omega

theorem Mx_eq (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) (hC : C'.length = C.length) :
    Mx A' n' J m C' = mT n' ++ midR (decide (n = 1)) (endsE A) J m (startsT C) := by
  obtain ⟨e1, e2, e3⟩ := flags_eq hs hA hC
  simp only [Mx, e1, e2, e3]

theorem length_mT_eq (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) : (mT n').length = (mT n).length := by
  have := n_rel hs hA
  by_cases h : n = 1 <;> by_cases h' : n' = 1 <;> simp [mT, h, h'] <;> omega

theorem length_Mx_eq (hs : Skel (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) (hC : C'.length = C.length) :
    (Mx A' n' J m C').length = (Mx A n J m C).length := by
  rw [Mx_eq hs hA hC, Mx, List.length_append, List.length_append, length_mT_eq hs hA]

/-- The moving toad run is an entry when it has length at least 2. -/
theorem isEnt_T (hJ : J = [] ∨ J = [(F, 1)]) (h2 : 2 ≤ n) : isEntB (A ++ (T, n) :: (J ++ (E, m) :: C)) A.length = true := by
  rw [isEntB_iff]
  refine ⟨by rw [length_R]; omega, by rw [cellAt_def, runAt_R_T]; simp, by rw [lenAt_def, runAt_R_T]; exact h2,
    not_dead_T hJ⟩

theorem n_close {j : Nat} (h : Rel (j + 2) (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) (hJ : J = [] ∨ J = [(F, 1)]) (h2 : 2 ≤ n) : n = n' ∨ (6 ≤ n ∧ 6 ≤ n') := by
  have := h.2.1 _ (isEnt_T hJ h2)
  rw [lenAt_def, lenAt_def, runAt_R_T, ← hA, runAt_R_T] at this
  unfold close at this; simp only at this; omega

theorem origin {j : Nat} (h : Rel (j + 2) (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) (hC : C'.length = C.length) (hJ : J = [] ∨ J = [(F, 1)])
    (hn : 1 ≤ n) (hn' : 1 ≤ n') (hpos : PosR (A ++ (T, n) :: (J ++ (E, m) :: C))) {i : Nat}
    (hi : isEntB (moveX A n J m C) i = true) :
    Orig (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')) (moveX A n J m C) (moveX A' n' J m C') i := by
  have hs := h.1
  obtain ⟨e1, e2, e3⟩ := flags_eq hs hA hC
  have hLm := length_Mx_eq hs hA hC
  have hX := length_moveX (A := A) (n := n) (J := J) (m := m) (C := C)
  rw [isEntB_iff] at hi
  obtain ⟨hil, hiE, hi2, hid⟩ := hi
  rcases Nat.lt_or_ge i A.length with ha | ha
  · -- the prefix
    obtain ⟨hc, hl⟩ := runAt_X_A (n := n) (J := J) (m := m) (C := C) ha
    obtain ⟨hc', hl'⟩ := runAt_X_A (A := A') (n := n') (J := J) (m := m) (C := C') (i := i) (by omega)
    obtain ⟨cA, -, -⟩ := cells_A hs hA ha
    have hb : ¬ ((decide (n = 1) && endsE A) = true ∧ i + 1 = A.length) := by
      rintro ⟨hf, hia⟩
      have := (endsE_iff.1 (f1_spec hf)).2
      rw [show A.length - 1 = i by omega, ← hc] at this
      exact hiE this
    have hb' : ¬ ((decide (n' = 1) && endsE A') = true ∧ i + 1 = A'.length) := by rw [e1, e3, hA]; exact hb
    rw [if_neg hb] at hl; rw [if_neg hb'] at hl'
    left
    refine ⟨i, (0 : Int), ?_, by omega, by omega, ?_, ?_⟩
    · rw [isEntB_iff]
      refine ⟨by rw [length_R]; omega, ?_, ?_, fun hd => hid ((dead_transfer hJ hd).1 ha)⟩
      · rw [cellAt_def, runAt_R_A ha, ← cellAt_def, ← hc]; exact hiE
      · rw [lenAt_def, runAt_R_A ha, ← lenAt_def]; omega
    · rw [hl, lenAt_def (A ++ _), runAt_R_A ha]; simp [lenAt]
    · rw [hl', lenAt_def (A' ++ _), runAt_R_A (by omega)]; simp [lenAt]
  rcases Nat.lt_or_ge i (A.length + (Mx A n J m C).length) with hm' | hm'
  · -- the middle: only the toad run `(T, n - 1)`
    have hr := runAt_X_M (A := A) (n := n) (J := J) (m := m) (C := C) ha hm'
    have hE' : cellAt (Mx A n J m C) (i - A.length) ≠ E := by rw [cellAt_def, ← hr]; exact hiE
    have h2' : 2 ≤ lenAt (Mx A n J m C) (i - A.length) := by rw [lenAt_def, ← hr]; exact hi2
    obtain ⟨hk, hn2, hr0⟩ := Mx_long hJ hE' h2'
    have hia : i = A.length := by omega
    subst hia
    have hn2' : 2 ≤ n' := by rcases n_rel hs hA with h' | h' <;> omega
    have hr' := runAt_X_M (A := A') (n := n') (J := J) (m := m) (C := C') (i := A.length) (by omega) (by omega)
    have hr0' : runAt (Mx A' n' J m C') 0 = (T, n' - 1) := by
      rw [Mx_eq hs hA hC]; simp [mT, show n' ≠ 1 by omega, runAt_cons_zero]
    left
    refine ⟨A.length, (-1 : Int), isEnt_T hJ hn2, by omega, by omega, ?_, ?_⟩
    · rw [lenAt_def (moveX A n J m C), hr, Nat.sub_self, hr0, lenAt_def (A ++ _), runAt_R_T]; simp; omega
    · rw [lenAt_def (moveX A' n' J m C'), hr', hA, Nat.sub_self, hr0', show A.length = A'.length from hA.symm,
        lenAt_def (A' ++ _), runAt_R_T]; simp; omega
  · -- the suffix
    obtain ⟨hc, hl⟩ := runAt_X_C (A := A) (n := n) (J := J) (m := m) (C := C) hm'
    obtain ⟨hc', hl'⟩ := runAt_X_C (A := A') (n := n') (J := J) (m := m) (C := C') (by rw [hA, hLm]; exact hm')
    rw [hA, hLm] at hc' hl'
    rw [e2] at hl'
    generalize hcdef : i - (A.length + (Mx A n J m C).length) = c at hc hl hc' hl'
    have hcl : c < C.length := by omega
    obtain ⟨cC, lC, -⟩ := cells_C hs hA c
    have hRc : runAt (A ++ (T, n) :: (J ++ (E, m) :: C)) (A.length + 2 + J.length + c) = runAt C c := by
      rw [runAt_R_C (by omega)]; congr 1; omega
    have hRc' : runAt (A' ++ (T, n') :: (J ++ (E, m) :: C')) (A.length + 2 + J.length + c) = runAt C' c := by
      rw [runAt_R_C (by omega), hA]; congr 1; omega
    have hent : 2 ≤ lenAt C c → isEntB (A ++ (T, n) :: (J ++ (E, m) :: C)) (A.length + 2 + J.length + c) = true := by
      intro h2c
      rw [isEntB_iff]
      refine ⟨by rw [length_R]; omega, by rw [cellAt_def, hRc, ← cellAt_def, ← hc]; exact hiE,
        by rw [lenAt_def, hRc]; exact h2c, fun hd => hid ?_⟩
      have := (dead_transfer hJ hd).2 (by omega)
      rwa [show A.length + 2 + J.length + c - (A.length + 2 + J.length) + (A.length + (Mx A n J m C).length) = i by
        omega] at this
    by_cases hb : (decide (m = 1) && startsT C) = true ∧ i = A.length + (Mx A n J m C).length
    · rw [if_pos hb] at hl hl'
      have hc0 : c = 0 := by omega
      obtain ⟨q, C₀, hCq⟩ := startsT_spec (f2_spec hb.1)
      have hq : 1 ≤ lenAt C 0 := by
        have := hpos (T, q) (by simp [hCq])
        rw [hCq]; exact this
      rcases Nat.lt_or_ge (lenAt C 0) 2 with hq1 | hq2
      · right
        have : lenAt C' 0 = lenAt C 0 := by rw [hc0] at lC; omega
        rw [hc0] at hl hl'
        exact ⟨by rw [hl, hl', this], by omega⟩
      · left
        refine ⟨A.length + 2 + J.length + c, (1 : Int), hent (by rw [hc0]; exact hq2), by omega, by omega, ?_, ?_⟩
        · rw [hl, lenAt_def (A ++ _), hRc]; simp [lenAt]
        · rw [hl', lenAt_def (A' ++ _), hRc']; simp [lenAt]
    · rw [if_neg hb] at hl hl'
      left
      refine ⟨A.length + 2 + J.length + c, (0 : Int), hent (by omega), by omega, by omega, ?_, ?_⟩
      · rw [hl, lenAt_def (A ++ _), hRc]; simp [lenAt]
      · rw [hl', lenAt_def (A' ++ _), hRc']; simp [lenAt]

theorem skel_moveX {j : Nat} (h : Rel (j + 2) (A ++ (T, n) :: (J ++ (E, m) :: C)) (A' ++ (T, n') :: (J ++ (E, m) :: C')))
    (hA : A'.length = A.length) (hC : C'.length = C.length) (hJ : J = [] ∨ J = [(F, 1)]) (hn : 1 ≤ n) :
    Skel (moveX A n J m C) (moveX A' n' J m C') := by
  have hs := h.1
  obtain ⟨e1, e2, e3⟩ := flags_eq hs hA hC
  have hLm := length_Mx_eq hs hA hC
  refine ⟨by rw [length_moveX, length_moveX, hA, hLm, hC], fun i => ?_⟩
  rcases Nat.lt_or_ge i A.length with ha | ha
  · obtain ⟨hc, hl⟩ := runAt_X_A (n := n) (J := J) (m := m) (C := C) ha
    obtain ⟨hc', hl'⟩ := runAt_X_A (A := A') (n := n') (J := J) (m := m) (C := C') (i := i) (by omega)
    obtain ⟨cA, lA, eA⟩ := cells_A hs hA ha
    rw [e1, e3, hA] at hl'
    refine ⟨by rw [hc, hc', cA], ?_, fun hE => ?_⟩
    · rw [hl, hl']; omega
    · rw [hc] at hE; rw [hl, hl', eA hE]
  rcases Nat.lt_or_ge i (A.length + (Mx A n J m C).length) with hm' | hm'
  · have hr := runAt_X_M (A := A) (n := n) (J := J) (m := m) (C := C) ha hm'
    have hr' := runAt_X_M (A := A') (n := n') (J := J) (m := m) (C := C') (i := i) (by omega) (by omega)
    rw [hA, Mx_eq hs hA hC] at hr'
    by_cases hn1 : n = 1
    · have hn1' : n' = 1 := by have := e3; simp [hn1] at this; exact this
      have hM : Mx A n J m C = mT n' ++ midR (decide (n = 1)) (endsE A) J m (startsT C) := by
        simp [Mx, mT, hn1, hn1']
      rw [← hM] at hr'
      rw [cellAt_def, cellAt_def, lenAt_def, lenAt_def, hr, hr']
      exact ⟨rfl, Or.inl rfl, fun _ => rfl⟩
    · have hn2 : 2 ≤ n := by omega
      have hn1' : n' ≠ 1 := by intro h'; have := e3; simp [hn1, h'] at this
      have hM : Mx A n J m C = (T, n - 1) :: midR (decide (n = 1)) (endsE A) J m (startsT C) := by
        simp [Mx, mT, hn1]
      have hM' : mT n' ++ midR (decide (n = 1)) (endsE A) J m (startsT C) =
          (T, n' - 1) :: midR (decide (n = 1)) (endsE A) J m (startsT C) := by simp [mT, hn1']
      rw [hM] at hr; rw [hM'] at hr'
      rw [cellAt_def, cellAt_def, lenAt_def, lenAt_def, hr, hr']
      cases hk : i - A.length with
      | zero =>
        rw [runAt_cons_zero, runAt_cons_zero]
        refine ⟨rfl, ?_, fun h' => absurd h' (by simp)⟩
        rcases n_close h hA hJ hn2 with e | e <;> omega
      | succ k => rw [runAt_cons_succ, runAt_cons_succ]; exact ⟨rfl, Or.inl rfl, fun _ => rfl⟩
  · obtain ⟨hc, hl⟩ := runAt_X_C (A := A) (n := n) (J := J) (m := m) (C := C) hm'
    obtain ⟨hc', hl'⟩ := runAt_X_C (A := A') (n := n') (J := J) (m := m) (C := C') (i := i) (by rw [hA, hLm]; exact hm')
    rw [hA, hLm] at hc' hl'
    rw [e2] at hl'
    obtain ⟨cC, lC, eC⟩ := cells_C hs hA (i - (A.length + (Mx A n J m C).length))
    refine ⟨by rw [hc, hc', cC], ?_, fun hE => ?_⟩
    · rw [hl, hl']; omega
    · rw [hc] at hE; rw [hl, hl', eC hE]

end Pair

/-- **The margin lemma for Left moves.** -/
theorem margin_left (j : Nat) (R R' X : RL) (h : Rel (j + 2) R R') (hR : maxB R = true) (hR' : maxB R' = true)
    (hX : X ∈ lmovesR R) : ∃ X' ∈ lmovesR R', Rel j X X' := by
  obtain ⟨A, n, J, m, C, rfl, hJ, hn, hm, rfl⟩ := lmovesR_struct hR hX
  obtain ⟨A', n', C', rfl, hA, hC⟩ := decomp_rel h.1 hJ
  have hn' : 1 ≤ n' := posR_of_maxB hR' (T, n') (by simp)
  have hpos := posR_of_maxB hR
  refine ⟨moveX A' n' J m C', moveX_mem hJ hn', skel_moveX h hA hC hJ hn, fun i hi => ?_, fun i k hi hk => ?_⟩
  · exact pc_anchor_of_orig h (origin h hA hC hJ hn hn' hpos hi)
  · exact pc_pair_of_orig h (origin h hA hC hJ hn hn' hpos hi) (origin h hA hC hJ hn hn' hpos hk)
      (isEntB_iff.1 hi).2.2.1 (isEntB_iff.1 hk).2.2.1

end Col
end Cgt
