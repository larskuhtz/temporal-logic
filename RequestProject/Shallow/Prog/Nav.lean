module

public import RequestProject.Shallow.Prog.Scan
public import RequestProject.Shallow.QSpec

/-!
# Navigation routines in the loop language

`tendP`, `fendP` (bracket scans), `isLeafP`, `cntP` (counting tokens of a given code),
`ctwP`/`nxtP` (one step of the path towards a target position).
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {x : Word} {C : ℕ}

/-- Variables written by a program are among `W`. -/
lemma frame_of_sub {P : Pr V} {W : List (Fin V)} (h : ∀ z ∈ P.wr, z ∈ W) (ρ : Fin V → ℕ)
    (z : Fin V) (hz : z ∉ W) : (P.run x C ρ).1 z = ρ z :=
  Pr.run_frame _ _ _ (fun h' => hz (h z h'))

/-! ## Code predicates -/

/-- `k = 3` -/
def cUT : CodePred upT where
  e g := .bin .eq g (.c 3)
  spec x C ρ g hC := by
    simp only [eval_bin, ap_eq, eval_c, upT, beq_iff_eq]
    rw [min_eq_left (by omega)]

/-- `k = 4` -/
def cDT : CodePred downT where
  e g := .bin .eq g (.c 4)
  spec x C ρ g hC := by
    simp only [eval_bin, ap_eq, eval_c, downT, beq_iff_eq]
    rw [min_eq_left (by omega)]

/-- `k ∈ {8, 10}` -/
def cUF : CodePred upF where
  e g := .bin .lt (.c 0) (.bin .add (.bin .eq g (.c 8)) (.bin .eq g (.c 10)))
  spec x C ρ g hC := by
    simp only [eval_bin, ap_eq, ap_lt, ap_add, eval_c, upF, Bool.or_eq_true, beq_iff_eq]
    rw [min_eq_left (show 8 ≤ C by omega), min_eq_left (show 10 ≤ C by omega),
      min_eq_left (show 0 ≤ C by omega)]
    split_ifs <;> simp_all <;> omega

/-- `k ∈ {2, 6}` -/
def cDF : CodePred downF where
  e g := .bin .lt (.c 0) (.bin .add (.bin .eq g (.c 2)) (.bin .eq g (.c 6)))
  spec x C ρ g hC := by
    simp only [eval_bin, ap_eq, ap_lt, ap_add, eval_c, downF, Bool.or_eq_true, beq_iff_eq]
    rw [min_eq_left (show 2 ≤ C by omega), min_eq_left (show 6 ≤ C by omega),
      min_eq_left (show 0 ≤ C by omega)]
    split_ifs <;> simp_all <;> omega

lemma udT : ∀ k, ¬ (upT k = true ∧ downT k = true) := by
  intro k; simp only [upT, downT, beq_iff_eq]; omega

lemma udF : ∀ k, ¬ (upF k = true ∧ downF k = true) := by
  intro k; simp only [upF, downF, Bool.or_eq_true, beq_iff_eq]; omega

/-- The scan variables. -/
abbrev scanW : List (Fin V) := [sR, sP, sC, sD, sI]

/-- `sR := tend e` -/
def tendP (e : Ex V) : Pr V := scanP cUT cDT e 0
/-- `sR := fend e` -/
def fendP (e : Ex V) : Pr V := scanP cUF cDF e 1

lemma tendP_wr (e : Ex V) : ∀ z ∈ (tendP e).wr, z ∈ scanW := by
  intro z hz; rcases scanP_wr _ _ _ _ z hz with h | h | h | h | h <;> simp [h]

lemma fendP_wr (e : Ex V) : ∀ z ∈ (fendP e).wr, z ∈ scanW := by
  intro z hz; rcases scanP_wr _ _ _ _ z hz with h | h | h | h | h <;> simp [h]

section

variable {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

theorem run_tendP (hE : Env ts q a C ρ) (e : Ex V)
    (he : e.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1) :
    ((tendP e).run (pack (encodeToks ts) q a) C ρ).1 sR =
      tend ts (e.eval (pack (encodeToks ts) q a) C ρ) ∧
    ((tendP e).run (pack (encodeToks ts) q a) C ρ).2 = [] := by
  obtain ⟨h1, h2, -⟩ := run_scanP cUT cDT udT e 0 (by omega) hE he
  exact ⟨h1, h2⟩

theorem run_fendP (hE : Env ts q a C ρ) (e : Ex V)
    (he : e.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1) :
    ((fendP e).run (pack (encodeToks ts) q a) C ρ).1 sR =
      fend ts (e.eval (pack (encodeToks ts) q a) C ρ) ∧
    ((fendP e).run (pack (encodeToks ts) q a) C ρ).2 = [] := by
  obtain ⟨h1, h2, -⟩ := run_scanP cUF cDF udF e 1 (by omega) hE he
  exact ⟨h1, h2⟩

end


/-! ## Leaves -/

/-- result of `isLeafP` -/
abbrev vLf : Fin V := 15

/-- `vLf := [isLeaf e]` -/
def isLeafP (e : Ex V) : Pr V :=
  .seq (tendP (.bin .add e (.c 1))) (.set vLf (.bin .eq (tokE (.v sR)) (.c 4)))

lemma isLeafP_wr (e : Ex V) : ∀ z ∈ (isLeafP e).wr, z ∈ vLf :: scanW := by
  intro z hz
  simp only [isLeafP, Pr.wr, List.mem_append, List.mem_singleton] at hz
  rcases hz with h | h
  · exact List.mem_cons_of_mem _ (tendP_wr _ z h)
  · simp [h]

theorem run_isLeafP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (e : Ex V)
    (he : e.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length) :
    ((isLeafP e).run (pack (encodeToks ts) q a) C ρ).1 vLf =
      (if isLeaf ts (e.eval (pack (encodeToks ts) q a) C ρ) then 1 else 0) ∧
    ((isLeafP e).run (pack (encodeToks ts) q a) C ρ).2 = [] := by
  have hC := hE.len_le
  set x := pack (encodeToks ts) q a
  have hev : (Ex.bin .add e (.c 1) : Ex V).eval x C ρ = e.eval x C ρ + 1 := by
    simp only [eval_bin, ap_add, eval_c]; rw [min_eq_left (by omega), min_eq_left (by omega)]
  obtain ⟨h1, h2⟩ := run_tendP hE (.bin .add e (.c 1)) (by rw [hev]; omega)
  set ρ1 := ((tendP (.bin .add e (.c 1))).run x C ρ).1
  have hE1 : Env ts q a C ρ1 := hE.congr (frame_of_sub (tendP_wr _) _ _ (by decide))
    (frame_of_sub (tendP_wr _) _ _ (by decide))
  have hle : tend ts (e.eval x C ρ + 1) ≤ ts.length + 1 := by
    have := scan_le (ts := ts) upT downT (e.eval x C ρ + 1) 0
    simp only [tend]; omega
  refine ⟨?_, ?_⟩
  · simp only [isLeafP, run_seq, run_set, Function.update_self]
    rw [hev] at h1
    simp only [eval_bin, ap_eq, eval_c]
    rw [eval_tokE ts q a C ρ1 _ hE1.hq hE1.hC hE1.hN (by simp only [eval_v]; omega)]
    simp only [eval_v, isLeaf, beq_iff_eq]
    simp only [h1, min_eq_left (show 4 ≤ C by omega)]
  · simp only [isLeafP, run_seq, run_set, List.append_nil]; exact h2

/-! ## Counting -/

/-- result of `cntP` -/
abbrev vCr : Fin V := 16
/-- loop counter of `cntP` -/
abbrev vCi : Fin V := 17
/-- start position of `cntP` -/
abbrev vCa : Fin V := 18

/-- `vCr := cnt ts k a n` -/
def cntP (k : ℕ) (a n : Ex V) : Pr V :=
  .seq (.set vCa a) (.seq (.set vCr (.c 0)) (.loop vCi n
    (.ite (.bin .eq (tokE (.bin .add (.v vCa) (.v vCi))) (.c k))
      (.set vCr (.bin .add (.v vCr) (.c 1))) .skip)))

lemma cntP_wr (k : ℕ) (a n : Ex V) : ∀ z ∈ (cntP k a n).wr, z ∈ [vCa, vCr, vCi] := by
  intro z hz; simp only [cntP, Pr.wr] at hz; simp at hz ⊢; omega

lemma cnt_succ (ts : List Tok) (c a n : ℕ) :
    cnt ts c a (n + 1) = cnt ts c a n + (if tc ts (a + n) = c then 1 else 0) := by
  rw [cnt_add]; simp [cnt, List.range_one]
  split_ifs <;> simp_all

lemma cnt_le (ts : List Tok) (c a n : ℕ) : cnt ts c a n ≤ n := by
  unfold cnt; exact (List.length_filter_le _ _).trans (by simp)

theorem run_cntP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (k : ℕ) (hk : k ≤ 29) (ea en : Ex V)
    (ha : ea.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1)
    (hn : en.eval (pack (encodeToks ts) q a) C (Function.update (Function.update ρ vCa
      (ea.eval (pack (encodeToks ts) q a) C ρ)) vCr 0) ≤ ts.length + 1) :
    ((cntP k ea en).run (pack (encodeToks ts) q a) C ρ).1 vCr =
      cnt ts k (ea.eval (pack (encodeToks ts) q a) C ρ) (en.eval (pack (encodeToks ts) q a) C
        (Function.update (Function.update ρ vCa (ea.eval (pack (encodeToks ts) q a) C ρ)) vCr 0)) ∧
    ((cntP k ea en).run (pack (encodeToks ts) q a) C ρ).2 = [] := by
  have hC := hE.len_le
  set x := pack (encodeToks ts) q a
  set av := ea.eval x C ρ
  refine ⟨?_, Pr.run_silent _ (by simp [cntP, Pr.silent]) _⟩
  simp only [cntP, run_seq, run_set, eval_c]
  rw [min_eq_left (show 0 ≤ C by omega)]
  set ρ1 := Function.update (Function.update ρ vCa av) vCr 0
  set nv := en.eval x C ρ1
  have key := run_loop_inv (w := x) (C := C) vCi en
    (.ite (.bin .eq (tokE (.bin .add (.v vCa) (.v vCi))) (.c k))
      (.set vCr (.bin .add (.v vCr) (.c 1))) .skip) ρ1
    (fun i ρ' => ρ' vCr = cnt ts k av i ∧ ρ' vCa = av ∧ ρ' vN = ρ vN ∧ ρ' vL = ρ vL)
    ⟨by simp [ρ1, cnt], by simp (disch := decide) [ρ1, Function.update_of_ne],
      by simp (disch := decide) [ρ1, Function.update_of_ne],
      by simp (disch := decide) [ρ1, Function.update_of_ne]⟩
    (by
      intro i hi ρ' ⟨hr, ha', hN', hL'⟩
      set ρ'' := Function.update ρ' vCi i
      have e1 : ρ'' vCr = cnt ts k av i := by simp (disch := decide) [ρ'', Function.update_of_ne, hr]
      have e2 : ρ'' vCa = av := by simp (disch := decide) [ρ'', Function.update_of_ne, ha']
      have e3 : ρ'' vN = ρ vN := by simp (disch := decide) [ρ'', Function.update_of_ne, hN']
      have e4 : ρ'' vL = ρ vL := by simp (disch := decide) [ρ'', Function.update_of_ne, hL']
      have e5 : ρ'' vCi = i := by simp [ρ'']
      have hE'' : Env ts q a C ρ'' := hE.congr e3 e4
      have hi' : i < ts.length + 2 := by omega
      have hpos : (Ex.bin .add (.v vCa) (.v vCi) : Ex V).eval x C ρ'' = av + i := by
        simp only [eval_bin, ap_add, eval_v, e2, e5]; rw [min_eq_left (by omega)]
      have htok : (tokE (.bin .add (.v vCa) (.v vCi))).eval x C ρ'' = tc ts (av + i) := by
        rw [eval_tokE ts q a C ρ'' _ hE''.hq hE''.hC hE''.hN (by rw [hpos]; omega), hpos]
      have hcl := cnt_le ts k av i
      by_cases ht : tc ts (av + i) = k
      · rw [run_ite_pos (by simp only [eval_bin, ap_eq, htok, eval_c]; rw [min_eq_left (by omega)]; simp [ht])]
        simp only [run_set, Function.update_self, eval_bin, ap_add, eval_v, eval_c, e1]
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [cnt_succ, if_pos ht, min_eq_left (by omega), min_eq_left (by omega)]
        · simp (disch := decide) [Function.update_of_ne, e2]
        · simp (disch := decide) [Function.update_of_ne, e3]
        · simp (disch := decide) [Function.update_of_ne, e4]
      · rw [run_ite_neg (by simp only [eval_bin, ap_eq, htok, eval_c]; rw [min_eq_left (by omega)]; simp [ht])]
        simp only [run_skip]
        exact ⟨by rw [cnt_succ, if_neg ht, e1]; rfl, e2, e3, e4⟩)
  exact key.1


/-! ## Paths -/

/-- current child in `ctwP` (also the result of `nxtP`) -/
abbrev wC : Fin V := 19
/-- target in `ctwP` -/
abbrev wL : Fin V := 20
/-- done flag of `ctwP` -/
abbrev wD : Fin V := 21
/-- loop counter of `ctwP` -/
abbrev wI : Fin V := 22

/-- The body of `ctwP`. -/
def ctwBody : Pr V :=
  .ite (.v wD) .skip
    (.ite (.bin .lt (.v wC) (.v vL))
      (.seq (tendP (.v wC))
        (.ite (.bin .lt (.c 0) (.bin .mul (.bin .eq (.bin .lt (.v wL) (.v sR)) (.c 0))
            (.bin .eq (.bin .eq (tokE (.v sR)) (.c 4)) (.c 0))))
          (.set wC (.v sR)) (.set wD (.c 1))))
      (.set wD (.c 1)))

/-- `wC := ctw c ℓ` -/
def ctwP (c ℓ : Ex V) : Pr V :=
  .seq (.set wC c) (.seq (.set wL ℓ) (.seq (.set wD (.c 0))
    (.loop wI (.bin .add (.v vL) (.c 2)) ctwBody)))

lemma ctwP_wr (c ℓ : Ex V) : ∀ z ∈ (ctwP c ℓ).wr, z ∈ [wC, wL, wD, wI, sR, sP, sC, sD, sI] := by
  intro z hz
  simp only [ctwP, ctwBody, Pr.wr, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with h | h | h | h | h | ((h | h | h) | h) <;>
    first | exact h.elim | (subst h; decide) | (have := tendP_wr _ z h; simp at this ⊢; omega)

theorem run_ctwP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (c ℓ : Ex V)
    (hc : c.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1) :
    ((ctwP c ℓ).run (pack (encodeToks ts) q a) C ρ).1 wC =
      ctw ts (c.eval (pack (encodeToks ts) q a) C ρ)
        (ℓ.eval (pack (encodeToks ts) q a) C
          (Function.update ρ wC (c.eval (pack (encodeToks ts) q a) C ρ))) ∧
    ((ctwP c ℓ).run (pack (encodeToks ts) q a) C ρ).2 = [] := by
  have hC := hE.len_le
  set x := pack (encodeToks ts) q a
  set cv := c.eval x C ρ
  set lv := ℓ.eval x C (Function.update ρ wC cv)
  refine ⟨?_, Pr.run_silent _ (by simp [ctwP, ctwBody, tendP, scanP, Pr.silent]) _⟩
  simp only [ctwP, run_seq, run_set, eval_c]
  rw [min_eq_left (show 0 ≤ C by omega)]
  set ρ1 := Function.update (Function.update (Function.update ρ wC cv) wL lv) wD 0
  set G := ctw ts cv lv
  have hb : (Ex.bin .add (.v vL) (.c 2) : Ex V).eval x C ρ1 = ts.length + 2 := by
    simp (disch := decide) [ρ1, Function.update_of_ne, hE.hL]; omega
  have key := run_loop_inv (w := x) (C := C) wI (.bin .add (.v vL) (.c 2)) ctwBody ρ1
    (fun i ρ' => ρ' vN = ρ vN ∧ ρ' vL = ρ vL ∧ ρ' wL = lv ∧
      ((ρ' wD = 1 ∧ ρ' wC = G) ∨ (ρ' wD = 0 ∧ ctw ts (ρ' wC) lv = G ∧ i ≤ ρ' wC ∧
        ρ' wC ≤ ts.length + 1)))
    ⟨by simp (disch := decide) [ρ1, Function.update_of_ne],
      by simp (disch := decide) [ρ1, Function.update_of_ne],
      by simp (disch := decide) [ρ1, Function.update_of_ne],
      Or.inr ⟨by simp [ρ1], by simp (disch := decide) [ρ1, Function.update_of_ne, G],
        Nat.zero_le _, by simp (disch := decide) [ρ1, Function.update_of_ne]; omega⟩⟩
    (by
      intro i hi ρ' ⟨hN', hL', hl', hI⟩
      set ρ'' := Function.update ρ' wI i
      have e3 : ρ'' vN = ρ vN := by simp (disch := decide) [ρ'', Function.update_of_ne, hN']
      have e4 : ρ'' vL = ρ vL := by simp (disch := decide) [ρ'', Function.update_of_ne, hL']
      have e5 : ρ'' wL = lv := by simp (disch := decide) [ρ'', Function.update_of_ne, hl']
      have e6 : ρ'' wD = ρ' wD := by simp (disch := decide) [ρ'', Function.update_of_ne]
      have e7 : ρ'' wC = ρ' wC := by simp (disch := decide) [ρ'', Function.update_of_ne]
      have hE'' : Env ts q a C ρ'' := hE.congr e3 e4
      rcases hI with ⟨hd, hr⟩ | ⟨hd, hg, hle, hub⟩
      · rw [ctwBody, run_ite_pos (by simp [e6, hd])]
        exact ⟨e3, e4, e5, Or.inl ⟨by simp [e6, hd], by simp [e7, hr]⟩⟩
      · rw [ctwBody, run_ite_neg (by simp [e6, hd])]
        by_cases hlt : ρ' wC < ts.length
        · rw [run_ite_pos (by simp [e7, e4, hE.hL, hlt])]
          obtain ⟨h1, h2⟩ := run_tendP hE'' (.v wC) (by simp [e7]; omega)
          set ρ3 := ((tendP (.v wC)).run x C ρ'').1
          have f : ∀ z ∉ scanW, ρ3 z = ρ'' z := fun z hz => frame_of_sub (tendP_wr _) _ z hz
          have hE3 : Env ts q a C ρ3 := hE''.congr (f _ (by decide)) (f _ (by decide))
          simp only [eval_v, e7] at h1
          have hgt : ρ' wC < tend ts (ρ' wC) := tend_gt ts (by omega)
          have hub' : tend ts (ρ' wC) ≤ ts.length + 1 := by
            have := scan_le (ts := ts) upT downT (ρ' wC) 0; simp only [tend]; omega
          have htok : (tokE (.v sR)).eval x C ρ3 = tc ts (tend ts (ρ' wC)) := by
            rw [eval_tokE ts q a C ρ3 _ hE3.hq hE3.hC hE3.hN (by simp only [eval_v]; omega)]
            simp [h1]
          have hl3 : ρ3 wL = lv := by rw [f _ (by decide), e5]
          have hcond : (tend ts (ρ' wC) ≤ lv ∧ tc ts (tend ts (ρ' wC)) ≠ 4) ↔
              (Ex.bin .lt (.c 0) (.bin .mul (.bin .eq (.bin .lt (.v wL) (.v sR)) (.c 0))
                (.bin .eq (.bin .eq (tokE (.v sR)) (.c 4)) (.c 0))) : Ex V).eval x C ρ3 ≠ 0 := by
            simp only [eval_bin, ap_lt, ap_mul, ap_eq, eval_c, eval_v, htok, hl3, h1]
            rw [min_eq_left (show 0 ≤ C by omega), min_eq_left (show 4 ≤ C by omega)]
            split_ifs <;> simp_all <;> omega
          have hctw := ctw_eq (ts := ts) (ρ' wC) lv
          rw [if_neg (by omega)] at hctw
          rw [run_seq]
          by_cases hc' : tend ts (ρ' wC) ≤ lv ∧ tc ts (tend ts (ρ' wC)) ≠ 4
          · rw [run_ite_pos (hcond.1 hc')]
            rw [if_pos hc'] at hctw
            simp only [run_set, eval_v, h1]
            refine ⟨?_, ?_, ?_, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
            · simp (disch := decide) [Function.update_of_ne, f _ (show vN ∉ scanW by decide), e3]
            · simp (disch := decide) [Function.update_of_ne, f _ (show vL ∉ scanW by decide), e4]
            · simp (disch := decide) [Function.update_of_ne, hl3]
            · simp (disch := decide) [Function.update_of_ne, f _ (show wD ∉ scanW by decide), e6, hd]
            · simp only [Function.update_self]; rw [← hctw, hg]
            · simp only [Function.update_self]; omega
            · simp only [Function.update_self]; omega
          · rw [run_ite_neg (by have := hcond.not.1 hc'; simpa using this)]
            rw [if_neg hc'] at hctw
            simp only [run_set, eval_c]
            refine ⟨?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
            · rw [Function.update_of_ne (by decide)]; exact (f _ (by decide)).trans e3
            · rw [Function.update_of_ne (by decide)]; exact (f _ (by decide)).trans e4
            · rw [Function.update_of_ne (by decide)]; exact hl3
            · simp only [Function.update_self]; omega
            · rw [Function.update_of_ne (by decide)]
              refine (f _ (by decide)).trans ?_
              rw [e7, ← hg, hctw]
        · rw [run_ite_neg (by simp [e7, e4, hE.hL]; omega)]
          have hctw := ctw_eq (ts := ts) (ρ' wC) lv
          rw [if_pos (by omega)] at hctw
          simp only [run_set, eval_c]
          refine ⟨?_, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
          · simp (disch := decide) [Function.update_of_ne, e3]
          · simp (disch := decide) [Function.update_of_ne, e4]
          · simp (disch := decide) [Function.update_of_ne, e5]
          · simp only [Function.update_self]; omega
          · rw [Function.update_of_ne (by decide), e7, ← hg, hctw])
  rw [hb] at key
  obtain ⟨-, -, -, key⟩ := key
  rcases key with ⟨-, h⟩ | ⟨-, -, h1, h2⟩
  · exact h
  · omega

end SQ

end PathChecking
