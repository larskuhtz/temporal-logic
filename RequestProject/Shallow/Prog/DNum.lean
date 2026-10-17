module

public import RequestProject.Shallow.Prog.Fuel
public import RequestProject.Shallow.ValidT

/-!
# Checking binary numbers in the loop language

`numOKP p` computes `numOK ts p` (a canonical binary number starts at `p`).
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- digits: loop counter -/
abbrev dI : Fin V := 15
/-- digits: position -/
abbrev dP : Fin V := 16
/-- digits: canonical so far -/
abbrev dOk : Fin V := 17
/-- digits: done flag -/
abbrev dD : Fin V := 18
/-- digits: result -/
abbrev dR : Fin V := 19

/-- One step of `digitsOK`. -/
def digBody : Pr V :=
  .ite (.bin .lt (.v dP) (.v vL))
    (.ite (.bin .eq (tokE (.v dP)) (.c 2)) (.seq (.set dR (.v dOk)) (.set dD (.c 1)))
      (.ite (.bin .eq (tokE (.v dP)) (.c 0))
        (.seq (.set dOk (.c 0)) (.set dP (.bin .add (.v dP) (.c 1))))
        (.ite (.bin .eq (tokE (.v dP)) (.c 1))
          (.seq (.set dOk (.c 1)) (.set dP (.bin .add (.v dP) (.c 1))))
          (.seq (.set dR (.c 0)) (.set dD (.c 1))))))
    (.seq (.set dR (.c 0)) (.set dD (.c 1)))

/-- `dR := numOK ts p`. -/
def numOKP (p : Ex V) : Pr V :=
  .seq (.set dP p) (.seq (.seq (.set dOk (.c 1)) (.set dD (.c 0)))
    (fuelP dI dD (.bin .add (.v vL) (.c 1)) digBody))

/-- Frame of `numOKP`. -/
abbrev numW : List (Fin V) := [dI, dP, dOk, dD, dR]

lemma sp_numOKP (hE : Env ts q a C ρ) (p : Ex V)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C (numOKP p) ρ numW []
      (fun r => r dR = if numOK ts (p.eval (pack (encodeToks ts) q a) C ρ) then 1 else 0) := by
  set x := pack (encodeToks ts) q a
  set p0 := p.eval x C ρ
  have hC := hE.len_le
  unfold numOKP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ dP p0)
    (by decide) rfl) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := numW) (a := dOk) (b := dD) (e1 := .c 1) (e2 := .c 0)
    (ρ := Function.update ρ dP p0) (x := x) (C := C)
    (Q := fun r => r dP = p0 ∧ r dOk = 1 ∧ r dD = 0
    ∧ r vN = ρ vN ∧ r vL = ρ vL) (by decide) (by decide)
    (by simp (disch := decide) [Function.update_of_ne]; omega)) (fun ρ2 f2 h2 => ?_) rfl
  have hE2 : Env ts q a C ρ2 := hE.congr h2.2.2.2.1 h2.2.2.2.2
  refine (sp_fuel dI dD _ digBody ρ2 numW
    (fun r => r dP ≤ ts.length ∧ r dOk ≤ 1 ∧
      digitsOK ts (r dP) (r dOk == 1) = numOK ts p0)
    (fun r => r dR = if numOK ts p0 then 1 else 0) (fun r => r dP) (by decide) (by decide)
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (fun r k => by simp (disch := decide) [Function.update_of_ne])
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (Or.inr ⟨h2.2.2.1, by rw [h2.1]; exact hp, by simp [h2.2.1], by
      rw [h2.1, h2.2.1]; rfl⟩) (fun r fr hd ⟨hpl, hok, hI⟩ => ?_) (fun r fr ⟨hpl, _, _⟩ => ?_)).mono
    (fun _ h => h) (fun _ _ h => h)
  · have hEr : Env ts q a C r := hE2.of_frame fr (by decide) (by decide)
    have hL : r vL = ts.length := hEr.hL
    unfold digBody
    rw [digitsOK_eq] at hI
    by_cases hlt : r dP < ts.length
    · refine sp_ite_pos (by simp [hL, hlt]) ?_
      have htok : (tokE (.v dP)).eval x C r = tc ts (r dP) := by
        rw [eval_tokE ts q a C r _ hE.hq hE.hC hEr.hN (by simp; omega)]; simp
      rw [if_neg (by omega)] at hI
      by_cases h2 : tc ts (r dP) = 2
      · refine sp_ite_pos (by simp [htok, h2, min_eq_left (show 2 ≤ C by omega)]) ?_
        refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
        rw [if_pos h2] at hI
        simp (disch := decide) [Function.update_of_ne]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hok with h | h <;> simp [h] at hI ⊢ <;>
          simp [← hI]
      · refine sp_ite_neg (by simp [htok, h2, min_eq_left (show 2 ≤ C by omega)]) ?_
        rw [if_neg h2] at hI
        by_cases h0 : tc ts (r dP) = 0
        · refine sp_ite_pos (by simp [htok, h0]) ?_
          refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ?_, ?_⟩)
          · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
          · simp (disch := first | decide | omega) [Function.update_of_ne]
            rw [if_pos h0] at hI
            exact ⟨by omega, hI⟩
          · simp (disch := first | decide | omega) [Function.update_of_ne]
        · refine sp_ite_neg (by simp [htok, h0]) ?_
          rw [if_neg h0] at hI
          by_cases h1 : tc ts (r dP) = 1
          · refine sp_ite_pos (by simp [htok, h1, min_eq_left (show 1 ≤ C by omega)]) ?_
            refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ?_, ?_⟩)
            · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
            · simp (disch := first | decide | omega) [Function.update_of_ne]
              rw [if_pos h1] at hI
              exact ⟨by omega, hI⟩
            · simp (disch := first | decide | omega) [Function.update_of_ne]
          · refine sp_ite_neg (by simp [htok, h1, min_eq_left (show 1 ≤ C by omega)]) ?_
            rw [if_neg h1] at hI
            refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
            simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
    · refine sp_ite_neg (by simp [hL, hlt]) ?_
      rw [if_pos (by omega)] at hI
      refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
      simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
  · have hEr : Env ts q a C r := hE2.of_frame fr (by decide) (by decide)
    simp only [eval_bin, ap_add, eval_v, eval_c, hE2.hL]
    rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega)]
    omega

/-! ## End of a number -/

/-- never -/
def cUN : CodePred upN where
  e _ := .c 0
  spec x C ρ g hC := by simp [upN]

/-- `k = 2` -/
def cDN : CodePred downN where
  e g := .bin .eq g (.c 2)
  spec x C ρ g hC := by
    simp only [eval_bin, ap_eq, eval_c, downN, beq_iff_eq]
    rw [min_eq_left (by omega)]

lemma udN : ∀ k, ¬ (upN k = true ∧ downN k = true) := by
  intro k; simp [upN]

/-- `sR := numEnd e` -/
def numEndP (e : Ex V) : Pr V := scanP cUN cDN e 1

lemma sp_numEndP (hE : Env ts q a C ρ) (e : Ex V) :
    Sp (pack (encodeToks ts) q a) C (numEndP e) ρ scanW []
      (fun ρ' => ρ' sR = numEnd ts (e.eval (pack (encodeToks ts) q a) C ρ)) := by
  obtain ⟨h1, h2, -⟩ := run_scanP cUN cDN udN e 1 (by omega) hE
  refine sp_of_silent h2 (fun z hz => ?_) h1
  rcases scanP_wr _ _ _ _ z hz with h | h | h | h | h <;> simp [h]

/-! ## Comparison of numbers -/

/-- cmp: loop counter -/
abbrev cI : Fin V := 20
/-- cmp: first position -/
abbrev cP : Fin V := 21
/-- cmp: second position -/
abbrev cQ : Fin V := 22
/-- cmp: accumulator -/
abbrev cA : Fin V := 23
/-- cmp: done flag -/
abbrev cD : Fin V := 24
/-- cmp: result -/
abbrev cR : Fin V := 25

/-- One step of `cmpScan`. -/
def cmpBody : Pr V :=
  .ite (.bin .lt (tokE (.v cP)) (.c 2))
    (.ite (.bin .lt (tokE (.v cQ)) (.c 2))
      (.seq (.set cA (iteE (.bin .eq (tokE (.v cP)) (tokE (.v cQ))) (.v cA) (tokE (.v cQ))))
        (.seq (.set cP (.bin .add (.v cP) (.c 1))) (.set cQ (.bin .add (.v cQ) (.c 1)))))
      (.seq (.set cA (iteE (.bin .eq (tokE (.v cP)) (.c 1)) (.c 0) (.v cA)))
        (.set cP (.bin .add (.v cP) (.c 1)))))
    (.ite (.bin .lt (tokE (.v cQ)) (.c 2))
      (.seq (.set cA (iteE (.bin .eq (tokE (.v cQ)) (.c 1)) (.c 1) (.v cA)))
        (.set cQ (.bin .add (.v cQ) (.c 1))))
      (.seq (.set cR (.v cA)) (.set cD (.c 1))))

/-- `cR := cmpScan ts p q acc`. -/
def cmpP (p q : Ex V) (acc : ℕ) : Pr V :=
  .seq (.seq (.set cP p) (.set cQ q)) (.seq (.seq (.set cA (.c acc)) (.set cD (.c 0)))
    (fuelP cI cD (.bin .add (.bin .add (.v vL) (.v vL)) (.c 1)) cmpBody))

/-- Frame of `cmpP`. -/
abbrev cmpW : List (Fin V) := [cI, cP, cQ, cA, cD, cR]

lemma dig_eq_of_lt {p : ℕ} (h : tc ts p < 2) : dig ts p = some (tc ts p == 1) := by
  unfold dig
  rcases (show tc ts p = 0 ∨ tc ts p = 1 by omega) with h | h <;> simp [h]

lemma dig_eq_none {p : ℕ} (h : ¬ tc ts p < 2) : dig ts p = none := by
  unfold dig
  rw [if_neg (by omega), if_neg (by omega)]

lemma tc_lt_of_dig {p : ℕ} (h : tc ts p < 2) : p < ts.length :=
  lt_of_tc_ne (by omega)

lemma sp_cmpP (hE : Env ts q a C ρ) (p e : Ex V) (acc : Bool)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length)
    (he : e.eval (pack (encodeToks ts) q a) C (Function.update ρ cP
      (p.eval (pack (encodeToks ts) q a) C ρ)) ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C (cmpP p e (if acc then 1 else 0)) ρ cmpW []
      (fun r => r cR = if cmpScan ts (p.eval (pack (encodeToks ts) q a) C ρ)
        (e.eval (pack (encodeToks ts) q a) C (Function.update ρ cP
          (p.eval (pack (encodeToks ts) q a) C ρ))) acc then 1 else 0) := by
  set x := pack (encodeToks ts) q a
  set p0 := p.eval x C ρ
  set q0 := e.eval x C (Function.update ρ cP p0)
  have hC := hE.len_le
  unfold cmpP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := cmpW) (a := cP) (b := cQ) (e1 := p)
    (e2 := e) (ρ := ρ) (x := x) (C := C)
    (Q := fun r => r cP = p0 ∧ r cQ = q0 ∧ r vN = ρ vN ∧ r vL = ρ vL) (by decide) (by decide)
    (by simp (disch := decide) [Function.update_of_ne, p0, q0])) (fun ρ1 f1 h1 => ?_) rfl
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := cmpW) (a := cA) (b := cD)
    (e1 := .c (if acc then 1 else 0)) (e2 := .c 0) (ρ := ρ1) (x := x) (C := C)
    (Q := fun r => r cP = p0 ∧ r cQ = q0 ∧ r cA = (if acc then 1 else 0) ∧ r cD = 0 ∧
      r vN = ρ vN ∧ r vL = ρ vL) (by decide) (by decide)
    (by simp (disch := first | decide | omega) [Function.update_of_ne, h1];
        split_ifs <;> omega)) (fun ρ2 f2 h2 => ?_) rfl
  obtain ⟨h2p, h2q, h2a, h2d, h2N, h2L⟩ := h2
  have hE2 : Env ts q a C ρ2 := hE.congr h2N h2L
  refine (sp_fuel cI cD _ cmpBody ρ2 cmpW
    (fun r => r cP ≤ ts.length ∧ r cQ ≤ ts.length ∧ r cA ≤ 1 ∧
      cmpScan ts (r cP) (r cQ) (r cA == 1) = cmpScan ts p0 q0 acc)
    (fun r => r cR = if cmpScan ts p0 q0 acc then 1 else 0) (fun r => r cP + r cQ)
    (by decide) (by decide)
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (fun r k => by simp (disch := decide) [Function.update_of_ne])
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (Or.inr ⟨h2d, by rw [h2p]; exact hp, by rw [h2q]; exact he, by rw [h2a]; split_ifs <;> omega,
      by rw [h2p, h2q, h2a]; cases acc <;> rfl⟩)
    (fun r fr hd ⟨hpl, hql, hal, hI⟩ => ?_) (fun r fr ⟨hpl, hql, _, _⟩ => ?_)).mono
    (fun _ h => h) (fun _ _ h => h)
  · have hEr : Env ts q a C r := hE2.of_frame fr (by decide) (by decide)
    have htp : (tokE (.v cP)).eval x C r = tc ts (r cP) := by
      rw [eval_tokE ts q a C r _ hE.hq hE.hC hEr.hN (by simp; omega)]; simp
    have htq : (tokE (.v cQ)).eval x C r = tc ts (r cQ) := by
      rw [eval_tokE ts q a C r _ hE.hq hE.hC hEr.hN (by simp; omega)]; simp
    have hle1 := tc_lt_29 (ts := ts) (p := r cP)
    unfold cmpBody
    by_cases hdp : tc ts (r cP) < 2
    · have hpL := tc_lt_of_dig hdp
      refine sp_ite_pos (by simp [htp, hdp, min_eq_left (show 2 ≤ C by omega)]) ?_
      by_cases hdq : tc ts (r cQ) < 2
      · have hqL := tc_lt_of_dig hdq
        refine sp_ite_pos (by simp [htq, hdq, min_eq_left (show 2 ≤ C by omega)]) ?_
        rw [cmpScan_ss (dig_eq_of_lt hdp) (dig_eq_of_lt hdq)] at hI
        refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r' => r' = Function.update r cA
          (if tc ts (r cP) = tc ts (r cQ) then r cA else tc ts (r cQ))) (by decide) ?_)
          (fun r1 _ h1 => ?_) rfl
        · have hev : (iteE (.bin .eq (tokE (.v cP)) (tokE (.v cQ))) (.v cA) (tokE (.v cQ))).eval
              x C r = if tc ts (r cP) = tc ts (r cQ) then r cA else tc ts (r cQ) := by
            rw [eval_iteE _ _ _ (by simp only [eval_bin, ap_eq, htp, htq]; split_ifs <;> simp) (by simp; omega)
              (by rw [htq]; omega)]
            simp [htp, htq]
          show Function.update r cA _ = _
          rw [hev]
        · subst h1
          refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
          · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
          · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
          · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
          · simp (disch := first | decide | omega) [Function.update_of_ne]
            split_ifs <;> omega
          · simp (disch := first | decide | omega) [Function.update_of_ne]
            rw [← hI]
            congr 1
            rcases (show tc ts (r cP) = 0 ∨ tc ts (r cP) = 1 by omega) with h | h <;>
              rcases (show tc ts (r cQ) = 0 ∨ tc ts (r cQ) = 1 by omega) with h' | h' <;>
              simp [h, h']
          · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
      · refine sp_ite_neg (by simp [htq, hdq, min_eq_left (show 2 ≤ C by omega)]) ?_
        rw [cmpScan_sn (dig_eq_of_lt hdp) (dig_eq_none hdq)] at hI
        have hev : (iteE (.bin .eq (tokE (.v cP)) (.c 1)) (.c 0) (.v cA)).eval x C r =
            if tc ts (r cP) = 1 then 0 else r cA := by
          rw [eval_iteE _ _ _ (by simp only [eval_bin, ap_eq, htp, eval_c]; split_ifs <;> simp)
            (by simp) (by simp; omega)]
          simp [htp, min_eq_left (show 1 ≤ C by omega)]
        refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
        · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
        · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
        · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
        · simp (disch := first | decide | omega) [Function.update_of_ne, hev]
          split_ifs <;> omega
        · simp (disch := first | decide | omega) [Function.update_of_ne, hev]
          rw [← hI]
          rcases (show tc ts (r cP) = 0 ∨ tc ts (r cP) = 1 by omega) with h | h <;> simp [h]
        · simp (disch := first | decide | omega) [Function.update_of_ne]
    · refine sp_ite_neg (by simp [htp, hdp, min_eq_left (show 2 ≤ C by omega)]) ?_
      by_cases hdq : tc ts (r cQ) < 2
      · have hqL := tc_lt_of_dig hdq
        refine sp_ite_pos (by simp [htq, hdq, min_eq_left (show 2 ≤ C by omega)]) ?_
        rw [cmpScan_ns (dig_eq_none hdp) (dig_eq_of_lt hdq)] at hI
        have hev : (iteE (.bin .eq (tokE (.v cQ)) (.c 1)) (.c 1) (.v cA)).eval x C r =
            if tc ts (r cQ) = 1 then 1 else r cA := by
          rw [eval_iteE _ _ _ (by simp only [eval_bin, ap_eq, htq, eval_c]; split_ifs <;> simp)
            (by simp) (by simp; omega)]
          simp [htq, min_eq_left (show 1 ≤ C by omega)]
        refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
        · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
        · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
        · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
        · simp (disch := first | decide | omega) [Function.update_of_ne, hev]
          split_ifs <;> omega
        · simp (disch := first | decide | omega) [Function.update_of_ne, hev]
          rw [← hI]
          rcases (show tc ts (r cQ) = 0 ∨ tc ts (r cQ) = 1 by omega) with h | h <;> simp [h]
        · simp (disch := first | decide | omega) [Function.update_of_ne]
      · refine sp_ite_neg (by simp [htq, hdq, min_eq_left (show 2 ≤ C by omega)]) ?_
        rw [cmpScan_nn (dig_eq_none hdp) (dig_eq_none hdq)] at hI
        refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
        simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hal with h | h <;> simp [h]
  · simp only [eval_bin, ap_add, eval_v, eval_c, hE2.hL]
    rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega), min_eq_left (by omega)]
    omega

end SQ

end PathChecking
