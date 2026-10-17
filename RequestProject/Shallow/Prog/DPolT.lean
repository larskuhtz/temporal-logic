module

public import RequestProject.Shallow.Prog.DLab
public import RequestProject.Shallow.Prog.Pro

/-!
# Checking trees with shallow branching in the loop language

`polTP p` computes `polT ts b p 1` (a list of trees with branching depth `< b`, closed by `)`,
starts at `p`), with the bound `b` in `vD`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- trees: loop counter -/
abbrev tI : Fin V := 39
/-- trees: position -/
abbrev tP : Fin V := 40
/-- trees: depth -/
abbrev tC : Fin V := 41
/-- trees: done flag -/
abbrev tD : Fin V := 42
/-- trees: result -/
abbrev tR : Fin V := 43

/-- Stop with result `b`. -/
def stopT (b : ℕ) : Pr V := .seq (.set tR (.c b)) (.set tD (.c 1))

/-- One step of `polT` at a node. -/
def polTLpP : Pr V :=
  .ite (.bin .eq (tokE (.bin .add (.v tP) (.c 1))) (.c 3))
    (.seq (labSufP (.bin .add (.v tP) (.c 2))) (.seq (tendP (.bin .add (.v tP) (.c 1)))
      (.ite (.v lR) (.seq (.set tP (.v sR)) (.set tC (.bin .add (.v tC) (.c 1)))) (stopT 0))))
    (stopT 0)

/-- One step of `polT`. -/
def polTBody : Pr V :=
  .ite (.bin .lt (.v tP) (.v vL))
    (.ite (.bin .eq (tokE (.v tP)) (.c 4))
      (.ite (.bin .eq (.v tC) (.c 1)) (stopT 1)
        (.ite (.bin .mul (.bin .eq (tokE (.bin .add (.v tP) (.c 1))) (.c 3))
            (.bin .lt (.bin .add (.v vD) (.c 1)) (.v tC)))
          (stopT 0)
          (.seq (.set tP (.bin .add (.v tP) (.c 1))) (.set tC (.bin .sub (.v tC) (.c 1))))))
      (.ite (.bin .eq (tokE (.v tP)) (.c 3)) polTLpP (stopT 0)))
    (stopT 0)

/-- `tR := polT ts vD p 1`. -/
def polTP (p : Ex V) : Pr V :=
  .seq (.seq (.set tP p) (.set tC (.c 1))) (.seq (.set tD (.c 0))
    (fuelP tI tD (.bin .add (.v vL) (.c 1)) polTBody))

/-- Frame of `polTP`. -/
abbrev polTW : List (Fin V) :=
  [tI, tP, tC, tD, tR, lI, lQ, lD, lR, lE, dI, dP, dOk, dD, dR, sR, sP, sC, sD, sI,
    cI, cP, cQ, cA, cD, cR]

lemma sp_polTP (hE : Env ts q a C ρ) (p : Ex V)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length)
    (hp1 : 1 ≤ p.eval (pack (encodeToks ts) q a) C ρ) (hb : ρ vD + 2 ≤ C) :
    Sp (pack (encodeToks ts) q a) C (polTP p) ρ polTW []
      (fun r => r tR =
        if polT ts (ρ vD) (p.eval (pack (encodeToks ts) q a) C ρ) 1 then 1 else 0) := by
  set x := pack (encodeToks ts) q a
  set p0 := p.eval x C ρ
  set b := ρ vD
  have hC := hE.len_le
  unfold polTP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := polTW) (a := tP) (b := tC) (e1 := p)
    (e2 := .c 1) (ρ := ρ) (x := x) (C := C)
    (Q := fun r => r tP = p0 ∧ r tC = 1 ∧ r vN = ρ vN ∧ r vL = ρ vL) (by decide) (by decide)
    (by simp (disch := first | decide | omega) [Function.update_of_ne, p0]))
    (fun ρ1 f1 h1 => ?_) rfl
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ1 tD 0)
    (by decide) (by simp)) (fun ρ2 f2 h2 => ?_) rfl
  subst h2
  obtain ⟨h1p, h1c, h1N, h1L⟩ := h1
  have hE2 : Env ts q a C (Function.update ρ1 tD 0) :=
    hE.congr (by simp (disch := decide) [Function.update_of_ne, h1N])
      (by simp (disch := decide) [Function.update_of_ne, h1L])
  refine (sp_fuel tI tD _ polTBody _ polTW
    (fun r => r tP ≤ ts.length ∧ 1 ≤ r tC ∧ r tC ≤ r tP ∧ polT ts b (r tP) (r tC) = polT ts b p0 1)
    (fun r => r tR = if polT ts b p0 1 then 1 else 0) (fun r => r tP)
    (by decide) (by decide)
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (fun r k => by simp (disch := decide) [Function.update_of_ne])
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (Or.inr ⟨by simp, by simp (disch := decide) [Function.update_of_ne, h1p, h1c, hp, hp1]⟩)
    (fun r fr hd ⟨hpl, hc1, hcp, hI⟩ => ?_) (fun r fr ⟨hpl, _⟩ => ?_)).mono
    (fun _ h => h) (fun _ _ h => h)
  · have hEr : Env ts q a C r := hE2.of_frame fr (by decide) (by decide)
    have hL : r vL = ts.length := hEr.hL
    have hb' : r vD = b := by
      rw [fr vD (by decide)]; simp (disch := decide) [Function.update_of_ne, f1 vD (by decide), b]
    rw [polT_eq] at hI
    unfold polTBody
    by_cases hlt : r tP < ts.length
    · refine sp_ite_pos (by simp [hL, hlt]) ?_
      rw [if_neg (by omega)] at hI
      have ht : (tokE (.v tP)).eval x C r = tc ts (r tP) := by
        rw [eval_tokE ts q a C r _ hE.hq hE.hC hEr.hN (by simp; omega)]; simp
      have ht1 : (tokE (.bin .add (.v tP) (.c 1))).eval x C r = tc ts (r tP + 1) := by
        rw [eval_tokE ts q a C r _ hE.hq hE.hC hEr.hN (by simp)]
        simp (disch := omega)
      by_cases h4 : tc ts (r tP) = 4
      · refine sp_ite_pos (by simp [ht, h4, min_eq_left (show 4 ≤ C by omega)]) ?_
        rw [if_pos h4] at hI
        by_cases hc : r tC = 1
        · refine sp_ite_pos (by simp [hc, min_eq_left (show 1 ≤ C by omega)])
            (sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩))
          simp (disch := first | decide | omega) [Function.update_of_ne]
          rw [← hI, hc]; rfl
        · refine sp_ite_neg (by simp [hc, min_eq_left (show 1 ≤ C by omega)]) ?_
          by_cases hk : tc ts (r tP + 1) = 3 ∧ b + 2 ≤ r tC
          · refine sp_ite_pos (by
              simp only [eval_bin, ap_mul, ap_eq, ap_lt, ap_add, eval_v, eval_c, ht1, hb']
              simp (disch := omega) only [min_eq_left]
              simp [hk.1]; omega) (sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩))
            simp (disch := first | decide | omega) [Function.update_of_ne]
            rw [← hI]; simp [hc, hk.1, hk.2]
          · refine sp_ite_neg (by
              simp only [eval_bin, ap_mul, ap_eq, ap_lt, ap_add, eval_v, eval_c, ht1, hb']
              simp (disch := omega) only [min_eq_left]
              by_cases h3 : tc ts (r tP + 1) = 3
              · have : ¬ b + 2 ≤ r tC := fun h => hk ⟨h3, h⟩
                simp [h3]; omega
              · simp [h3]) ?_
            have hI' : polT ts b (r tP + 1) (r tC - 1) = polT ts b p0 1 := by
              rw [← hI]
              have hc' : (r tC == 1) = false := by simpa using hc
              by_cases h3 : tc ts (r tP + 1) = 3
              · have : ¬ b + 2 ≤ r tC := fun h => hk ⟨h3, h⟩
                have e3 : (tc ts (r tP + 1) == 3) = true := by simpa using h3
                have e4 : decide (b + 2 ≤ r tC) = false := by simpa using this
                simp [hc', e3, e4]
              · have e3 : (tc ts (r tP + 1) == 3) = false := by simpa using h3
                simp [hc', e3]
            refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
            · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
            · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
            · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
            · simp (disch := first | decide | omega) [Function.update_of_ne]; omega
            · simp (disch := first | decide | omega) [Function.update_of_ne, hI']
            · simp (disch := first | decide | omega) [Function.update_of_ne]
      · refine sp_ite_neg (by simp [ht, h4, min_eq_left (show 4 ≤ C by omega)]) ?_
        rw [if_neg h4] at hI
        by_cases h3 : tc ts (r tP) = 3
        · refine sp_ite_pos (by simp [ht, h3, min_eq_left (show 3 ≤ C by omega)]) ?_
          rw [if_pos h3] at hI
          unfold polTLpP
          by_cases h3' : tc ts (r tP + 1) = 3
          · have hlt1 : r tP + 1 < ts.length := lt_of_tc_ne (by omega)
            refine sp_ite_pos (by simp [ht1, h3', min_eq_left (show 3 ≤ C by omega)]) ?_
            refine sp_seqE (o1 := []) (o2 := []) ((sp_labSufP hEr (.bin .add (.v tP) (.c 2))
              (by simp (disch := omega); omega)).frame.mono
              (W' := polTW) (by decide) (fun _ _ h => h)) (fun r1 _ h1 => ?_) rfl
            obtain ⟨h1R, h1f⟩ := h1
            have hE1 : Env ts q a C r1 := hEr.of_frame h1f (by decide) (by decide)
            have h1P : r1 tP = r tP := h1f tP (by decide)
            have h1C : r1 tC = r tC := h1f tC (by decide)
            have h1D : r1 tD = r tD := h1f tD (by decide)
            simp (disch := omega) only [eval_bin, ap_add, eval_v, eval_c, min_eq_left] at h1R
            refine sp_seqE (o1 := []) (o2 := []) ((sp_tendP hE1 (.bin .add (.v tP) (.c 1))).frame.mono
              (W' := polTW) (by decide) (fun _ _ h => h)) (fun r2 _ h2 => ?_) rfl
            obtain ⟨h2R, h2f⟩ := h2
            simp (disch := omega) only [eval_bin, ap_add, eval_v, eval_c, min_eq_left, h1P] at h2R
            have h2C : r2 tC = r tC := (h2f tC (by decide)).trans h1C
            have h2D : r2 tD = r tD := (h2f tD (by decide)).trans h1D
            have h2lR : r2 lR = if labSuf ts (r tP + 2) then 1 else 0 :=
              (h2f lR (by decide)).trans h1R
            have hne : tend ts (r tP + 1) ≤ ts.length := by
              have := scan_le (ts := ts) upT downT (r tP + 1) 0
              simp only [tend]; omega
            have hgt : r tP + 1 ≤ tend ts (r tP + 1) := le_scan (ts := ts) upT downT _ 0
            have hv : validLab ts (r tP + 1) = labSuf ts (r tP + 2) := by
              simp [validLab, h3']
            rw [hv] at hI
            by_cases hl : labSuf ts (r tP + 2) = true
            · rw [hl, Bool.true_and] at hI
              refine sp_ite_pos (by simp [h2lR, hl]) ?_
              refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
              · simp (disch := first | decide | omega) [Function.update_of_ne, h2D, hd]
              · simp (disch := first | decide | omega) [Function.update_of_ne, h2R, hne]
              · simp (disch := first | decide | omega) [Function.update_of_ne, h2C]
              · simp (disch := first | decide | omega) [Function.update_of_ne, h2C, h2R,
                  ]
                omega
              · simp (disch := first | decide | omega) [Function.update_of_ne, h2C, h2R,
                  hI]
              · simp (disch := first | decide | omega) [Function.update_of_ne, h2R]; omega
            · rw [Bool.not_eq_true] at hl
              rw [hl, Bool.false_and] at hI
              refine sp_ite_neg (by simp [h2lR, hl]) (sp_set2 (by decide) (by decide)
                (Or.inl ⟨by simp; omega, ?_⟩))
              simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
          · refine sp_ite_neg (by simp [ht1, h3', min_eq_left (show 3 ≤ C by omega)]) ?_
            have hv : validLab ts (r tP + 1) = false := by simp [validLab, h3']
            rw [hv, Bool.false_and] at hI
            refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
            simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
        · refine sp_ite_neg (by simp [ht, h3, min_eq_left (show 3 ≤ C by omega)]) ?_
          rw [if_neg h3] at hI
          refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
          simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
    · refine sp_ite_neg (by simp [hL, hlt]) ?_
      rw [if_pos (by omega)] at hI
      refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
      simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
  · simp only [eval_bin, ap_add, eval_v, eval_c, hE2.hL]
    rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega)]
    omega

end SQ

end PathChecking
