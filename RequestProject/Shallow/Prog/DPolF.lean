module

public import RequestProject.Shallow.Prog.DLab

/-!
# Checking formulas in the loop language

`polFP p` computes `polF ts p 1` (a formula starts at `p`).
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- formulas: loop counter -/
abbrev fI : Fin V := 34
/-- formulas: position -/
abbrev fP : Fin V := 35
/-- formulas: number of formulas still to read -/
abbrev fC : Fin V := 36
/-- formulas: done flag -/
abbrev fD : Fin V := 37
/-- formulas: result -/
abbrev fR : Fin V := 38

/-- Stop with result `b`. -/
def stopF (b : ℕ) : Pr V := .seq (.set fR (.c b)) (.set fD (.c 1))

/-- One step of `polF` at an atom. -/
def polFAtP : Pr V :=
  .seq (numOKP (.bin .add (.v fP) (.c 1))) (.seq (numEndP (.bin .add (.v fP) (.c 1)))
    (.ite (.bin .eq (.v dR) (.c 0)) (stopF 0)
      (.ite (.bin .eq (.v fC) (.c 1)) (stopF 1)
        (.seq (.set fP (.v sR)) (.set fC (.bin .sub (.v fC) (.c 1)))))))

/-- One step of `polF`. -/
def polFBody : Pr V :=
  .ite (.bin .lt (.v fP) (.v vL))
    (.ite (.bin .eq (tokE (.v fP)) (.c 5)) polFAtP
    (.ite (.bin .eq (tokE (.v fP)) (.c 6))
      (.ite (.bin .eq (.v fC) (.c 1)) (stopF 1)
        (.seq (.set fP (.bin .add (.v fP) (.c 1))) (.set fC (.bin .sub (.v fC) (.c 1)))))
    (.ite (.bin .add (.bin .add (.bin .eq (tokE (.v fP)) (.c 7)) (.bin .eq (tokE (.v fP)) (.c 9)))
        (.bin .eq (tokE (.v fP)) (.c 11)))
      (.set fP (.bin .add (.v fP) (.c 1)))
    (.ite (.bin .add (.bin .eq (tokE (.v fP)) (.c 8)) (.bin .eq (tokE (.v fP)) (.c 10)))
      (.seq (.set fP (.bin .add (.v fP) (.c 1))) (.set fC (.bin .add (.v fC) (.c 1))))
      (stopF 0)))))
    (stopF 0)

/-- `fR := polF ts p 1`. -/
def polFP (p : Ex V) : Pr V :=
  .seq (.seq (.set fP p) (.set fC (.c 1))) (.seq (.set fD (.c 0))
    (fuelP fI fD (.bin .add (.v vL) (.c 1)) polFBody))

/-- Frame of `polFP`. -/
abbrev polFW : List (Fin V) :=
  [fI, fP, fC, fD, fR, dI, dP, dOk, dD, dR, sR, sP, sC, sD, sI]

lemma sp_polFP (hE : Env ts q a C ρ) (p : Ex V)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length)
    (hp1 : 1 ≤ p.eval (pack (encodeToks ts) q a) C ρ) :
    Sp (pack (encodeToks ts) q a) C (polFP p) ρ polFW []
      (fun r => r fR = if polF ts (p.eval (pack (encodeToks ts) q a) C ρ) 1 then 1 else 0) := by
  set x := pack (encodeToks ts) q a
  set p0 := p.eval x C ρ
  have hC := hE.len_le
  unfold polFP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := polFW) (a := fP) (b := fC) (e1 := p)
    (e2 := .c 1) (ρ := ρ) (x := x) (C := C)
    (Q := fun r => r fP = p0 ∧ r fC = 1 ∧ r vN = ρ vN ∧ r vL = ρ vL) (by decide) (by decide)
    (by simp (disch := first | decide | omega) [Function.update_of_ne, p0]))
    (fun ρ1 f1 h1 => ?_) rfl
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ1 fD 0)
    (by decide) (by simp)) (fun ρ2 f2 h2 => ?_) rfl
  subst h2
  obtain ⟨h1p, h1c, h1N, h1L⟩ := h1
  have hE2 : Env ts q a C (Function.update ρ1 fD 0) :=
    hE.congr (by simp (disch := decide) [Function.update_of_ne, h1N])
      (by simp (disch := decide) [Function.update_of_ne, h1L])
  refine (sp_fuel fI fD _ polFBody _ polFW
    (fun r => r fP ≤ ts.length ∧ 1 ≤ r fC ∧ r fC ≤ r fP ∧ polF ts (r fP) (r fC) = polF ts p0 1)
    (fun r => r fR = if polF ts p0 1 then 1 else 0) (fun r => r fP)
    (by decide) (by decide)
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (fun r k => by simp (disch := decide) [Function.update_of_ne])
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (Or.inr ⟨by simp, by simp (disch := decide) [Function.update_of_ne, h1p, h1c, hp, hp1]⟩)
    (fun r fr hd ⟨hpl, hc1, hcp, hI⟩ => ?_) (fun r fr ⟨hpl, _⟩ => ?_)).mono
    (fun _ h => h) (fun _ _ h => h)
  · have hEr : Env ts q a C r := hE2.of_frame fr (by decide) (by decide)
    have hL : r vL = ts.length := hEr.hL
    rw [polF_eq] at hI
    unfold polFBody
    by_cases hlt : r fP < ts.length
    · refine sp_ite_pos (by simp [hL, hlt]) ?_
      rw [if_neg (by omega)] at hI
      have ht : (tokE (.v fP)).eval x C r = tc ts (r fP) := by
        rw [eval_tokE ts q a C r _ hE.hq hE.hC hEr.hN (by simp; omega)]; simp
      have hle := tc_lt_29 (ts := ts) hlt
      by_cases h5 : tc ts (r fP) = 5
      · refine sp_ite_pos (by simp [ht, h5, min_eq_left (show 5 ≤ C by omega)]) ?_
        rw [if_pos h5] at hI
        unfold polFAtP
        refine sp_seqE (o1 := []) (o2 := []) ((sp_numOKP hEr (.bin .add (.v fP) (.c 1))
          (by simp (disch := omega) [] <;> omega)).frame.mono
          (W' := polFW) (by decide) (fun _ _ h => h)) (fun r1 _ h1 => ?_) rfl
        obtain ⟨h1R, h1f⟩ := h1
        have hE1 : Env ts q a C r1 := hEr.of_frame h1f (by decide) (by decide)
        have h1P : r1 fP = r fP := h1f fP (by decide)
        have h1C : r1 fC = r fC := h1f fC (by decide)
        have h1D : r1 fD = r fD := h1f fD (by decide)
        simp (disch := omega) only [eval_bin, ap_add, eval_v, eval_c, min_eq_left] at h1R
        refine sp_seqE (o1 := []) (o2 := []) ((sp_numEndP hE1 (.bin .add (.v fP) (.c 1))
          (by simp (disch := omega) [h1P]; omega)).frame.mono
          (W' := polFW) (by decide) (fun _ _ h => h)) (fun r2 _ h2 => ?_) rfl
        obtain ⟨h2R, h2f⟩ := h2
        simp (disch := omega) only [eval_bin, ap_add, eval_v, eval_c, min_eq_left, h1P] at h2R
        have h2P : r2 fP = r fP := (h2f fP (by decide)).trans h1P
        have h2C : r2 fC = r fC := (h2f fC (by decide)).trans h1C
        have h2D : r2 fD = r fD := (h2f fD (by decide)).trans h1D
        have h2dR : r2 dR = if numOK ts (r fP + 1) then 1 else 0 := (h2f dR (by decide)).trans h1R
        have hne : numEnd ts (r fP + 1) ≤ ts.length := by
          have := scan_le (ts := ts) upN downN (r fP + 1) 1
          simp only [numEnd]; omega
        have hgt : r fP + 1 ≤ numEnd ts (r fP + 1) := le_scan (ts := ts) upN downN _ 1
        by_cases hn : numOK ts (r fP + 1) = true
        · rw [hn, Bool.true_and] at hI
          refine sp_ite_neg (by simp [h2dR, hn]) ?_
          by_cases hc : r fC = 1
          · refine sp_ite_pos (by simp [h2C, hc, min_eq_left (show 1 ≤ C by omega)]) (sp_set2 (by decide) (by decide)
              (Or.inl ⟨by simp; omega, ?_⟩))
            simp (disch := first | decide | omega) [Function.update_of_ne]
            rw [← hI, hc]; rfl
          · refine sp_ite_neg (by simp [h2C, hc, min_eq_left (show 1 ≤ C by omega)]) ?_
            refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
            · simp (disch := first | decide | omega) [Function.update_of_ne, h2D, hd]
            · simp (disch := first | decide | omega) [Function.update_of_ne, h2R, hne]
            · simp (disch := first | decide | omega) [Function.update_of_ne, h2C]
              omega
            · simp (disch := first | decide | omega) [Function.update_of_ne, h2C, h2R,
                ]
              omega
            · simp (disch := first | decide | omega) [Function.update_of_ne, h2C, h2R,
                ]
              rw [← hI]; simp [hc]
            · simp (disch := first | decide | omega) [Function.update_of_ne, h2R]; omega
        · rw [Bool.not_eq_true] at hn
          rw [hn, Bool.false_and] at hI
          refine sp_ite_pos (by simp [h2dR, hn]) (sp_set2 (by decide) (by decide)
            (Or.inl ⟨by simp; omega, ?_⟩))
          simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
      · refine sp_ite_neg (by simp [ht, h5, min_eq_left (show 5 ≤ C by omega)]) ?_
        rw [if_neg h5] at hI
        by_cases h6 : tc ts (r fP) = 6
        · refine sp_ite_pos (by simp [ht, h6, min_eq_left (show 6 ≤ C by omega)]) ?_
          rw [if_pos h6] at hI
          by_cases hc : r fC = 1
          · refine sp_ite_pos (by simp [hc, min_eq_left (show 1 ≤ C by omega)]) (sp_set2 (by decide) (by decide)
              (Or.inl ⟨by simp; omega, ?_⟩))
            simp (disch := first | decide | omega) [Function.update_of_ne]
            rw [← hI, hc]; rfl
          · refine sp_ite_neg (by simp [hc, min_eq_left (show 1 ≤ C by omega)]) ?_
            refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
            · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
            · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
            · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
            · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
            · simp (disch := first | decide | omega) [Function.update_of_ne]
              rw [← hI]; simp [hc]
            · simp (disch := first | decide | omega) [Function.update_of_ne]
        · refine sp_ite_neg (by simp [ht, h6, min_eq_left (show 6 ≤ C by omega)]) ?_
          rw [if_neg h6] at hI
          by_cases hn : tc ts (r fP) = 7 ∨ tc ts (r fP) = 9 ∨ tc ts (r fP) = 11
          · refine sp_ite_pos (by
              simp only [eval_bin, ap_add, ap_eq, ht, eval_c]
              simp (disch := omega) only [min_eq_left]
              rcases hn with h | h | h <;> simp [h] <;> omega) ?_
            rw [if_pos hn] at hI
            refine sp_set (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
            · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
            · simp (disch := first | decide | omega) [] <;> omega
            · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
            · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
            · simp (disch := first | decide | omega) [Function.update_of_ne, hI]
            · simp (disch := first | decide | omega) []
          · refine sp_ite_neg (by
              simp only [eval_bin, ap_add, ap_eq, ht, eval_c]
              simp (disch := omega) only [min_eq_left]
              simp only [not_or] at hn
              simp [hn.1, hn.2.1, hn.2.2]) ?_
            rw [if_neg hn] at hI
            by_cases hu : tc ts (r fP) = 8 ∨ tc ts (r fP) = 10
            · refine sp_ite_pos (by
                simp only [eval_bin, ap_add, ap_eq, ht, eval_c]
                simp (disch := omega) only [min_eq_left]
                rcases hu with h | h <;> simp [h] <;> omega) ?_
              rw [if_pos hu] at hI
              refine sp_set2 (by decide) (by decide) (Or.inr ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩)
              · simp (disch := first | decide | omega) [Function.update_of_ne, hd]
              · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
              · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
              · simp (disch := first | decide | omega) [Function.update_of_ne] <;> omega
              · simp (disch := first | decide | omega) [Function.update_of_ne, hI]
              · simp (disch := first | decide | omega) [Function.update_of_ne]
            · refine sp_ite_neg (by
                simp only [eval_bin, ap_add, ap_eq, ht, eval_c]
                simp (disch := omega) only [min_eq_left]
                simp only [not_or] at hu
                simp [hu.1, hu.2]) ?_
              rw [if_neg hu] at hI
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
