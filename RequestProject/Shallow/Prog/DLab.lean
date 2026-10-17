module

public import RequestProject.Shallow.Prog.DNum

/-!
# Checking labels in the loop language

`labSufP q` computes `labSuf ts q` (a strictly increasing list of numbers closed by `)` starts
at `q`).
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- labels: loop counter -/
abbrev lI : Fin V := 26
/-- labels: position -/
abbrev lQ : Fin V := 27
/-- labels: done flag -/
abbrev lD : Fin V := 28
/-- labels: result -/
abbrev lR : Fin V := 29
/-- labels: end of the current number -/
abbrev lE : Fin V := 30

/-- The test of a number of a label: canonical, and closing the label or smaller than the next
number. -/
def labCondE : Ex V :=
  .bin .mul (.v dR) (.bin .add (.bin .eq (tokE (.v lE)) (.c 4)) (.v cR))

/-- One step of `labSuf` at a number. -/
def labNumP : Pr V :=
  .seq (numOKP (.v lQ)) (.seq (numEndP (.v lQ)) (.seq (.set lE (.v sR))
    (.seq (cmpP (.v lQ) (.v lE) 0)
      (.ite labCondE (.set lQ (.v lE)) (.seq (.set lR (.c 0)) (.set lD (.c 1)))))))

/-- One step of `labSuf`. -/
def labBody : Pr V :=
  .ite (.bin .lt (.v lQ) (.v vL))
    (.ite (.bin .eq (tokE (.v lQ)) (.c 4)) (.seq (.set lR (.c 1)) (.set lD (.c 1))) labNumP)
    (.seq (.set lR (.c 0)) (.set lD (.c 1)))

/-- `lR := labSuf ts p`. -/
def labSufP (p : Ex V) : Pr V :=
  .seq (.seq (.set lQ p) (.set lD (.c 0)))
    (fuelP lI lD (.bin .add (.v vL) (.c 1)) labBody)

/-- Frame of `labSufP`. -/
abbrev labW : List (Fin V) :=
  [lI, lQ, lD, lR, lE, dI, dP, dOk, dD, dR, sR, sP, sC, sD, sI, cI, cP, cQ, cA, cD, cR]

lemma sp_labSufP (hE : Env ts q a C ρ) (p : Ex V)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C (labSufP p) ρ labW []
      (fun r => r lR = if labSuf ts (p.eval (pack (encodeToks ts) q a) C ρ) then 1 else 0) := by
  set x := pack (encodeToks ts) q a
  set p0 := p.eval x C ρ
  have hC := hE.len_le
  unfold labSufP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := labW) (a := lQ) (b := lD) (e1 := p)
    (e2 := .c 0) (ρ := ρ) (x := x) (C := C)
    (Q := fun r => r lQ = p0 ∧ r lD = 0 ∧ r vN = ρ vN ∧ r vL = ρ vL) (by decide) (by decide)
    (by simp (disch := decide) [Function.update_of_ne, p0])) (fun ρ2 f2 h2 => ?_) rfl
  obtain ⟨h2q, h2d, h2N, h2L⟩ := h2
  have hE2 : Env ts q a C ρ2 := hE.congr h2N h2L
  refine (sp_fuel lI lD _ labBody ρ2 labW
    (fun r => r lQ ≤ ts.length ∧ labSuf ts (r lQ) = labSuf ts p0)
    (fun r => r lR = if labSuf ts p0 then 1 else 0) (fun r => r lQ)
    (by decide) (by decide)
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (fun r k => by simp (disch := decide) [Function.update_of_ne])
    (fun r k h => by simpa (disch := decide) [Function.update_of_ne] using h)
    (Or.inr ⟨h2d, by rw [h2q]; exact hp, by rw [h2q]⟩)
    (fun r fr hd ⟨hql, hI⟩ => ?_) (fun r fr ⟨hql, _⟩ => ?_)).mono
    (fun _ h => h) (fun _ _ h => h)
  · have hEr : Env ts q a C r := hE2.of_frame fr (by decide) (by decide)
    have hL : r vL = ts.length := hEr.hL
    rw [labSuf_eq] at hI
    unfold labBody
    by_cases hlt : r lQ < ts.length
    · refine sp_ite_pos (by simp [hL, hlt]) ?_
      rw [if_neg (by omega)] at hI
      have htq : (tokE (.v lQ)).eval x C r = tc ts (r lQ) := by
        rw [eval_tokE ts q a C r _ hE.hq hE.hC hEr.hN (by simp; omega)]; simp
      by_cases h4 : tc ts (r lQ) = 4
      · refine sp_ite_pos (by simp [htq, h4, min_eq_left (show 4 ≤ C by omega)]) ?_
        rw [if_pos h4] at hI
        refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
        simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
      · refine sp_ite_neg (by simp [htq, h4, min_eq_left (show 4 ≤ C by omega)]) ?_
        rw [if_neg h4] at hI
        unfold labNumP
        -- the number
        refine sp_seqE (o1 := []) (o2 := []) ((sp_numOKP hEr (.v lQ) (by simp; omega)).frame.mono
          (W' := labW) (by decide) (fun _ _ h => h)) (fun r1 _ h1 => ?_) rfl
        obtain ⟨h1R, h1f⟩ := h1
        have hE1 : Env ts q a C r1 := hEr.of_frame h1f (by decide) (by decide)
        have h1Q : r1 lQ = r lQ := h1f lQ (by decide)
        simp only [eval_v] at h1R
        -- its end
        refine sp_seqE (o1 := []) (o2 := []) ((sp_numEndP hE1 (.v lQ)).frame.mono
          (W' := labW) (by decide) (fun _ _ h => h)) (fun r2 _ h2 => ?_) rfl
        obtain ⟨h2R, h2f⟩ := h2
        have hE2' : Env ts q a C r2 := hE1.of_frame h2f (by decide) (by decide)
        simp only [eval_v, h1Q] at h2R
        have h2Q : r2 lQ = r lQ := (h2f lQ (by decide)).trans h1Q
        have h2D : r2 dR = r1 dR := h2f dR (by decide)
        have hne : numEnd ts (r lQ) ≤ ts.length := by
          have := scan_le (ts := ts) upN downN (r lQ) 1
          simp only [numEnd]; omega
        have hgt : r lQ < numEnd ts (r lQ) := lt_scan (ts := ts) upN downN 1 hlt
        refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r' => r' = Function.update r2 lE
          (numEnd ts (r lQ))) (by decide) (by simp [h2R])) (fun r3 _ h3 => ?_) rfl
        subst h3
        set r3 := Function.update r2 lE (numEnd ts (r lQ)) with hr3
        have hE3 : Env ts q a C r3 := hE2'.congr (by simp (disch := decide) [r3, Function.update_of_ne])
          (by simp (disch := decide) [r3, Function.update_of_ne])
        have h3Q : r3 lQ = r lQ := by simp (disch := decide) [r3, Function.update_of_ne, h2Q]
        have h3E : r3 lE = numEnd ts (r lQ) := by simp [r3]
        have h3D : r3 dR = r1 dR := by simp (disch := decide) [r3, Function.update_of_ne, h2D]
        -- the comparison
        refine sp_seqE (o1 := []) (o2 := []) ((sp_cmpP hE3 (.v lQ) (.v lE) false
          (by simp; omega) (by simp (disch := decide) [Function.update_of_ne]; omega)).frame.mono
          (W' := labW) (by decide) (fun _ _ h => h)) (fun r4 _ h4 => ?_) rfl
        obtain ⟨h4R, h4f⟩ := h4
        simp (disch := decide) only [eval_v, Function.update_of_ne, h3Q, h3E] at h4R
        have h4Q : r4 lQ = r lQ := (h4f lQ (by decide)).trans h3Q
        have h4E : r4 lE = numEnd ts (r lQ) := (h4f lE (by decide)).trans h3E
        have h4D : r4 dR = if numOK ts (r lQ) then 1 else 0 := by
          rw [h4f dR (by decide), h3D, h1R]
        have hE4 : Env ts q a C r4 := hE3.of_frame h4f (by decide) (by decide)
        have hte : (tokE (.v lE)).eval x C r4 = tc ts (numEnd ts (r lQ)) := by
          rw [eval_tokE ts q a C r4 _ hE.hq hE.hC hE4.hN (by simp; omega)]; simp [h4E]
        have hcond : labCondE.eval x C r4 ≠ 0 ↔ (numOK ts (r lQ) &&
            (tc ts (numEnd ts (r lQ)) == 4 || numLt ts (r lQ) (numEnd ts (r lQ)))) = true := by
          simp only [labCondE, eval_bin, ap_mul, ap_add, ap_eq, eval_v, eval_c, hte, h4D, h4R,
            min_eq_left (show 4 ≤ C by omega), numLt]
          by_cases hn : numOK ts (r lQ) <;> by_cases ht : tc ts (numEnd ts (r lQ)) = 4 <;>
            by_cases hc : cmpScan ts (r lQ) (numEnd ts (r lQ)) false <;> simp [hn, ht, hc] <;> omega
        by_cases hc : (numOK ts (r lQ) &&
            (tc ts (numEnd ts (r lQ)) == 4 || numLt ts (r lQ) (numEnd ts (r lQ)))) = true
        · refine sp_ite_pos (hcond.2 hc) (sp_set (by decide) (Or.inr ⟨?_, ⟨?_, ?_⟩, ?_⟩))
          · rw [Function.update_of_ne (by decide), h4f lD (by decide)]
            simp (disch := decide) [r3, Function.update_of_ne, h2f lD (by decide),
              h1f lD (by decide), hd]
          · simp [h4E, hne]
          · simp [h4E]; rw [← hI, hc]; rfl
          · simp [h4E]; omega
        · refine sp_ite_neg (by simpa using mt hcond.1 hc) ?_
          refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
          simp (disch := first | decide | omega) [Function.update_of_ne]
          rw [← hI]; simp at hc ⊢
          intro h1 h2
          obtain ⟨ha, hb⟩ := hc h1
          rcases h2 with h2 | h2
          · exact absurd h2 ha
          · rw [hb] at h2; exact absurd h2 (by decide)
    · refine sp_ite_neg (by simp [hL, hlt]) ?_
      rw [if_pos (by omega)] at hI
      refine sp_set2 (by decide) (by decide) (Or.inl ⟨by simp; omega, ?_⟩)
      simp (disch := first | decide | omega) [Function.update_of_ne, ← hI]
  · simp only [eval_bin, ap_add, eval_v, eval_c, hE2.hL]
    rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega)]
    omega

end SQ

end PathChecking
