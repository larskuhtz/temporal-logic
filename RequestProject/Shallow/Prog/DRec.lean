module

public import RequestProject.Shallow.Prog.DPolF
public import RequestProject.Shallow.Prog.DPolT

/-!
# Recognising instances with shallow branching in the loop language

`recP` computes `recog ts b` (with `b` in `vD`) into `vRC`, and `fend ts 1` into `vFE`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- `fend ts 1` -/
abbrev vFE : Fin V := 47
/-- the result of the recognizer -/
abbrev vRC : Fin V := 48
/-- start of the children of the root -/
abbrev vTO : Fin V := 49

lemma recog_eq (b : ℕ) : recog ts b =
    (tc ts 0 == 3 && polF ts 1 1 && tc ts (fend ts 1) == 4 && tc ts (fend ts 1 + 1) == 3 &&
      tc ts (fend ts 1 + 2) == 3 && labSuf ts (fend ts 1 + 3) &&
      polT ts b (tend ts (fend ts 1 + 2)) 1 && tend ts (fend ts 1 + 1) == ts.length) := by
  simp only [recog, validT', validLab, Bool.and_assoc]

/-- The token test of the recognizer. -/
def recCondE : Ex V :=
  .bin .mul (.bin .mul (.bin .mul (.bin .mul (.bin .eq (tokE (.c 0)) (.c 3)) (.v fR))
    (.bin .eq (tokE (.v vFE)) (.c 4))) (.bin .eq (tokE (.bin .add (.v vFE) (.c 1))) (.c 3)))
    (.bin .eq (tokE (.bin .add (.v vFE) (.c 2))) (.c 3))

/-- The recognizer after the token test. -/
def recTreeP : Pr V :=
  .seq (labSufP (.bin .add (.v vFE) (.c 3))) (.seq (tendP (.bin .add (.v vFE) (.c 2)))
    (.seq (.set vTO (.v sR))
      (.ite (.v lR) (.seq (polTP (.v vTO)) (.seq (tendP (.bin .add (.v vFE) (.c 1)))
        (.set vRC (.bin .mul (.v tR) (.bin .eq (.v sR) (.v vL)))))) .skip)))

/-- The recognizer. -/
def recP : Pr V :=
  .seq (polFP (.c 1)) (.seq (fendP (.c 1)) (.seq (.seq (.set vFE (.v sR)) (.set vRC (.c 0)))
    (.ite recCondE recTreeP .skip)))

/-- Frame of `recP`. -/
abbrev recW : List (Fin V) :=
  [tI, tP, tC, tD, tR, lI, lQ, lD, lR, lE, dI, dP, dOk, dD, dR, sR, sP, sC, sD, sI,
    cI, cP, cQ, cA, cD, cR, fI, fP, fC, fD, fR, vFE, vRC, vTO]

lemma sp_recP (hE : Env ts q a C ρ) (hL1 : 1 ≤ ts.length) (hb : ρ vD + 2 ≤ C) :
    Sp (pack (encodeToks ts) q a) C recP ρ recW []
      (fun r => r vRC = (if recog ts (ρ vD) then 1 else 0) ∧ r vFE = fend ts 1) := by
  set x := pack (encodeToks ts) q a
  set b := ρ vD
  have hC := hE.len_le
  set f := fend ts 1 with hf
  have hfL : f ≤ ts.length := fend_le' ts hL1
  unfold recP
  -- the formula
  refine sp_seqE (o1 := []) (o2 := []) ((sp_polFP hE (.c 1) (by simp; omega)
    (by simp; omega)).frame.mono (W' := recW) (by decide) (fun _ _ h => h))
    (fun r1 _ h1 => ?_) rfl
  obtain ⟨h1R, h1f⟩ := h1
  have hE1 : Env ts q a C r1 := hE.of_frame h1f (by decide) (by decide)
  simp only [eval_c, min_eq_left (show 1 ≤ C by omega)] at h1R
  refine sp_seqE (o1 := []) (o2 := []) ((sp_fendP hE1 (.c 1)).frame.mono
    (W' := recW) (by decide) (fun _ _ h => h)) (fun r2 _ h2 => ?_) rfl
  obtain ⟨h2R, h2f⟩ := h2
  simp only [eval_c, min_eq_left (show 1 ≤ C by omega)] at h2R
  have hE2 : Env ts q a C r2 := hE1.of_frame h2f (by decide) (by decide)
  have h2fR : r2 fR = if polF ts 1 1 then 1 else 0 := (h2f fR (by decide)).trans h1R
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := recW) (a := vFE) (b := vRC)
    (e1 := .v sR) (e2 := .c 0) (ρ := r2) (x := x) (C := C)
    (Q := fun r => r = Function.update (Function.update r2 vFE f) vRC 0) (by decide) (by decide)
    (by simp [h2R, f])) (fun r3 _ h3 => ?_) rfl
  subst h3
  set r3 := Function.update (Function.update r2 vFE f) vRC 0 with hr3
  have hE3 : Env ts q a C r3 := hE2.congr (by simp (disch := decide) [r3, Function.update_of_ne])
    (by simp (disch := decide) [r3, Function.update_of_ne])
  have h3F : r3 vFE = f := by simp (disch := decide) [r3, Function.update_of_ne]
  have h3R : r3 vRC = 0 := by simp [r3]
  have h3fR : r3 fR = if polF ts 1 1 then 1 else 0 := by
    simp (disch := decide) [r3, Function.update_of_ne, h2fR]
  have h3D : r3 vD = b := by
    simp (disch := decide) [r3, Function.update_of_ne, h2f vD (by decide), h1f vD (by decide), b]
  -- the token test
  have ht0 : (tokE (.c 0)).eval x C r3 = tc ts 0 := by
    rw [eval_tokE ts q a C r3 _ hE.hq hE.hC hE3.hN (by simp)]; simp
  have htf : (tokE (.v vFE)).eval x C r3 = tc ts f := by
    rw [eval_tokE ts q a C r3 _ hE.hq hE.hC hE3.hN (by simp; omega)]; simp [h3F]
  have htf1 : (tokE (.bin .add (.v vFE) (.c 1))).eval x C r3 = tc ts (f + 1) := by
    rw [eval_tokE ts q a C r3 _ hE.hq hE.hC hE3.hN (by simp)]
    simp (disch := omega) [h3F]
  have htf2 : (tokE (.bin .add (.v vFE) (.c 2))).eval x C r3 = tc ts (f + 2) := by
    rw [eval_tokE ts q a C r3 _ hE.hq hE.hC hE3.hN (by simp)]
    simp (disch := omega) [h3F]
  have hcond : recCondE.eval x C r3 ≠ 0 ↔ (tc ts 0 == 3 && polF ts 1 1 && tc ts f == 4 &&
      tc ts (f + 1) == 3 && tc ts (f + 2) == 3) = true := by
    simp only [recCondE, eval_bin, ap_mul, ap_eq, eval_v, eval_c, ht0, htf, htf1, htf2, h3fR]
    simp (disch := omega) only [min_eq_left]
    by_cases e1 : tc ts 0 = 3 <;> by_cases e2 : polF ts 1 1 <;> by_cases e3 : tc ts f = 4 <;>
      by_cases e4 : tc ts (f + 1) = 3 <;> by_cases e5 : tc ts (f + 2) = 3 <;>
      simp [e1, e2, e3, e4, e5]; omega
  rw [recog_eq, ← hf]
  by_cases hc : (tc ts 0 == 3 && polF ts 1 1 && tc ts f == 4 && tc ts (f + 1) == 3 &&
      tc ts (f + 2) == 3) = true
  · refine sp_ite_pos (hcond.2 hc) ?_
    have e5 : tc ts (f + 2) = 3 := by simp at hc; exact hc.2
    have hf2 : f + 2 < ts.length := lt_of_tc_ne (by omega)
    unfold recTreeP
    refine sp_seqE (o1 := []) (o2 := []) ((sp_labSufP hE3 (.bin .add (.v vFE) (.c 3))
      (by simp (disch := omega) [h3F]; omega)).frame.mono
      (W' := recW) (by decide) (fun _ _ h => h)) (fun r4 _ h4 => ?_) rfl
    obtain ⟨h4R, h4f⟩ := h4
    simp (disch := omega) only [eval_bin, ap_add, eval_v, eval_c, min_eq_left, h3F] at h4R
    have hE4 : Env ts q a C r4 := hE3.of_frame h4f (by decide) (by decide)
    have h4F : r4 vFE = f := (h4f vFE (by decide)).trans h3F
    refine sp_seqE (o1 := []) (o2 := []) ((sp_tendP hE4 (.bin .add (.v vFE) (.c 2))).frame.mono
      (W' := recW) (by decide) (fun _ _ h => h)) (fun r5 _ h5 => ?_) rfl
    obtain ⟨h5R, h5f⟩ := h5
    simp (disch := omega) only [eval_bin, ap_add, eval_v, eval_c, min_eq_left, h4F] at h5R
    have hE5 : Env ts q a C r5 := hE4.of_frame h5f (by decide) (by decide)
    have h5F : r5 vFE = f := (h5f vFE (by decide)).trans h4F
    have h5lR : r5 lR = if labSuf ts (f + 3) then 1 else 0 := (h5f lR (by decide)).trans h4R
    have h5Rec : r5 vRC = 0 := by
      rw [h5f vRC (by decide), h4f vRC (by decide), h3R]
    have h5D : r5 vD = b := by rw [h5f vD (by decide), h4f vD (by decide), h3D]
    refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update r5 vTO
      (tend ts (f + 2))) (by decide) (by simp [h5R])) (fun r6 _ h6 => ?_) rfl
    subst h6
    set r6 := Function.update r5 vTO (tend ts (f + 2)) with hr6
    have hE6 : Env ts q a C r6 := hE5.congr (by simp (disch := decide) [r6, Function.update_of_ne])
      (by simp (disch := decide) [r6, Function.update_of_ne])
    have hte : tend ts (f + 2) ≤ ts.length := tend_le' ts (by omega)
    have hte1 : f + 2 ≤ tend ts (f + 2) := le_scan (ts := ts) upT downT _ 0
    by_cases hl : labSuf ts (f + 3) = true
    · refine sp_ite_pos (by simp (disch := decide) [r6, Function.update_of_ne, h5lR, hl]) ?_
      have h6D : r6 vD = b := by simp (disch := decide) [r6, Function.update_of_ne, h5D]
      refine sp_seqE (o1 := []) (o2 := []) ((sp_polTP hE6 (.v vTO) (by simp [r6]; omega)
        (by simp [r6]; omega) (by rw [h6D]; omega)).frame.mono (W' := recW) (by decide) (fun _ _ h => h)) (fun r7 _ h7 => ?_) rfl
      obtain ⟨h7R, h7f⟩ := h7
      simp (disch := decide) only [eval_v, r6, Function.update_self, Function.update_of_ne,
        h5D] at h7R
      have hE7 : Env ts q a C r7 := hE6.of_frame h7f (by decide) (by decide)
      have h7F : r7 vFE = f := by
        rw [h7f vFE (by decide)]; simp (disch := decide) [r6, Function.update_of_ne, h5F]
      refine sp_seqE (o1 := []) (o2 := []) ((sp_tendP hE7 (.bin .add (.v vFE) (.c 1))).frame.mono
        (W' := recW) (by decide) (fun _ _ h => h)) (fun r8 _ h8 => ?_) rfl
      obtain ⟨h8R, h8f⟩ := h8
      simp (disch := omega) only [eval_bin, ap_add, eval_v, eval_c, min_eq_left, h7F] at h8R
      have hE8 : Env ts q a C r8 := hE7.of_frame h8f (by decide) (by decide)
      have h8tR : r8 tR = if polT ts b (tend ts (f + 2)) 1 then 1 else 0 :=
        (h8f tR (by decide)).trans h7R
      refine sp_set (by decide) ⟨?_, ?_⟩
      · simp only [Function.update_self, eval_bin, ap_mul, ap_eq, eval_v, h8tR, h8R, hE8.hL]
        simp at hc
        simp only [hc, hl, beq_self_eq_true, Bool.true_and, Bool.and_true]
        by_cases e1 : polT ts b (tend ts (f + 2)) 1 = true <;>
          by_cases e2 : tend ts (f + 1) = ts.length <;> simp [e1, e2]; omega
      · rw [Function.update_of_ne (by decide), h8f vFE (by decide), h7F]
    · rw [Bool.not_eq_true] at hl
      refine sp_ite_neg (by simp (disch := decide) [r6, Function.update_of_ne, h5lR, hl])
        (sp_skip ⟨?_, ?_⟩)
      · simp (disch := decide) [r6, Function.update_of_ne, h5Rec, hl]
      · simp (disch := decide) [r6, Function.update_of_ne, h5F]
  · refine sp_ite_neg (by simpa using mt hcond.1 hc) (sp_skip ⟨?_, h3F⟩)
    rw [h3R]
    rw [Bool.not_eq_true] at hc
    simp only [Bool.and_assoc] at hc ⊢
    rw [show (tc ts 0 == 3 && (polF ts 1 1 && (tc ts f == 4 && (tc ts (f + 1) == 3 &&
      (tc ts (f + 2) == 3 && (labSuf ts (f + 3) && (polT ts b (tend ts (f + 2)) 1 &&
        tend ts (f + 1) == ts.length))))))) = false by
      revert hc
      cases tc ts 0 == 3 <;> cases polF ts 1 1 <;> cases tc ts f == 4 <;>
        cases tc ts (f + 1) == 3 <;> cases tc ts (f + 2) == 3 <;> simp]
    rfl

end SQ

end PathChecking
