module

public import RequestProject.BLMS.LClass

/-!
# Runs and actions in the loop language

`nextRunP` computes `(toLC C).nextRun (Conc.inp C) d` and `actionP` the action of the algorithm
on the decoded intervals of two codes.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL

variable {C : Circuit} {w : Word} {K : ℕ}

/-- input `d` of `nextRunP` -/
abbrev vNd : Var := 67
/-- start of the run -/
abbrev vNf : Var := 68
/-- end of the run -/
abbrev vNs : Var := 69
/-- loop variable -/
abbrev vNk : Var := 70
/-- output: left end -/
abbrev vNa : Var := 71
/-- output: right end -/
abbrev vNb : Var := 72
/-- code of the top of stack -/
abbrev vAI : Var := 73
/-- code of the current interval -/
abbrev vAJ : Var := 74
/-- code of the action -/
abbrev vAc : Var := 75
/-- decoded top of stack -/
abbrev vIa : Var := 76
/-- decoded top of stack -/
abbrev vIb : Var := 77
/-- decoded current interval -/
abbrev vJa : Var := 78
/-- decoded current interval -/
abbrev vJb : Var := 79

/-! ## Runs -/

/-- Read gate `vNk`. -/
def nbody : Pr V := .seq (.set vGi (.v vNk)) gateP

lemma nbody_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ)
    (p : ℕ) :
    GateOut C p (st w K nbody (Function.update ρ vNk p)) ∧
      st w K nbody (Function.update ρ vNk p) vNk = p ∧
      ∀ z ∉ gateP.wr, z ≠ vGi → z ≠ vNk → st w K nbody (Function.update ρ vNk p) z = ρ z := by
  unfold nbody
  simp only [st_seq, st_set, eval_v, Function.update_self]
  have G3 := (hG.upd vNk (by decide) p).upd vGi (by decide) p
  have g := gateP_spec hE hC _ G3.nt G3.ng
  simp only [Function.update_self] at g
  refine ⟨g, ?_, fun z hz h1 h2 => ?_⟩
  · rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true})
  · rw [st_frame _ _ _ hz, Function.update_of_ne h1, Function.update_of_ne h2]

/-- `(vNa, vNb) := nextRun vNd`. -/
def nextRunP : Pr V :=
  .seq (firstFP vNf vNk vN nbody (andB (notB (ltB (.v vNk) (.v vNd))) (.v vGT)))
    (.ite (ltB (.v vNf) (.v vN))
      (.seq (firstFP vNs vNk vN nbody (andB (ltB (.v vNf) (.v vNk)) (notB (.v vGT))))
        (.seq (.set vNa (.v vNf)) (.set vNb (.v vNs))))
      (.seq (.set vNa (.v vN)) (.set vNb (.v vN))))

lemma nextRunP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ) :
    st w K nextRunP ρ vNa = ((toLC C).nextRun (Conc.inp C) (ρ vNd)).1 ∧
      st w K nextRunP ρ vNb = ((toLC C).nextRun (Conc.inp C) (ρ vNd)).2 := by
  have hK := hE.nK
  unfold nextRunP
  simp only [st_seq]
  have h1 := firstFP_spec (w := w) (K := K) vNf vNk vN nbody
    (andB (notB (ltB (.v vNk) (.v vNd))) (.v vGT)) ρ
    (fun p => decide (ρ vNd ≤ p) && Conc.inp C p) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by omega) (by
      intro p hp ρ' hfr
      have Gq := hG.fr ρ' (fun z hz => hfr z (by revert z; decide) (by revert z; decide)
        (by revert z; decide))
      obtain ⟨g, gk, gf⟩ := nbody_spec hE hC ρ' Gq p
      rw [eval_andB (eval_notB eval_ltB)
        (show (Ex.v vGT : Ex V).eval w K (st w K nbody (Function.update ρ' vNk p)) = _ from g.t)
        (by omega), toNat_ne_zero]
      simp only [eval_v, gk, gf vNd (by decide) (by decide) (by decide),
        hfr vNd (by decide) (by decide) (by decide)]
      simp)
  have fr1 : ∀ z ∉ (firstFP vNf vNk vN nbody
      (andB (notB (ltB (.v vNk) (.v vNd))) (.v vGT))).wr, st w K (firstFP vNf vNk vN nbody
      (andB (notB (ltB (.v vNk) (.v vNd))) (.v vGT))) ρ z = ρ z := fun z hz => st_frame _ _ _ hz
  have G1 := hG.st (w := w) (K := K) (firstFP vNf vNk vN nbody
      (andB (notB (ltB (.v vNk) (.v vNd))) (.v vGT))) (globs_disj _ (by decide))
  generalize st w K (firstFP vNf vNk vN nbody
      (andB (notB (ltB (.v vNk) (.v vNd))) (.v vGT))) ρ = ρ1 at h1 fr1 G1
  rw [hG.n] at h1
  set f := firstF (fun p => decide (ρ vNd ≤ p) && Conc.inp C p) (toLC C).N with hf
  have hN1 : ρ1 vN = (toLC C).N := G1.n
  rw [st_ite]
  simp only [eval_ltB, eval_v, h1, hN1, toNat_ne_zero, decide_eq_true_eq]
  unfold LC.nextRun
  rw [← hf]
  by_cases hfN : f < (toLC C).N
  · rw [if_pos hfN, if_pos hfN]
    have h2 := firstFP_spec (w := w) (K := K) vNs vNk vN nbody
      (andB (ltB (.v vNf) (.v vNk)) (notB (.v vGT))) ρ1
      (fun q => decide (f < q) && !Conc.inp C q) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega) (by
        intro p hp ρ' hfr
        have Gq := G1.fr ρ' (fun z hz => hfr z (by revert z; decide) (by revert z; decide)
          (by revert z; decide))
        obtain ⟨g, gk, gf⟩ := nbody_spec hE hC ρ' Gq p
        rw [eval_andB eval_ltB (eval_notB
          (show (Ex.v vGT : Ex V).eval w K (st w K nbody (Function.update ρ' vNk p)) = _ from g.t))
          (by omega), toNat_ne_zero]
        simp only [eval_v, gk, gf vNf (by decide) (by decide) (by decide),
          hfr vNf (by decide) (by decide) (by decide), h1])
    rw [hN1] at h2
    simp only [st_seq, st_set, eval_v]
    have hs : st w K (firstFP vNs vNk vN nbody (andB (ltB (.v vNf) (.v vNk)) (notB (.v vGT)))) ρ1
        vNf = f := by rw [st_frame _ _ _ (by decide), h1]
    refine ⟨?_, ?_⟩
    · simp (config := {decide := true}) only [Function.update_of_ne, ne_eq,
        Function.update_self, hs]
    · simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne, ne_eq, h2]
  · rw [if_neg hfN, if_neg hfN]
    simp (config := {decide := true}) [hN1, LC.vR]

/-! ## Actions -/

lemma eval_eqB {ρ : Var → ℕ} {a b : Ex V} :
    (Ex.bin .eq a b).eval w K ρ = (decide (a.eval w K ρ = b.eval w K ρ)).toNat := by
  simp only [eval_bin, ap_eq]
  by_cases h : a.eval w K ρ = b.eval w K ρ <;> simp [h]

/-- Decode the codes `vAI` and `vAJ`. -/
def decodeP : Pr V :=
  .seq (.set vIa (.bin .div (.v vAI) (.bin .add (.v vN) (.c 1))))
  (.seq (.set vIb (.bin .mod (.v vAI) (.bin .add (.v vN) (.c 1))))
  (.seq (.set vJa (.bin .div (.v vAJ) (.bin .add (.v vN) (.c 1))))
   (.set vJb (.bin .mod (.v vAJ) (.bin .add (.v vN) (.c 1))))))

/-- `[(ρ a, ρ b) = vL]` -/
def isVL (a b : Var) : Ex V := andB (.bin .eq (.v a) (.c 0)) (.bin .eq (.v b) (.c 0))

/-- The classification part of `actionP`. -/
def actCls : Pr V :=
  .seq (.set vPa (.v vIa)) (.seq (.set vPb (.v vIb)) (.seq (.set vPc (.v vJa))
    (.seq (.set vPd (.v vJb)) (.seq classifyP
      (.ite (.bin .eq (.v vPt) (.c 1)) (.set vAc (.c 2))
        (.ite (.bin .eq (.v vPt) (.c 2)) (.set vAc (.c 3)) (.set vAc (.c 4))))))))

/-- The part of `actionP` after decoding. -/
def actRest : Pr V :=
  .ite (andB (.bin .eq (.v vJa) (.v vN)) (.bin .eq (.v vJb) (.v vN)))
    (.ite (isVL vIa vIb) (.set vAc (.c 1)) (.set vAc (.c 4)))
    (.seq (.set vSa (.v vJa)) (.seq (.set vSb (.v vJb)) (.seq iterIP
      (.ite (ltB (.v vSa) (.v vSb)) (.set vAc (.c 0))
        (.ite (isVL vIa vIb) (.set vAc (.c 3)) actCls)))))

/-- `vAc :=` the code of the action on the codes `vAI`, `vAJ`. -/
def actionP : Pr V := .seq decodeP actRest

/-- Codes of actions. -/
def actCode : LC.Act → ℕ
  | .accept => 0
  | .reject => 1
  | .merge => 2
  | .push => 3
  | .disc => 4

/-- Codes of outcomes. -/
def outCode : LC.Outc → ℕ
  | .merge => 2
  | .push => 3
  | .disc => 4

lemma decodeP_spec (hE : Env C w K) (ρ : Var → ℕ) (hG : Glob C ρ) :
    st w K decodeP ρ vIa = ((toLC C).dec (ρ vAI)).1 ∧ st w K decodeP ρ vIb = ((toLC C).dec (ρ vAI)).2 ∧
    st w K decodeP ρ vJa = ((toLC C).dec (ρ vAJ)).1 ∧ st w K decodeP ρ vJb = ((toLC C).dec (ρ vAJ)).2 := by
  have hK := hE.nK
  have hN := N_le (C := C)
  unfold decodeP
  simp (config := {decide := true}) only [st_seq, st_set, Function.update_self,
    Function.update_of_ne, ne_eq, eval_bin, ap_div, ap_mod, ap_add, eval_v, eval_c, hG.n,
    min_eq_left (show 1 ≤ K by omega), min_eq_left (show (toLC C).N + 1 ≤ K by omega), LC.dec,
    and_self]

lemma isVL_eval {ρ : Var → ℕ} {a b : Var} (hK : 1 ≤ K) :
    (isVL a b).eval w K ρ ≠ 0 ↔ (ρ a, ρ b) = LC.vL := by
  rw [isVL, eval_andB eval_eqB eval_eqB hK, toNat_ne_zero]
  simp [LC.vL, min_eq_left (Nat.zero_le K)]

lemma actCls_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ) :
    st w K actCls ρ vAc = outCode ((toLC C).classify (ρ vIa, ρ vIb) (ρ vJa, ρ vJb)) := by
  have hK := hE.nK
  unfold actCls
  simp only [st_seq, st_set, eval_v]
  simp (config := {decide := true}) only [Function.update_of_ne, ne_eq]
  have G1 := (((hG.upd vPa (by decide) (ρ vIa)).upd vPb (by decide) (ρ vIb)).upd vPc (by decide)
    (ρ vJa)).upd vPd (by decide) (ρ vJb)
  have hc := classifyP_spec hE hC _ G1
  simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne, ne_eq]
    at hc
  generalize st w K classifyP _ = ρ2 at hc
  unfold LC.classify
  generalize (toLC C).pfold (toLC C).D (ρ vIa, ρ vIb) (ρ vJa, ρ vJb) = r at hc ⊢
  rcases r with ⟨a, b, c, d⟩ | ⟨_ | _ | _⟩ <;>
    simp only [PRep] at hc <;>
    simp [st_ite, hc, outCode, min_eq_left (show 4 ≤ K by have := hE.lenK; omega),
      min_eq_left (show 3 ≤ K by have := hE.lenK; omega),
      min_eq_left (show 2 ≤ K by omega), min_eq_left (show 1 ≤ K by omega)]

set_option maxRecDepth 100000 in
lemma actionP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ) (hG : Glob C ρ) :
    st w K actionP ρ vAc =
      actCode ((toLC C).action ((toLC C).dec (ρ vAI)) ((toLC C).dec (ρ vAJ))) ∧
    st w K actionP ρ vIa = ((toLC C).dec (ρ vAI)).1 ∧ st w K actionP ρ vIb = ((toLC C).dec (ρ vAI)).2 ∧
    st w K actionP ρ vJa = ((toLC C).dec (ρ vAJ)).1 ∧ st w K actionP ρ vJb = ((toLC C).dec (ρ vAJ)).2 := by
  have hK := hE.nK
  have hK4 : 4 ≤ K := by have := hE.lenK; omega
  obtain ⟨d1, d2, d3, d4⟩ := decodeP_spec hE ρ hG
  have G1 := hG.st (w := w) (K := K) decodeP (globs_disj _ (by decide))
  unfold actionP
  simp only [st_seq]
  generalize st w K decodeP ρ = ρ1 at d1 d2 d3 d4 G1
  refine ⟨?_, by rw [st_frame _ _ _ (by decide), d1], by rw [st_frame _ _ _ (by decide), d2],
    by rw [st_frame _ _ _ (by decide), d3], by rw [st_frame _ _ _ (by decide), d4]⟩
  generalize (toLC C).dec (ρ vAI) = I at d1 d2
  generalize (toLC C).dec (ρ vAJ) = J at d3 d4
  unfold actRest LC.action
  rw [st_ite]
  have hc1 : (andB (.bin .eq (.v vJa) (.v vN)) (.bin .eq (.v vJb) (.v vN)) : Ex V).eval w K ρ1 ≠ 0
      ↔ J = (toLC C).vR := by
    rw [eval_andB eval_eqB eval_eqB (by omega), toNat_ne_zero]
    simp [d3, d4, G1.n, LC.vR, Prod.ext_iff]
  have hI : (isVL vIa vIb).eval w K ρ1 ≠ 0 ↔ I = LC.vL := by
    rw [isVL_eval (by omega), d1, d2]
  by_cases hJ : J = (toLC C).vR
  · rw [if_pos (hc1.2 hJ), if_pos hJ, st_ite]
    by_cases hIL : I = LC.vL
    · rw [if_pos (hI.2 hIL), if_pos hIL]; simp [actCode, min_eq_left (show 1 ≤ K by omega)]
    · rw [if_neg (fun h => hIL (hI.1 h)), if_neg hIL]; simp [actCode, min_eq_left hK4]
  · rw [if_neg (fun h => hJ (hc1.1 h)), if_neg hJ]
    simp only [st_seq, st_set, eval_v, d3]
    simp (config := {decide := true}) only [Function.update_of_ne, ne_eq, d4]
    have G2 := (G1.upd vSa (by decide) J.1).upd vSb (by decide) J.2
    obtain ⟨i1, i2⟩ := iterIP_spec hE hC _ G2
    simp (config := {decide := true}) only [Function.update_self, Function.update_of_ne, ne_eq]
      at i1 i2
    have fr : ∀ z ∉ iterIP.wr, st w K iterIP (Function.update (Function.update ρ1 vSa J.1) vSb J.2) z
        = Function.update (Function.update ρ1 vSa J.1) vSb J.2 z := fun z hz => st_frame _ _ _ hz
    have G3 := G2.st (w := w) (K := K) iterIP (globs_disj _ (by decide))
    generalize st w K iterIP (Function.update (Function.update ρ1 vSa J.1) vSb J.2) = ρ3
      at i1 i2 fr G3
    rw [st_ite]
    simp only [eval_ltB, eval_v, i1, i2, toNat_ne_zero, decide_eq_true_eq]
    unfold LC.loneAcc
    by_cases hA : ((toLC C).iterI (toLC C).D J).1 < ((toLC C).iterI (toLC C).D J).2
    · rw [if_pos hA, if_pos (by simpa using hA)]; simp [actCode]
    · rw [if_neg hA, if_neg (by simpa using hA), st_ite]
      have hI3 : (isVL vIa vIb).eval w K ρ3 ≠ 0 ↔ I = LC.vL := by
        rw [isVL_eval (by omega), fr _ (by decide), fr _ (by decide)]
        simp (config := {decide := true}) only [Function.update_of_ne, ne_eq, d1, d2]
      by_cases hIL : I = LC.vL
      · rw [if_pos (hI3.2 hIL), if_pos hIL]
        simp [actCode, min_eq_left (show 3 ≤ K by omega)]
      · rw [if_neg (fun h => hIL (hI3.1 h)), if_neg hIL, actCls_spec hE hC ρ3 G3]
        have e : ∀ z ∈ [vIa, vIb, vJa, vJb], ρ3 z = ρ1 z := by
          intro z hz; rw [fr _ (by revert z; decide), Function.update_of_ne, Function.update_of_ne]
          · intro h; subst h; revert hz; decide
          · intro h; subst h; revert hz; decide
        rw [e vIa (by decide), e vIb (by decide), e vJa (by decide), e vJb (by decide), d1, d2, d3,
          d4]
        rcases (toLC C).classify (I.1, I.2) (J.1, J.2) with _ | _ | _ <;> rfl

end LP

end BLMS

end PathChecking
