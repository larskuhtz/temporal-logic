module

public import RequestProject.Shallow.Prog.Tr

/-!
# The query program

`queryP` emits the query `QP ts r₀ d m N u ℓ j A` with `r₀` in `vR0`, `d` in `vD`, `m` in `vM`,
`N = |ts| + 1` in `vNq`, `u` in `vU`, `ℓ` in `vLl`, `j` in `vJ`; the answers `A` of the previous
round are read from the packed input.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- root position `r₀` -/
abbrev vR0 : Fin V := 53
/-- depth bound `d` -/
abbrev vD : Fin V := 54
/-- saved count -/
abbrev vC4 : Fin V := 55
/-- result of `tailP` -/
abbrev vTc : Fin V := 56

/-- `vTc := [tailCond ts r₀ d u]`. -/
def tailP : Pr V :=
  .seq (isLeafP (.v vU)) (.seq (cntP 4 (.v vR0) (.bin .sub (.v vU) (.v vR0)))
    (.seq (.set vC4 (.v vCr)) (.seq (cntP 3 (.v vR0) (.bin .sub (.v vU) (.v vR0)))
      (.set vTc (.bin .lt (.c 0) (.bin .add (.v vLf)
        (.bin .lt (.bin .add (.v vD) (.v vC4)) (.bin .add (.v vCr) (.c 1)))))))))

/-- Frame of `tailP`. -/
abbrev tailW : List (Fin V) := [vLf, sR, sP, sC, sD, sI, vCa, vCr, vCi, vC4, vTc]

lemma sp_tailP (hE : Env ts q a C ρ) (hu : ρ vU ≤ ts.length) (hr : ρ vR0 ≤ ts.length + 1) :
    Sp (pack (encodeToks ts) q a) C tailP ρ tailW []
      (fun ρ' => ρ' vTc = if tailCond ts (ρ vR0) (ρ vD) (ρ vU) then 1 else 0) := by
  have hC := hE.len_le
  unfold tailP
  refine sp_seqE (o2 := []) ((sp_isLeafP hE (.v vU) (by simpa using hu)).frame.mono
    (by decide) (fun _ _ h => h)) (fun ρ1 f1 h1 => ?_) rfl
  simp only [eval_v] at h1
  have hE1 := hE.of_frame f1 (by decide) (by decide)
  have hU1 : ρ1 vU = ρ vU := f1 _ (by decide)
  have hR1 : ρ1 vR0 = ρ vR0 := f1 _ (by decide)
  have hsub : ∀ ρ' : Fin V → ℕ, ρ' vU = ρ vU → ρ' vR0 = ρ vR0 →
      (Ex.bin .sub (.v vU) (.v vR0) : Ex V).eval (pack (encodeToks ts) q a) C ρ' =
        ρ vU - ρ vR0 := by
    intro ρ' h1 h2; simp [h1, h2]
  refine sp_seqE (o2 := []) ((sp_cntP hE1 4 (by norm_num) (.v vR0) (.bin .sub (.v vU) (.v vR0))
    (by simp only [eval_v, hR1]; exact hr) (by
      rw [hsub _ (by simp (disch := decide) [Function.update_of_ne, hU1])
        (by simp (disch := decide) [Function.update_of_ne, hR1])]; omega)).frame.mono
    (by decide) (fun _ _ h => h)) (fun ρ2 f2 h2 => ?_) rfl
  rw [hsub _ (by simp (disch := decide) [Function.update_of_ne, hU1])
    (by simp (disch := decide) [Function.update_of_ne, hR1])] at h2
  simp only [eval_v, hR1] at h2
  have hE2 := hE1.of_frame f2 (by decide) (by decide)
  have hU2 : ρ2 vU = ρ vU := (f2 _ (by decide)).trans hU1
  have hR2 : ρ2 vR0 = ρ vR0 := (f2 _ (by decide)).trans hR1
  have hLf2 : ρ2 vLf = if isLeaf ts (ρ vU) then 1 else 0 := by
    rw [h2.2 vLf (by decide), h1.1]
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ2 vC4
    (cnt ts 4 (ρ vR0) (ρ vU - ρ vR0))) (by decide) (by rw [eval_v, h2.1]))
    (fun ρ3 _ h3 => ?_) rfl
  subst h3
  set ρ3 := Function.update ρ2 vC4 (cnt ts 4 (ρ vR0) (ρ vU - ρ vR0))
  have g3 : ∀ v, v ≠ vC4 → ρ3 v = ρ2 v := fun v hv => Function.update_of_ne hv _ _
  have hE3 : Env ts q a C ρ3 := hE2.congr (g3 _ (by decide)) (g3 _ (by decide))
  refine sp_seqE (o2 := []) ((sp_cntP hE3 3 (by norm_num) (.v vR0) (.bin .sub (.v vU) (.v vR0))
    (by simp only [eval_v, g3 vR0 (by decide), hR2]; exact hr) (by
      rw [hsub _ (by simp (disch := decide) [Function.update_of_ne, g3, hU2])
        (by simp (disch := decide) [Function.update_of_ne, g3, hR2])]; omega)).frame.mono
    (by decide) (fun _ _ h => h)) (fun ρ4 _ h4 => ?_) rfl
  rw [hsub _ (by simp (disch := decide) [Function.update_of_ne, g3, hU2])
    (by simp (disch := decide) [Function.update_of_ne, g3, hR2])] at h4
  simp only [eval_v, g3 vR0 (by decide), hR2] at h4
  refine sp_set (by decide) ?_
  have hc3 := cnt_le ts 3 (ρ vR0) (ρ vU - ρ vR0)
  have hLf4 : ρ4 vLf = if isLeaf ts (ρ vU) then 1 else 0 := by
    rw [h4.2 vLf (by decide), g3 vLf (by decide), hLf2]
  have hC44 : ρ4 vC4 = cnt ts 4 (ρ vR0) (ρ vU - ρ vR0) := by
    rw [h4.2 vC4 (by decide)]; exact Function.update_self _ _ _
  have hD4 : ρ4 vD = ρ vD := by
    rw [h4.2 vD (by decide), g3 vD (by decide), f2 vD (by decide), f1 vD (by decide)]
  simp only [Function.update_self, eval_bin, ap_lt, ap_add, eval_v, eval_c, h4.1, hLf4, hC44,
    hD4, tailCond]
  rw [min_eq_left (show 0 ≤ C by omega), min_eq_left (show 1 ≤ C by omega),
    min_eq_left (show cnt ts 3 (ρ vR0) (ρ vU - ρ vR0) + 1 ≤ C by omega)]
  by_cases hl : isLeaf ts (ρ vU) = true <;>
    by_cases hd : ρ vD + cnt ts 4 (ρ vR0) (ρ vU - ρ vR0) ≤ cnt ts 3 (ρ vR0) (ρ vU - ρ vR0) <;>
    simp only [hl, hd, Bool.true_or, Bool.false_or, decide_true, decide_false, if_true,
      if_false] <;> split_ifs <;> omega

/-- The query program. -/
def queryP : Pr V := .seq tailP (.ite (.v vTc)
  (.seq (outToks [Tok.lpar]) (.seq eraseLoopP (.seq (outToks [Tok.rpar, Tok.lpar])
    (.seq (labLoopP false) (.seq (outToks [Tok.rpar, Tok.lpar]) (.seq (labLoopP true)
      (outToks [Tok.rpar])))))))
  (.seq (outToks [Tok.lpar]) (.seq trLoopP (.seq (outToks [Tok.rpar, Tok.lpar, Tok.rpar, Tok.lpar])
    (.seq lettersP (outToks [Tok.rpar]))))))

/-- Frame of `queryP`. -/
abbrev queryW : List (Fin V) :=
  [vLf, sR, sP, sC, sD, sI, vCa, vCr, vCi, vC4, vTc, vE, vK, vX, vT, vY, vE2, vK2,
    wC, wL, wD, wI, vC3, vK3, vZ, vZy, vZi, vE5, vK5, vX2, vK4, vLp, vE6, vK6,
    vE7, vK7, vX3, vF, vI3, vCd]

lemma sp_queryP (hE : Env ts q a C ρ) (hM : ρ vNq = ts.length + 1)
    (ha : (ts.length + 1) ^ 3 ≤ a.length) (hu : ρ vU ≤ ts.length) (hj : ρ vJ ≤ ts.length)
    (hr : ρ vR0 ≤ ts.length + 1) :
    Sp (pack (encodeToks ts) q a) C queryP ρ queryW
      (encodeToks (QP ts (ρ vR0) (ρ vD) (ρ vM) (ts.length + 1) (ρ vU) (ρ vLl) (ρ vJ)
        (ansF (ts.length + 1) a))) (fun _ => True) := by
  unfold queryP
  refine sp_seqE (o1 := []) (o2 := encodeToks (QP ts (ρ vR0) (ρ vD) (ρ vM) (ts.length + 1)
      (ρ vU) (ρ vLl) (ρ vJ) (ansF (ts.length + 1) a)))
    ((sp_tailP hE hu hr).mono (by decide) (fun _ _ h => h)) (fun ρ1 f1 h1 => ?_) (by simp)
  have g : ∀ v, v ∉ queryW → ρ1 v = ρ v := f1
  have hE1 := hE.of_frame g (by decide) (by decide)
  by_cases ht : tailCond ts (ρ vR0) (ρ vD) (ρ vU) = true
  · rw [QP, if_pos ht]
    refine sp_ite_pos (by simp [h1, ht]) ?_
    refine sp_seqE (sp_outToks (Q := fun r => r = ρ1) rfl) (fun ρ2 _ h2 => ?_)
      (o2 := encodeToks (eraseToks ts (ρ vJ)) ++ (encodeToks [Tok.rpar, Tok.lpar] ++
        (encodeToks (stemToks ts (ρ vU)) ++ (encodeToks [Tok.rpar, Tok.lpar] ++
          (encodeToks (leafToks ts (ρ vU)) ++ encodeToks [Tok.rpar])))))
      (by simp [encodeToks])
    subst h2
    refine sp_seqE ((sp_eraseLoopP hE1 (by rw [g _ (by decide)]; exact hj)).mono (by decide)
      (fun _ _ h => h)) (fun ρ3 f3 _ => ?_) (by rw [g _ (by decide)])
    have g3 : ∀ v, v ∉ queryW → ρ3 v = ρ v := fun v hv => (f3 v hv).trans (g v hv)
    have hE3 := hE.of_frame g3 (by decide) (by decide)
    refine sp_seqE (sp_outToks (Q := fun r => r = ρ3) rfl) (fun ρ4 _ h4 => ?_) rfl
    subst h4
    refine sp_seqE ((sp_labLoopP hE3 false (by rw [g3 _ (by decide)]; exact hu)).mono
      (by decide) (fun _ _ h => h)) (fun ρ5 f5 _ => ?_)
      (by rw [g3 _ (by decide), labAt_false]; rfl)
    have g5 : ∀ v, v ∉ queryW → ρ5 v = ρ v := fun v hv => (f5 v hv).trans (g3 v hv)
    have hE5 := hE.of_frame g5 (by decide) (by decide)
    refine sp_seqE (sp_outToks (Q := fun r => r = ρ5) rfl) (fun ρ6 _ h6 => ?_) rfl
    subst h6
    refine sp_seqE ((sp_labLoopP hE5 true (by rw [g5 _ (by decide)]; exact hu)).mono
      (by decide) (fun _ _ h => h)) (fun ρ7 _ _ => sp_outToks trivial)
      (by rw [g5 _ (by decide), labAt_true]; rfl)
  · rw [QP, if_neg ht]
    refine sp_ite_neg (by simp [h1, ht]) ?_
    refine sp_seqE (sp_outToks (Q := fun r => r = ρ1) rfl) (fun ρ2 _ h2 => ?_)
      (o2 := encodeToks (trToks ts (ρ vM) (ρ vJ)) ++
        (encodeToks [Tok.rpar, Tok.lpar, Tok.rpar, Tok.lpar] ++
        (encodeToks (letterToks ts (ρ vM) (ts.length + 1) (ρ vU) (ansF (ts.length + 1) a) (ρ vLl) ++
          rng (ρ vU) (tend ts (ρ vU) - ρ vU)
            (letterToks ts (ρ vM) (ts.length + 1) (ρ vU) (ansF (ts.length + 1) a))) ++
          encodeToks [Tok.rpar])))
      (by simp [encodeToks])
    subst h2
    refine sp_seqE ((sp_trLoopP hE1 (by rw [g _ (by decide)]; exact hj)).mono (by decide)
      (fun _ _ h => h)) (fun ρ3 f3 _ => ?_) (by rw [g vM (by decide), g vJ (by decide)])
    have g3 : ∀ v, v ∉ queryW → ρ3 v = ρ v := fun v hv => (f3 v hv).trans (g v hv)
    have hE3 := hE.of_frame g3 (by decide) (by decide)
    refine sp_seqE (sp_outToks (Q := fun r => r = ρ3) rfl) (fun ρ4 _ h4 => ?_) rfl
    subst h4
    refine sp_seqE ((sp_lettersP hE3 (by rw [g3 _ (by decide), hM]) ha
      (by rw [g3 _ (by decide)]; exact hu)).mono (by decide) (fun _ _ h => h))
      (fun ρ5 _ _ => sp_outToks trivial)
      (by rw [g3 vM (by decide), g3 vU (by decide), g3 vLl (by decide)])

end SQ

end PathChecking
