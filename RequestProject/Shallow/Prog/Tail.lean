module

public import RequestProject.Shallow.Prog.Emit

/-!
# Emitting the tail lasso

`labLoopP lf` emits `stemToks ts u` (`lf = false`) or `leafToks ts u` (`lf = true`) for the node
position `u` held in `vU`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ}

/-- `u` (node position of the query) -/
abbrev vU : Fin V := 28
/-- node position in `nodeP` -/
abbrev vY : Fin V := 29
/-- inner loop counter -/
abbrev vK2 : Fin V := 30
/-- inner length temporary -/
abbrev vE2 : Fin V := 31

/-- Labels of inner nodes (`lf = false`) or of leaves (`lf = true`). -/
def labAt (ts : List Tok) (lf : Bool) (i : ℕ) : List Tok :=
  if isNode ts i && (isLeaf ts i == lf) then labCopy ts i else []

lemma labAt_false (ts : List Tok) : labAt ts false = stemAt ts := by
  funext i; simp only [labAt, stemAt]; cases isLeaf ts i <;> simp

lemma labAt_true (ts : List Tok) : labAt ts true = leafAt ts := by
  funext i; simp only [labAt, leafAt]; cases isLeaf ts i <;> simp

/-- Copy the label of the node at `vY`. -/
def labCopyP : Pr V :=
  .seq (tendP (.bin .add (.v vY) (.c 1))) (.seq (.set vE2 (.bin .sub (.v sR) (.bin .add (.v vY) (.c 1))))
    (.loop vK2 (.v vE2) (cpP (.bin .add (.bin .add (.v vY) (.c 1)) (.v vK2)))))

/-- Variables written by `labCopyP`. -/
def labCopyW : List (Fin V) := [sR, sP, sC, sD, sI, vE2, vK2, vT]

lemma run_labCopyP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (hy : ρ vY ≤ ts.length) :
    ∃ ρ', labCopyP.run (pack (encodeToks ts) q a) C ρ =
        (ρ', encodeToks (labCopy ts (ρ vY))) ∧ ∀ v, v ∉ labCopyW → ρ' v = ρ v := by
  have hC := hE.len_le
  have hev : (Ex.bin .add (.v vY) (.c 1) : Ex V).eval (pack (encodeToks ts) q a) C ρ = ρ vY + 1 := by
    simp only [eval_bin, ap_add, eval_v, eval_c]
    simp (disch := omega) only [min_eq_left]
  obtain ⟨f1, f2⟩ := run_tendP hE (.bin .add (.v vY) (.c 1))
  rw [hev] at f1
  set ρ1 := ((tendP (.bin .add (.v vY) (.c 1))).run (pack (encodeToks ts) q a) C ρ).1
  have r1 : (tendP (.bin .add (.v vY) (.c 1))).run (pack (encodeToks ts) q a) C ρ = (ρ1, []) :=
    Prod.ext rfl f2
  have g1 : ∀ v, v ∉ labCopyW → ρ1 v = ρ v := fun v hv =>
    frame_of_sub (tendP_wr _) ρ v (fun h => hv (by simp [labCopyW] at h ⊢; omega))
  have hte : tend ts (ρ vY + 1) ≤ ts.length + 1 :=
    (scan_le _ _ _ _).trans (by omega)
  have hY1 : ρ1 vY = ρ vY := g1 vY (by decide)
  set ρ2 := Function.update ρ1 vE2 (tend ts (ρ vY + 1) - (ρ vY + 1))
  have r2 : (Pr.set vE2 (.bin .sub (.v sR) (.bin .add (.v vY) (.c 1)))).run
      (pack (encodeToks ts) q a) C ρ1 = (ρ2, []) := by
    simp only [run_set, eval_bin, ap_sub, ap_add, eval_v, eval_c, f1, hY1, ρ2]
    simp (disch := omega) only [min_eq_left]
  have g2 : ∀ v, v ∉ labCopyW → ρ2 v = ρ v := fun v hv => by
    simp only [ρ2]; rw [Function.update_of_ne (ne_of_nmem hv (by decide)), g1 v hv]
  obtain ⟨ρ3, r3, g3⟩ := run_rng (x := pack (encodeToks ts) q a) (C := C) vK2 (.v vE2)
    (cpP (.bin .add (.bin .add (.v vY) (.c 1)) (.v vK2))) ρ2 labCopyW (ρ vY + 1) (cp ts)
    (fun k hk ρ' hρ' => by
      simp only [eval_v, ρ2, Function.update_self] at hk
      have hE' : Env ts q a C (Function.update ρ' vK2 k) := hE.congr
        (by rw [Function.update_of_ne (by decide), hρ' _ (by decide), g2 _ (by decide)])
        (by rw [Function.update_of_ne (by decide), hρ' _ (by decide), g2 _ (by decide)])
      have hev' : (Ex.bin .add (.bin .add (.v vY) (.c 1)) (.v vK2) : Ex V).eval
          (pack (encodeToks ts) q a) C (Function.update ρ' vK2 k) = ρ vY + 1 + k := by
        simp only [eval_bin, ap_add, eval_v, eval_c, Function.update_self,
          Function.update_of_ne (show vY ≠ vK2 by decide), hρ' vY (by decide), g2 vY (by decide)]
        simp (disch := omega) only [min_eq_left]
      obtain ⟨ρ'', h1, h2⟩ := run_cpP hE' (.bin .add (.bin .add (.v vY) (.c 1)) (.v vK2))
      rw [hev'] at h1
      refine ⟨ρ'', h1, fun v hv => ?_⟩
      rw [h2 v (ne_of_nmem hv (by decide)), Function.update_of_ne (ne_of_nmem hv (by decide)),
        hρ' v hv, g2 v hv])
  refine ⟨ρ3, ?_, fun v hv => by rw [g3 v hv, g2 v hv]⟩
  unfold labCopyP
  rw [seq_eq r1 (seq_eq r2 r3)]
  simp [ρ2, labCopy]

/-- `isNode` at `vY`, as an expression with values in `{0, 1}`. -/
def isNodeE : Ex V :=
  .bin .mul (.bin .eq (tokE (.v vY)) (.c 3)) (.bin .eq (tokE (.bin .add (.v vY) (.c 1))) (.c 3))

/-- Emit `labAt ts lf p`. -/
def nodeP (lf : Bool) (p : Ex V) : Pr V :=
  .seq (.set vY p) (.seq (isLeafP (.v vY))
    (.ite (.bin .mul isNodeE (.bin .eq (.v vLf) (.c (if lf then 1 else 0)))) labCopyP .skip))

/-- Variables written by `nodeP`. -/
def nodeW : List (Fin V) := [vY, vLf, sR, sP, sC, sD, sI, vE2, vK2, vT]

lemma labCopyW_sub : ∀ z ∈ labCopyW, z ∈ nodeW := by decide

lemma run_nodeP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (lf : Bool) (p : Ex V)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ < ts.length) :
    ∃ ρ', (nodeP lf p).run (pack (encodeToks ts) q a) C ρ =
        (ρ', encodeToks (labAt ts lf (p.eval (pack (encodeToks ts) q a) C ρ))) ∧
      ∀ v, v ∉ nodeW → ρ' v = ρ v := by
  have hC := hE.len_le
  unfold nodeP
  rw [run_seq, run_set]
  generalize p.eval (pack (encodeToks ts) q a) C ρ = pv at hp ⊢
  set ρ1 := Function.update ρ vY pv
  have hE1 : Env ts q a C ρ1 :=
    hE.congr (Function.update_of_ne (by decide) _ _) (Function.update_of_ne (by decide) _ _)
  obtain ⟨l1, l2⟩ := run_isLeafP hE1 (.v vY) (by simp [ρ1]; omega)
  set ρ2 := ((isLeafP (.v vY)).run (pack (encodeToks ts) q a) C ρ1).1
  have r2 : (isLeafP (.v vY)).run (pack (encodeToks ts) q a) C ρ1 = (ρ2, []) := Prod.ext rfl l2
  have g2 : ∀ v, v ∉ nodeW → ρ2 v = ρ v := fun v hv => by
    simp only [ρ2]
    rw [frame_of_sub (isLeafP_wr _) ρ1 v (fun h => hv (by simp [nodeW] at h ⊢; omega))]
    simp only [ρ1]; rw [Function.update_of_ne (ne_of_nmem hv (by decide))]
  have hY2 : ρ2 vY = pv := by
    simp only [ρ2]; rw [frame_of_sub (isLeafP_wr _) ρ1 vY (by decide)]; simp [ρ1]
  have hE2 : Env ts q a C ρ2 := hE.congr (g2 _ (by decide)) (g2 _ (by decide))
  simp only [eval_v, ρ1, Function.update_self] at l1
  have hnode : isNodeE.eval (pack (encodeToks ts) q a) C ρ2 = if isNode ts pv then 1 else 0 := by
    have hY1 : (Ex.bin .add (.v vY) (.c 1) : Ex V).eval (pack (encodeToks ts) q a) C ρ2 = pv + 1 := by
      simp only [eval_bin, ap_add, eval_v, eval_c, hY2]
      simp (disch := omega) only [min_eq_left]
    simp only [isNodeE, eval_bin, ap_mul, ap_eq, eval_c, eval_tokE_v hE2 vY (by omega), hY2,
      min_eq_left (show 3 ≤ C by omega)]
    rw [eval_tokE ts q a C ρ2 _ hE2.hq hE2.hC hE2.hN (by rw [hY1]; omega), hY1]
    simp only [isNode, Bool.and_eq_true, beq_iff_eq]
    by_cases h1 : tc ts pv = 3 <;> by_cases h2 : tc ts (pv + 1) = 3 <;> simp [h1, h2]; omega
  have hcond : (Ex.bin .mul isNodeE (.bin .eq (.v vLf) (.c (if lf then 1 else 0))) : Ex V).eval
      (pack (encodeToks ts) q a) C ρ2 =
        if (isNode ts pv && (isLeaf ts pv == lf)) then 1 else 0 := by
    simp only [eval_bin, ap_mul, ap_eq, eval_v, eval_c, hnode, l1]
    rw [min_eq_left (show (if lf = true then 1 else 0) ≤ C by split_ifs <;> omega)]
    cases lf <;> cases isNode ts pv <;> cases isLeaf ts pv <;> simp <;> omega
  by_cases hc : (isNode ts pv && (isLeaf ts pv == lf)) = true
  · rw [seq_eq r2 (run_ite_pos (by rw [hcond, if_pos hc]; simp))]
    obtain ⟨ρ3, r3, g3⟩ := run_labCopyP hE2 (by rw [hY2]; omega)
    rw [r3, hY2]
    refine ⟨ρ3, by simp [labAt, hc], fun v hv => ?_⟩
    rw [g3 v (fun h => hv (labCopyW_sub v h)), g2 v hv]
  · rw [seq_eq r2 (run_ite_neg (by rw [hcond, if_neg hc]))]
    refine ⟨ρ2, by simp [labAt, hc]; rfl, g2⟩

/-- Emit `rng u (tend ts u - u) (labAt ts lf)` (`u` in `vU`). -/
def labLoopP (lf : Bool) : Pr V :=
  .seq (tendP (.v vU)) (.seq (.set vE (.bin .sub (.v sR) (.v vU)))
    (.loop vK (.v vE) (nodeP lf (.bin .add (.v vU) (.v vK)))))

/-- Variables written by `labLoopP`. -/
def labLoopW : List (Fin V) := [vE, vK, vY, vLf, sR, sP, sC, sD, sI, vE2, vK2, vT]

lemma nodeW_sub : ∀ z ∈ nodeW, z ∈ labLoopW := by decide

lemma scanW_sub_labLoopW : ∀ z ∈ scanW, z ∈ labLoopW := by decide

lemma run_labLoopP {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (lf : Bool) (hu : ρ vU ≤ ts.length) :
    ∃ ρ', (labLoopP lf).run (pack (encodeToks ts) q a) C ρ =
        (ρ', encodeToks (rng (ρ vU) (tend ts (ρ vU) - ρ vU) (labAt ts lf))) ∧
      ∀ v, v ∉ labLoopW → ρ' v = ρ v := by
  have hC := hE.len_le
  obtain ⟨f1, f2⟩ := run_tendP hE (.v vU)
  set ρ1 := ((tendP (.v vU)).run (pack (encodeToks ts) q a) C ρ).1
  have r1 : (tendP (.v vU)).run (pack (encodeToks ts) q a) C ρ = (ρ1, []) := Prod.ext rfl f2
  have g1 : ∀ v, v ∉ labLoopW → ρ1 v = ρ v := fun v hv =>
    frame_of_sub (tendP_wr _) ρ v (fun h => hv (scanW_sub_labLoopW v h))
  have hte : tend ts (ρ vU) ≤ ts.length := (scan_le _ _ _ _).trans (by omega)
  have hU1 : ρ1 vU = ρ vU := g1 vU (by decide)
  set ρ2 := Function.update ρ1 vE (tend ts (ρ vU) - ρ vU)
  have r2 : (Pr.set vE (.bin .sub (.v sR) (.v vU))).run (pack (encodeToks ts) q a) C ρ1 =
      (ρ2, []) := by
    simp only [run_set, eval_bin, ap_sub, eval_v, f1, hU1, ρ2]
  have g2 : ∀ v, v ∉ labLoopW → ρ2 v = ρ v := fun v hv => by
    simp only [ρ2]; rw [Function.update_of_ne (ne_of_nmem hv (by decide)), g1 v hv]
  obtain ⟨ρ3, r3, g3⟩ := run_rng (x := pack (encodeToks ts) q a) (C := C) vK (.v vE)
    (nodeP lf (.bin .add (.v vU) (.v vK))) ρ2 labLoopW (ρ vU) (labAt ts lf) (fun k hk ρ' hρ' => by
      simp only [eval_v, ρ2, Function.update_self] at hk
      have hE' : Env ts q a C (Function.update ρ' vK k) := hE.congr
        (by rw [Function.update_of_ne (by decide), hρ' _ (by decide), g2 _ (by decide)])
        (by rw [Function.update_of_ne (by decide), hρ' _ (by decide), g2 _ (by decide)])
      have hev : (Ex.bin .add (.v vU) (.v vK) : Ex V).eval (pack (encodeToks ts) q a) C
          (Function.update ρ' vK k) = ρ vU + k := by
        simp only [eval_bin, ap_add, eval_v, Function.update_self,
          Function.update_of_ne (show vU ≠ vK by decide), hρ' vU (by decide), g2 vU (by decide)]
        exact min_eq_left (by omega)
      obtain ⟨ρ'', h1, h2⟩ := run_nodeP hE' lf _ (by rw [hev]; omega)
      rw [hev] at h1
      refine ⟨ρ'', h1, fun v hv => ?_⟩
      rw [h2 v (fun h => hv (nodeW_sub v h)),
        Function.update_of_ne (ne_of_nmem hv (by decide)), hρ' v hv, g2 v hv])
  refine ⟨ρ3, ?_, fun v hv => by rw [g3 v hv, g2 v hv]⟩
  unfold labLoopP
  rw [seq_eq r1 (seq_eq r2 r3)]
  simp [ρ2]

end SQ

end PathChecking
