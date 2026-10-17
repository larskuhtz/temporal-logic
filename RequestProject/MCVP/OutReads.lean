module

public import RequestProject.MCVP.OutFormula

/-!
# Streaming the labels of register nodes

The label of `R_g` (sorted) consists of a head part (`act_g` and possibly `init`) and the
numbers `in_k = 4k + 3` for all gates `k` reading `g`, in increasing order of `k`.  For the
latter the program loops over `k = 0, …, n-1`, locates gate `k` and compares its arguments with
`g`.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-! ## Token lists -/

/-- Head part of the label of `R_g`. -/
def headToks (C : List MGate) (g : ℕ) : List Tok :=
  if g = 0 then natToks 1 ++ (if (gateAt C g).isTrue then natToks 4 else [])
  else (if (gateAt C g).isTrue then natToks 4 else []) ++ natToks (4 * g + 1)

/-- Contribution of gate `k` to the label of `R_g`. -/
def readsToks (C : List MGate) (g k : ℕ) : List Tok :=
  if (gateAt C k).reads g then natToks (4 * k + 3) else []

lemma reads_flatMap (C : List MGate) (g n : ℕ) :
    (((List.range n).filter (fun k => decide ((gateAt C k).reads g))).map aIn).flatMap natToks =
      (List.range n).flatMap (readsToks C g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.flatMap_append, ih,
      List.flatMap_append]
    congr 1
    by_cases h : (gateAt C n).reads g <;> simp [h, readsToks, aIn]

lemma labelList_flatMap (C : List MGate) (g : ℕ) :
    (labelList C g).flatMap natToks = headToks C g ++ (List.range C.length).flatMap (readsToks C g) := by
  rw [labelList, List.flatMap_append, reads_flatMap]
  congr 1
  unfold headToks
  split_ifs <;> simp [aAct, aInit]

lemma treeBlock_eq {C : List MGate} (hC : WellFormed C) (g : ℕ) :
    treeBlock C g = [Tok.lpar, Tok.lpar] ++ headToks C g ++
      (List.range C.length).flatMap (readsToks C g) ++
      ([Tok.rpar] ++ sideLeaf.toks ++ [Tok.lpar, Tok.lpar]) ++ natToks (4 * g + 2) ++ [Tok.rpar] := by
  rw [treeBlock, finsetToks_regLabel hC, labelList_flatMap]
  simp

/-! ## Comparing arguments -/

lemma cmpRes_valid {p y i : ℕ} {σ τ : St 20} (hres : CmpRes w p y σ τ)
    (hAt : At w p (encodeToks (natToks i))) :
    τ.pos = p + 5 * (natToks i).length ∧ (τ.reg rEq ≠ 0 ↔ i = y) := by
  rcases hres with ⟨ds, hnum, hpos, -, -, heq, -⟩ | ⟨-, hno⟩
  · obtain rfl := NumAt.unique hnum (numAt_natToks.1 hAt)
    rw [hpos, natToks_length, heq, ofBits_bits]
    exact ⟨rfl, Iff.rfl⟩
  · exact absurd (numAt_natToks.1 hAt) (hno _)

/-- Read the two arguments of a gate and emit `in_k` if one of them is `g`. -/
def readsCheck : Stmt 20 :=
  cmpNum rK ⨟ clear rFl ⨟ .ite (.zero rEq) .skip (.inc rFl) ⨟ cmpNum rK ⨟
  .ite (.zero rFl) (.ite (.zero rEq) .skip (emitNum rCnt 3)) (emitNum rCnt 3)

/-- Registers modified by `readsCheck`. -/
def rcClob : List (Fin 20) := rFl :: (cmpClob ++ numClob)

lemma rK_not_mem_cmpClob : rK ∉ cmpClob := by decide
lemma rCnt_not_mem_numClob : rCnt ∉ numClob := by decide

lemma ach_readsCheck (σ : St 20) (Q : St 20 → Prop) (i j : ℕ)
    (hAt : At w σ.pos (encodeToks (natToks i ++ natToks j)))
    (hB : 4 * σ.reg rCnt + 3 ≤ B) (hK : σ.reg rK ≤ B) (hB1 : 1 ≤ B)
    (h : ∀ τ : St 20, τ.out = σ.out ++
        encodeToks (if i = σ.reg rK ∨ j = σ.reg rK then natToks (4 * σ.reg rCnt + 3) else []) →
      (∀ x, x ∉ rcClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B readsCheck σ Q := by
  obtain ⟨hAi, hAj⟩ := At.toks_append.1 hAt
  have hle1 := hAi.le
  have hle2 := hAj.le
  rw [encodeToks_length] at hle1 hle2
  unfold readsCheck
  refine ach_seq (ach_cmpNum rK rK_not_mem_cmpClob σ _ hAi.1 (by omega) hK hB1 ?_)
  intro τ₁ ho₁ hq1 hq2 hf₁ hres₁
  obtain ⟨hp₁, he₁⟩ := cmpRes_valid hres₁ hAi
  have hK1 : τ₁.reg rK = σ.reg rK := hf₁ rK rK_not_mem_cmpClob
  have hC1 : τ₁.reg rCnt = σ.reg rCnt := hf₁ rCnt (by decide)
  -- set the flag
  have step2 : ∀ τ₂ : St 20, τ₂.pos = τ₁.pos → τ₂.out = τ₁.out →
      (∀ x, x ≠ rFl → τ₂.reg x = τ₁.reg x) → (τ₂.reg rFl ≠ 0 ↔ i = σ.reg rK) →
      Ach w B (cmpNum rK ⨟ .ite (.zero rFl) (.ite (.zero rEq) .skip (emitNum rCnt 3))
        (emitNum rCnt 3)) τ₂ Q := by
    intro τ₂ hp₂ ho₂ hf₂ hfl
    have hK2 : τ₂.reg rK = σ.reg rK := (hf₂ rK (by decide)).trans hK1
    have hC2 : τ₂.reg rCnt = σ.reg rCnt := (hf₂ rCnt (by decide)).trans hC1
    refine ach_seq (ach_cmpNum rK rK_not_mem_cmpClob τ₂ _ (by omega) (by omega) (by omega) hB1 ?_)
    intro τ₃ ho₃ _ _ hf₃ hres₃
    obtain ⟨-, he₃⟩ := cmpRes_valid hres₃ (by rw [hp₂, hp₁]; exact hAj)
    have hK3 : τ₃.reg rK = σ.reg rK := (hf₃ rK rK_not_mem_cmpClob).trans hK2
    rw [hK2] at he₃
    have hC3 : τ₃.reg rCnt = σ.reg rCnt := (hf₃ rCnt (by decide)).trans hC2
    have hFl3 : τ₃.reg rFl = τ₂.reg rFl := hf₃ rFl (by decide)
    have hfr : ∀ x, x ∉ rcClob → τ₃.reg x = σ.reg x := by
      intro x hx
      simp only [rcClob, List.mem_cons, List.mem_append, not_or] at hx
      rw [hf₃ x hx.2.1, hf₂ x hx.1, hf₁ x hx.2.1]
    have emit : (i = σ.reg rK ∨ j = σ.reg rK) → Ach w B (emitNum rCnt 3) τ₃ Q := by
      intro hc
      refine ach_emitNum rCnt rCnt_not_mem_numClob 3 τ₃ _ (by omega) hB1 ?_
      intro τ' _ ho' hf'
      refine h τ' ?_ ?_
      · rw [ho', ho₃, ho₂, ho₁, hC3, if_pos hc]
      · intro x hx
        simp only [rcClob, List.mem_cons, List.mem_append, not_or] at hx
        rw [hf' x hx.2.2, hfr x (by simp [rcClob, hx.1, hx.2.1, hx.2.2])]
    refine ach_ite ?_
    by_cases hF : τ₃.reg rFl = 0
    · rw [if_pos (by simp [Cond.eval, hF])]
      have hi : i ≠ σ.reg rK := fun hi => hfl.2 hi (by rw [← hFl3]; exact hF)
      refine ach_ite ?_
      by_cases hE : τ₃.reg rEq = 0
      · rw [if_pos (by simp [Cond.eval, hE])]
        have hj : j ≠ σ.reg rK := fun hj => (he₃.2 hj) hE
        refine ach_skip (h τ₃ ?_ hfr)
        rw [ho₃, ho₂, ho₁, if_neg (by tauto)]; simp [encodeToks]
      · rw [if_neg (by simp [Cond.eval, hE])]
        exact emit (Or.inr (he₃.1 hE))
    · rw [if_neg (by simp [Cond.eval, hF])]
      exact emit (Or.inl (hfl.1 (by rw [← hFl3]; exact hF)))
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_ite ?_)))
  by_cases hE : τ₁.reg rEq = 0
  · rw [if_pos (by simp [Cond.eval, St.setReg_apply, hE])]
    refine ach_skip (step2 _ (by simp) (by simp) (fun x hx => by simp [St.setReg_apply, hx]) ?_)
    simp only [St.setReg_apply, if_true, ne_eq, not_true_eq_false, false_iff]
    intro hi; exact (he₁.2 hi) hE
  · rw [if_neg (by simp [Cond.eval, St.setReg_apply, hE])]
    refine ach_inc (by simp; omega) (step2 _ (by simp) (by simp)
      (fun x hx => by simp [St.setReg_apply, hx]) ?_)
    simp only [St.setReg_apply, if_true]
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, true_iff]
    exact he₁.1 hE

end MCVPReduction

end PathChecking
