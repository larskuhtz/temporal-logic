module

public import RequestProject.MCVP.OutReads

/-!
# Streaming the tree

For `g = n-1, …, 0` the program emits the block of the tree belonging to gate `g` (opening of
the register node `R_g` with its sorted label and side leaf, opening of the dummy node `D_g`
with its label), and finally the `2n` closing brackets.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

lemma length_le_word {C : List MGate} (hw : w = encodeCircuit C) : C.length ≤ w.length := by
  have := length_le_toks C
  have := encodeCircuit_length C
  rw [← hw] at this; omega

/-! ## The loop over the gates reading `g` -/

/-- Action on the first token of gate `rCnt`. -/
def readsTok (t : Tok) : Stmt 20 := if t = .tag 2 ∨ t = .tag 3 then readsCheck else .skip

/-- Locate gate `rCnt` and emit `in_{rCnt}` if it reads gate `rK`. -/
def readsBody : Stmt 20 := locate rCnt ⨟ caseTok readsTok .skip

/-- Registers modified by `readsBody`. -/
def rbClob : List (Fin 20) := locClob ++ rcClob

lemma ach_readsBody {C : List MGate} (hw : w = encodeCircuit C) (τ : St 20) (Q : St 20 → Prop)
    (hk : τ.reg rCnt < C.length) (hB : 4 * w.length + 4 ≤ B) (hK : τ.reg rK ≤ B)
    (h : ∀ τ' : St 20, τ'.out = τ.out ++ encodeToks (readsToks C (τ.reg rK) (τ.reg rCnt)) →
      (∀ x, x ∉ rbClob → τ'.reg x = τ.reg x) → Q τ') :
    Ach w B readsBody τ Q := by
  have hCw := length_le_word hw
  unfold readsBody
  refine ach_seq (ach_locate rCnt (by decide) hw τ _ hk.le (by omega) ?_)
  intro τ₁ hp ho hf
  have hk1 : τ₁.reg rCnt = τ.reg rCnt := hf rCnt (by decide)
  have hK1 : τ₁.reg rK = τ.reg rK := hf rK (by decide)
  have hAt := gate_at_index hw hk
  rw [← hp] at hAt
  have hfr : ∀ τ' : St 20, (∀ x, x ∉ rcClob → τ'.reg x = τ₁.reg x) →
      ∀ x, x ∉ rbClob → τ'.reg x = τ.reg x := by
    intro τ' h' x hx
    simp only [rbClob, List.mem_append, not_or] at hx
    rw [h' x hx.2, hf x hx.1]
  cases hG : gateAt C (τ.reg rCnt) with
  | input b =>
    rw [hG] at hAt
    have hr : readsToks C (τ.reg rK) (τ.reg rCnt) = [] := by
      simp [readsToks, hG, MGate.reads]
    cases b
    · refine ach_caseTok_pos _ _ _ τ₁ (.tag 0) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [readsTok, Tok.tag.injEq]
      exact ach_skip (h _ (by simp [hr, ho, encodeToks]) (hfr _ (fun _ _ => rfl)))
    · refine ach_caseTok_pos _ _ _ τ₁ (.tag 1) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [readsTok, Tok.tag.injEq]
      exact ach_skip (h _ (by simp [hr, ho, encodeToks]) (hfr _ (fun _ _ => rfl)))
  | and i j =>
    rw [hG] at hAt
    have hc := At.toks_cons.1 (by simpa [MGate.toks] using hAt)
    refine ach_caseTok_pos _ _ _ τ₁ (.tag 2) hc.1 ?_
    simp only [readsTok, true_or, if_true]
    refine ach_readsCheck _ _ i j hc.2 (by simp; omega) (by simp; omega) (by omega) ?_
    intro τ' h1 h2
    refine h τ' ?_ (hfr _ h2)
    rw [h1, ho]; simp [readsToks, hG, MGate.reads, hk1, hK1, eq_comm]
  | or i j =>
    rw [hG] at hAt
    have hc := At.toks_cons.1 (by simpa [MGate.toks] using hAt)
    refine ach_caseTok_pos _ _ _ τ₁ (.tag 3) hc.1 ?_
    simp only [readsTok, or_true, if_true]
    refine ach_readsCheck _ _ i j hc.2 (by simp; omega) (by simp; omega) (by omega) ?_
    intro τ' h1 h2
    refine h τ' ?_ (hfr _ h2)
    rw [h1, ho]; simp [readsToks, hG, MGate.reads, hk1, hK1, eq_comm]

/-- Loop over all gates `k = 0, …, n-1`, emitting `in_k` for those reading gate `rK`. -/
def readsLoop : Stmt 20 := clear rCnt ⨟ copy rN rCnt2 rTmp ⨟ forUp rCnt rCnt2 readsBody

/-- Registers modified by `readsLoop`. -/
def rlClob : List (Fin 20) := rCnt :: rCnt2 :: rbClob

lemma ach_readsLoop {C : List MGate} (hw : w = encodeCircuit C) (σ : St 20) (Q : St 20 → Prop)
    (hN : σ.reg rN = C.length) (hB : 4 * w.length + 4 ≤ B) (hK : σ.reg rK ≤ B)
    (h : ∀ τ : St 20,
      τ.out = σ.out ++ encodeToks ((List.range C.length).flatMap (readsToks C (σ.reg rK))) →
      (∀ x, x ∉ rlClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B readsLoop σ Q := by
  have hCw := length_le_word hw
  set N := C.length
  unfold readsLoop
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_copy rN rCnt2 rTmp (by decide) (by decide)
    (by decide) _ _ (by simp [St.setReg_apply]; omega) ?_)))
  refine ach_forUp rCnt rCnt2 (by decide) readsBody (fun j τ => τ.out = σ.out ++
      encodeToks ((List.range j).flatMap (readsToks C (σ.reg rK))) ∧
      ∀ x, x ∉ rlClob → τ.reg x = σ.reg x) Q N _ ⟨by simp [encodeToks], ?_⟩
    (by simp [St.setReg_apply]) (by simp [St.setReg_apply, hN]) (by omega) ?_
    (fun τ hP => h τ hP.1 hP.2)
  · intro x hx
    simp only [rlClob, rbClob, locClob, rcClob, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false, not_or] at hx
    simp [St.setReg_apply, hx.1, hx.2.1, hx.2.2.1.2.1]
  · intro j hj τ ⟨ho, hf⟩ hi hc
    have hKτ : τ.reg rK = σ.reg rK := hf rK (by decide)
    refine ach_readsBody hw τ _ (by omega) hB (by omega) ?_
    intro τ' h1 h2
    refine ⟨by rw [h2 rCnt (by decide), hi], by rw [h2 rCnt2 (by decide), hc], ?_, ?_⟩
    · simp only [St.setReg_out]
      rw [h1, ho, hKτ, hi, List.range_succ, List.flatMap_append, encodeToks_append]
      simp
    · intro x hx
      simp only [rlClob, List.mem_cons, not_or] at hx
      simp only [St.setReg_apply, if_neg hx.1, if_neg hx.2.1]
      rw [h2 x hx.2.2, hf x (by simp [rlClob, hx.1, hx.2.1, hx.2.2])]

/-! ## The head of a label -/

/-- `rFl := [gate rK is the constant true]`. -/
def trueFlag : Stmt 20 :=
  locate rK ⨟ clear rFl ⨟ caseTok (fun t => if t = .tag 1 then .inc rFl else .skip) .skip

lemma ach_trueFlag {C : List MGate} (hw : w = encodeCircuit C) (τ : St 20) (Q : St 20 → Prop)
    (hk : τ.reg rK < C.length) (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ' : St 20, τ'.out = τ.out → (τ'.reg rFl ≠ 0 ↔ (gateAt C (τ.reg rK)).isTrue) →
      (∀ x, x ∉ rFl :: locClob → τ'.reg x = τ.reg x) → Q τ') :
    Ach w B trueFlag τ Q := by
  have hCw := length_le_word hw
  unfold trueFlag
  refine ach_seq (ach_locate rK rK_not_mem_locClob hw τ _ hk.le (by omega) ?_)
  intro τ₁ hp ho hf
  have hAt := gate_at_index hw hk
  rw [← hp] at hAt
  refine ach_seq (ach_clear _ _ _ ?_)
  have hfr : ∀ τ' : St 20, (∀ x, x ≠ rFl → τ'.reg x = τ₁.reg x) →
      ∀ x, x ∉ rFl :: locClob → τ'.reg x = τ.reg x := by
    intro τ' h' x hx
    simp only [List.mem_cons, not_or] at hx
    rw [h' x hx.1, hf x hx.2]
  cases hG : gateAt C (τ.reg rK) with
  | input b =>
    rw [hG] at hAt
    cases b
    · refine ach_caseTok_pos _ _ _ _ (.tag 0) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [Tok.tag.injEq]
      exact ach_skip (h _ (by simp [ho]) (by simp [St.setReg_apply, MGate.isTrue, hG])
        (hfr _ (fun x hx => by simp [St.setReg_apply, hx])))
    · refine ach_caseTok_pos _ _ _ _ (.tag 1) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [if_true]
      exact ach_inc (by simp; omega) (h _ (by simp [ho]) (by simp [St.setReg_apply, MGate.isTrue, hG])
        (hfr _ (fun x hx => by simp [St.setReg_apply, hx])))
  | and i j =>
    rw [hG] at hAt
    refine ach_caseTok_pos _ _ _ _ (.tag 2) (At.toks_cons.1 (by simpa [MGate.toks] using hAt)).1 ?_
    simp only [Tok.tag.injEq]
    exact ach_skip (h _ (by simp [ho]) (by simp [St.setReg_apply, MGate.isTrue, hG])
      (hfr _ (fun x hx => by simp [St.setReg_apply, hx])))
  | or i j =>
    rw [hG] at hAt
    refine ach_caseTok_pos _ _ _ _ (.tag 3) (At.toks_cons.1 (by simpa [MGate.toks] using hAt)).1 ?_
    simp only [Tok.tag.injEq]
    exact ach_skip (h _ (by simp [ho]) (by simp [St.setReg_apply, MGate.isTrue, hG])
      (hfr _ (fun x hx => by simp [St.setReg_apply, hx])))

/-- Emit the head part of the label of `R_{rK}`, given the flag `rFl`. -/
def headProg : Stmt 20 :=
  .ite (.zero rK) (emitNum rK 1 ⨟ .ite (.zero rFl) .skip (emitToks (natToks 4)))
    (.ite (.zero rFl) .skip (emitToks (natToks 4)) ⨟ emitNum rK 1)

lemma ach_headProg (C : List MGate) (τ : St 20) (Q : St 20 → Prop)
    (hB : 4 * τ.reg rK + 1 ≤ B) (hB1 : 1 ≤ B)
    (hfl : τ.reg rFl ≠ 0 ↔ (gateAt C (τ.reg rK)).isTrue)
    (h : ∀ τ' : St 20, τ'.out = τ.out ++ encodeToks (headToks C (τ.reg rK)) →
      (∀ x, x ∉ numClob → τ'.reg x = τ.reg x) → Q τ') :
    Ach w B headProg τ Q := by
  unfold headProg
  refine ach_ite ?_
  by_cases hk : τ.reg rK = 0
  · rw [if_pos (by simp [Cond.eval, hk])]
    refine ach_seq (ach_emitNum rK rK_not_mem_numClob 1 τ _ hB hB1 ?_)
    intro τ₁ _ ho hf
    have hfl1 : τ₁.reg rFl = τ.reg rFl := hf rFl (by decide)
    refine ach_ite ?_
    by_cases hF : τ.reg rFl = 0
    · rw [if_pos (by simp [Cond.eval, hfl1, hF])]
      refine ach_skip (h τ₁ ?_ hf)
      have : ¬ (gateAt C (τ.reg rK)).isTrue := fun h' => hfl.2 h' hF
      rw [ho, headToks, if_pos hk, if_neg this, hk]; simp
    · rw [if_neg (by simp [Cond.eval, hfl1, hF])]
      refine ach_emitToks _ _ _ (h _ ?_ (fun x hx => by simpa using hf x hx))
      have : (gateAt C (τ.reg rK)).isTrue := hfl.1 hF
      rw [ho, headToks, if_pos hk, if_pos this, hk]; simp [encodeToks_append]
  · rw [if_neg (by simp [Cond.eval, hk])]
    have tail : ∀ τ₁ : St 20, τ₁.reg rK = τ.reg rK →
        (∀ x, x ∉ numClob → τ₁.reg x = τ.reg x) →
        τ₁.out = τ.out ++ encodeToks (if (gateAt C (τ.reg rK)).isTrue then natToks 4 else []) →
        Ach w B (emitNum rK 1) τ₁ Q := by
      intro τ₁ h1 h2 h3
      refine ach_emitNum rK rK_not_mem_numClob 1 τ₁ _ (by omega) hB1 ?_
      intro τ' _ ho hf
      refine h τ' ?_ (fun x hx => (hf x hx).trans (h2 x hx))
      rw [ho, h3, h1, headToks, if_neg hk]; simp [encodeToks_append]
    refine ach_seq (ach_ite ?_)
    by_cases hF : τ.reg rFl = 0
    · rw [if_pos (by simp [Cond.eval, hF])]
      have : ¬ (gateAt C (τ.reg rK)).isTrue := fun h' => hfl.2 h' hF
      exact ach_skip (tail τ rfl (fun _ _ => rfl) (by simp [this, encodeToks]))
    · rw [if_neg (by simp [Cond.eval, hF])]
      have : (gateAt C (τ.reg rK)).isTrue := hfl.1 hF
      exact ach_emitToks _ _ _ (tail _ rfl (fun _ _ => rfl) (by simp [this]))

/-! ## One block of the tree -/

/-- Emit the block of the tree belonging to gate `rK`. -/
def treeBody : Stmt 20 :=
  emitToks [.lpar, .lpar] ⨟ trueFlag ⨟ headProg ⨟ readsLoop ⨟
  emitToks ([.rpar] ++ sideLeaf.toks ++ [.lpar, .lpar]) ⨟ emitNum rK 2 ⨟ emitToks [.rpar]

/-- Registers modified by `treeBody`. -/
def tbClob : List (Fin 20) := rFl :: (locClob ++ numClob ++ rlClob)

lemma ach_treeBody {C : List MGate} (hw : w = encodeCircuit C) (hwf : WellFormed C) (τ : St 20)
    (Q : St 20 → Prop) (hk : τ.reg rK < C.length) (hN : τ.reg rN = C.length)
    (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ' : St 20, τ'.out = τ.out ++ encodeToks (treeBlock C (τ.reg rK)) →
      (∀ x, x ∉ tbClob → τ'.reg x = τ.reg x) → Q τ') :
    Ach w B treeBody τ Q := by
  have hCw := length_le_word hw
  unfold treeBody
  refine ach_seq (ach_emitToks _ _ _ (ach_seq (ach_trueFlag hw _ _ (by simpa using hk) hB ?_)))
  intro τ₁ ho₁ hfl hf₁
  have hK1 : τ₁.reg rK = τ.reg rK := hf₁ rK (by decide)
  refine ach_seq (ach_headProg C τ₁ _ (by omega) (by omega) (by rw [hK1]; simpa using hfl) ?_)
  intro τ₂ ho₂ hf₂
  have hK2 : τ₂.reg rK = τ.reg rK := (hf₂ rK (by decide)).trans hK1
  have hN2 : τ₂.reg rN = C.length := by
    rw [hf₂ rN (by decide), hf₁ rN (by decide)]; simpa using hN
  refine ach_seq (ach_readsLoop hw τ₂ _ hN2 hB (by omega) ?_)
  intro τ₃ ho₃ hf₃
  have hK3 : τ₃.reg rK = τ.reg rK := (hf₃ rK (by decide)).trans hK2
  refine ach_seq (ach_emitToks _ _ _ (ach_seq (ach_emitNum rK rK_not_mem_numClob 2 _ _
    (by simp; omega) (by omega) ?_)))
  intro τ₄ _ ho₄ hf₄
  refine ach_emitToks _ _ _ (h _ ?_ ?_)
  · simp only [ho₄, ho₃, ho₂, ho₁, hK3, hK2, hK1, List.append_assoc]
    rw [treeBlock_eq hwf]
    simp only [← encodeToks_append, List.append_assoc]
  · intro x hx
    simp only [tbClob, List.mem_cons, List.mem_append, not_or] at hx
    simp only
    rw [hf₄ x hx.2.1.2, hf₃ x hx.2.2, hf₂ x hx.2.1.2, hf₁ x (by simp [hx.1, hx.2.1.1])]

/-! ## The whole tree -/

/-- Emit the blocks of all gates, from the last gate down to gate `0`. -/
def treeLoop : Stmt 20 := copy rN rK rTmp ⨟ forDown rK treeBody

/-- Registers modified by `treeLoop`. -/
def tlClob : List (Fin 20) := rK :: tbClob

lemma ach_treeLoop {C : List MGate} (hw : w = encodeCircuit C) (hwf : WellFormed C) (σ : St 20)
    (Q : St 20 → Prop) (hN : σ.reg rN = C.length) (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ : St 20,
      τ.out = σ.out ++ encodeToks ((List.range C.length).reverse.flatMap (treeBlock C)) →
      (∀ x, x ∉ tlClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B treeLoop σ Q := by
  have hCw := length_le_word hw
  set N := C.length
  unfold treeLoop
  refine ach_seq (ach_copy rN rK rTmp (by decide) (by decide) (by decide) σ _ (by omega) ?_)
  refine ach_forDown rK treeBody (fun j τ => τ.out = σ.out ++
      encodeToks ((List.range' j (N - j)).reverse.flatMap (treeBlock C)) ∧
      ∀ x, x ∉ tlClob → τ.reg x = σ.reg x) Q N _ ⟨by simp [encodeToks], ?_⟩
    (by simp [St.setReg_apply, hN]) ?_ ?_
  · intro x hx
    have h1 : x ≠ rK := by rintro rfl; exact hx (by decide)
    have h2 : x ≠ rTmp := by rintro rfl; exact hx (by decide)
    simp [St.setReg_apply, h1, h2]
  · intro j hj τ ⟨ho, hf⟩ hr
    have hNτ : τ.reg rN = N := (hf rN (by decide)).trans hN
    refine ach_treeBody hw hwf _ _ (by simp; omega) (by simp [St.setReg_apply, hNτ, N]) hB ?_
    intro τ' h1 h2
    refine ⟨by rw [h2 rK (by decide)]; simp, ?_, ?_⟩
    · rw [h1]; simp only [St.setReg_out, ho, St.setReg_reg, Function.update_self,
        List.append_assoc, ← encodeToks_append]
      rw [show N - j = (N - (j + 1)) + 1 by omega, range'_reverse_succ]
      simp
    · intro x hx
      have hx1 : x ∉ tbClob := fun h' => hx (List.mem_cons_of_mem _ h')
      have hx2 : x ≠ rK := fun h' => hx (by rw [h']; simp [tlClob])
      rw [h2 x hx1]; simp [St.setReg_apply, hx2, hf x hx]
  · intro τ ⟨ho, hf⟩ _
    refine h τ ?_ hf
    rw [ho, List.range_eq_range']; simp

/-- Emit the `2n` closing brackets. -/
def closeLoop : Stmt 20 := copy rN rK rTmp ⨟ forDown rK (emitToks [.rpar, .rpar])

lemma ach_closeLoop (σ : St 20) (Q : St 20 → Prop) (n : ℕ) (hN : σ.reg rN = n) (hB : n ≤ B)
    (h : ∀ τ : St 20, τ.out = σ.out ++ encodeToks (List.replicate (2 * n) Tok.rpar) → Q τ) :
    Ach w B closeLoop σ Q := by
  unfold closeLoop
  refine ach_seq (ach_copy rN rK rTmp (by decide) (by decide) (by decide) σ _ (by omega) ?_)
  refine ach_forDown rK _ (fun j τ => τ.out = σ.out ++
      encodeToks (List.replicate (2 * (n - j)) Tok.rpar)) Q n _ (by simp [encodeToks])
    (by simp [St.setReg_apply, hN]) ?_ (fun τ hP _ => h τ (by simpa using hP))
  intro j hj τ ho hr
  refine ach_emitToks _ _ _ ⟨by simp, ?_⟩
  simp only [St.setReg_out, ho, List.append_assoc, ← encodeToks_append]
  congr 2
  rw [show 2 * (n - j) = 2 * (n - (j + 1)) + 2 by omega, List.replicate_add]
  rfl

end MCVPReduction

end PathChecking
