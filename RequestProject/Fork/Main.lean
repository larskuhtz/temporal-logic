module

public import RequestProject.Fork.Toks
public import RequestProject.MCVP.Main

/-!
# CTL* tree checking is P-hard already on single-fork trees

`forkProg` is a register program (the same 20 registers and the same bound `4|w| + 4` as the
caterpillar reduction `redProg`) that validates its input circuit and then streams the
single-fork CTL* instance `(forkFormula C, forkTree C)`. Compiling it with
`logspaceComputable_of_prog` gives a logspace transducer for the reduction map `forkRedFun`.

Main results:

* `forkRedFun_correct : w ∈ MCVP ↔ forkRedFun w ∈ CTLStarSingleForkTreeChecking`;
* `forkRedFun_logspaceComputable : LogspaceComputable forkRedFun`;
* `MCVP_logspaceReducible_singleFork : LogspaceReducible MCVP CTLStarSingleForkTreeChecking`
  (combined with `PHardness.MCVP_PHard` in `RequestProject/Statements.lean`).
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-! ## The reduction map -/

/-- The single-fork instance of CTL* tree checking produced from a circuit. -/
def forkInstanceWord (C : List MGate) : Word :=
  encodeToks (Tok.lpar :: ((forkFormula C).toks ++ (Tok.rpar :: (forkTree C).toks)))

open Classical in
/-- **The single-fork reduction map** on binary words: valid encodings of circuits are mapped
to the encoding of the instance of `forkFormula_correct`; all other words are mapped to the
empty word (which is not an instance). -/
noncomputable def forkRedFun (w : Word) : Word :=
  if h : ValidCode w then forkInstanceWord h.choose else []

lemma forkRedFun_encode {C : List MGate} (hC : C ≠ []) (hwf : WellFormed C) :
    forkRedFun (encodeCircuit C) = forkInstanceWord C := by
  have hv : ValidCode (encodeCircuit C) := ⟨C, hC, hwf, rfl⟩
  rw [forkRedFun, dif_pos hv]
  have := hv.choose_spec.2.2
  rw [encodeCircuit_injective this.symm]

lemma forkRedFun_invalid {w : Word} (h : ¬ ValidCode w) : forkRedFun w = [] := by
  rw [forkRedFun, dif_neg h]

/-- **Correctness of the single-fork reduction map.** -/
theorem forkRedFun_correct (w : Word) :
    w ∈ MCVP ↔ forkRedFun w ∈ CTLStarSingleForkTreeChecking := by
  constructor
  · rintro ⟨C, hC, hwf, rfl, hev⟩
    rw [forkRedFun_encode hC hwf]
    exact ⟨_, _, rfl, forkTree_isSingleFork C, (forkFormula_correct C hwf).2 hev⟩
  · rintro ⟨φ, t, hx, -, hsat⟩
    by_cases hv : ValidCode w
    · obtain ⟨C, hC, hwf, rfl⟩ := hv
      rw [forkRedFun_encode hC hwf, forkInstanceWord] at hx
      obtain ⟨rfl, rfl⟩ := instance_injective hx
      exact ⟨C, hC, hwf, rfl, (forkFormula_correct C hwf).1 hsat⟩
    · rw [forkRedFun_invalid hv] at hx
      simp [encodeToks, Tok.bits] at hx

/-! ## Streaming the formula -/

/-- Emit the prefix block for the gate whose first token is `t`. -/
def fkBlockTok (t : Tok) : Stmt 20 :=
  if t = .tag 2 then emitItems rK (forkWrapItems (.and 0 0))
  else if t = .tag 3 then emitItems rK (forkWrapItems (.or 0 0)) else .skip

/-- Locate gate `rK` and emit its prefix block. -/
def fkFormulaBody : Stmt 20 := locate rK ⨟ caseTok fkBlockTok .skip

lemma ach_fkFormulaBody {C : List MGate} (hw : w = encodeCircuit C) (τ : St 20)
    (Q : St 20 → Prop) (hk : τ.reg rK < C.length) (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ' : St 20, τ'.out = τ.out ++ encodeToks (forkFormulaBlock C (τ.reg rK)) →
      (∀ x, x ∉ fClob → τ'.reg x = τ.reg x) → Q τ') :
    Ach w B fkFormulaBody τ Q := by
  have hCw := length_le_word hw
  unfold fkFormulaBody
  refine ach_seq (ach_locate rK rK_not_mem_locClob hw τ _ hk.le (by omega) ?_)
  intro τ₁ hp ho hf
  have hk1 : τ₁.reg rK = τ.reg rK := hf rK rK_not_mem_locClob
  have hAt := gate_at_index hw hk
  rw [← hp] at hAt
  have fin : ∀ τ' : St 20, τ'.out = τ₁.out ++ encodeToks (forkFormulaBlock C (τ.reg rK)) →
      (∀ x, x ∉ numClob → τ'.reg x = τ₁.reg x) → Q τ' := by
    intro τ' h1 h2
    refine h τ' (by rw [h1, ho]) ?_
    intro x hx
    simp only [fClob, List.mem_append, not_or] at hx
    rw [h2 x hx.2, hf x hx.1]
  have emitB : ∀ (G : MGate) (σ' : St 20), σ'.reg rK = τ.reg rK → σ'.out = τ₁.out →
      (∀ x, x ∉ numClob → σ'.reg x = τ₁.reg x) → gateAt C (τ.reg rK) = G →
      Ach w B (emitItems rK (forkWrapItems G)) σ' Q := by
    intro G σ' h1 h2 h3 hG
    refine ach_emitItems rK rK_not_mem_numClob _ σ' Q (by omega) (by omega)
      (forkWrapItems_num_le G) ?_
    intro τ' _ h4 h5
    refine fin τ' ?_ (fun x hx => (h5 x hx).trans (h3 x hx))
    rw [h4, h2, h1, forkFormulaBlock, hG]
  cases hG : gateAt C (τ.reg rK) with
  | input b =>
    rw [hG] at hAt
    have hfb : forkFormulaBlock C (τ.reg rK) = [] := by simp [forkFormulaBlock, hG, forkWrapItems]
    cases b
    · refine ach_caseTok_pos _ _ _ τ₁ (.tag 0) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [fkBlockTok, Tok.tag.injEq]
      exact ach_skip (fin _ (by simp [hfb, encodeToks]) (fun _ _ => rfl))
    · refine ach_caseTok_pos _ _ _ τ₁ (.tag 1) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [fkBlockTok, Tok.tag.injEq]
      exact ach_skip (fin _ (by simp [hfb, encodeToks]) (fun _ _ => rfl))
  | and i j =>
    rw [hG] at hAt
    refine ach_caseTok_pos _ _ _ τ₁ (.tag 2) (At.toks_cons.1 (by simpa [MGate.toks] using hAt)).1 ?_
    simp only [fkBlockTok, if_true]
    exact emitB (.and i j) _ (by simpa using hk1) rfl (fun _ _ => rfl) hG
  | or i j =>
    rw [hG] at hAt
    refine ach_caseTok_pos _ _ _ τ₁ (.tag 3) (At.toks_cons.1 (by simpa [MGate.toks] using hAt)).1 ?_
    simp only [fkBlockTok, Tok.tag.injEq]
    exact emitB (.or i j) _ (by simpa using hk1) rfl (fun _ _ => rfl) hG

/-- Emit the prefix blocks of all levels, from the last gate down to gate `0`. -/
def fkFormulaLoop : Stmt 20 := copy rN rK rTmp ⨟ forDown rK fkFormulaBody

lemma ach_fkFormulaLoop {C : List MGate} (hw : w = encodeCircuit C) (σ : St 20)
    (Q : St 20 → Prop) (hN : σ.reg rN = C.length) (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ : St 20,
      τ.out = σ.out ++ encodeToks ((List.range C.length).reverse.flatMap (forkFormulaBlock C)) →
      (∀ x, x ∉ flClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B fkFormulaLoop σ Q := by
  have hCw := length_le_word hw
  set N := C.length
  unfold fkFormulaLoop
  refine ach_seq (ach_copy rN rK rTmp (by decide) (by decide) (by decide) σ _ (by omega) ?_)
  refine ach_forDown rK fkFormulaBody (fun j τ => τ.out = σ.out ++
      encodeToks ((List.range' j (N - j)).reverse.flatMap (forkFormulaBlock C)) ∧
      ∀ x, x ∉ flClob → τ.reg x = σ.reg x) Q N _ ⟨by simp [encodeToks], ?_⟩
    (by simp [St.setReg_apply, hN]) ?_ ?_
  · intro x hx
    simp only [flClob, fClob, locClob, numClob, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false, not_or] at hx
    simp [St.setReg_apply, hx.1, hx.2.1.2.1]
  · intro j hj τ ⟨ho, hf⟩ hr
    refine ach_fkFormulaBody hw _ _ (by simp; omega) hB ?_
    intro τ' h1 h2
    refine ⟨by rw [h2 rK (by decide)]; simp, ?_, ?_⟩
    · rw [h1]; simp only [St.setReg_out, ho, St.setReg_reg, Function.update_self,
        List.append_assoc, ← encodeToks_append]
      rw [show N - j = (N - (j + 1)) + 1 by omega, range'_reverse_succ]
      simp
    · intro x hx
      have hx1 : x ∉ fClob := fun h' => hx (List.mem_cons_of_mem _ h')
      have hx2 : x ≠ rK := fun h' => hx (by rw [h']; simp [flClob])
      rw [h2 x hx1]; simp [St.setReg_apply, hx2, hf x hx]
  · intro τ ⟨ho, hf⟩ _
    refine h τ ?_ hf
    rw [ho, List.range_eq_range']; simp

/-! ## Streaming the tree -/

/-- Emit the block of the tree belonging to gate `rK`: `( label(R_{rK})`. -/
def fkTreeBody : Stmt 20 :=
  emitToks [.lpar, .lpar] ⨟ trueFlag ⨟ headProg ⨟ readsLoop ⨟ emitToks [.rpar]

lemma ach_fkTreeBody {C : List MGate} (hw : w = encodeCircuit C) (hwf : WellFormed C)
    (τ : St 20) (Q : St 20 → Prop) (hk : τ.reg rK < C.length) (hN : τ.reg rN = C.length)
    (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ' : St 20, τ'.out = τ.out ++ encodeToks (forkTreeBlock C (τ.reg rK)) →
      (∀ x, x ∉ tbClob → τ'.reg x = τ.reg x) → Q τ') :
    Ach w B fkTreeBody τ Q := by
  have hCw := length_le_word hw
  unfold fkTreeBody
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
  refine ach_emitToks _ _ _ (h _ ?_ ?_)
  · have hK3 : τ₃.reg rK = τ.reg rK := (hf₃ rK (by decide)).trans hK2
    simp only [ho₃, ho₂, ho₁, hK2, hK1, List.append_assoc]
    rw [forkTreeBlock_eq hwf]
    simp only [← encodeToks_append, List.append_assoc]
  · intro x hx
    simp only [tbClob, List.mem_cons, List.mem_append, not_or] at hx
    simp only
    rw [hf₃ x hx.2.2, hf₂ x hx.2.1.2, hf₁ x (by simp [hx.1, hx.2.1.1])]

/-- Emit the blocks of all gates, from the last gate down to gate `0`. -/
def fkTreeLoop : Stmt 20 := copy rN rK rTmp ⨟ forDown rK fkTreeBody

lemma ach_fkTreeLoop {C : List MGate} (hw : w = encodeCircuit C) (hwf : WellFormed C)
    (σ : St 20) (Q : St 20 → Prop) (hN : σ.reg rN = C.length) (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ : St 20,
      τ.out = σ.out ++ encodeToks ((List.range C.length).reverse.flatMap (forkTreeBlock C)) →
      (∀ x, x ∉ tlClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B fkTreeLoop σ Q := by
  have hCw := length_le_word hw
  set N := C.length
  unfold fkTreeLoop
  refine ach_seq (ach_copy rN rK rTmp (by decide) (by decide) (by decide) σ _ (by omega) ?_)
  refine ach_forDown rK fkTreeBody (fun j τ => τ.out = σ.out ++
      encodeToks ((List.range' j (N - j)).reverse.flatMap (forkTreeBlock C)) ∧
      ∀ x, x ∉ tlClob → τ.reg x = σ.reg x) Q N _ ⟨by simp [encodeToks], ?_⟩
    (by simp [St.setReg_apply, hN]) ?_ ?_
  · intro x hx
    have h1 : x ≠ rK := by rintro rfl; exact hx (by decide)
    have h2 : x ≠ rTmp := by rintro rfl; exact hx (by decide)
    simp [St.setReg_apply, h1, h2]
  · intro j hj τ ⟨ho, hf⟩ hr
    have hNτ : τ.reg rN = N := (hf rN (by decide)).trans hN
    refine ach_fkTreeBody hw hwf _ _ (by simp; omega) (by simp [St.setReg_apply, hNτ, N]) hB ?_
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

/-- Emit the `n` closing brackets. -/
def fkCloseLoop : Stmt 20 := copy rN rK rTmp ⨟ forDown rK (emitToks [.rpar])

lemma ach_fkCloseLoop (σ : St 20) (Q : St 20 → Prop) (n : ℕ) (hN : σ.reg rN = n) (hB : n ≤ B)
    (h : ∀ τ : St 20, τ.out = σ.out ++ encodeToks (List.replicate n Tok.rpar) → Q τ) :
    Ach w B fkCloseLoop σ Q := by
  unfold fkCloseLoop
  refine ach_seq (ach_copy rN rK rTmp (by decide) (by decide) (by decide) σ _ (by omega) ?_)
  refine ach_forDown rK _ (fun j τ => τ.out = σ.out ++
      encodeToks (List.replicate (n - j) Tok.rpar)) Q n _ (by simp [encodeToks])
    (by simp [St.setReg_apply, hN]) ?_ (fun τ hP _ => h τ (by simpa using hP))
  intro j hj τ ho hr
  refine ach_emitToks _ _ _ ⟨by simp, ?_⟩
  simp only [St.setReg_out, ho, List.append_assoc, ← encodeToks_append]
  congr 2
  rw [show n - j = (n - (j + 1)) + 1 by omega, List.replicate_succ']

/-! ## The whole program -/

/-- Output phase: stream `( Φ_n ) t` for the (valid) input circuit. -/
def fkOutputProg : Stmt 20 :=
  emitToks [.lpar] ⨟ fkFormulaLoop ⨟ emitToks ((CTLStar.ap aInit).toks ++ [.rpar]) ⨟
  fkTreeLoop ⨟ emitToks (selfLeaf.toks ++ walkLeaf.toks) ⨟ fkCloseLoop

/-- **The single-fork reduction program**: validate the input, and if it is valid, stream
the instance. -/
def forkProg : Stmt 20 := validate ⨟ .ite (.zero rOk) .skip fkOutputProg

lemma ach_fkOutputProg {C : List MGate} (hw : w = encodeCircuit C) (hC : C ≠ [])
    (hwf : WellFormed C) (σ : St 20) (hN : σ.reg rN = C.length) (hB : 4 * w.length + 4 ≤ B) :
    Ach w B fkOutputProg σ (fun τ => τ.out = σ.out ++ forkInstanceWord C) := by
  have hCw := length_le_word hw
  unfold fkOutputProg
  refine ach_seq (ach_emitToks _ _ _
    (ach_seq (ach_fkFormulaLoop hw _ _ (by simpa using hN) hB ?_)))
  intro τ₁ ho₁ hf₁
  have hN1 : τ₁.reg rN = C.length := (hf₁ rN rN_not_mem_flClob).trans (by simpa using hN)
  refine ach_seq (ach_emitToks _ _ _
    (ach_seq (ach_fkTreeLoop hw hwf _ _ (by simpa using hN1) hB ?_)))
  intro τ₂ ho₂ hf₂
  have hN2 : τ₂.reg rN = C.length := (hf₂ rN rN_not_mem_tlClob).trans (by simpa using hN1)
  refine ach_seq (ach_emitToks _ _ _ (ach_fkCloseLoop _ _ C.length (by simpa using hN2)
    (by omega) ?_))
  intro τ₃ ho₃
  rw [ho₃]
  simp only [ho₂, ho₁, forkInstanceWord, forkFormula, forkLevel_toks, forkTree_toks C hC]
  simp only [← encodeToks_append, List.append_assoc]
  simp

lemma ach_forkProg (w : Word) :
    Ach w (redBound w) forkProg (St.init 20) (fun τ => τ.out = forkRedFun w) := by
  unfold forkProg
  refine ach_seq (ach_validate _ _ (by simp [redBound]; omega) ?_)
  intro τ ho _ hok hN
  refine ach_ite ?_
  by_cases h0 : τ.reg rOk = 0
  · rw [if_pos (by simp [Cond.eval, h0])]
    refine ach_skip ?_
    have hnv : ¬ ValidCode w := fun h' => (hok.2 h') h0
    rw [ho, forkRedFun_invalid hnv]; rfl
  · rw [if_neg (by simp [Cond.eval, h0])]
    obtain ⟨C, hC, hwf, hw⟩ := hok.1 h0
    refine (ach_fkOutputProg hw hC hwf τ (hN C hw h0) (by simp [redBound])).mono ?_
    intro τ' h'
    rw [h', ho, hw, forkRedFun_encode hC hwf]; rfl

/-- **The single-fork reduction map is logspace computable.** -/
theorem forkRedFun_logspaceComputable : LogspaceComputable forkRedFun := by
  refine logspaceComputable_of_prog forkProg forkRedFun redBound 4 redBound_lt ?_
  intro w
  obtain ⟨σ', h1, h2⟩ := ach_forkProg w
  exact ⟨σ', h1, h2⟩

/-- **MCVP is logspace many-one reducible to CTL* tree checking on single-fork trees.** -/
theorem MCVP_logspaceReducible_singleFork :
    LogspaceReducible MCVP CTLStarSingleForkTreeChecking :=
  ⟨forkRedFun, forkRedFun_logspaceComputable, forkRedFun_correct⟩

end MCVPReduction

end PathChecking
