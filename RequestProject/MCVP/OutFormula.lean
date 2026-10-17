module

public import RequestProject.MCVP.Loops

/-!
# Streaming the formula

For `k = n-1, …, 0` the program locates gate `k` on the input, reads its type and emits the
prefix block of level `k` of the formula `Φ_n`.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-- Downward ranges `[j + len - 1, …, j]`. -/
lemma range'_reverse_succ (j n : ℕ) :
    (List.range' j (n + 1)).reverse = (List.range' (j + 1) n).reverse ++ [j] := by
  rw [List.range'_succ, List.reverse_cons]

lemma wrapItems_num_le (G : MGate) : ∀ c, Item.num c ∈ wrapItems G → c ≤ 3 := by
  cases G <;> simp [wrapItems, thetaItems]

/-- Emit the prefix block for the gate whose first token is `t`. -/
def blockTok (t : Tok) : Stmt 20 :=
  if t = .tag 2 then emitItems rK (wrapItems (.and 0 0))
  else if t = .tag 3 then emitItems rK (wrapItems (.or 0 0)) else .skip

/-- Locate gate `rK` and emit its prefix block. -/
def formulaBody : Stmt 20 := locate rK ⨟ caseTok blockTok .skip

/-- Registers modified by `formulaBody`. -/
def fClob : List (Fin 20) := locClob ++ numClob

lemma rK_not_mem_locClob : rK ∉ locClob := by decide
lemma rK_not_mem_numClob : rK ∉ numClob := by decide

lemma ach_formulaBody {C : List MGate} (hw : w = encodeCircuit C) (τ : St 20) (Q : St 20 → Prop)
    (hk : τ.reg rK < C.length) (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ' : St 20, τ'.out = τ.out ++ encodeToks (formulaBlock C (τ.reg rK)) →
      (∀ x, x ∉ fClob → τ'.reg x = τ.reg x) → Q τ') :
    Ach w B formulaBody τ Q := by
  have hCw : C.length ≤ w.length := by
    have := length_le_toks C
    have := encodeCircuit_length C
    rw [← hw] at this; omega
  unfold formulaBody
  refine ach_seq (ach_locate rK rK_not_mem_locClob hw τ _ hk.le (by omega) ?_)
  intro τ₁ hp ho hf
  have hk1 : τ₁.reg rK = τ.reg rK := hf rK rK_not_mem_locClob
  have hAt := gate_at_index hw hk
  rw [← hp] at hAt
  have fin : ∀ τ' : St 20, τ'.out = τ₁.out ++ encodeToks (formulaBlock C (τ.reg rK)) →
      (∀ x, x ∉ numClob → τ'.reg x = τ₁.reg x) → Q τ' := by
    intro τ' h1 h2
    refine h τ' (by rw [h1, ho]) ?_
    intro x hx
    simp only [fClob, List.mem_append, not_or] at hx
    rw [h2 x hx.2, hf x hx.1]
  have emitB : ∀ (G : MGate) (σ' : St 20), σ'.reg rK = τ.reg rK → σ'.out = τ₁.out →
      (∀ x, x ∉ numClob → σ'.reg x = τ₁.reg x) → gateAt C (τ.reg rK) = G →
      Ach w B (emitItems rK (wrapItems G)) σ' Q := by
    intro G σ' h1 h2 h3 hG
    refine ach_emitItems rK rK_not_mem_numClob _ σ' Q (by omega) (by omega) (wrapItems_num_le G) ?_
    intro τ' _ h4 h5
    refine fin τ' ?_ (fun x hx => (h5 x hx).trans (h3 x hx))
    rw [h4, h2, h1, formulaBlock, hG]
  cases hG : gateAt C (τ.reg rK) with
  | input b =>
    rw [hG] at hAt
    have hfb : formulaBlock C (τ.reg rK) = [] := by simp [formulaBlock, hG, wrapItems]
    cases b
    · refine ach_caseTok_pos _ _ _ τ₁ (.tag 0) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [blockTok, Tok.tag.injEq]
      exact ach_skip (fin _ (by simp [hfb, encodeToks]) (fun _ _ => rfl))
    · refine ach_caseTok_pos _ _ _ τ₁ (.tag 1) (by simpa [MGate.toks, encodeToks] using hAt) ?_
      simp only [blockTok, Tok.tag.injEq]
      exact ach_skip (fin _ (by simp [hfb, encodeToks]) (fun _ _ => rfl))
  | and i j =>
    rw [hG] at hAt
    refine ach_caseTok_pos _ _ _ τ₁ (.tag 2) (At.toks_cons.1 (by simpa [MGate.toks] using hAt)).1 ?_
    simp only [blockTok, if_true]
    refine emitB (.and i j) _ (by simpa using hk1) rfl (fun _ _ => rfl) hG
  | or i j =>
    rw [hG] at hAt
    refine ach_caseTok_pos _ _ _ τ₁ (.tag 3) (At.toks_cons.1 (by simpa [MGate.toks] using hAt)).1 ?_
    simp only [blockTok, Tok.tag.injEq]
    refine emitB (.or i j) _ (by simpa using hk1) rfl (fun _ _ => rfl) hG

/-- Emit the prefix blocks of all levels, from the last gate down to gate `0`. -/
def formulaLoop : Stmt 20 := copy rN rK rTmp ⨟ forDown rK formulaBody

/-- Registers modified by `formulaLoop`. -/
def flClob : List (Fin 20) := rK :: fClob

lemma ach_formulaLoop {C : List MGate} (hw : w = encodeCircuit C) (σ : St 20) (Q : St 20 → Prop)
    (hN : σ.reg rN = C.length) (hB : 4 * w.length + 4 ≤ B)
    (h : ∀ τ : St 20,
      τ.out = σ.out ++ encodeToks ((List.range C.length).reverse.flatMap (formulaBlock C)) →
      (∀ x, x ∉ flClob → τ.reg x = σ.reg x) → Q τ) :
    Ach w B formulaLoop σ Q := by
  have hCw : C.length ≤ w.length := by
    have := length_le_toks C
    have := encodeCircuit_length C
    rw [← hw] at this; omega
  set N := C.length
  unfold formulaLoop
  refine ach_seq (ach_copy rN rK rTmp (by decide) (by decide) (by decide) σ _ (by omega) ?_)
  refine ach_forDown rK formulaBody (fun j τ => τ.out = σ.out ++
      encodeToks ((List.range' j (N - j)).reverse.flatMap (formulaBlock C)) ∧
      ∀ x, x ∉ flClob → τ.reg x = σ.reg x) Q N _ ⟨by simp [encodeToks], ?_⟩ (by simp [St.setReg_apply, hN]) ?_ ?_
  · intro x hx
    simp only [flClob, fClob, locClob, numClob, List.mem_cons, List.mem_append, List.not_mem_nil,
      or_false, not_or] at hx
    simp [St.setReg_apply, hx.1, hx.2.1.2.1]
  · intro j hj τ ⟨ho, hf⟩ hr
    refine ach_formulaBody hw _ _ (by simp; omega) hB ?_
    intro τ' h1 h2
    refine ⟨by rw [h2 rK (by decide)]; simp, ?_, ?_⟩
    · rw [h1]; simp only [St.setReg_out, ho, St.setReg_reg, Function.update_self, List.append_assoc,
        ← encodeToks_append]
      rw [show N - j = (N - (j + 1)) + 1 by omega, range'_reverse_succ]
      simp
    · intro x hx
      have hx1 : x ∉ fClob := fun h' => hx (List.mem_cons_of_mem _ h')
      have hx2 : x ≠ rK := fun h' => hx (by rw [h']; simp [flClob])
      rw [h2 x hx1]; simp [St.setReg_apply, hx2, hf x hx]
  · intro τ ⟨ho, hf⟩ _
    refine h τ ?_ hf
    rw [ho, List.range_eq_range']; simp

end MCVPReduction

end PathChecking
