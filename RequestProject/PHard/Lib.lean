module

public import RequestProject.PHard.Expr
public import RequestProject.MCVP.Defs

/-!
# Program fragments for the tableau reduction

Programs with 64 registers; registers `0 … 29` hold data, registers `30 … 63` are
temporaries used by expression evaluation.

* `emitNum e`: output the binary token encoding of the value of `e`;
* `seek i`: move the input head to the position stored in register `i`;
* `symCase f`: branch on the input symbol under the head;
* `assignAll l`: a sequence of assignments `rᵢ := eᵢ`;
* `countLen`: store the input length in register `0`;
* `forLoop body`: `while r₆ ≠ 0 do (body; r₅ := r₅ + 1; r₆ := r₆ - 1)`.
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS
open MCVPReduction

variable {w : Word} {B : ℕ}

/-- The output is extended by the tokens `ts`; head position and data registers unchanged. -/
def Ext (σ τ : St 64) (ts : List Tok) : Prop :=
  τ.out = σ.out ++ encodeToks ts ∧ τ.pos = σ.pos ∧ ∀ x : Fin 64, x.val < 30 → τ.reg x = σ.reg x

lemma Ext.trans {σ τ υ : St 64} {ts us : List Tok} (h1 : Ext σ τ ts) (h2 : Ext τ υ us) :
    Ext σ υ (ts ++ us) :=
  ⟨by rw [h2.1, h1.1, encodeToks_append, List.append_assoc], h2.2.1.trans h1.2.1,
    fun x hx => (h2.2.2 x hx).trans (h1.2.2 x hx)⟩

/-! ## Output -/

/-- Output the binary encoding of the value of `e`. -/
def emitNum (e : AE) : Stmt 64 := evalTo e 30 31 ⨟ emitNat (R 30) (R 31) (R 32) (R 33)

lemma ach_emitNum (e : AE) (σ : St 64) (Q : St 64 → Prop) (hRL : e.RL 30) (hK : e.ht ≤ 14)
    (hB : e.Bnd σ.reg B) (hB1 : 1 ≤ B) (h : ∀ τ, Ext σ τ (natToks (e.eval σ.reg)) → Q τ) :
    Ach w B (emitNum e) σ Q := by
  refine ach_seq (ach_comp e 30 31 σ _ (by omega) (AE.RL_mono (by omega) hRL) (by omega) hB ?_)
  intro τ ho hp hv hk
  refine ach_emitNat _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) τ Q
    (by rw [hv]; exact AE.eval_le hB) hB1 ?_
  intro τ' hp' ho' hf'
  refine h τ' ⟨by rw [ho', ho, hv], hp'.trans hp, fun x hx => ?_⟩
  rw [hf' x (ne_R hx (by omega) (by omega)) (ne_R hx (by omega) (by omega))
    (ne_R hx (by omega) (by omega)), hk x (by omega) (ne_R hx (by omega) (by omega))]

/-- Output a constant gate. -/
def emitIn (b : Bool) : Stmt 64 := emitToks (MGate.input b).toks

lemma ach_emitIn (b : Bool) (σ : St 64) (Q : St 64 → Prop)
    (h : ∀ τ, Ext σ τ (MGate.input b).toks → Q τ) : Ach w B (emitIn b) σ Q :=
  ach_emitToks _ _ _ (h _ ⟨rfl, rfl, fun _ _ => rfl⟩)

/-- Output an `∧` gate. -/
def emitAnd (e₁ e₂ : AE) : Stmt 64 := emitToks [Tok.tag 2] ⨟ emitNum e₁ ⨟ emitNum e₂

/-- Output an `∨` gate. -/
def emitOr (e₁ e₂ : AE) : Stmt 64 := emitToks [Tok.tag 3] ⨟ emitNum e₁ ⨟ emitNum e₂

lemma ach_emitBin (k : Fin 24) (e₁ e₂ : AE) (σ : St 64) (Q : St 64 → Prop) (h1 : e₁.RL 30)
    (h2 : e₂.RL 30) (hK1 : e₁.ht ≤ 14) (hK2 : e₂.ht ≤ 14) (hB1 : e₁.Bnd σ.reg B)
    (hB2 : e₂.Bnd σ.reg B) (hB : 1 ≤ B)
    (h : ∀ τ, Ext σ τ (Tok.tag k :: (natToks (e₁.eval σ.reg) ++ natToks (e₂.eval σ.reg))) → Q τ) :
    Ach w B (emitToks [Tok.tag k] ⨟ emitNum e₁ ⨟ emitNum e₂) σ Q := by
  refine ach_seq (ach_emitToks _ _ _ (ach_seq (ach_emitNum e₁ _ _ h1 hK1 hB1 hB ?_)))
  intro τ hτ
  have e1 : e₂.eval τ.reg = e₂.eval σ.reg := AE.eval_congr hτ.2.2 h2
  refine ach_emitNum e₂ _ _ h2 hK2 (AE.Bnd_congr hτ.2.2 h2 hB2) hB ?_
  intro τ' hτ'
  have h0 : Ext σ { σ with out := σ.out ++ encodeToks [Tok.tag k] } [Tok.tag k] :=
    ⟨rfl, rfl, fun _ _ => rfl⟩
  have := (h0.trans hτ).trans hτ'
  rw [e1] at this
  exact h τ' (by simpa using this)

lemma ach_emitAnd (e₁ e₂ : AE) (σ : St 64) (Q : St 64 → Prop) (h1 : e₁.RL 30)
    (h2 : e₂.RL 30) (hK1 : e₁.ht ≤ 14) (hK2 : e₂.ht ≤ 14) (hB1 : e₁.Bnd σ.reg B)
    (hB2 : e₂.Bnd σ.reg B) (hB : 1 ≤ B)
    (h : ∀ τ, Ext σ τ (MGate.and (e₁.eval σ.reg) (e₂.eval σ.reg)).toks → Q τ) :
    Ach w B (emitAnd e₁ e₂) σ Q :=
  ach_emitBin 2 e₁ e₂ σ Q h1 h2 hK1 hK2 hB1 hB2 hB h

lemma ach_emitOr (e₁ e₂ : AE) (σ : St 64) (Q : St 64 → Prop) (h1 : e₁.RL 30)
    (h2 : e₂.RL 30) (hK1 : e₁.ht ≤ 14) (hK2 : e₂.ht ≤ 14) (hB1 : e₁.Bnd σ.reg B)
    (hB2 : e₂.Bnd σ.reg B) (hB : 1 ≤ B)
    (h : ∀ τ, Ext σ τ (MGate.or (e₁.eval σ.reg) (e₂.eval σ.reg)).toks → Q τ) :
    Ach w B (emitOr e₁ e₂) σ Q :=
  ach_emitBin 3 e₁ e₂ σ Q h1 h2 hK1 hK2 hB1 hB2 hB h

/-! ## Input -/

/-- Move the input head to the left end marker. -/
def goLeft : Stmt 64 := .loop (.not (.sym .lend)) .left

lemma ach_goLeft (σ : St 64) (Q : St 64 → Prop) (h : Q { σ with pos := 0 }) :
    Ach w B goLeft σ Q := by
  refine ach_loop (fun n τ => τ = { σ with pos := n }) _ ?_ σ.pos σ (by rfl)
  intro n τ hτ
  subst hτ
  rcases n with _ | n
  · left
    exact ⟨by simp [Cond.eval, inputSym_eq_lend], h⟩
  · right
    exact ⟨by simp [Cond.eval, inputSym_eq_lend], ach_left ⟨n, by omega, by simp⟩⟩

/-- Move the input head to the position stored in register `i`. -/
def seek (i : ℕ) : Stmt 64 :=
  evalTo (.reg i) 30 31 ⨟ goLeft ⨟ whileNZ (R 30) (.dec (R 30) ⨟ .right)

lemma ach_seek (i : ℕ) (hi : i < 30) (σ : St 64) (Q : St 64 → Prop)
    (hv : σ.reg (R i) ≤ w.length + 1) (hB : σ.reg (R i) ≤ B)
    (h : ∀ τ : St 64, τ.out = σ.out → τ.pos = σ.reg (R i) →
      (∀ x : Fin 64, x.val < 30 → τ.reg x = σ.reg x) → Q τ) : Ach w B (seek i) σ Q := by
  refine ach_seq (ach_comp (.reg i) 30 31 σ _ (by omega) (by simp [AE.RL]; omega)
    (by simp [AE.ht]) hB ?_)
  intro τ ho hp hval hk
  simp only [AE.eval] at hval
  refine ach_seq (ach_goLeft _ _ ?_)
  set v := σ.reg (R i)
  refine ach_loop (fun k υ => υ.reg (R 30) = k ∧ k ≤ v ∧ υ.pos = v - k ∧ υ.out = σ.out ∧
      ∀ x : Fin 64, x.val < 30 → υ.reg x = σ.reg x) Q ?_ v _
    ⟨hval, le_rfl, by simp, ho, fun x hx => hk x (by omega) (ne_R hx (by omega) (by omega))⟩
  rintro k υ ⟨hk1, hkv, hp1, ho1, hf1⟩
  rcases k with _ | k
  · left; exact ⟨by simp [Cond.eval, hk1], h υ ho1 (by omega) hf1⟩
  · right
    refine ⟨by simp [Cond.eval, hk1], ach_seq (ach_dec (ach_right ⟨k, by omega, ?_, by omega,
      ?_, ho1, ?_⟩))⟩
    · simp [St.setReg_apply, hk1]
    · simp [hp1]; omega
    · intro x hx
      simp only [St.setReg_reg]
      rw [Function.update_of_ne (ne_R hx (by omega) (by omega))]
      exact hf1 x hx

/-- Branch on the input symbol under the head. -/
def symCase (f : InSym → Stmt 64) : Stmt 64 :=
  .ite (.sym .lend) (f .lend) (.ite (.sym .rend) (f .rend)
    (.ite (.sym (.bit false)) (f (.bit false)) (f (.bit true))))

lemma ach_symCase (f : InSym → Stmt 64) (σ : St 64) (Q : St 64 → Prop)
    (h : Ach w B (f (inputSym w σ.pos)) σ Q) : Ach w B (symCase f) σ Q := by
  unfold symCase
  rcases hs : inputSym w σ.pos with _ | _ | ⟨_ | _⟩ <;> rw [hs] at h
  · exact ach_iteT (by simp [Cond.eval, hs]) h
  · exact ach_iteF (by simp [Cond.eval, hs]) (ach_iteT (by simp [Cond.eval, hs]) h)
  · exact ach_iteF (by simp [Cond.eval, hs]) (ach_iteF (by simp [Cond.eval, hs])
      (ach_iteT (by simp [Cond.eval, hs]) h))
  · exact ach_iteF (by simp [Cond.eval, hs]) (ach_iteF (by simp [Cond.eval, hs])
      (ach_iteF (by simp [Cond.eval, hs]) h))

/-- Store the input length in register `0`. -/
def countLen : Stmt 64 :=
  goLeft ⨟ .right ⨟ clear (R 0) ⨟ .loop (.not (.sym .rend)) (.inc (R 0) ⨟ .right)

lemma ach_countLen (σ : St 64) (Q : St 64 → Prop) (hB : w.length ≤ B)
    (h : ∀ τ : St 64, τ.out = σ.out → τ.reg (R 0) = w.length →
      (∀ x : Fin 64, x ≠ R 0 → τ.reg x = σ.reg x) → Q τ) : Ach w B countLen σ Q := by
  refine ach_seq (ach_goLeft _ _ (ach_seq (ach_right (ach_seq (ach_clear _ _ _ ?_)))))
  refine ach_loop (fun k υ => υ.reg (R 0) = w.length - k ∧ k ≤ w.length ∧
      υ.pos = w.length + 1 - k ∧ υ.out = σ.out ∧ ∀ x : Fin 64, x ≠ R 0 → υ.reg x = σ.reg x)
    Q ?_ w.length _ ⟨by simp [St.setReg_apply], le_rfl, by simp, rfl, fun x hx => by
      simp [St.setReg_apply, hx]⟩
  rintro k υ ⟨hk1, hkn, hp1, ho1, hf1⟩
  rcases k with _ | k
  · left
    refine ⟨?_, h υ ho1 (by omega) hf1⟩
    simp [Cond.eval, hp1, inputSym_eq_rend (w := w) (p := w.length + 1) (by omega) le_rfl]
  · right
    have hne : inputSym w υ.pos ≠ .rend := by
      rw [Ne, inputSym_eq_rend (by omega) (by omega)]; omega
    refine ⟨by simp [Cond.eval, hne], ach_seq (ach_inc (by omega) (ach_right ⟨k, by omega, ?_,
      by omega, ?_, ho1, ?_⟩))⟩
    · simp [St.setReg_apply, hk1]; omega
    · simp [hp1]; omega
    · intro x hx
      simp [St.setReg_apply, hx, hf1 x hx]

/-! ## Assignments -/

/-- A sequence of assignments `rᵢ := eᵢ` (with temporaries from register `30` on). -/
def assignAll : List (ℕ × AE) → Stmt 64
  | [] => .skip
  | (i, e) :: l => evalTo e i 30 ⨟ assignAll l

/-- The register file after a sequence of assignments. -/
def updAll : List (ℕ × AE) → (Fin 64 → ℕ) → (Fin 64 → ℕ)
  | [], ρ => ρ
  | (i, e) :: l, ρ => updAll l (Function.update ρ (R i) (e.eval ρ))

/-- Side conditions of a sequence of assignments. -/
def AllOK (B : ℕ) : List (ℕ × AE) → (Fin 64 → ℕ) → Prop
  | [], _ => True
  | (i, e) :: l, ρ => i < 30 ∧ e.RL 30 ∧ e.ht ≤ 14 ∧ e.Bnd ρ B ∧
      AllOK B l (Function.update ρ (R i) (e.eval ρ))

lemma update_congr {ρ ρ' : Fin 64 → ℕ} {i v : ℕ}
    (hρ : ∀ x : Fin 64, x.val < 30 → ρ' x = ρ x) :
    ∀ x : Fin 64, x.val < 30 → Function.update ρ' (R i) v x = Function.update ρ (R i) v x := by
  intro x hx
  by_cases h : x = R i
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, hρ x hx]

lemma updAll_congr : ∀ (l : List (ℕ × AE)) {ρ ρ' : Fin 64 → ℕ}, AllOK B l ρ →
    (∀ x : Fin 64, x.val < 30 → ρ' x = ρ x) →
    ∀ x : Fin 64, x.val < 30 → updAll l ρ' x = updAll l ρ x
  | [], _, _, _, hρ => hρ
  | (i, e) :: l, ρ, ρ', h, hρ => by
    simp only [updAll]
    rw [AE.eval_congr hρ h.2.1]
    exact updAll_congr l h.2.2.2.2 (update_congr hρ)

lemma AllOK_congr : ∀ (l : List (ℕ × AE)) {ρ ρ' : Fin 64 → ℕ}, AllOK B l ρ →
    (∀ x : Fin 64, x.val < 30 → ρ' x = ρ x) → AllOK B l ρ'
  | [], _, _, _, _ => trivial
  | (i, e) :: l, ρ, ρ', h, hρ => by
    refine ⟨h.1, h.2.1, h.2.2.1, AE.Bnd_congr hρ h.2.1 h.2.2.2.1, ?_⟩
    rw [AE.eval_congr hρ h.2.1]
    exact AllOK_congr l h.2.2.2.2 (update_congr hρ)

lemma ach_assignAll : ∀ (l : List (ℕ × AE)) (σ : St 64) (Q : St 64 → Prop), AllOK B l σ.reg →
    (∀ τ : St 64, τ.out = σ.out → τ.pos = σ.pos →
      (∀ x : Fin 64, x.val < 30 → τ.reg x = updAll l σ.reg x) → Q τ) →
    Ach w B (assignAll l) σ Q
  | [], σ, Q, _, h => ach_skip (h σ rfl rfl (fun _ _ => rfl))
  | (i, e) :: l, σ, Q, hok, h => by
    obtain ⟨hi, hRL, hK, hB, hok'⟩ := hok
    refine ach_seq (ach_comp e i 30 σ _ hi hRL (by omega) hB ?_)
    intro τ ho hp hv hk
    have hρ : ∀ x : Fin 64, x.val < 30 →
        τ.reg x = Function.update σ.reg (R i) (e.eval σ.reg) x := by
      intro x hx
      by_cases hxi : x = R i
      · subst hxi; rw [hv]; simp
      · rw [Function.update_of_ne hxi]; exact hk x hx hxi
    refine ach_assignAll l τ Q (AllOK_congr l hok' hρ) ?_
    intro τ' ho' hp' hv'
    refine h τ' (ho'.trans ho) (hp'.trans hp) ?_
    intro x hx
    rw [hv' x hx]
    exact updAll_congr l hok' hρ x hx

/-! ## Counting loop -/

/-- `while r₆ ≠ 0 do (body; r₅ := r₅ + 1; r₆ := r₆ - 1)`. -/
def forLoop (body : Stmt 64) : Stmt 64 := whileNZ (R 6) (body ⨟ .inc (R 5) ⨟ .dec (R 6))

lemma ach_forLoop (body : Stmt 64) (P : ℕ → St 64 → Prop)
    (Q : St 64 → Prop) (m : ℕ) (σ : St 64) (hσ : P 0 σ) (hi : σ.reg (R 5) = 0)
    (hc : σ.reg (R 6) = m) (hmB : m ≤ B)
    (hstep : ∀ j, j < m → ∀ τ : St 64, P j τ → τ.reg (R 5) = j → τ.reg (R 6) = m - j →
      Ach w B body τ (fun τ' => τ'.reg (R 5) = j ∧ τ'.reg (R 6) = m - j ∧
        P (j + 1) ((τ'.setReg (R 5) (j + 1)).setReg (R 6) (m - j - 1))))
    (hQ : ∀ τ : St 64, P m τ → Q τ) : Ach w B (forLoop body) σ Q := by
  have hic : R 5 ≠ R 6 := by decide
  refine ach_loop (fun n τ => n ≤ m ∧ τ.reg (R 6) = n ∧ τ.reg (R 5) = m - n ∧ P (m - n) τ) Q ?_
    m σ ⟨le_rfl, hc, by simp [hi], by simpa using hσ⟩
  rintro n τ ⟨hn, hcn, hin, hP⟩
  rcases n with _ | n
  · left; exact ⟨by simp [Cond.eval, hcn], hQ τ (by simpa using hP)⟩
  · right
    refine ⟨by simp [Cond.eval, hcn], ach_seq ?_⟩
    have := hstep (m - (n + 1)) (by omega) τ hP hin (by omega)
    refine this.mono ?_
    rintro τ' ⟨h1, h2, h3⟩
    refine ach_seq (ach_inc (by omega) (ach_dec ⟨n, by omega, by omega, ?_, ?_, ?_⟩))
    · simp [St.setReg_apply, h2, hic.symm]; omega
    · simp [St.setReg_apply, hic, h1]; omega
    · convert h3 using 1
      · omega
      · ext x <;> simp [St.setReg_apply, h1, h2]
        split_ifs <;> omega

end LS

end PathChecking
