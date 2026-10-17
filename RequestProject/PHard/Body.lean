module

public import RequestProject.PHard.Prog

/-!
# The loop body of the tableau program: computing and emitting one gate

`body M c` computes, from the gate index `g` in register `5`, the gate `gateFn M c w g` and
outputs its encoding (`ach_body`).
-/

@[expose] public section

namespace PathChecking

namespace PHardness

open Classical MCVPReduction LS
open scoped LS

noncomputable section

variable (M : TM) (c : ℕ) (w : Word)

/-- The scratch registers hold the decoded gate index. -/
structure DV (g : ℕ) (τ : St 64) : Prop where
  r0 : τ.reg (R 0) = w.length
  r1 : τ.reg (R 1) = Tb c w.length
  r2 : τ.reg (R 2) = NE M c w.length
  r3 : τ.reg (R 3) = Sb M c w.length
  r5 : τ.reg (R 5) = g
  r9 : τ.reg (R 9) = g % Sb M c w.length
  r10 : τ.reg (R 10) = g / Sb M c w.length / NE M c w.length
  r11 : τ.reg (R 11) = g / Sb M c w.length % NE M c w.length
  r13 : τ.reg (R 13) = (g % Sb M c w.length - 1) % 2
  r14 : τ.reg (R 14) = (g % Sb M c w.length - 1) / 2 / NE M c w.length
  r15 : τ.reg (R 15) = (g % Sb M c w.length - 1) / 2 % NE M c w.length
  r16 : τ.reg (R 16) = eP M c w.length (g / Sb M c w.length % NE M c w.length)
  r17 : τ.reg (R 17) = eJ M c w.length (g / Sb M c w.length % NE M c w.length)
  r18 : τ.reg (R 18) = eZ M (g / Sb M c w.length % NE M c w.length)
  r19 : τ.reg (R 19) = eP M c w.length ((g % Sb M c w.length - 1) / 2 / NE M c w.length)
  r20 : τ.reg (R 20) = eJ M c w.length ((g % Sb M c w.length - 1) / 2 / NE M c w.length)
  r21 : τ.reg (R 21) = eZ M ((g % Sb M c w.length - 1) / 2 / NE M c w.length)
  r22 : τ.reg (R 22) = eP M c w.length ((g % Sb M c w.length - 1) / 2 % NE M c w.length)
  r23 : τ.reg (R 23) = eJ M c w.length ((g % Sb M c w.length - 1) / 2 % NE M c w.length)
  r24 : τ.reg (R 24) = eZ M ((g % Sb M c w.length - 1) / 2 % NE M c w.length)

lemma DV.transfer {g : ℕ} {τ τ' : St 64} (h : DV M c w g τ)
    (hr : ∀ x : Fin 64, x.val < 25 → τ'.reg x = τ.reg x) : DV M c w g τ' := by
  have e : ∀ i, i < 25 → τ'.reg (R i) = τ.reg (R i) := fun i hi => hr _ (by rw [R_val (by omega)]; omega)
  exact ⟨by rw [e 0 (by omega), h.r0], by rw [e 1 (by omega), h.r1], by rw [e 2 (by omega), h.r2],
    by rw [e 3 (by omega), h.r3], by rw [e 5 (by omega), h.r5], by rw [e 9 (by omega), h.r9],
    by rw [e 10 (by omega), h.r10], by rw [e 11 (by omega), h.r11],
    by rw [e 13 (by omega), h.r13], by rw [e 14 (by omega), h.r14],
    by rw [e 15 (by omega), h.r15], by rw [e 16 (by omega), h.r16],
    by rw [e 17 (by omega), h.r17], by rw [e 18 (by omega), h.r18],
    by rw [e 19 (by omega), h.r19], by rw [e 20 (by omega), h.r20],
    by rw [e 21 (by omega), h.r21], by rw [e 22 (by omega), h.r22],
    by rw [e 23 (by omega), h.r23], by rw [e 24 (by omega), h.r24]⟩

/-- Invariant of the branches of the body. -/
def Inv (σ : St 64) (g : ℕ) (τ : St 64) : Prop :=
  τ.out = σ.out ∧ (∀ x : Fin 64, x.val < 8 → τ.reg x = σ.reg x) ∧ DV M c w g τ

/-- Postcondition of the body. -/
def Post (σ : St 64) (g : ℕ) (τ : St 64) : Prop :=
  τ.out = σ.out ++ encodeToks (gateFn M c w g).toks ∧
    ∀ x : Fin 64, x.val < 8 → τ.reg x = σ.reg x

lemma Inv.transfer {σ τ τ' : St 64} {g : ℕ} (h : Inv M c w σ g τ) (ho : τ'.out = τ.out)
    (hr : ∀ x : Fin 64, x.val < 25 → τ'.reg x = τ.reg x) : Inv M c w σ g τ' :=
  ⟨ho.trans h.1, fun x hx => (hr x (by omega)).trans (h.2.1 x hx), h.2.2.transfer M c w hr⟩

lemma Inv.agree {σ τ τ' : St 64} {g : ℕ} (h : Inv M c w σ g τ) (ha : Agree 30 τ τ') :
    Inv M c w σ g τ' := h.transfer M c w ha.1 (fun x hx => ha.2.2 x (by omega))

lemma post_of_ext {σ τ τ' : St 64} {g : ℕ} {ts : List Tok} (h : Inv M c w σ g τ)
    (hE : Ext τ τ' ts) (hts : ts = (gateFn M c w g).toks) : Post M c w σ g τ' :=
  ⟨by rw [hE.1, h.1, hts], fun x hx => (hE.2.2 x (by omega)).trans (h.2.1 x hx)⟩

/-! ## Emitting the gates -/

/-- `g - 2 ∨ g - 1`. -/
def emitT : Stmt 64 := emitOr (.sub (rg 5) (cst 2)) (.sub (rg 5) (cst 1))
/-- `g - 2 ∨ g - 2`. -/
def emitF : Stmt 64 := emitOr (.sub (rg 5) (cst 2)) (.sub (rg 5) (cst 2))

lemma Bd_pos (n : ℕ) : 2 ≤ Bd M c n := le_trans (by omega) ((n_le_NE M c n).trans (NE_le_Bd M c n))

lemma ach_emitTF (b : Bool) {σ τ : St 64} {g : ℕ} (hI : Inv M c w σ g τ)
    (hg : g ≤ Bd M c w.length)
    (hG : gateFn M c w g = .or (g - 2) (if b then g - 1 else g - 2)) :
    Ach w (Bd M c w.length) (if b then emitT else emitF) τ (Post M c w σ g) := by
  have h5 := hI.2.2.r5
  have hB := Bd_pos M c w.length
  cases b
  · refine ach_emitOr _ _ τ _ (by simp [AE.RL]) (by simp [AE.RL]) (by simp [AE.ht])
      (by simp [AE.ht]) (by simp [AE.Bnd, h5]; omega) (by simp [AE.Bnd, h5]; omega) (by omega) ?_
    intro τ' hE
    refine post_of_ext M c w hI hE ?_
    simp [hG, AE.eval, h5]
  · refine ach_emitOr _ _ τ _ (by simp [AE.RL]) (by simp [AE.RL]) (by simp [AE.ht])
      (by simp [AE.ht]) (by simp [AE.Bnd, h5]; omega) (by simp [AE.Bnd, h5]; omega) (by omega) ?_
    intro τ' hE
    refine post_of_ext M c w hI hE ?_
    simp [hG, AE.eval, h5]

lemma ach_emitIn' (b : Bool) {σ τ : St 64} {g : ℕ} (hI : Inv M c w σ g τ)
    (hG : gateFn M c w g = .input b) :
    Ach w (Bd M c w.length) (emitIn b) τ (Post M c w σ g) :=
  ach_emitIn b τ _ (fun τ' hE => post_of_ext M c w hI hE (by rw [hG]))

end

end PHardness

end PathChecking
