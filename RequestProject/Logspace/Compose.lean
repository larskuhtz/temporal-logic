module

public import RequestProject.Logspace.SimTM
public import RequestProject.Logspace.Machine

/-!
# Composition of logspace computable functions

Given machines `M₁` computing `f` and `M₂` computing `g` in logarithmic space, we write a
register program computing `g ∘ f`: it simulates `M₂` on the virtual input `f w`; whenever
`M₂` needs the input symbol at position `i`, the program re-runs `M₁` on `w` from the start,
counting output bits until the `i`-th one is produced.  All registers stay polynomially
bounded (the output of `M₁` has polynomial length), so `logspaceComputable_of_prog` yields a
logspace machine.

## References

That logspace computable functions compose is a classical result: N. D. Jones,
*Space-Bounded Reducibility among Combinatorial Problems*, J. Comput. System Sci. 11(1), 1975
[Jon75]. See also the textbooks of Papadimitriou [Pap94] (Chapter 8) and Arora–Barak [AB09]
(Chapter 4). The proof here uses the usual recompute-on-demand argument. Full entries are in
`REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

open Classical

lemma TM.step_of_not_halt (M : TM) (u : Word) (c : M.Cfg) (h : M.halt c.state = false) :
    M.step u c =
      { state := (M.δ c.state (inputSym u c.inPos) (c.tape c.workPos)).1
        inPos := min ((M.δ c.state (inputSym u c.inPos) (c.tape c.workPos)).2.2.2.1.move c.inPos)
          (u.length + 1)
        tape := Function.update c.tape c.workPos
          (M.δ c.state (inputSym u c.inPos) (c.tape c.workPos)).2.1
        workPos := (M.δ c.state (inputSym u c.inPos) (c.tape c.workPos)).2.2.1.move c.workPos
        output := c.output ++ (M.δ c.state (inputSym u c.inPos) (c.tape c.workPos)).2.2.2.2.toList
      } := by
  unfold TM.step
  rw [if_neg (by simp [h])]

lemma inputSym_of_getElem? {u : Word} {p : ℕ} {b : Bool} (hp : 1 ≤ p) (h : u[p - 1]? = some b) :
    inputSym u p = .bit b := by
  simp [inputSym, show p ≠ 0 by omega, h]

lemma inputSym_of_le {u : Word} {p : ℕ} (hp : 1 ≤ p) (h : u.length + 1 ≤ p) :
    inputSym u p = .rend := by
  simp [inputSym, show p ≠ 0 by omega, List.getElem?_eq_none (show u.length ≤ p - 1 by omega)]

namespace LS

open scoped LS

/-! ## Registers -/

/-- Registers of the simulation of `M₁`. -/
def r1 (i : Fin 8) : Fin 20 := ⟨i.val, by omega⟩
/-- Registers of the simulation of `M₂`; `r2 7` receives the virtual input symbol. -/
def r2 (i : Fin 8) : Fin 20 := ⟨i.val + 8, by omega⟩
/-- Input head position of `M₂` on the virtual input. -/
def rI : Fin 20 := ⟨16, by omega⟩
/-- Output counter. -/
def rC : Fin 20 := ⟨17, by omega⟩
/-- "Found" flag. -/
def rF : Fin 20 := ⟨18, by omega⟩
/-- Temporary. -/
def rT : Fin 20 := ⟨19, by omega⟩

lemma r1_injective : Function.Injective r1 := by
  intro i j h; simp only [r1, Fin.mk.injEq] at h; exact Fin.ext h
lemma r2_injective : Function.Injective r2 := by
  intro i j h; simp only [r2, Fin.mk.injEq] at h; exact Fin.ext (by omega)

@[simp] lemma r1_eq_iff (i j : Fin 8) : r1 i = r1 j ↔ i = j := r1_injective.eq_iff
@[simp] lemma r2_eq_iff (i j : Fin 8) : r2 i = r2 j ↔ i = j := r2_injective.eq_iff
@[simp] lemma r1_val (i : Fin 8) : (r1 i).val = i.val := rfl
@[simp] lemma r2_val (i : Fin 8) : (r2 i).val = i.val + 8 := rfl
@[simp] lemma rI_val : rI.val = 16 := rfl
@[simp] lemma rC_val : rC.val = 17 := rfl
@[simp] lemma rF_val : rF.val = 18 := rfl
@[simp] lemma rT_val : rT.val = 19 := rfl

lemma fin20_ne {a b : Fin 20} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

@[simp] lemma r1_ne_r2 (i j : Fin 8) : r1 i ≠ r2 j := fin20_ne (by simp; omega)
@[simp] lemma r2_ne_r1 (i j : Fin 8) : r2 i ≠ r1 j := fin20_ne (by simp; omega)
@[simp] lemma r1_ne_rI (i : Fin 8) : r1 i ≠ rI := fin20_ne (by simp; omega)
@[simp] lemma r1_ne_rC (i : Fin 8) : r1 i ≠ rC := fin20_ne (by simp; omega)
@[simp] lemma r1_ne_rF (i : Fin 8) : r1 i ≠ rF := fin20_ne (by simp; omega)
@[simp] lemma r1_ne_rT (i : Fin 8) : r1 i ≠ rT := fin20_ne (by simp; omega)
@[simp] lemma r2_ne_rI (i : Fin 8) : r2 i ≠ rI := fin20_ne (by simp; omega)
@[simp] lemma r2_ne_rC (i : Fin 8) : r2 i ≠ rC := fin20_ne (by simp; omega)
@[simp] lemma r2_ne_rF (i : Fin 8) : r2 i ≠ rF := fin20_ne (by simp; omega)
@[simp] lemma r2_ne_rT (i : Fin 8) : r2 i ≠ rT := fin20_ne (by simp; omega)
@[simp] lemma rI_ne_r1 (i : Fin 8) : rI ≠ r1 i := (r1_ne_rI i).symm
@[simp] lemma rC_ne_r1 (i : Fin 8) : rC ≠ r1 i := (r1_ne_rC i).symm
@[simp] lemma rF_ne_r1 (i : Fin 8) : rF ≠ r1 i := (r1_ne_rF i).symm
@[simp] lemma rT_ne_r1 (i : Fin 8) : rT ≠ r1 i := (r1_ne_rT i).symm
@[simp] lemma rI_ne_r2 (i : Fin 8) : rI ≠ r2 i := (r2_ne_rI i).symm
@[simp] lemma rC_ne_r2 (i : Fin 8) : rC ≠ r2 i := (r2_ne_rC i).symm
@[simp] lemma rF_ne_r2 (i : Fin 8) : rF ≠ r2 i := (r2_ne_rF i).symm
@[simp] lemma rT_ne_r2 (i : Fin 8) : rT ≠ r2 i := (r2_ne_rT i).symm
@[simp] lemma rI_ne_rC : rI ≠ rC := by decide
@[simp] lemma rI_ne_rF : rI ≠ rF := by decide
@[simp] lemma rI_ne_rT : rI ≠ rT := by decide
@[simp] lemma rC_ne_rI : rC ≠ rI := by decide
@[simp] lemma rC_ne_rF : rC ≠ rF := by decide
@[simp] lemma rC_ne_rT : rC ≠ rT := by decide
@[simp] lemma rF_ne_rI : rF ≠ rI := by decide
@[simp] lemma rF_ne_rC : rF ≠ rC := by decide
@[simp] lemma rF_ne_rT : rF ≠ rT := by decide
@[simp] lemma rT_ne_rI : rT ≠ rI := by decide
@[simp] lemma rT_ne_rC : rT ≠ rC := by decide
@[simp] lemma rT_ne_rF : rT ≠ rF := by decide

/-! ## Reading an input symbol -/

/-- `r := code of the current input symbol`. -/
def getSym {K : ℕ} (r : Fin K) : Stmt K :=
  .ite (.sym .lend) (setC r 0) (.ite (.sym .rend) (setC r 1)
    (.ite (.sym (.bit false)) (setC r 2) (setC r 3)))

lemma ach_getSym {K : ℕ} {w : Word} {B : ℕ} (r : Fin K) (σ : St K) (Q : St K → Prop)
    (hB : 3 ≤ B) (h : Q (σ.setReg r (symCode (inputSym w σ.pos)))) :
    Ach w B (getSym r) σ Q := by
  unfold getSym
  rcases hx : inputSym w σ.pos with _ | _ | ⟨_ | _⟩ <;> rw [hx] at h
  · exact ach_iteT (by simp [Cond.eval, hx]) (ach_setC _ _ _ _ (by omega) h)
  · exact ach_iteF (by simp [Cond.eval, hx]) (ach_iteT (by simp [Cond.eval, hx])
      (ach_setC _ _ _ _ (by omega) h))
  · exact ach_iteF (by simp [Cond.eval, hx]) (ach_iteF (by simp [Cond.eval, hx])
      (ach_iteT (by simp [Cond.eval, hx]) (ach_setC _ _ _ _ (by omega) h)))
  · exact ach_iteF (by simp [Cond.eval, hx]) (ach_iteF (by simp [Cond.eval, hx])
      (ach_iteF (by simp [Cond.eval, hx]) (ach_setC _ _ _ _ (by omega) h)))

/-! ## The subroutine: the `i`-th symbol of the end-marked word `f w` -/

/-- Input head moves of `M₁`: the real input head. -/
def inMv1 : InSym → Dir → Stmt 20
  | _, .left => .left
  | _, .stay => .skip
  | _, .right => .right

/-- Output of `M₁`: count down, and record the bit when the counter is `0`. -/
def outAct1 : Option Bool → Stmt 20
  | none => .skip
  | some b => .ite (.zero rC) (setC (r2 7) (symCode (.bit b)) ⨟ setC rF 1) (.dec rC)

/-- One step of the simulation of `M₁`. -/
noncomputable def body1 (M : TM) : Stmt 20 :=
  getSym (r1 7) ⨟ simStep M r1 inMv1 outAct1 ⨟ .ite (.zero rF) .skip (clear (r1 6))

/-- Initial configuration of `M₁` (registers `r1 1, r1 2, r1 3` are cleared). -/
noncomputable def init1 (M : TM) : Stmt 20 :=
  setC (r1 0) (M.eQ M.start) ⨟ clear (r1 1) ⨟ clear (r1 2) ⨟ clear (r1 3) ⨟
    setC (r1 6) (if M.halt M.start then 0 else 1)

/-- `r2 7 := code of the symbol at position rI of the end-marked word f w`. -/
noncomputable def sub (M : TM) : Stmt 20 :=
  .ite (.zero rI) (setC (r2 7) 0)
    (rewind ⨟ .left ⨟ init1 M ⨟ copy rI rC rT ⨟ .dec rC ⨟ setC (r2 7) 1 ⨟ clear rF ⨟
      .loop (.not (.zero (r1 6))) (body1 M))

/-- Registers not touched by the subroutine. -/
def SubFrame (σ τ : St 20) : Prop :=
  ∀ y : Fin 20, 8 ≤ y.val → y.val ≤ 16 → y ≠ r2 7 → τ.reg y = σ.reg y

lemma ach_inMv1 {w : Word} {B : ℕ} (x : InSym) (d : Dir) (σ : St 20) (Q : St 20 → Prop)
    (hp : σ.pos ≤ w.length + 1) (h : Q { σ with pos := min (d.move σ.pos) (w.length + 1) }) :
    Ach w B (inMv1 x d) σ Q := by
  cases d with
  | left =>
    refine ach_left ?_
    simp only [Dir.move] at h
    rwa [min_eq_left (by omega)] at h
  | stay =>
    refine ach_skip ?_
    simp only [Dir.move] at h
    rw [min_eq_left hp] at h
    simpa using h
  | right => exact ach_right h

lemma ach_outAct1 {w : Word} {B : ℕ} (o : Option Bool) (σ : St 20) (Q : St 20 → Prop)
    (hB : 3 ≤ B)
    (h : match o with
      | none => Q σ
      | some b => if σ.reg rC = 0 then Q ((σ.setReg (r2 7) (symCode (.bit b))).setReg rF 1)
          else Q (σ.setReg rC (σ.reg rC - 1))) :
    Ach w B (outAct1 o) σ Q := by
  cases o with
  | none => exact ach_skip h
  | some b =>
    simp only at h
    unfold outAct1
    by_cases h0 : σ.reg rC = 0
    · rw [if_pos h0] at h
      refine ach_iteT (by simp [Cond.eval, h0]) (ach_seq (ach_setC _ _ _ _ ?_
        (ach_setC _ _ _ _ (by omega) h)))
      cases b <;> simp [symCode] <;> omega
    · rw [if_neg h0] at h
      exact ach_iteF (by simp [Cond.eval, h0]) (ach_dec h)

section Sub

variable (M : TM) (f : Word → Word) (w : Word) (B S : ℕ)

/-- Loop invariant of the subroutine before the symbol is found: the registers represent the
configuration of `M` at time `t`. -/
def Inv1 (σ₀ : St 20) (i t : ℕ) (τ : St 20) : Prop :=
  Rep M r1 S (M.run w t).state (M.run w t).workPos (M.run w t).tape τ ∧
  τ.pos = (M.run w t).inPos ∧
  τ.reg (r1 6) = (if M.halt (M.run w t).state then 0 else 1) ∧ τ.reg rF = 0 ∧
  τ.reg (r2 7) = 1 ∧ τ.reg rC + (M.run w t).output.length = i - 1 ∧ τ.out = σ₀.out ∧
  SubFrame σ₀ τ

/-- After the symbol is found. -/
def Fnd (σ₀ : St 20) (i : ℕ) (τ : St 20) : Prop :=
  τ.reg (r1 6) = 0 ∧ τ.reg (r2 7) = symCode (inputSym (f w) i) ∧ τ.out = σ₀.out ∧
  SubFrame σ₀ τ

variable {M f w B S}

lemma Rep_setReg {K : ℕ} {M : TM} {ρ : Fin 8 → Fin K} {S : ℕ} {st : M.Q} {wp : ℕ}
    {T : ℕ → M.Γ} {σ : St K} (h : Rep M ρ S st wp T σ) (r : Fin K) (v : ℕ)
    (h0 : r ≠ ρ 0) (h1 : r ≠ ρ 1) (h2 : r ≠ ρ 2) (h3 : r ≠ ρ 3) :
    Rep M ρ S st wp T (σ.setReg r v) := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := h
  exact ⟨by simp [St.setReg_apply, Ne.symm h0, e0], by simp [St.setReg_apply, Ne.symm h1, e1], e2,
    by simp [St.setReg_apply, Ne.symm h2, e3], by simp [St.setReg_apply, Ne.symm h3, e4]⟩

lemma body1_step {T₀ : ℕ} (hT₀ : M.HaltsWith w T₀ (f w)) (hS : ∀ t, (M.run w t).workPos ≤ S)
    (hB1 : M.nQ + S + 2 + M.nG ^ (S + 2) ≤ B) (hB2 : (f w).length + 4 ≤ B)
    (σ₀ : St 20) (i t : ℕ) (τ : St 20) (hi1 : 1 ≤ i) (hτ : Inv1 M w S σ₀ i t τ)
    (hnh : M.halt (M.run w t).state = false) (ht : t < T₀) :
    Ach w B (body1 M) τ (fun τ' => Inv1 M w S σ₀ i (t + 1) τ' ∨ Fnd f w σ₀ i τ') := by
  obtain ⟨hRep, hpos, hrun, hF, hS2, hC, hout, hfr⟩ := hτ
  set c := M.run w t with hc
  have hstep := M.step_of_not_halt w c hnh
  have hc' : M.run w (t + 1) = M.step w c := M.run_succ w t
  rw [hstep] at hc'
  unfold body1
  refine ach_seq (ach_getSym (r1 7) τ _ (by omega) ?_)
  rw [hpos]
  set x := inputSym w c.inPos with hx
  set δv := M.δ c.state x (c.tape c.workPos) with hδv
  refine ach_seq (ach_simStep M r1 r1_injective inMv1 outAct1 S c.state c.workPos c.tape x
    (τ.setReg (r1 7) (symCode x)) (Rep_setReg hRep _ _ (by simp) (by simp) (by simp) (by simp))
    (by simp) ?_ hB1 _ ?_)
  · have := hS (t + 1); rw [hc'] at this; exact this
  intro σ' hRep' hrun' hfr' hpos' hout'
  rw [← hδv] at hRep' hrun' ⊢
  simp only [St.setReg_pos, St.setReg_out] at hpos' hout'
  have hfr8 : ∀ y : Fin 20, 8 ≤ y.val → σ'.reg y = τ.reg y := by
    intro y hy
    have hy' : ∀ i : Fin 8, y ≠ r1 i := fun i h => by subst h; simp at hy; omega
    rw [hfr' y hy', St.setReg_apply, if_neg (hy' 7)]
  have eC : σ'.reg rC = τ.reg rC := hfr8 rC (by simp)
  have eF : σ'.reg rF = τ.reg rF := hfr8 rF (by simp)
  have e27 : σ'.reg (r2 7) = τ.reg (r2 7) := hfr8 (r2 7) (by simp)
  have hpre : (M.run w (t + 1)).output <+: f w := by
    rw [← hT₀.2]; exact M.output_prefix w ht
  refine ach_seq (ach_inMv1 x _ σ' _ (by rw [hpos', hpos]; exact M.inPos_le w t) ?_)
  refine ach_outAct1 _ _ _ (by omega) ?_
  rw [hc'] at hpre
  rcases ho : δv.2.2.2.2 with _ | b
  · refine ach_iteT (by simp [Cond.eval, eF, hF]) (ach_skip (Or.inl ?_))
    unfold Inv1
    rw [hc']
    refine ⟨hRep', by simp [hpos', hpos], hrun', by simp [eF, hF], by simp [e27, hS2], ?_,
      by simp [hout', hout], fun y h1 h2 h3 => by simp [hfr8 y h1, hfr y h1 h2 h3]⟩
    simp [ho, eC, hC]
  · simp only
    by_cases h0 : σ'.reg rC = 0
    · rw [if_pos h0]
      refine ach_iteF (by simp [Cond.eval, St.setReg_apply]) (ach_clear _ _ _ (Or.inr ?_))
      refine ⟨by simp [St.setReg_apply], ?_, by simp [hout', hout], ?_⟩
      · simp only [ho] at hpre
        have hlen : c.output.length = i - 1 := by rw [eC] at h0; omega
        obtain ⟨u, hu⟩ := hpre
        have hget : (f w)[i - 1]? = some b := by
          rw [← hu, ← hlen]; simp
        simp [St.setReg_apply, inputSym_of_getElem? hi1 hget]
      · intro y h1 h2 h3
        have : y ≠ rF := fun h => by subst h; simp at h2
        have : y ≠ r1 6 := fun h => by subst h; simp at h1
        simp [St.setReg_apply, *, hfr8 y h1, hfr y h1 h2 h3]
    · rw [if_neg h0]
      refine ach_iteT (by simp [Cond.eval, St.setReg_apply, eF, hF]) (ach_skip (Or.inl ?_))
      unfold Inv1
      rw [hc']
      refine ⟨Rep_setReg hRep' _ _ (by simp) (by simp) (by simp) (by simp), by simp [hpos', hpos],
        by simp [St.setReg_apply, hrun'], by simp [St.setReg_apply, eF, hF],
        by simp [St.setReg_apply, e27, hS2], ?_, by simp [hout', hout], ?_⟩
      · simp [St.setReg_apply, ho, eC]
        rw [eC] at h0
        omega
      · intro y h1 h2 h3
        have : y ≠ rC := fun h => by subst h; simp at h2
        simp [St.setReg_apply, this, hfr8 y h1, hfr y h1 h2 h3]

lemma ach_subLoop {T₀ : ℕ} (hT₀ : M.HaltsWith w T₀ (f w)) (hS : ∀ t, (M.run w t).workPos ≤ S)
    (hB1 : M.nQ + S + 2 + M.nG ^ (S + 2) ≤ B) (hB2 : (f w).length + 4 ≤ B)
    (σ : St 20) (i : ℕ) (hi0 : i ≠ 0) (Q : St 20 → Prop)
    (h : ∀ σ' : St 20, σ'.reg (r2 7) = symCode (inputSym (f w) i) → σ'.out = σ.out →
      SubFrame σ σ' → Q σ') (τ₀ : St 20) (hinit : Inv1 M w S σ i 0 τ₀) :
    Ach w B (.loop (.not (.zero (r1 6))) (body1 M)) τ₀ Q := by
  refine ach_loop (fun n τ => (∃ t, t ≤ T₀ ∧ n = T₀ - t ∧ Inv1 M w S σ i t τ) ∨
      Fnd f w σ i τ) Q ?_ T₀ τ₀ (Or.inl ⟨0, by omega, by omega, hinit⟩)
  rintro n τ (⟨t, htT, rfl, hinv⟩ | ⟨h6, h27, hout, hfr⟩)
  · by_cases hh : M.halt (M.run w t).state
    · left
      refine ⟨by simp [Cond.eval, hinv.2.2.1, hh], h τ ?_ hinv.2.2.2.2.2.2.1 hinv.2.2.2.2.2.2.2⟩
      rw [hinv.2.2.2.2.1]
      have hout : (M.run w t).output = f w := by
        rw [← hT₀.2, M.run_halted' w hh htT]
      have := hinv.2.2.2.2.2.1
      rw [hout] at this
      rw [inputSym_of_le (by omega) (by omega)]
      rfl
    · right
      have hh' : M.halt (M.run w t).state = false := by simpa using hh
      have htT' : t < T₀ := by
        rcases Nat.lt_or_ge t T₀ with h' | h'
        · exact h'
        · have : t = T₀ := by omega
          subst this; rw [hT₀.1] at hh'; exact absurd hh' (by simp)
      refine ⟨by simp [Cond.eval, hinv.2.2.1, hh'], ?_⟩
      refine (body1_step hT₀ hS hB1 hB2 σ i t τ (by omega) hinv hh' htT').mono ?_
      rintro τ' (h' | h')
      · exact ⟨T₀ - (t + 1), by omega, Or.inl ⟨t + 1, by omega, rfl, h'⟩⟩
      · exact ⟨0, by omega, Or.inr h'⟩
  · left
    exact ⟨by simp [Cond.eval, h6], h τ h27 hout hfr⟩

lemma ach_sub {T₀ : ℕ} (hT₀ : M.HaltsWith w T₀ (f w)) (hS : ∀ t, (M.run w t).workPos ≤ S)
    (hB1 : M.nQ + S + 2 + M.nG ^ (S + 2) ≤ B) (hB2 : (f w).length + 4 ≤ B)
    (σ : St 20) (hil : σ.reg rI ≤ (f w).length + 1) (Q : St 20 → Prop)
    (h : ∀ σ' : St 20, σ'.reg (r2 7) = symCode (inputSym (f w) (σ.reg rI)) → σ'.out = σ.out →
      SubFrame σ σ' → Q σ') :
    Ach w B (sub M) σ Q := by
  set i := σ.reg rI with hi
  unfold sub
  refine ach_ite ?_
  by_cases hi0 : i = 0
  · rw [if_pos (by simp [Cond.eval, ← hi, hi0])]
    refine ach_setC _ _ _ _ (by omega) (h _ ?_ rfl ?_)
    · simp [hi0, inputSym, symCode]
    · intro y _ _ h3; simp [St.setReg_apply, h3]
  rw [if_neg (by simp [Cond.eval, ← hi, hi0])]
  have hQ := M.eQ_lt M.start
  refine ach_seq (ach_rewind _ _ (ach_seq (ach_left (ach_seq (ach_seq (ach_setC _ _ _ _
    (by omega) (ach_seq (ach_clear _ _ _ (ach_seq (ach_clear _ _ _ (ach_seq (ach_clear _ _ _
    (ach_setC _ _ _ _ (by split_ifs <;> omega) ?_)))))))))))))
  refine ach_seq (ach_copy _ _ _ (by simp) (by simp) (by simp) _ _
    (by simp [St.setReg_apply, ← hi]; omega) ?_)
  refine ach_seq (ach_dec (ach_seq (ach_setC _ _ _ _ (by omega) (ach_seq (ach_clear _ _ _ ?_)))))
  refine ach_subLoop hT₀ hS hB1 hB2 σ i hi0 Q h _ ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp [St.setReg_apply, M.run_zero, TM.init, encL, encR_blank, ← hi]
  · intro y h1 h2 h3
    have : y ≠ rC := fun h => by subst h; simp at h2
    have : y ≠ rT := fun h => by subst h; simp at h2
    have : y ≠ rF := fun h => by subst h; simp at h2
    have : ∀ j : Fin 8, y ≠ r1 j := fun j h => by subst h; simp at h1; omega
    simp [*]

end Sub

/-! ## The main loop: simulating `M₂` on the virtual input `f w` -/

/-- Input head moves of `M₂`: the register `rI`. -/
def inMv2 : InSym → Dir → Stmt 20
  | _, .left => .dec rI
  | _, .stay => .skip
  | x, .right => if x = .rend then .skip else .inc rI

/-- Output of `M₂`: the real output. -/
def outAct2 : Option Bool → Stmt 20
  | none => .skip
  | some b => .out b

/-- One step of `M₂`: fetch the virtual input symbol, then simulate. -/
noncomputable def body2 (M₁ M₂ : TM) : Stmt 20 :=
  sub M₁ ⨟ simStep M₂ r2 inMv2 outAct2

/-- The program computing `g ∘ f`. -/
noncomputable def compProg (M₁ M₂ : TM) : Stmt 20 :=
  setC (r2 0) (M₂.eQ M₂.start) ⨟ setC (r2 6) (if M₂.halt M₂.start then 0 else 1) ⨟
    .loop (.not (.zero (r2 6))) (body2 M₁ M₂)

lemma ach_inMv2 {w u : Word} {B : ℕ} (x : InSym) (d : Dir) (σ : St 20) (Q : St 20 → Prop)
    (hx : x = inputSym u (σ.reg rI)) (hp : σ.reg rI ≤ u.length + 1) (hB : u.length + 1 ≤ B)
    (h : Q (σ.setReg rI (min (d.move (σ.reg rI)) (u.length + 1)))) :
    Ach w B (inMv2 x d) σ Q := by
  cases d with
  | left =>
    refine ach_dec ?_
    simp only [Dir.move] at h
    rwa [min_eq_left (by omega)] at h
  | stay =>
    refine ach_skip ?_
    simp only [Dir.move] at h
    rw [min_eq_left hp] at h
    simpa using h
  | right =>
    simp only [Dir.move] at h
    show Ach w B (if x = .rend then .skip else .inc rI) σ Q
    by_cases hr : x = .rend
    · rw [if_pos hr]
      refine ach_skip ?_
      have h1 : 1 ≤ σ.reg rI := by
        by_contra h0
        rw [show σ.reg rI = 0 by omega] at hx
        simp [inputSym] at hx
        exact absurd hr (by rw [hx]; simp)
      have := (inputSym_eq_rend (w := u) h1 hp).1 (hx ▸ hr)
      rw [min_eq_right (by omega), ← this] at h
      simpa using h
    · rw [if_neg hr]
      have h2 : σ.reg rI ≠ u.length + 1 := by
        intro he
        apply hr
        rw [hx, he]
        exact inputSym_of_le (by omega) le_rfl
      refine ach_inc (by omega) ?_
      rwa [min_eq_left (by omega)] at h

section Main

variable {M₁ M₂ : TM} {f g : Word → Word} {w : Word} {B S₁ S₂ : ℕ}

/-- Invariant of the main loop: the registers represent the configuration of `M₂` on `f w`
at time `t`. -/
def Inv2 (M₂ : TM) (u : Word) (S₂ t : ℕ) (τ : St 20) : Prop :=
  Rep M₂ r2 S₂ (M₂.run u t).state (M₂.run u t).workPos (M₂.run u t).tape τ ∧
  τ.reg rI = (M₂.run u t).inPos ∧
  τ.reg (r2 6) = (if M₂.halt (M₂.run u t).state then 0 else 1) ∧
  τ.out = (M₂.run u t).output

lemma body2_step {T₀ : ℕ} (hT₀ : M₁.HaltsWith w T₀ (f w)) (hS₁ : ∀ t, (M₁.run w t).workPos ≤ S₁)
    (hS₂ : ∀ t, (M₂.run (f w) t).workPos ≤ S₂)
    (hB1 : M₁.nQ + S₁ + 2 + M₁.nG ^ (S₁ + 2) ≤ B) (hB2 : (f w).length + 4 ≤ B)
    (hB3 : M₂.nQ + S₂ + 2 + M₂.nG ^ (S₂ + 2) ≤ B)
    (t : ℕ) (τ : St 20) (hτ : Inv2 M₂ (f w) S₂ t τ)
    (hnh : M₂.halt (M₂.run (f w) t).state = false) :
    Ach w B (body2 M₁ M₂) τ (Inv2 M₂ (f w) S₂ (t + 1)) := by
  obtain ⟨hRep, hI, hrun, hout⟩ := hτ
  set u := f w with hu
  set c := M₂.run u t with hc
  have hstep := M₂.step_of_not_halt u c hnh
  have hc' : M₂.run u (t + 1) = M₂.step u c := M₂.run_succ u t
  rw [hstep] at hc'
  have hIle : τ.reg rI ≤ u.length + 1 := by rw [hI]; exact M₂.inPos_le u t
  unfold body2
  refine ach_seq (ach_sub hT₀ hS₁ hB1 hB2 τ hIle _ ?_)
  intro σ' h27 hout' hfr
  rw [hI] at h27
  set x := inputSym u c.inPos with hx
  set δv := M₂.δ c.state x (c.tape c.workPos) with hδv
  have eR : ∀ j : Fin 8, j ≠ 7 → σ'.reg (r2 j) = τ.reg (r2 j) := fun j hj =>
    hfr (r2 j) (by simp) (by simp only [r2_val]; omega) (by simpa using hj)
  have eI : σ'.reg rI = τ.reg rI := hfr rI (by simp) (by simp) (by simp)
  obtain ⟨e0, e1, e2, e3, e4⟩ := hRep
  have hRep1 : Rep M₂ r2 S₂ c.state c.workPos c.tape σ' :=
    ⟨by rw [eR 0 (by decide), e0], by rw [eR 1 (by decide), e1], e2,
      by rw [eR 2 (by decide), e3], by rw [eR 3 (by decide), e4]⟩
  refine ach_simStep M₂ r2 r2_injective inMv2 outAct2 S₂ c.state c.workPos c.tape x σ' hRep1
    h27 ?_ hB3 _ ?_
  · have := hS₂ (t + 1); rw [hc'] at this; exact this
  intro σ'' hRep' hrun' hfr' hpos' hout''
  rw [← hδv] at hRep' hrun' ⊢
  have eI' : σ''.reg rI = c.inPos := by rw [hfr' rI (by simp), eI, hI]
  refine ach_seq (ach_inMv2 (u := u) x _ σ'' _ (by rw [eI']) (by rw [eI']; exact M₂.inPos_le u t)
    (by omega) ?_)
  rcases ho : δv.2.2.2.2 with _ | b
  · refine ach_skip ?_
    unfold Inv2
    rw [hc']
    refine ⟨Rep_setReg hRep' rI (min (δv.2.2.2.1.move (σ''.reg rI)) (u.length + 1)) (by simp) (by simp) (by simp) (by simp), by simp [eI'],
      by simp [St.setReg_apply, hrun'], ?_⟩
    simp [hout'', hout', hout, ho]
  · refine ach_out ?_
    unfold Inv2
    rw [hc']
    refine ⟨Rep_setReg hRep' rI (min (δv.2.2.2.1.move (σ''.reg rI)) (u.length + 1)) (by simp) (by simp) (by simp) (by simp), by simp [eI'],
      by simp [St.setReg_apply, hrun'], ?_⟩
    simp [hout'', hout', hout, ho]

lemma ach_mainLoop {T₀ T₂ : ℕ} (hT₀ : M₁.HaltsWith w T₀ (f w))
    (hT₂ : M₂.HaltsWith (f w) T₂ (g (f w))) (hS₁ : ∀ t, (M₁.run w t).workPos ≤ S₁)
    (hS₂ : ∀ t, (M₂.run (f w) t).workPos ≤ S₂)
    (hB1 : M₁.nQ + S₁ + 2 + M₁.nG ^ (S₁ + 2) ≤ B) (hB2 : (f w).length + 4 ≤ B)
    (hB3 : M₂.nQ + S₂ + 2 + M₂.nG ^ (S₂ + 2) ≤ B) (τ₀ : St 20)
    (hinit : Inv2 M₂ (f w) S₂ 0 τ₀) :
    Ach w B (.loop (.not (.zero (r2 6))) (body2 M₁ M₂)) τ₀ (fun σ => σ.out = g (f w)) := by
  refine ach_loop (fun n τ => ∃ t, t ≤ T₂ ∧ n = T₂ - t ∧ Inv2 M₂ (f w) S₂ t τ) _ ?_ T₂ τ₀
    ⟨0, by omega, by omega, hinit⟩
  rintro n τ ⟨t, htT, rfl, hinv⟩
  by_cases hh : M₂.halt (M₂.run (f w) t).state
  · left
    refine ⟨by simp [Cond.eval, hinv.2.2.1, hh], ?_⟩
    rw [hinv.2.2.2, ← hT₂.2, M₂.run_halted' _ hh htT]
  · right
    have hh' : M₂.halt (M₂.run (f w) t).state = false := by simpa using hh
    have htT' : t < T₂ := by
      rcases Nat.lt_or_ge t T₂ with h' | h'
      · exact h'
      · have : t = T₂ := by omega
        subst this; rw [hT₂.1] at hh'; exact absurd hh' (by simp)
    refine ⟨by simp [Cond.eval, hinv.2.2.1, hh'], ?_⟩
    exact (body2_step hT₀ hS₁ hS₂ hB1 hB2 hB3 t τ hinv hh').mono
      (fun τ' h' => ⟨T₂ - (t + 1), by omega, t + 1, by omega, rfl, h'⟩)

lemma ach_compProg {T₀ T₂ : ℕ} (hT₀ : M₁.HaltsWith w T₀ (f w))
    (hT₂ : M₂.HaltsWith (f w) T₂ (g (f w))) (hS₁ : ∀ t, (M₁.run w t).workPos ≤ S₁)
    (hS₂ : ∀ t, (M₂.run (f w) t).workPos ≤ S₂)
    (hB1 : M₁.nQ + S₁ + 2 + M₁.nG ^ (S₁ + 2) ≤ B) (hB2 : (f w).length + 4 ≤ B)
    (hB3 : M₂.nQ + S₂ + 2 + M₂.nG ^ (S₂ + 2) ≤ B) :
    Ach w B (compProg M₁ M₂) (St.init 20) (fun σ => σ.out = g (f w)) := by
  have hQ := M₂.eQ_lt M₂.start
  unfold compProg
  refine ach_seq (ach_setC _ _ _ _ (by omega) (ach_seq (ach_setC _ _ _ _
    (by split_ifs <;> omega) ?_)))
  refine ach_mainLoop hT₀ hT₂ hS₁ hS₂ hB1 hB2 hB3 _ ?_
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals simp [St.setReg_apply, St.init, M₂.run_zero, TM.init, encL, encR_blank]

end Main

/-- A crude polynomial bound used for the register bound. -/
lemma le_two_pow_mul {a L : ℕ} (hL : 1 ≤ L) : a ≤ 2 ^ (a * L) :=
  (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hL))

lemma pow_le_two_pow_mul {G k L c : ℕ} (hL : 1 ≤ L) (hk : k ≤ c * L + 2) :
    G ^ k ≤ 2 ^ (G * ((c + 2) * L)) := by
  calc G ^ k ≤ (2 ^ G) ^ k := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
    _ = 2 ^ (G * k) := by rw [← pow_mul]
    _ ≤ 2 ^ (G * ((c + 2) * L)) := Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ (by nlinarith))

lemma register_bound (q₁ G₁ c₁ q₂ G₂ c₂ e₁ n nf : ℕ)
    (hfl : nf + 2 ≤ 2 ^ (e₁ * (Nat.log 2 n + 1))) :
    (q₁ + c₁ * (Nat.log 2 n + 1) + 2 + G₁ ^ (c₁ * (Nat.log 2 n + 1) + 2)) +
      (q₂ + c₂ * (Nat.log 2 nf + 1) + 2 + G₂ ^ (c₂ * (Nat.log 2 nf + 1) + 2)) + (nf + 4) <
    2 ^ ((q₁ + c₁ + G₁ * (c₁ + 2) + q₂ + c₂ * (e₁ + 1) + G₂ * (c₂ * (e₁ + 1) + 2) + e₁ + 4) *
      (Nat.log 2 n + 1)) := by
  set L := Nat.log 2 n + 1 with hL
  set m := q₁ + c₁ + G₁ * (c₁ + 2) + q₂ + c₂ * (e₁ + 1) + G₂ * (c₂ * (e₁ + 1) + 2) + e₁
  have hL1 : 1 ≤ L := by omega
  have hmL : ∀ a, a ≤ m → 2 ^ (a * L) ≤ 2 ^ (m * L) := fun a ha =>
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ ha)
  have he : 1 ≤ e₁ * L := by
    by_contra h0
    rw [show e₁ * L = 0 by omega] at hfl
    simp at hfl
  have hlog : Nat.log 2 nf < e₁ * L := by
    rcases Nat.eq_zero_or_pos nf with h0 | h0
    · rw [h0, Nat.log_zero_right]; omega
    · exact Nat.log_lt_of_lt_pow (by omega) (by omega)
  have hS2 : c₂ * (Nat.log 2 nf + 1) ≤ c₂ * (e₁ + 1) * L := by
    have : Nat.log 2 nf + 1 ≤ (e₁ + 1) * L := by nlinarith
    calc c₂ * (Nat.log 2 nf + 1) ≤ c₂ * ((e₁ + 1) * L) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  have hX : 1 ≤ 2 ^ (m * L) := Nat.one_le_two_pow
  have t1 : q₁ ≤ 2 ^ (m * L) := (le_two_pow_mul hL1).trans (hmL _ (by omega))
  have t2 : c₁ * L ≤ 2 ^ (m * L) := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega)))
  have t3 : G₁ ^ (c₁ * L + 2) ≤ 2 ^ (m * L) :=
    (pow_le_two_pow_mul hL1 (c := c₁) le_rfl).trans (by
      rw [← mul_assoc]; exact hmL _ (by omega))
  have t4 : q₂ ≤ 2 ^ (m * L) := (le_two_pow_mul hL1).trans (hmL _ (by omega))
  have t5 : c₂ * (Nat.log 2 nf + 1) ≤ 2 ^ (m * L) := hS2.trans ((Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))))
  have t6 : G₂ ^ (c₂ * (Nat.log 2 nf + 1) + 2) ≤ 2 ^ (m * L) :=
    (pow_le_two_pow_mul hL1 (c := c₂ * (e₁ + 1)) (by omega)).trans (by
      rw [← mul_assoc]; exact hmL _ (by omega))
  have t7 : nf + 4 ≤ 2 * 2 ^ (m * L) := by
    have : 2 ^ (e₁ * L) ≤ 2 ^ (m * L) := hmL _ (by omega)
    omega
  have h16 : 2 ^ (4 + m * L) ≤ 2 ^ ((m + 4) * L) :=
    Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  rw [pow_add] at h16
  omega

end LS

open LS in
/-- **Composition of logspace computable functions.** -/
theorem LogspaceComputable.comp {f g : Word → Word} (hf : LogspaceComputable f)
    (hg : LogspaceComputable g) : LogspaceComputable (g ∘ f) := by
  obtain ⟨M₁, c₁, e₁, hM₁, hS₁, hlen⟩ := hf.exists_bound
  obtain ⟨M₂, c₂, hM₂, hS₂⟩ := hg
  let S₁ : Word → ℕ := fun w => c₁ * (Nat.log 2 w.length + 1)
  let S₂ : Word → ℕ := fun w => c₂ * (Nat.log 2 (f w).length + 1)
  let B : Word → ℕ := fun w => (M₁.nQ + S₁ w + 2 + M₁.nG ^ (S₁ w + 2)) +
    (M₂.nQ + S₂ w + 2 + M₂.nG ^ (S₂ w + 2)) + ((f w).length + 4)
  refine logspaceComputable_of_prog (compProg M₁ M₂) (g ∘ f) B
    (M₁.nQ + c₁ + M₁.nG * (c₁ + 2) + M₂.nQ + c₂ * (e₁ + 1) + M₂.nG * (c₂ * (e₁ + 1) + 2) + e₁ + 4)
    (fun w => ?_) (fun w => ?_)
  · exact register_bound _ _ _ _ _ _ _ _ _ (hlen w)
  · obtain ⟨T₀, hT₀⟩ := hM₁ w
    obtain ⟨T₂, hT₂⟩ := hM₂ (f w)
    obtain ⟨σ', h1, h2⟩ := ach_compProg (B := B w) hT₀ hT₂ (hS₁ w) (hS₂ (f w))
      (by simp only [B, S₁, S₂]; omega) (by simp only [B]; omega) (by simp only [B, S₁, S₂]; omega)
    exact ⟨σ', h1, h2⟩

/-- **Logspace many-one reductions compose.** -/
theorem LogspaceReducible.trans {A B C : Language} (hAB : LogspaceReducible A B)
    (hBC : LogspaceReducible B C) : LogspaceReducible A C := by
  obtain ⟨f, hf, hfAB⟩ := hAB
  obtain ⟨g, hg, hgBC⟩ := hBC
  exact ⟨g ∘ f, hf.comp hg, fun w => (hfAB w).trans (hgBC (f w))⟩

end PathChecking
