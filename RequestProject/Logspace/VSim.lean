module

public import RequestProject.Logspace.Compose

/-!
# Simulating a Turing machine on a virtual input

A generic register program `vsim M ρ fetch mv oa` runs the machine `M` on a *virtual* input
word `u`: the configuration of `M` is kept in the registers `ρ 0, …, ρ 6` (as in
`Logspace/SimTM.lean`), the input symbol under the virtual head is fetched into `ρ 7` by the
program `fetch`, the virtual input head is moved by `mv`, and every output bit of `M` is
handled by `oa`.  The behaviour of these three parameter programs is described abstractly by a
predicate `Aux p o σ` ("the virtual head is at `p` and the output so far is represented by
`σ` as `o`"), see `VSpec`.
-/

@[expose] public section

namespace PathChecking

open Classical

namespace LS

open scoped LS

variable {K : ℕ}

/-- The specification of the parameter programs of the virtual simulation. -/
structure VSpec (w : Word) (B : ℕ) (ρ : Fin 8 → Fin K) (u : Word) (fetch : Stmt K)
    (mv : InSym → Dir → Stmt K) (oa : Option Bool → Stmt K)
    (Aux : ℕ → List Bool → St K → Prop) : Prop where
  frame : ∀ p o (σ τ : St K), Aux p o σ → (∀ y, (∀ i, y ≠ ρ i) → τ.reg y = σ.reg y) →
    τ.pos = σ.pos → τ.out = σ.out → Aux p o τ
  fetch : ∀ p o (σ : St K), p ≤ u.length + 1 → Aux p o σ →
    Ach w B fetch σ (fun τ => τ.reg (ρ 7) = symCode (inputSym u p) ∧
      (∀ i : Fin 8, i ≠ 7 → τ.reg (ρ i) = σ.reg (ρ i)) ∧ Aux p o τ)
  mv : ∀ p o (σ : St K) x d, p ≤ u.length + 1 → x = inputSym u p → Aux p o σ →
    Ach w B (mv x d) σ (fun τ => (∀ i, τ.reg (ρ i) = σ.reg (ρ i)) ∧
      Aux (min (d.move p) (u.length + 1)) o τ)
  oa : ∀ p o (σ : St K) ob, Aux p o σ →
    Ach w B (oa ob) σ (fun τ => (∀ i, τ.reg (ρ i) = σ.reg (ρ i)) ∧ Aux p (o ++ ob.toList) τ)

/-- One step of the virtual simulation. -/
noncomputable def vBody (M : TM) (ρ : Fin 8 → Fin K) (fetch : Stmt K)
    (mv : InSym → Dir → Stmt K) (oa : Option Bool → Stmt K) : Stmt K :=
  fetch ⨟ simStep M ρ mv oa

/-- Initialisation of the simulation registers. -/
noncomputable def vInit (M : TM) (ρ : Fin 8 → Fin K) : Stmt K :=
  setC (ρ 0) (M.eQ M.start) ⨟ clear (ρ 1) ⨟ clear (ρ 2) ⨟ clear (ρ 3) ⨟
    setC (ρ 6) (if M.halt M.start then 0 else 1)

/-- The virtual simulation. -/
noncomputable def vsim (M : TM) (ρ : Fin 8 → Fin K) (fetch : Stmt K)
    (mv : InSym → Dir → Stmt K) (oa : Option Bool → Stmt K) : Stmt K :=
  vInit M ρ ⨟ .loop (.not (.zero (ρ 6))) (vBody M ρ fetch mv oa)

/-- Invariant of the simulation loop. -/
def VInv (M : TM) (ρ : Fin 8 → Fin K) (u : Word) (S : ℕ) (Aux : ℕ → List Bool → St K → Prop)
    (t : ℕ) (τ : St K) : Prop :=
  Rep M ρ S (M.run u t).state (M.run u t).workPos (M.run u t).tape τ ∧
  τ.reg (ρ 6) = (if M.halt (M.run u t).state then 0 else 1) ∧
  Aux (M.run u t).inPos (M.run u t).output τ

section Lemmas

variable {w : Word} {B : ℕ} {M : TM} {ρ : Fin 8 → Fin K} {u : Word} {S : ℕ} {fetch : Stmt K}
  {mv : InSym → Dir → Stmt K} {oa : Option Bool → Stmt K} {Aux : ℕ → List Bool → St K → Prop}

lemma Rep_congr {st : M.Q} {wp : ℕ} {T : ℕ → M.Γ} {σ τ : St K}
    (h : Rep M ρ S st wp T σ) (he : ∀ i, τ.reg (ρ i) = σ.reg (ρ i)) : Rep M ρ S st wp T τ := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := h
  exact ⟨by rw [he, e0], by rw [he, e1], e2, by rw [he, e3], by rw [he, e4]⟩

lemma vBody_step (hρ : Function.Injective ρ) (spec : VSpec w B ρ u fetch mv oa Aux)
    (hS : ∀ t, (M.run u t).workPos ≤ S) (hB : M.nQ + S + 2 + M.nG ^ (S + 2) ≤ B)
    (t : ℕ) (τ : St K) (hτ : VInv M ρ u S Aux t τ)
    (hnh : M.halt (M.run u t).state = false) :
    Ach w B (vBody M ρ fetch mv oa) τ (VInv M ρ u S Aux (t + 1)) := by
  obtain ⟨hRep, hrun, haux⟩ := hτ
  set c := M.run u t with hc
  have hstep := M.step_of_not_halt u c hnh
  have hc' : M.run u (t + 1) = M.step u c := M.run_succ u t
  rw [hstep] at hc'
  have hIle : c.inPos ≤ u.length + 1 := M.inPos_le u t
  unfold vBody
  refine ach_seq ((spec.fetch _ _ τ hIle haux).mono ?_)
  rintro σ' ⟨h7, hfr, haux'⟩
  set x := inputSym u c.inPos with hx
  set δv := M.δ c.state x (c.tape c.workPos) with hδv
  obtain ⟨e0, e1, e2, e3, e4⟩ := hRep
  have hRep1 : Rep M ρ S c.state c.workPos c.tape σ' :=
    ⟨by rw [hfr 0 (by decide), e0], by rw [hfr 1 (by decide), e1], e2,
      by rw [hfr 2 (by decide), e3], by rw [hfr 3 (by decide), e4]⟩
  refine ach_simStep M ρ hρ mv oa S c.state c.workPos c.tape x σ' hRep1 h7 ?_ hB _ ?_
  · have := hS (t + 1); rw [hc'] at this; exact this
  intro σ'' hRep' hrun' hfr' hpos' hout''
  rw [← hδv] at hRep' hrun' ⊢
  have aux'' := spec.frame _ _ σ' σ'' haux' hfr' hpos' hout''
  refine ach_seq ((spec.mv _ _ σ'' x δv.2.2.2.1 hIle rfl aux'').mono ?_)
  rintro σ3 ⟨hr3, aux3⟩
  refine (spec.oa _ _ σ3 δv.2.2.2.2 aux3).mono ?_
  rintro σ4 ⟨hr4, aux4⟩
  have hr : ∀ i, σ4.reg (ρ i) = σ''.reg (ρ i) := fun i => (hr4 i).trans (hr3 i)
  unfold VInv
  rw [hc']
  exact ⟨Rep_congr hRep' hr, by rw [hr]; exact hrun', aux4⟩

lemma ach_vLoop (hρ : Function.Injective ρ) (spec : VSpec w B ρ u fetch mv oa Aux)
    (hS : ∀ t, (M.run u t).workPos ≤ S) (hB : M.nQ + S + 2 + M.nG ^ (S + 2) ≤ B)
    {T₂ : ℕ} {o : Word} (hT₂ : M.HaltsWith u T₂ o) (τ₀ : St K)
    (hinit : VInv M ρ u S Aux 0 τ₀) :
    Ach w B (.loop (.not (.zero (ρ 6))) (vBody M ρ fetch mv oa)) τ₀
      (fun σ => ∃ p, Aux p o σ) := by
  refine ach_loop (fun n τ => ∃ t, t ≤ T₂ ∧ n = T₂ - t ∧ VInv M ρ u S Aux t τ) _ ?_ T₂ τ₀
    ⟨0, by omega, by omega, hinit⟩
  rintro n τ ⟨t, htT, rfl, hinv⟩
  by_cases hh : M.halt (M.run u t).state
  · left
    refine ⟨by simp [Cond.eval, hinv.2.1, hh], ?_⟩
    refine ⟨(M.run u t).inPos, ?_⟩
    have e : (M.run u t).output = o := by rw [← hT₂.2, M.run_halted' u hh htT]
    rw [← e]; exact hinv.2.2
  · right
    have hh' : M.halt (M.run u t).state = false := by simpa using hh
    have htT' : t < T₂ := by
      rcases Nat.lt_or_ge t T₂ with h' | h'
      · exact h'
      · have : t = T₂ := by omega
        subst this; rw [hT₂.1] at hh'; exact absurd hh' (by simp)
    refine ⟨by simp [Cond.eval, hinv.2.1, hh'], ?_⟩
    exact (vBody_step hρ spec hS hB t τ hinv hh').mono
      (fun τ' h' => ⟨T₂ - (t + 1), by omega, t + 1, by omega, rfl, h'⟩)

lemma ach_vInit (hρ : Function.Injective ρ) (spec : VSpec w B ρ u fetch mv oa Aux)
    (hB : M.nQ ≤ B) (τ : St K) (haux : Aux 0 [] τ) :
    Ach w B (vInit M ρ) τ (VInv M ρ u S Aux 0) := by
  have hQ := M.eQ_lt M.start
  have ne : ∀ i j : Fin 8, i ≠ j → ρ i ≠ ρ j := fun i j h => hρ.ne h
  unfold vInit
  refine ach_seq (ach_setC _ _ _ _ (by omega) ?_)
  refine ach_seq (ach_clear _ _ _ ?_)
  refine ach_seq (ach_clear _ _ _ ?_)
  refine ach_seq (ach_clear _ _ _ ?_)
  refine ach_setC _ _ _ _ (by split_ifs <;> omega) ?_
  set τ' := ((((τ.setReg (ρ 0) (M.eQ M.start)).setReg (ρ 1) 0).setReg (ρ 2) 0).setReg (ρ 3)
    0).setReg (ρ 6) (if M.halt M.start then 0 else 1) with hτ'
  have hoff : ∀ y, (∀ i, y ≠ ρ i) → τ'.reg y = τ.reg y := by
    intro y hy
    simp [hτ', St.setReg_apply, hy]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  all_goals simp only [M.run_zero, TM.init]
  · simp [hτ', St.setReg_apply, hρ.eq_iff]
  · simp [hτ', St.setReg_apply, hρ.eq_iff]
  · omega
  · simp [hτ', St.setReg_apply, hρ.eq_iff, encL]
  · simp [hτ', St.setReg_apply, hρ.eq_iff, encR_blank]
  · simp [hτ', St.setReg_apply]
  · exact spec.frame _ _ τ τ' haux hoff rfl rfl

/-- **The virtual simulation.**  If `M` halts on the virtual input `u` with output `o`, then
`vsim` terminates in a state where the output `o` has been handled. -/
theorem ach_vsim (hρ : Function.Injective ρ) (spec : VSpec w B ρ u fetch mv oa Aux)
    (hS : ∀ t, (M.run u t).workPos ≤ S) (hB : M.nQ + S + 2 + M.nG ^ (S + 2) ≤ B)
    {T₂ : ℕ} {o : Word} (hT₂ : M.HaltsWith u T₂ o) (τ : St K) (haux : Aux 0 [] τ) :
    Ach w B (vsim M ρ fetch mv oa) τ (fun σ => ∃ p, Aux p o σ) := by
  unfold vsim
  refine ach_seq ((ach_vInit (S := S) hρ spec (by omega) τ haux).mono ?_)
  intro σ h
  exact ach_vLoop hρ spec hS hB hT₂ σ h

end Lemmas

end LS

end PathChecking
