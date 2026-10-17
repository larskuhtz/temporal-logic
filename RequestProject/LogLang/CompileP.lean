module

public import RequestProject.LogLang.CompileE

/-!
# Compiling programs of the loop language into register programs

`compP K L s d` compiles the program `s`, placed at loop-nesting depth `d`.  Registers:
`0 … V-1` hold the variables, `V` holds the cap, `V+1+2j` / `V+2+2j` are the limit and the
counter of the loop at depth `j < L`, and registers `≥ V+1+2L` are scratch space.
-/

@[expose] public section

namespace PathChecking

namespace LL

open LS
open scoped LS

/-- Loop-nesting depth. -/
def Pr.ld {V : ℕ} : Pr V → ℕ
  | .skip => 0
  | .set _ _ => 0
  | .out _ => 0
  | .seq s t => max s.ld t.ld
  | .ite _ s t => max s.ld t.ld
  | .loop _ _ s => s.ld + 1

/-- Largest depth of an expression in a program. -/
def Pr.ed {V : ℕ} : Pr V → ℕ
  | .skip => 0
  | .set _ e => e.depth
  | .out e => e.depth
  | .seq s t => max s.ed t.ed
  | .ite e s t => max e.depth (max s.ed t.ed)
  | .loop _ e s => max e.depth s.ed

/-- Largest constant in a program. -/
def Pr.mc {V : ℕ} : Pr V → ℕ
  | .skip => 0
  | .set _ e => e.mc
  | .out e => e.mc
  | .seq s t => max s.mc t.mc
  | .ite e s t => max e.mc (max s.mc t.mc)
  | .loop _ e s => max e.mc s.mc

/-- Compilation of programs. -/
def compP (K L : ℕ) {V : ℕ} : Pr V → ℕ → Stmt (K + 1)
  | .skip, _ => .skip
  | .set x e, _ => compE K V e (V + 1 + 2 * L) (V + 2 + 2 * L) ⨟
      copy (R K (V + 1 + 2 * L)) (R K x) (R K (V + 2 + 2 * L))
  | .out e, _ => compE K V e (V + 1 + 2 * L) (V + 2 + 2 * L) ⨟
      .ite (.zero (R K (V + 1 + 2 * L))) (.out false) (.out true)
  | .seq s u, d => compP K L s d ⨟ compP K L u d
  | .ite e s u, d => compE K V e (V + 1 + 2 * L) (V + 2 + 2 * L) ⨟
      .ite (.zero (R K (V + 1 + 2 * L))) (compP K L u d) (compP K L s d)
  | .loop x e s, d => compE K V e (V + 1 + 2 * d) (V + 1 + 2 * L) ⨟ clear (R K (V + 2 + 2 * d)) ⨟
      whileNZ (R K (V + 1 + 2 * d)) (copy (R K (V + 2 + 2 * d)) (R K x) (R K (V + 1 + 2 * L)) ⨟
        compP K L s (d + 1) ⨟ .inc (R K (V + 2 + 2 * d)) ⨟ .dec (R K (V + 1 + 2 * d)))

section
variable {w : Word} {B C K L : ℕ}

/-- The body of the loop semantics. -/
def loopF {V : ℕ} (w : Word) (C : ℕ) (x : Fin V) (s : Pr V) (acc : (Fin V → ℕ) × List Bool)
    (i : ℕ) : (Fin V → ℕ) × List Bool :=
  ((s.run w C (Function.update acc.1 x i)).1, acc.2 ++ (s.run w C (Function.update acc.1 x i)).2)

lemma run_loop {V : ℕ} (x : Fin V) (e : Ex V) (s : Pr V) (ρ : Fin V → ℕ) :
    (Pr.loop x e s).run w C ρ = (List.range (e.eval w C ρ)).foldl (loopF w C x s) (ρ, []) := rfl

lemma foldl_range_succ {α : Type*} (f : α → ℕ → α) (a : α) (j : ℕ) :
    (List.range (j + 1)).foldl f a = f ((List.range j).foldl f a) j := by
  rw [List.range_succ, List.foldl_append]; rfl

lemma Pr.run_le {V : ℕ} (s : Pr V) (hC : 3 ≤ C) :
    ∀ ρ : Fin V → ℕ, (∀ x, ρ x ≤ C) → ∀ x, (s.run w C ρ).1 x ≤ C := by
  induction s with
  | skip => intro ρ hρ x; exact hρ x
  | set y e =>
    intro ρ hρ x
    simp only [Pr.run, Function.update_apply]
    split_ifs
    · exact Ex.eval_le _ _ hρ hC
    · exact hρ x
  | out e => intro ρ hρ x; exact hρ x
  | seq s t ihs iht => intro ρ hρ x; exact iht _ (ihs ρ hρ) x
  | ite e s t ihs iht =>
    intro ρ hρ x
    simp only [Pr.run]
    split_ifs
    · exact ihs ρ hρ x
    · exact iht ρ hρ x
  | loop y e s ih =>
    intro ρ hρ
    rw [run_loop]
    have key : ∀ j, j ≤ e.eval w C ρ → ∀ x,
        ((List.range j).foldl (loopF w C y s) (ρ, [])).1 x ≤ C := by
      intro j
      induction j with
      | zero => intro _ x; exact hρ x
      | succ j ihj =>
        intro hj x
        rw [foldl_range_succ]
        refine ih _ (fun z => ?_) x
        simp only [Function.update_apply]
        split_ifs
        · have := Ex.eval_le (w := w) e ρ hρ hC; omega
        · exact ihj (by omega) z
    exact key _ le_rfl

theorem ach_compP {V : ℕ} (s : Pr V) : ∀ (d : ℕ) (ρ : Fin V → ℕ) (σ : St (K + 1))
    (Q : St (K + 1) → Prop), d + s.ld ≤ L → V + 2 * L + 2 * s.ed + 8 ≤ K → s.mc ≤ B →
    (∀ x : Fin V, σ.reg (R K x) = ρ x) → (∀ x, ρ x ≤ C) → σ.reg (R K V) = C →
    σ.pos ≤ w.length + 1 → 4 ≤ C → C * C + 2 * C + w.length + 1 ≤ B →
    (∀ σ' : St (K + 1), (∀ x : Fin V, σ'.reg (R K x) = (s.run w C ρ).1 x) →
      σ'.reg (R K V) = C → σ'.pos ≤ w.length + 1 → σ'.out = σ.out ++ (s.run w C ρ).2 →
      (∀ i, V < i → i < V + 1 + 2 * d → σ'.reg (R K i) = σ.reg (R K i)) → Q σ') →
    Ach w B (compP K L s d) σ Q := by
  have hCB : ∀ {C B n : ℕ}, 4 ≤ C → C * C + 2 * C + n + 1 ≤ B → C ≤ B := by
    intro C B n h1 h2; nlinarith
  have hρeq : ∀ (σ : St (K + 1)) (ρ : Fin V → ℕ), (∀ x : Fin V, σ.reg (R K x) = ρ x) →
      (fun x : Fin V => σ.reg (R K x)) = ρ := fun σ ρ h => funext h
  induction s with
  | skip =>
    intro d ρ σ Q hd hK hmc hx hρ hcap hpos hC hB h
    exact ach_skip (h σ hx hcap hpos (by simp [Pr.run]) (fun _ _ _ => rfl))
  | set y e =>
    intro d ρ σ Q hd hK hmc hx hρ hcap hpos hC hB h
    simp only [Pr.ld, Pr.ed, Pr.mc] at hd hK hmc
    have hyV := y.isLt
    refine ach_seq (ach_compE e _ _ σ _ (by omega) (by omega) (by omega) hcap
      (fun z => (hx z).trans_le (hρ z)) hpos hmc hC hB ?_)
    intro σ₁ ho1 hp1 hv1 hfr1
    rw [hρeq σ ρ hx] at hv1
    refine ach_copy _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
      (by rw [hv1]; exact (Ex.eval_le _ _ hρ (by omega)).trans (hCB hC hB)) ?_
    refine h _ (fun z => ?_) ?_ (by simpa using hp1) (by simp [ho1, Pr.run])
      (fun i hi1 hi2 => ?_)
    · have hzV := z.isLt
      simp only [Pr.run, Function.update_apply]
      by_cases hzy : z = y
      · subst hzy; rs
      · have hzy' : (z : ℕ) ≠ y := fun e => hzy (Fin.ext e)
        rw [if_neg hzy]
        rs
        rw [hfr1 z (by omega) (by omega), hx]
    · rs
      rw [hfr1 V (by omega) (by omega), hcap]
    · rs
      exact hfr1 i (by omega) (by omega)
  | out e =>
    intro d ρ σ Q hd hK hmc hx hρ hcap hpos hC hB h
    simp only [Pr.ld, Pr.ed, Pr.mc] at hd hK hmc
    refine ach_seq (ach_compE e _ _ σ _ (by omega) (by omega) (by omega) hcap
      (fun z => (hx z).trans_le (hρ z)) hpos hmc hC hB ?_)
    intro σ₁ ho1 hp1 hv1 hfr1
    rw [hρeq σ ρ hx] at hv1
    have hx1 : ∀ z : Fin V, σ₁.reg (R K z) = ρ z := fun z => by
      have := z.isLt; rw [hfr1 z (by omega) (by omega), hx]
    have hcap1 : σ₁.reg (R K V) = C := by rw [hfr1 V (by omega) (by omega), hcap]
    refine ach_ite ?_
    by_cases h0 : e.eval w C ρ = 0
    · rw [if_pos (by simp [Cond.eval, hv1, h0])]
      refine ach_out (h _ hx1 hcap1 hp1 (by simp [ho1, Pr.run, h0]) (fun i hi1 hi2 => ?_))
      exact hfr1 i (by omega) (by omega)
    · rw [if_neg (by simp [Cond.eval, hv1, h0])]
      refine ach_out (h _ hx1 hcap1 hp1 (by simp [ho1, Pr.run, h0]) (fun i hi1 hi2 => ?_))
      exact hfr1 i (by omega) (by omega)
  | seq s u ihs ihu =>
    intro d ρ σ Q hd hK hmc hx hρ hcap hpos hC hB h
    simp only [Pr.ld, Pr.ed, Pr.mc] at hd hK hmc
    refine ach_seq (ihs d ρ σ _ (by omega) (by omega) (le_trans (le_max_left _ _) hmc) hx hρ
      hcap hpos hC hB ?_)
    intro σ₁ hx1 hcap1 hp1 ho1 hfr1
    refine ihu d _ σ₁ _ (by omega) (by omega) (le_trans (le_max_right _ _) hmc) hx1
      (Pr.run_le s (by omega) ρ hρ) hcap1 hp1 hC hB ?_
    intro σ₂ hx2 hcap2 hp2 ho2 hfr2
    refine h σ₂ hx2 hcap2 hp2 (by rw [ho2, ho1]; simp [Pr.run]) (fun i hi1 hi2 => ?_)
    rw [hfr2 i hi1 hi2, hfr1 i hi1 hi2]
  | ite e s u ihs ihu =>
    intro d ρ σ Q hd hK hmc hx hρ hcap hpos hC hB h
    simp only [Pr.ld, Pr.ed, Pr.mc] at hd hK hmc
    refine ach_seq (ach_compE e _ _ σ _ (by omega) (by omega) (by omega) hcap
      (fun z => (hx z).trans_le (hρ z)) hpos (le_trans (le_max_left _ _) hmc) hC hB ?_)
    intro σ₁ ho1 hp1 hv1 hfr1
    rw [hρeq σ ρ hx] at hv1
    have hx1 : ∀ z : Fin V, σ₁.reg (R K z) = ρ z := fun z => by
      have := z.isLt; rw [hfr1 z (by omega) (by omega), hx]
    have hcap1 : σ₁.reg (R K V) = C := by rw [hfr1 V (by omega) (by omega), hcap]
    refine ach_ite ?_
    by_cases h0 : e.eval w C ρ = 0
    · rw [if_pos (by simp [Cond.eval, hv1, h0])]
      refine ihu d ρ σ₁ _ (by omega) (by omega)
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hmc) hx1 hρ hcap1 hp1 hC hB ?_
      intro σ₂ hx2 hcap2 hp2 ho2 hfr2
      refine h σ₂ (by simpa [Pr.run, h0] using hx2) hcap2 hp2
        (by rw [ho2, ho1]; simp [Pr.run, h0]) (fun i hi1 hi2 => ?_)
      rw [hfr2 i hi1 hi2, hfr1 i (by omega) (by omega)]
    · rw [if_neg (by simp [Cond.eval, hv1, h0])]
      refine ihs d ρ σ₁ _ (by omega) (by omega)
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hmc) hx1 hρ hcap1 hp1 hC hB ?_
      intro σ₂ hx2 hcap2 hp2 ho2 hfr2
      refine h σ₂ (by simpa [Pr.run, h0] using hx2) hcap2 hp2
        (by rw [ho2, ho1]; simp [Pr.run, h0]) (fun i hi1 hi2 => ?_)
      rw [hfr2 i hi1 hi2, hfr1 i (by omega) (by omega)]
  | loop y e s ih =>
    intro d ρ σ Q hd hK hmc hx hρ hcap hpos hC hB h
    simp only [Pr.ld, Pr.ed, Pr.mc] at hd hK hmc
    have hyV := y.isLt
    refine ach_seq (ach_compE e _ _ σ _ (by omega) (by omega) (by omega) hcap
      (fun z => (hx z).trans_le (hρ z)) hpos (le_trans (le_max_left _ _) hmc) hC hB ?_)
    intro σ₁ ho1 hp1 hv1 hfr1
    rw [hρeq σ ρ hx] at hv1
    set N := e.eval w C ρ with hN
    have hNC : N ≤ C := Ex.eval_le _ _ hρ (by omega)
    have hCB' : C ≤ B := hCB hC hB
    set F := fun j => (List.range j).foldl (loopF w C y s) (ρ, []) with hF
    have hFle : ∀ j, j ≤ N → ∀ z, (F j).1 z ≤ C := by
      intro j
      induction j with
      | zero => intro _ z; exact hρ z
      | succ j ihj =>
        intro hj z
        simp only [hF, foldl_range_succ]
        refine Pr.run_le s (by omega) _ (fun z' => ?_) z
        simp only [Function.update_apply]
        split_ifs
        · omega
        · exact ihj (by omega) z'
    refine ach_seq (ach_clear _ _ _ ?_)
    refine ach_loop (fun n τ => ∃ j, j + n = N ∧ τ.reg (R K (V + 1 + 2 * d)) = n ∧
        τ.reg (R K (V + 2 + 2 * d)) = j ∧ (∀ z : Fin V, τ.reg (R K z) = (F j).1 z) ∧
        τ.reg (R K V) = C ∧ τ.pos ≤ w.length + 1 ∧ τ.out = σ.out ++ (F j).2 ∧
        (∀ i, V < i → i < V + 1 + 2 * d → τ.reg (R K i) = σ.reg (R K i))) Q ?_ N _
      ⟨0, by omega, by rs, by rs, fun z => ?_, by rs; rw [hfr1 V (by omega) (by omega), hcap],
        by simpa using hp1, by simp [ho1, hF], fun i hi1 hi2 => ?_⟩
    · rintro n τ ⟨j, hjn, hlim, hcnt, hxj, hcapj, hpj, hoj, hfrj⟩
      rcases n with _ | n
      · left
        refine ⟨by simp [Cond.eval, hlim], h τ ?_ hcapj hpj ?_ hfrj⟩
        · intro z; rw [hxj z, run_loop, ← hN, show j = N by omega]
        · rw [hoj, run_loop, ← hN, show j = N by omega]
      · right
        refine ⟨by simp [Cond.eval, hlim], ?_⟩
        refine ach_seq (ach_copy _ _ _ (R_ne (by omega) (by omega) (by omega))
          (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
          (by rw [hcnt]; omega) ?_)
        refine ach_seq (ih (d + 1) (Function.update (F j).1 y j) _ _ (by omega) (by omega)
          (le_trans (le_max_right _ _) hmc) (fun z => ?_) (fun z => ?_) (by rs)
          (by simpa using hpj) hC hB ?_)
        · simp only [Function.update_apply]
          have hzV := z.isLt
          by_cases hzy : z = y
          · subst hzy; rs
          · have hzy' : (z : ℕ) ≠ y := fun e => hzy (Fin.ext e)
            rw [if_neg hzy]
            rs
            exact hxj z
        · simp only [Function.update_apply]
          split_ifs
          · omega
          · exact hFle j (by omega) z
        intro σ₂ hx2 hcap2 hp2 ho2 hfr2
        have hlim2 : σ₂.reg (R K (V + 1 + 2 * d)) = n + 1 := by
          rw [hfr2 _ (by omega) (by omega)]; rs
        have hcnt2 : σ₂.reg (R K (V + 2 + 2 * d)) = j := by
          rw [hfr2 _ (by omega) (by omega)]; rs
        refine ach_seq (ach_inc (by rw [hcnt2]; omega) (ach_dec ⟨n, by omega, j + 1,
          by omega, by rs, by rs, fun z => ?_, by rs, by simpa using hp2, ?_, fun i hi1 hi2 => ?_⟩))
        · have hzV := z.isLt
          rs
          rw [hx2 z, hF]
          simp only [foldl_range_succ, loopF]
        · simp only [St.setReg_out]
          rw [ho2, hF]
          simp only [foldl_range_succ, loopF, St.setReg_out, hoj, List.append_assoc]
          rfl
        · rs
          rw [hfr2 i (by omega) (by omega)]
          rs
          exact hfrj i hi1 hi2
    · have hzV := z.isLt
      rs
      rw [hfr1 z (by omega) (by omega), hx]
      simp [hF]
    · rw [setReg_R (by omega) (by omega), if_neg (by omega)]
      exact hfr1 i (by omega) (by omega)

end

end LL

end PathChecking
