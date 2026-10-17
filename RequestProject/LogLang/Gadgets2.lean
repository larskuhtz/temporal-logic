module

public import RequestProject.LogLang.Gadgets

/-!
# More register-program gadgets: division, input head movement, reading symbols
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-- `q := x / y; x := x % y` (temporaries `f s₁ s₂ s₃`). -/
def divR (x y q f s₁ s₂ s₃ : Fin K) : Stmt K :=
  clear q ⨟ flagGe x y f s₁ s₂ s₃ ⨟
    whileNZ f (copy y s₁ s₂ ⨟ subR x s₁ ⨟ .inc q ⨟ flagGe x y f s₁ s₂ s₃)

lemma ach_divR (x y q f s₁ s₂ s₃ : Fin K)
    (hd : [x, y, q, f, s₁, s₂, s₃].Nodup)
    (σ : St K) (Q : St K → Prop) (hBx : σ.reg x ≤ B) (hBy : σ.reg y ≤ B) (hB1 : 1 ≤ B)
    (h : ∀ σ' : St K, σ'.pos = σ.pos → σ'.out = σ.out →
      σ'.reg q = σ.reg x / σ.reg y → σ'.reg x = σ.reg x % σ.reg y →
      Frame σ σ' [x, q, f, s₁, s₂, s₃] → Q σ') :
    Ach w B (divR x y q f s₁ s₂ s₃) σ Q := by
  have hxy : x ≠ y := fun e => by subst e; simp at hd
  have hxq : x ≠ q := fun e => by subst e; simp at hd
  have hxf : x ≠ f := fun e => by subst e; simp at hd
  have hx1 : x ≠ s₁ := fun e => by subst e; simp at hd
  have hx2 : x ≠ s₂ := fun e => by subst e; simp at hd
  have hx3 : x ≠ s₃ := fun e => by subst e; simp at hd
  have hyq : y ≠ q := fun e => by subst e; simp at hd
  have hyf : y ≠ f := fun e => by subst e; simp at hd
  have hy1 : y ≠ s₁ := fun e => by subst e; simp at hd
  have hy2 : y ≠ s₂ := fun e => by subst e; simp at hd
  have hy3 : y ≠ s₃ := fun e => by subst e; simp at hd
  have hqf : q ≠ f := fun e => by subst e; simp at hd
  have hq1 : q ≠ s₁ := fun e => by subst e; simp at hd
  have hq2 : q ≠ s₂ := fun e => by subst e; simp at hd
  have hq3 : q ≠ s₃ := fun e => by subst e; simp at hd
  have hf1 : f ≠ s₁ := fun e => by subst e; simp at hd
  have hf2 : f ≠ s₂ := fun e => by subst e; simp at hd
  have hf3 : f ≠ s₃ := fun e => by subst e; simp at hd
  have h12 : s₁ ≠ s₂ := fun e => by subst e; simp at hd
  have h13 : s₁ ≠ s₃ := fun e => by subst e; simp at hd
  have h23 : s₂ ≠ s₃ := fun e => by subst e; simp at hd
  have hyx := hxy.symm
  have hqx := hxq.symm
  have hfx := hxf.symm
  have h1x := hx1.symm
  have h2x := hx2.symm
  have h3x := hx3.symm
  have hqy := hyq.symm
  have hfy := hyf.symm
  have h1y := hy1.symm
  have h2y := hy2.symm
  have h3y := hy3.symm
  have hfq := hqf.symm
  have h1q := hq1.symm
  have h2q := hq2.symm
  have h3q := hq3.symm
  have h1f := hf1.symm
  have h2f := hf2.symm
  have h3f := hf3.symm
  have h21 := h12.symm
  have h31 := h13.symm
  have h32 := h23.symm
  refine ach_seq (ach_clear q _ _ ?_)
  refine ach_seq (ach_flagGe x y f s₁ s₂ s₃ hx1 hx2 hx3 hyf hy1 hy2 hy3 hf1 hf2 hf3
    h12 h13 h23 _ _ (by simp [St.setReg_apply, *])
    (by simp [St.setReg_apply, *]) hB1 ?_)
  intro σ₁ hp1 ho1 hf1' hfr1
  have e1x : σ₁.reg x = (σ.reg x) := by rw [hfr1 x (by simp [hxf, hx1, hx2, hx3])]; simp [St.setReg_apply, *]
  have e1y : σ₁.reg y = (σ.reg y) := by rw [hfr1 y (by simp [hyf, hy1, hy2, hy3])]; simp [St.setReg_apply, *]
  have e1q : σ₁.reg q = 0 := by rw [hfr1 q (by simp [hqf, hq1, hq2, hq3])]; simp [St.setReg_apply]
  -- loop invariant
  refine ach_loop (fun n τ => ∃ m, n + m * (σ.reg y) = (σ.reg x) ∧ (σ.reg y = 0 → m = 0) ∧ τ.reg x = n ∧ τ.reg y = (σ.reg y) ∧ τ.reg q = m ∧
      τ.reg f = (if (σ.reg y) ≠ 0 ∧ (σ.reg y) ≤ n then 1 else 0) ∧ τ.pos = σ.pos ∧ τ.out = σ.out ∧
      Frame σ τ [x, q, f, s₁, s₂, s₃]) Q ?_ (σ.reg x) σ₁
    ⟨0, by simp, fun _ => rfl, e1x, e1y, e1q, by rw [hf1']; simp [St.setReg_apply, *], by simp [hp1], by simp [ho1], ?_⟩
  · rintro n τ ⟨m, hm, hm0, hx, hy, hq, hf, hp, ho, hfr⟩
    by_cases hc : (σ.reg y) ≠ 0 ∧ (σ.reg y) ≤ n
    · right
      refine ⟨by simp [Cond.eval, hf, hc], ?_⟩
      refine ach_seq (ach_copy y s₁ s₂ hy1 hy2 h12 _ _ (by rw [hy]; exact hBy) ?_)
      refine ach_seq (ach_subR x s₁ hx1 _ _ ?_)
      refine ach_seq (ach_inc ?_ ?_)
      · simp [St.setReg_apply, *]
        have : m * (σ.reg y) ≤ (σ.reg x) := by omega
        have : m ≤ m * (σ.reg y) := Nat.le_mul_of_pos_right _ (by omega)
        omega
      refine ach_flagGe x y f s₁ s₂ s₃ hx1 hx2 hx3 hyf hy1 hy2 hy3 hf1 hf2 hf3
        h12 h13 h23 _ _ ?_ ?_ hB1 ?_
      · simp [St.setReg_apply, *]; omega
      · simp [St.setReg_apply, *]
      intro σ₂ hp2 ho2 hf2' hfr2
      refine ⟨n - (σ.reg y), by omega, m + 1, ?_, fun h0 => absurd h0 hc.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have : (m + 1) * (σ.reg y) = m * (σ.reg y) + (σ.reg y) := by ring
        omega
      · rw [hfr2 x (by simp [hxf, hx1, hx2, hx3])]
        simp [St.setReg_apply, *]
      · rw [hfr2 y (by simp [hyf, hy1, hy2, hy3])]
        simp [St.setReg_apply, *]
      · rw [hfr2 q (by simp [hqf, hq1, hq2, hq3])]
        simp [St.setReg_apply, *]
      · rw [hf2']
        simp [St.setReg_apply, *]
      · rw [hp2]; simp [hp]
      · rw [ho2]; simp [ho]
      · intro r hr
        have hr' := hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
        rw [hfr2 r (by simp [hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1, hr'.2.2.2.2.2])]
        simp [St.setReg_apply, *]
        exact hfr r hr
    · left
      refine ⟨by simp [Cond.eval, hf, hc], h τ hp ho ?_ ?_ hfr⟩
      · rw [hq]
        by_cases hY : (σ.reg y) = 0
        · simp only [hY, Nat.div_zero]; exact hm0 hY
        · have hn : n < (σ.reg y) := by push_neg at hc; exact hc hY
          rw [← hm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hn]; simp
      · rw [hx]
        by_cases hY : (σ.reg y) = 0
        · simp [hY] at hm ⊢; omega
        · have hn : n < (σ.reg y) := by push_neg at hc; exact hc hY
          rw [← hm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hn]
  · intro r hr
    have hr' := hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
    rw [hfr1 r (by simp [hr'.2.2.1, hr'.2.2.2.1, hr'.2.2.2.2.1, hr'.2.2.2.2.2])]
    simp [St.setReg_apply, *]

/-- Move the input head to the left end marker (position `0`). -/
def goLend : Stmt K := .loop (.not (.sym .lend)) .left

lemma ach_goLend (σ : St K) (Q : St K → Prop) (h : Q { σ with pos := 0 }) :
    Ach w B goLend σ Q := by
  refine ach_loop (fun n τ => τ = { σ with pos := n }) _ ?_ σ.pos σ (by rfl)
  intro n τ hτ
  subst hτ
  rcases n with _ | n
  · left
    exact ⟨by simp [Cond.eval, inputSym_eq_lend], h⟩
  · right
    exact ⟨by simp [Cond.eval, inputSym_eq_lend], ach_left ⟨n, by omega, by simp⟩⟩

/-- Move the input head `p` positions to the right (consuming register `p`). -/
def moveR (p : Fin K) : Stmt K := whileNZ p (.right ⨟ .dec p)

lemma ach_moveR (p : Fin K) (σ : St K) (Q : St K → Prop) (hpos : σ.pos ≤ w.length + 1)
    (h : Q ({ σ with pos := min (σ.pos + σ.reg p) (w.length + 1) }.setReg p 0)) :
    Ach w B (moveR p) σ Q := by
  refine ach_loop (fun n τ => ∃ a, τ = { σ with pos := a }.setReg p n ∧ a ≤ w.length + 1 ∧
      min (a + n) (w.length + 1) = min (σ.pos + σ.reg p) (w.length + 1)) _ ?_ (σ.reg p) σ
    ⟨σ.pos, by st_tac, hpos, rfl⟩
  rintro n τ ⟨a, rfl, hapos, ha⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply], ?_⟩
    convert h using 1
    simp at ha
    ext <;> simp [St.setReg]
    · omega
  · right
    refine ⟨by simp [Cond.eval, St.setReg_apply], ach_seq (ach_right (ach_dec
      ⟨n, by omega, min (a + 1) (w.length + 1), ?_, by omega, ?_⟩))⟩
    · ext <;> simp [St.setReg]
    · rw [← ha]; omega

/-- `t := symNum (symbol under the head)`. -/
def readSym (t : Fin K) : Stmt K :=
  .ite (.sym (.bit false)) (setC t 0) (.ite (.sym (.bit true)) (setC t 1)
    (.ite (.sym .lend) (setC t 2) (setC t 3)))

lemma ach_readSym (t : Fin K) (σ : St K) (Q : St K → Prop) (hB : 3 ≤ B)
    (h : Q (σ.setReg t (LL.symNum (inputSym w σ.pos)))) : Ach w B (readSym t) σ Q := by
  unfold readSym
  rcases hs : inputSym w σ.pos with _ | _ | b
  · refine ach_iteF (by simp [Cond.eval, hs]) (ach_iteF (by simp [Cond.eval, hs])
      (ach_iteT (by simp [Cond.eval, hs]) (ach_setC _ _ _ _ (by omega) ?_)))
    simpa [hs, LL.symNum] using h
  · refine ach_iteF (by simp [Cond.eval, hs]) (ach_iteF (by simp [Cond.eval, hs])
      (ach_iteF (by simp [Cond.eval, hs]) (ach_setC _ _ _ _ (by omega) ?_)))
    simpa [hs, LL.symNum] using h
  · cases b
    · refine ach_iteT (by simp [Cond.eval, hs]) (ach_setC _ _ _ _ (by omega) ?_)
      simpa [hs, LL.symNum] using h
    · refine ach_iteF (by simp [Cond.eval, hs]) (ach_iteT (by simp [Cond.eval, hs])
        (ach_setC _ _ _ _ (by omega) ?_))
      simpa [hs, LL.symNum] using h

/-- `t := |w|` (the head ends on the right end marker). -/
def lenR (t : Fin K) : Stmt K :=
  goLend ⨟ .right ⨟ clear t ⨟ .loop (.not (.sym .rend)) (.inc t ⨟ .right)

lemma ach_lenR (t : Fin K) (σ : St K) (Q : St K → Prop) (hB : w.length ≤ B)
    (h : Q ({ σ with pos := w.length + 1 }.setReg t w.length)) : Ach w B (lenR t) σ Q := by
  refine ach_seq (ach_goLend _ _ (ach_seq (ach_right (ach_seq (ach_clear _ _ _ ?_)))))
  refine ach_loop (fun n τ => τ = { σ with pos := w.length + 1 - n }.setReg t (w.length - n) ∧
      n ≤ w.length) _ ?_ w.length _ ⟨?_, le_rfl⟩
  · rintro n τ ⟨rfl, hn⟩
    rcases n with _ | n
    · left
      refine ⟨?_, by simpa using h⟩
      simp [Cond.eval, inputSym_eq_rend (w := w) (p := w.length + 1) (by omega) le_rfl]
    · right
      have hne : inputSym w (w.length - n) ≠ .rend := by
        rw [Ne, inputSym_eq_rend (by omega) (by omega)]; omega
      refine ⟨by simp [Cond.eval]; exact hne, ach_seq (ach_inc ?_ (ach_right ⟨n, by omega, ?_, by
        omega⟩))⟩
      · simp [St.setReg_apply]; omega
      · ext <;> simp [St.setReg, Function.update_apply]
        · omega
        · split_ifs <;> omega
  · ext <;> simp [St.setReg]

end LS

end PathChecking
