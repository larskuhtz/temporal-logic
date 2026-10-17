module

public import RequestProject.Logspace.Arith
public import RequestProject.LogLang.Defs

/-!
# Register-program gadgets used by the compiler of the loop language
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-- `x := x - y; y := 0`. -/
def subR (x y : Fin K) : Stmt K := whileNZ y (.dec y ⨟ .dec x)

lemma ach_subR (x y : Fin K) (hxy : x ≠ y) (σ : St K) (Q : St K → Prop)
    (h : Q ((σ.setReg y 0).setReg x (σ.reg x - σ.reg y))) : Ach w B (subR x y) σ Q := by
  refine ach_loop (fun n τ => τ = (σ.setReg y n).setReg x (σ.reg x - (σ.reg y - n)) ∧
    n ≤ σ.reg y) Q ?_ (σ.reg y) σ ⟨by st_tac, le_rfl⟩
  rintro n τ ⟨rfl, hn⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply, Ne.symm hxy], ?_⟩
    simpa using h
  · right
    refine ⟨by simp [Cond.eval, St.setReg_apply, Ne.symm hxy], ach_seq (ach_dec (ach_dec
      ⟨n, by omega, ?_, by omega⟩))⟩
    st_tac

/-- `t := t + x * y; x := 0; s := 0` (`y` is preserved). -/
def mulR (x y t s : Fin K) : Stmt K :=
  clear s ⨟ whileNZ x (.dec x ⨟ addTo2 y t s ⨟ addTo s y)

lemma ach_mulR (x y t s : Fin K) (hxy : x ≠ y) (hxt : x ≠ t) (hxs : x ≠ s) (hyt : y ≠ t)
    (hys : y ≠ s) (hts : t ≠ s) (σ : St K) (Q : St K → Prop)
    (hB : σ.reg t + σ.reg x * σ.reg y ≤ B) (hBy : σ.reg y ≤ B)
    (h : Q (((σ.setReg s 0).setReg x 0).setReg t (σ.reg t + σ.reg x * σ.reg y))) :
    Ach w B (mulR x y t s) σ Q := by
  refine ach_seq (ach_clear _ _ _ ?_)
  set X := σ.reg x
  set Y := σ.reg y
  set T := σ.reg t
  refine ach_loop (fun n τ => τ = ((σ.setReg s 0).setReg x n).setReg t (T + (X - n) * Y) ∧
    n ≤ X) Q ?_ X _ ⟨by st_tac, le_rfl⟩
  rintro n τ ⟨rfl, hn⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply, hxt], ?_⟩
    simpa using h
  · right
    have hmono : (X - (n + 1)) * Y + Y = (X - n) * Y := by
      rw [← Nat.succ_mul]; congr 1; omega
    have hle : (X - n) * Y ≤ X * Y := Nat.mul_le_mul_right _ (by omega)
    refine ⟨by simp [Cond.eval, St.setReg_apply, hxt], ach_seq (ach_dec (ach_seq
      (ach_addTo2 y t s hyt hys hts _ _ ?_ ?_ (ach_addTo s y (Ne.symm hys) _ _ ?_
        ⟨n, by omega, ?_, by omega⟩))))⟩
    · simp [St.setReg_apply, hyt, hys, hxt, hxy, Ne.symm hxy, Ne.symm hyt, Ne.symm hxt]; omega
    · simp [St.setReg_apply, hyt, hys, hxt, hxy, hts, Ne.symm hxy, Ne.symm hyt, Ne.symm hxt,
        Ne.symm hxs, Ne.symm hts]; omega
    · simp [St.setReg_apply, hyt, hys, hxt, hxy, hts, Ne.symm hxy, Ne.symm hyt, Ne.symm hxt,
        Ne.symm hxs, Ne.symm hts]; omega
    · ext r
      · rfl
      · simp only [St.setReg, Function.update_apply]
        split_ifs <;> simp_all <;> omega
      · rfl

/-- `t := min t c`, using the temporaries `s₁ s₂ s₃`. -/
def clampR (t c s₁ s₂ s₃ : Fin K) : Stmt K :=
  copy t s₁ s₂ ⨟ copy c s₂ s₃ ⨟ subR s₁ s₂ ⨟ .ite (.zero s₁) .skip (copy c t s₂)

/-- Frame condition: registers outside the list `L` are unchanged. -/
def Frame (σ σ' : St K) (L : List (Fin K)) : Prop := ∀ r, r ∉ L → σ'.reg r = σ.reg r

lemma ach_clampR (t c s₁ s₂ s₃ : Fin K) (h1 : t ≠ c) (h2 : t ≠ s₁) (h3 : t ≠ s₂) (h4 : t ≠ s₃)
    (h5 : c ≠ s₁) (h6 : c ≠ s₂) (h7 : c ≠ s₃) (h8 : s₁ ≠ s₂) (h9 : s₁ ≠ s₃) (h10 : s₂ ≠ s₃)
    (σ : St K) (Q : St K → Prop) (hBt : σ.reg t ≤ B) (hBc : σ.reg c ≤ B)
    (h : ∀ σ' : St K, σ'.pos = σ.pos → σ'.out = σ.out → σ'.reg t = min (σ.reg t) (σ.reg c) →
      Frame σ σ' [t, s₁, s₂, s₃] → Q σ') :
    Ach w B (clampR t c s₁ s₂ s₃) σ Q := by
  refine ach_seq (ach_copy t s₁ s₂ h2 h3 h8 _ _ hBt ?_)
  refine ach_seq (ach_copy c s₂ s₃ h6 h7 h10 _ _ (by simp [St.setReg_apply, h5, h6]; omega) ?_)
  refine ach_seq (ach_subR s₁ s₂ h8 _ _ ?_)
  refine ach_ite ?_
  by_cases hle : σ.reg t ≤ σ.reg c
  · rw [if_pos (by simp [Cond.eval, St.setReg_apply, h5, h6, h8, h9, h10]; omega)]
    refine ach_skip (h _ rfl rfl ?_ ?_)
    · simp [St.setReg_apply, h2, h3, h4]; omega
    · intro r hr; simp at hr; simp [St.setReg_apply, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]
  · rw [if_neg (by simp [Cond.eval, St.setReg_apply, h5, h6, h8, h9, h10]; omega)]
    refine ach_copy c t s₂ (Ne.symm h1) h6 h3 _ _ (by simp [St.setReg_apply, h5, h6, h7]; omega)
      (h _ rfl rfl ?_ ?_)
    · simp [St.setReg_apply, h3, h5, h6, h7, Ne.symm h1]; omega
    · intro r hr; simp at hr; simp [St.setReg_apply, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

/-- `f := 1` if `y ≠ 0 ∧ y ≤ x`, else `f := 0` (temporaries `s₁ s₂ s₃`). -/
def flagGe (x y f s₁ s₂ s₃ : Fin K) : Stmt K :=
  copy y s₁ s₂ ⨟ copy x s₂ s₃ ⨟ subR s₁ s₂ ⨟ clear f ⨟
    .ite (.zero y) .skip (.ite (.zero s₁) (.inc f) .skip)

lemma ach_flagGe (x y f s₁ s₂ s₃ : Fin K) (hxy : x ≠ y) (hxf : x ≠ f) (hx1 : x ≠ s₁)
    (hx2 : x ≠ s₂) (hx3 : x ≠ s₃) (hyf : y ≠ f) (hy1 : y ≠ s₁) (hy2 : y ≠ s₂) (hy3 : y ≠ s₃)
    (hf1 : f ≠ s₁) (hf2 : f ≠ s₂) (hf3 : f ≠ s₃) (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ s₃)
    (h23 : s₂ ≠ s₃) (σ : St K) (Q : St K → Prop) (hBx : σ.reg x ≤ B) (hBy : σ.reg y ≤ B)
    (hB1 : 1 ≤ B)
    (h : ∀ σ' : St K, σ'.pos = σ.pos → σ'.out = σ.out →
      σ'.reg f = (if σ.reg y ≠ 0 ∧ σ.reg y ≤ σ.reg x then 1 else 0) →
      Frame σ σ' [f, s₁, s₂, s₃] → Q σ') :
    Ach w B (flagGe x y f s₁ s₂ s₃) σ Q := by
  refine ach_seq (ach_copy y s₁ s₂ hy1 hy2 h12 _ _ hBy ?_)
  refine ach_seq (ach_copy x s₂ s₃ hx2 hx3 h23 _ _ (by simp [St.setReg_apply, hx1, hx2]; omega) ?_)
  refine ach_seq (ach_subR s₁ s₂ h12 _ _ ?_)
  refine ach_seq (ach_clear f _ _ ?_)
  have hfr : ∀ σ' : St K, (∀ r, r ≠ f → r ≠ s₁ → r ≠ s₂ → r ≠ s₃ → σ'.reg r = σ.reg r) →
      Frame σ σ' [f, s₁, s₂, s₃] := by
    intro σ' hr r hr'; simp at hr'; exact hr r hr'.1 hr'.2.1 hr'.2.2.1 hr'.2.2.2
  refine ach_ite ?_
  by_cases hy : σ.reg y = 0
  · rw [if_pos (by simp [Cond.eval, St.setReg_apply, hy, hyf, hy1, hy2, hy3])]
    refine ach_skip (h _ rfl rfl ?_ (hfr _ ?_))
    · simp [St.setReg_apply, hy]
    · intro r a b c d; simp [St.setReg_apply, a, b, c, d]
  · rw [if_neg (by simp [Cond.eval, St.setReg_apply, hy, hyf, hy1, hy2, hy3])]
    refine ach_ite ?_
    by_cases hle : σ.reg y ≤ σ.reg x
    · rw [if_pos (by simp [Cond.eval, St.setReg_apply, hf1, h12, h13, h23, hx1, hy1, hx2, hy2]; omega)]
      refine ach_inc (by simp [St.setReg_apply]; omega) (h _ rfl rfl ?_ (hfr _ ?_))
      · simp [St.setReg_apply, hy, hle]
      · intro r a b c d; simp [St.setReg_apply, a, b, c, d]
    · rw [if_neg (by simp [Cond.eval, St.setReg_apply, hf1, h12, h13, h23, hx1, hy1, hx2, hy2]; omega)]
      refine ach_skip (h _ rfl rfl ?_ (hfr _ ?_))
      · simp [St.setReg_apply, hle]
      · intro r a b c d; simp [St.setReg_apply, a, b, c, d]

end LS

end PathChecking
