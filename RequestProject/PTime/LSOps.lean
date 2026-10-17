module

public import RequestProject.PTime.RTok

/-!
# More arithmetic register programs

Truncated subtraction, comparison and multiplication, for the compiler of `PTime/HLComp.lean`.
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-- `r := r - s; s := 0`. -/
def subFrom (r s : Fin K) : Stmt K := whileNZ s (.dec s ⨟ .dec r)

lemma ach_subFrom (r s : Fin K) (hrs : r ≠ s) (σ : St K) (Q : St K → Prop)
    (h : Q ((σ.setReg r (σ.reg r - σ.reg s)).setReg s 0)) : Ach w B (subFrom r s) σ Q := by
  refine ach_loop (fun n τ => τ = (σ.setReg r (σ.reg r - (σ.reg s - n))).setReg s n ∧
    n ≤ σ.reg s) Q ?_ (σ.reg s) σ ⟨by st_tac, le_rfl⟩
  intro n τ ⟨hτ, hn⟩
  subst hτ
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply], ?_⟩
    simpa using h
  · right
    refine ⟨by simp [Cond.eval, St.setReg_apply],
      ach_seq (ach_dec (ach_dec ⟨n, by omega, ?_, by omega⟩))⟩
    st_tac

/-- `r := (r < s ? 1 : 0); s := s - r`. -/
def ltInto (r s : Fin K) : Stmt K :=
  whileNZ r (.dec r ⨟ .dec s) ⨟ .ite (.zero s) .skip (.inc r)

lemma ach_ltInto (r s : Fin K) (hrs : r ≠ s) (σ : St K) (Q : St K → Prop) (hB : 1 ≤ B)
    (h : Q ((σ.setReg r (if σ.reg r < σ.reg s then 1 else 0)).setReg s (σ.reg s - σ.reg r))) :
    Ach w B (ltInto r s) σ Q := by
  refine ach_seq (ach_loop (fun n τ => τ = (σ.setReg r n).setReg s (σ.reg s - (σ.reg r - n)) ∧
    n ≤ σ.reg r) _ ?_ (σ.reg r) σ ⟨by st_tac, le_rfl⟩)
  intro n τ ⟨hτ, hn⟩
  subst hτ
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply, hrs], ?_⟩
    refine ach_ite ?_
    by_cases hlt : σ.reg r < σ.reg s
    · rw [if_neg (by simp [Cond.eval, St.setReg_apply]; omega)]
      refine ach_inc (by simp [St.setReg_apply, hrs]; omega) ?_
      convert h using 1
      rw [if_pos hlt]; st_tac
    · rw [if_pos (by simp [Cond.eval, St.setReg_apply]; omega)]
      refine ach_skip ?_
      convert h using 1
      rw [if_neg hlt]; st_tac
  · right
    refine ⟨by simp [Cond.eval, St.setReg_apply, hrs],
      ach_seq (ach_dec (ach_dec ⟨n, by omega, ?_, by omega⟩))⟩
    st_tac

/-- `r := r * s`, using the registers `a`, `c`, `d`. -/
def mulInto (r s a c d : Fin K) : Stmt K :=
  clear a ⨟ whileNZ s (.dec s ⨟ copy r c d ⨟ addTo c a) ⨟ clear r ⨟ addTo a r

lemma ach_mulInto (r s a c d : Fin K) (hrs : r ≠ s) (hra : r ≠ a) (hrc : r ≠ c) (hrd : r ≠ d)
    (hsa : s ≠ a) (hsc : s ≠ c) (hsd : s ≠ d) (hac : a ≠ c) (had : a ≠ d) (hcd : c ≠ d)
    (σ : St K) (Q : St K → Prop) (hB1 : σ.reg r ≤ B) (hB2 : σ.reg r * σ.reg s ≤ B)
    (h : ∀ τ : St K, τ.reg r = σ.reg r * σ.reg s → τ.out = σ.out →
      (∀ x, x ≠ r → x ≠ s → x ≠ a → x ≠ c → x ≠ d → τ.reg x = σ.reg x) → Q τ) :
    Ach w B (mulInto r s a c d) σ Q := by
  have hsr := hrs.symm; have har := hra.symm; have hcr := hrc.symm; have hdr := hrd.symm
  have has := hsa.symm; have hcs := hsc.symm; have hds := hsd.symm; have hca := hac.symm
  have hda := had.symm; have hdc := hcd.symm
  set r0 := σ.reg r
  set s0 := σ.reg s
  refine ach_seq (ach_clear _ _ _ (ach_seq ?_))
  refine ach_loop (fun n τ => τ.reg s = n ∧ τ.reg a = r0 * (s0 - n) ∧ τ.reg r = r0 ∧
      τ.out = σ.out ∧ (∀ x, x ≠ s → x ≠ a → x ≠ c → x ≠ d → τ.reg x = σ.reg x) ∧ n ≤ s0) _ ?_
    s0 _ ⟨by simp [St.setReg_apply, *]; rfl, by simp [St.setReg_apply],
      by simp [St.setReg_apply, *]; rfl, by simp,
      fun x h1 h2 _ _ => by simp [St.setReg_apply, *], le_rfl⟩
  intro n τ ⟨h1, h2, h3, h4, h5, h6⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, h1], ach_seq (ach_clear _ _ _ (ach_addTo _ _ (Ne.symm hra) _ _ ?_ ?_))⟩
    · simp [St.setReg_apply, *]
    · apply h
      · simp [St.setReg_apply, *]
      · simpa using h4
      · intro x hx1 hx2 hx3 hx4 hx5
        simp [St.setReg_apply, *]
  · right
    have hle : r0 * (s0 - (n + 1)) + r0 ≤ B := by
      have : r0 * (s0 - (n + 1)) + r0 = r0 * (s0 - n) := by
        rw [show s0 - n = (s0 - (n + 1)) + 1 by omega, Nat.mul_succ]
      rw [this]; exact le_trans (Nat.mul_le_mul_left _ (by omega)) hB2
    refine ⟨by simp [Cond.eval, h1], ach_seq (ach_dec (ach_seq (ach_copy r c d hrc hrd hcd _ _
      (by simp [St.setReg_apply, *])
      (ach_addTo c a (Ne.symm hac) _ _ ?_ ⟨n, by omega, ?_, ?_, ?_, ?_, ?_, by omega⟩))))⟩
    · simp [St.setReg_apply, *]
    · simp [St.setReg_apply, *]
    · simp [St.setReg_apply, *]
      rw [show s0 - n = (s0 - (n + 1)) + 1 by omega, Nat.mul_succ]
    · simp [St.setReg_apply, *]
    · simpa using h4
    · intro x hx1 hx2 hx3 hx4
      simp [St.setReg_apply, *]

end LS

end PathChecking
