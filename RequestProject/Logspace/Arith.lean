module

public import RequestProject.Logspace.IO

/-!
# Arithmetic gadgets with constant parameters

* `caseReg r l`: run the `r`-th program of the list `l` (the register `r` is consumed);
* `mulAdd r t G d`: `r := G * r + d`;
* `divMod r q m G`: `q := r / G; m := r % G; r := 0`.

All specifications describe the final register state exactly.
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

@[simp] lemma St.setReg_setReg_same (σ : St K) (r : Fin K) (a b : ℕ) :
    (σ.setReg r a).setReg r b = σ.setReg r b := by
  st_tac

@[simp] lemma St.setReg_self (σ : St K) (r : Fin K) : σ.setReg r (σ.reg r) = σ := by
  st_tac

/-- `r := c`. -/
def setC (r : Fin K) (c : ℕ) : Stmt K := clear r ⨟ addConst r c

lemma ach_setC (r : Fin K) (c : ℕ) (σ : St K) (Q : St K → Prop) (hB : c ≤ B)
    (h : Q (σ.setReg r c)) : Ach w B (setC r c) σ Q :=
  ach_seq (ach_clear _ _ _ (ach_addConst _ _ _ _ (by simp [St.setReg_apply]; omega)
    (by simpa [St.setReg_apply] using h)))

/-- Case distinction on the value of a register (which is consumed). -/
def caseReg (r : Fin K) : List (Stmt K) → Stmt K
  | [] => .skip
  | s :: l => .ite (.zero r) s (.dec r ⨟ caseReg r l)

lemma ach_caseReg (r : Fin K) (l : List (Stmt K)) (k : ℕ) (hk : k < l.length) (σ : St K)
    (hr : σ.reg r = k) (Q : St K → Prop) (h : Ach w B (l[k]) (σ.setReg r 0) Q) :
    Ach w B (caseReg r l) σ Q := by
  induction l generalizing k σ with
  | nil => simp at hk
  | cons s l ih =>
    rcases k with _ | k
    · refine ach_iteT (by simp [Cond.eval, hr]) ?_
      have : σ.setReg r 0 = σ := by rw [← hr]; exact St.setReg_self σ r
      simpa [this] using h
    · refine ach_iteF (by simp [Cond.eval, hr]) (ach_seq (ach_dec ?_))
      refine ih k (by simpa using hk) _ (by simp [hr]) ?_
      simpa using h

/-- `r := G * r + d`, using the temporary `t` (which ends up `0`). -/
def mulAdd (r t : Fin K) (G d : ℕ) : Stmt K :=
  clear t ⨟ whileNZ r (.dec r ⨟ addConst t G) ⨟ addTo t r ⨟ addConst r d

lemma ach_mulAdd (r t : Fin K) (hrt : r ≠ t) (G d : ℕ) (σ : St K) (Q : St K → Prop)
    (hB : G * σ.reg r + d ≤ B)
    (h : Q ((σ.setReg r (G * σ.reg r + d)).setReg t 0)) : Ach w B (mulAdd r t G d) σ Q := by
  set v := σ.reg r
  refine ach_seq (ach_clear _ _ _ (ach_seq ?_))
  refine ach_loop (fun n τ => τ = ((σ.setReg t 0).setReg r n).setReg t (G * (v - n)) ∧ n ≤ v)
    _ ?_ v _ ⟨by st_tac, le_rfl⟩
  rintro n τ ⟨rfl, hn⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply, hrt], ?_⟩
    refine ach_seq (ach_addTo t r (Ne.symm hrt) _ _ (by simp [St.setReg_apply, hrt]; omega)
      (ach_addConst _ _ _ _ (by simp [St.setReg_apply, hrt]; omega) ?_))
    convert h using 1
    st_tac
  · right
    refine ⟨by simp [Cond.eval, St.setReg_apply, hrt], ach_seq (ach_dec ?_)⟩
    refine ach_addConst _ _ _ _ ?_ ⟨n, by omega, ?_, by omega⟩
    · simp [St.setReg_apply, Ne.symm hrt]
      have : G * (v - (n + 1)) + G = G * (v - n) := by
        rw [← Nat.mul_succ]; congr 1; omega
      have : G * (v - n) ≤ G * v := Nat.mul_le_mul_left _ (by omega)
      omega
    · ext x
      · rfl
      · simp only [St.setReg, Function.update_apply]
        split_ifs <;> simp_all
        rw [← Nat.mul_succ]; congr 1; omega
      · rfl

/-- One chunk of the division loop: having already removed `j` units in this chunk, remove
up to `n` more units from `r`.  If `r` runs out, `m := j + (rest)`, otherwise `q := q + 1`. -/
def chunk (r q m : Fin K) : ℕ → ℕ → Stmt K
  | 0, _ => .inc q
  | n + 1, j => .ite (.zero r) (addConst m j) (.dec r ⨟ chunk r q m n (j + 1))

lemma ach_chunk (r q m : Fin K) (hrq : r ≠ q) (hrm : r ≠ m) (n j : ℕ)
    (σ : St K) (Q : St K → Prop) (hm : σ.reg m = 0)
    (hB : σ.reg q + 1 + σ.reg r ≤ B) (hB' : j + σ.reg r ≤ B)
    (h : if n ≤ σ.reg r then Q ((σ.setReg r (σ.reg r - n)).setReg q (σ.reg q + 1))
      else Q ((σ.setReg r 0).setReg m (j + σ.reg r))) :
    Ach w B (chunk r q m n j) σ Q := by
  induction n generalizing j σ with
  | zero =>
    simp only [Nat.zero_le, if_true, Nat.sub_zero, St.setReg_self] at h
    exact ach_inc (by omega) h
  | succ n ih =>
    by_cases h0 : σ.reg r = 0
    · refine ach_iteT (by simp [Cond.eval, h0]) (ach_addConst _ _ _ _ (by omega) ?_)
      rw [if_neg (by omega)] at h
      convert h using 1
      st_tac
    · refine ach_iteF (by simp [Cond.eval, h0]) (ach_seq (ach_dec ?_))
      refine ih (j + 1) _ (by simp [St.setReg_apply, hrm.symm, hm])
        (by simp [St.setReg_apply, hrq.symm]; omega) (by simp; omega) ?_
      by_cases hn : n + 1 ≤ σ.reg r
      · rw [if_pos hn] at h
        rw [if_pos (by simp; omega)]
        convert h using 1
        st_tac
      · rw [if_neg hn] at h
        rw [if_neg (by simp; omega)]
        convert h using 1
        st_tac

/-- `q := r / G; m := r % G; r := 0` (for `G ≥ 1`). -/
def divMod (r q m : Fin K) (G : ℕ) : Stmt K :=
  clear q ⨟ clear m ⨟ whileNZ r (.dec r ⨟ chunk r q m (G - 1) 1)

lemma ach_divMod (r q m : Fin K) (hrq : r ≠ q) (hrm : r ≠ m) (hqm : q ≠ m) (G : ℕ)
    (hG : 1 ≤ G) (σ : St K) (Q : St K → Prop) (hB : σ.reg r ≤ B)
    (h : Q (((σ.setReg r 0).setReg q (σ.reg r / G)).setReg m (σ.reg r % G))) :
    Ach w B (divMod r q m G) σ Q := by
  set v := σ.reg r
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_clear _ _ _ ?_)))
  refine ach_loop (fun n τ => ∃ a c, τ = ((σ.setReg r n).setReg q a).setReg m c ∧
      G * a + c + n = v ∧ c < G ∧ (c ≠ 0 → n = 0)) Q ?_ v _
    ⟨0, 0, by st_tac, by omega, by omega, by omega⟩
  rintro n τ ⟨a, c, rfl, h1, h2, h3⟩
  have er : ∀ n a c, (((σ.setReg r n).setReg q a).setReg m c).reg r = n := by
    intro n a c; simp [St.setReg_apply, hrq, hrm]
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, er], ?_⟩
    have ha : a = v / G := by
      rw [← h1]; rw [Nat.add_zero, Nat.mul_add_div (by omega), Nat.div_eq_of_lt h2]; simp
    have hc : c = v % G := by
      rw [← h1]; simp [Nat.mod_eq_of_lt h2]
    subst ha hc
    exact h
  · right
    have hc : c = 0 := by by_contra hc; exact absurd (h3 hc) (by omega)
    subst hc
    refine ⟨by simp [Cond.eval, er], ach_seq (ach_dec ?_)⟩
    have e : ∀ x : St K, x = ((σ.setReg r (n + 1)).setReg q a).setReg m 0 →
        x.setReg r (x.reg r - 1) = ((σ.setReg r n).setReg q a).setReg m 0 := by
      rintro x rfl; st_tac
    rw [e _ rfl]
    have hGa : G * a + G ≤ v + G := by omega
    have eq : (((σ.setReg r n).setReg q a).setReg m 0).reg q = a := by
      simp [St.setReg_apply, hqm]
    have em : (((σ.setReg r n).setReg q a).setReg m 0).reg m = 0 := by
      simp [St.setReg_apply]
    have hGa' : a ≤ G * a := Nat.le_mul_of_pos_left _ h2
    refine ach_chunk r q m hrq hrm (G - 1) 1 _ _ em (by rw [eq, er]; omega)
      (by rw [er]; omega) ?_
    rw [eq, er]
    split_ifs with hle
    · refine ⟨n - (G - 1), by omega, a + 1, 0, ?_, ?_, by omega, by omega⟩
      · st_tac
      · rw [Nat.mul_succ]; omega
    · refine ⟨0, by omega, a, 1 + n, ?_, by omega, by omega, by omega⟩
      st_tac

end LS

end PathChecking
