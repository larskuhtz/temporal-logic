module

public import RequestProject.Logspace.Arith

/-!
# Register arithmetic: addition, truncated subtraction, multiplication, division

Each routine computes `dst := x op y` and may destroy its operands `x`, `y` and some
temporaries; all other registers are unchanged.
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-- The registers outside `S` are unchanged. -/
def RegFrame (S : List (Fin K)) (σ τ : St K) : Prop := ∀ z, z ∉ S → τ.reg z = σ.reg z

lemma RegFrame.refl (S : List (Fin K)) (σ : St K) : RegFrame S σ σ := fun _ _ => rfl

lemma RegFrame.trans {S : List (Fin K)} {σ τ υ : St K} (h1 : RegFrame S σ τ) (h2 : RegFrame S τ υ) :
    RegFrame S σ υ := fun z hz => (h2 z hz).trans (h1 z hz)

lemma RegFrame.mono {S S' : List (Fin K)} {σ τ : St K} (h : RegFrame S σ τ) (hS : ∀ z ∈ S, z ∈ S') :
    RegFrame S' σ τ := fun z hz => h z (fun h' => hz (hS z h'))

lemma RegFrame.setReg {S : List (Fin K)} (σ : St K) (r : Fin K) (v : ℕ) (hr : r ∈ S) :
    RegFrame S σ (σ.setReg r v) := by
  intro z hz
  have : z ≠ r := fun h => hz (h ▸ hr)
  simp [St.setReg_apply, this]

/-- `dst := x + y` (destroys `x`, `y`). -/
def opAdd (x y dst : Fin K) : Stmt K := clear dst ⨟ addTo x dst ⨟ addTo y dst

lemma ach_opAdd (x y dst : Fin K) (hxy : x ≠ y) (hxd : x ≠ dst) (hyd : y ≠ dst) (σ : St K)
    (Q : St K → Prop) (hB : σ.reg x + σ.reg y ≤ B)
    (h : ∀ τ : St K, τ.out = σ.out → τ.pos = σ.pos → τ.reg dst = σ.reg x + σ.reg y →
      RegFrame [x, y, dst] σ τ → Q τ) : Ach w B (opAdd x y dst) σ Q := by
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_addTo x dst hxd _ _ ?_ (ach_addTo y dst hyd _ _ ?_
    (h _ rfl rfl ?_ ?_)))))
  · simp [St.setReg_apply, hxd]; omega
  · simp [St.setReg_apply, hxd, hyd, Ne.symm hxy]; omega
  · simp [St.setReg_apply, hxd, hyd, Ne.symm hxy]
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp [St.setReg_apply, hz.1, hz.2.1, hz.2.2]

/-- `dst := x - y` (truncated; destroys `x`, `y`). -/
def opSub (x y dst : Fin K) : Stmt K := clear dst ⨟ addTo x dst ⨟ whileNZ y (.dec y ⨟ .dec dst)

lemma ach_opSub (x y dst : Fin K) (hxy : x ≠ y) (hxd : x ≠ dst) (hyd : y ≠ dst) (σ : St K)
    (Q : St K → Prop) (hB : σ.reg x ≤ B)
    (h : ∀ τ : St K, τ.out = σ.out → τ.pos = σ.pos → τ.reg dst = σ.reg x - σ.reg y →
      RegFrame [x, y, dst] σ τ → Q τ) : Ach w B (opSub x y dst) σ Q := by
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_addTo x dst hxd _ _ (by
    simp [St.setReg_apply, hxd]; omega) ?_)))
  set σ₁ := ((σ.setReg dst 0).setReg x 0).setReg dst ((σ.setReg dst 0).reg dst +
    (σ.setReg dst 0).reg x)
  have h1 : σ₁.reg dst = σ.reg x := by simp [σ₁, St.setReg_apply, hxd]
  have h2 : σ₁.reg y = σ.reg y := by simp [σ₁, St.setReg_apply, hyd, hxy.symm]
  have hf : RegFrame [x, y, dst] σ σ₁ := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp [σ₁, St.setReg_apply, hz.1, hz.2.2]
  refine ach_loop (fun k τ => τ.reg y = k ∧ k ≤ σ.reg y ∧ τ.reg dst = σ.reg x - (σ.reg y - k) ∧
      τ.out = σ.out ∧ τ.pos = σ.pos ∧ RegFrame [x, y, dst] σ τ) Q ?_ (σ.reg y) σ₁
    ⟨h2, le_rfl, by rw [h1]; omega, rfl, rfl, hf⟩
  rintro k τ ⟨hk, hkY, hd, ho, hp, hfr⟩
  rcases k with _ | k
  · left; exact ⟨by simp [Cond.eval, hk], h τ ho hp (by rw [hd]; omega) hfr⟩
  · right
    refine ⟨by simp [Cond.eval, hk], ach_seq (ach_dec (ach_dec ⟨k, by omega, ?_, by omega, ?_,
      ho, hp, ?_⟩))⟩
    · simp [St.setReg_apply, hyd, hk]
    · simp [St.setReg_apply, hyd.symm, hd]; omega
    · exact hfr.trans ((RegFrame.setReg _ _ _ (by simp)).trans (RegFrame.setReg _ _ _ (by simp)))

/-- `dst := x * y` (destroys `x`; uses temporaries `t₁ t₂`). -/
def opMul (x y dst t₁ t₂ : Fin K) : Stmt K :=
  clear dst ⨟ whileNZ x (.dec x ⨟ copy y t₁ t₂ ⨟ addTo t₁ dst)

lemma ach_opMul (x y dst t₁ t₂ : Fin K) (hxy : x ≠ y) (hxd : x ≠ dst) (hyd : y ≠ dst)
    (hx1 : x ≠ t₁) (hx2 : x ≠ t₂) (hy1 : y ≠ t₁) (hy2 : y ≠ t₂) (hd1 : dst ≠ t₁)
    (hd2 : dst ≠ t₂) (h12 : t₁ ≠ t₂) (σ : St K)
    (Q : St K → Prop) (hB : σ.reg x * σ.reg y ≤ B) (hBy : σ.reg y ≤ B)
    (h : ∀ τ : St K, τ.out = σ.out → τ.pos = σ.pos → τ.reg dst = σ.reg x * σ.reg y →
      RegFrame [x, dst, t₁, t₂] σ τ → Q τ) : Ach w B (opMul x y dst t₁ t₂) σ Q := by
  refine ach_seq (ach_clear _ _ _ ?_)
  refine ach_loop (fun k τ => τ.reg x = k ∧ k ≤ σ.reg x ∧ τ.reg dst = (σ.reg x - k) * σ.reg y ∧
      τ.out = σ.out ∧ τ.pos = σ.pos ∧ RegFrame [x, dst, t₁, t₂] σ τ) Q ?_ (σ.reg x) _
    ⟨by simp [St.setReg_apply, hxd], le_rfl, by simp [St.setReg_apply], rfl, rfl,
      RegFrame.setReg _ _ _ (by simp)⟩
  rintro k τ ⟨hk, hkX, hd, ho, hp, hfr⟩
  have hτy : τ.reg y = σ.reg y := hfr y (by simp [hxy.symm, hyd, hy1, hy2])
  rcases k with _ | k
  · left; exact ⟨by simp [Cond.eval, hk], h τ ho hp (by rw [hd]; simp) hfr⟩
  · right
    refine ⟨by simp [Cond.eval, hk], ach_seq (ach_dec (ach_seq (ach_copy y t₁ t₂ hy1 hy2 h12 _ _
      (by simp [St.setReg_apply, hxy.symm, hτy, hBy]) (ach_addTo t₁ dst hd1.symm _ _ ?_
      ⟨k, by omega, ?_, by omega, ?_, ho, hp, ?_⟩))))⟩
    · have : (σ.reg x - (k + 1)) * σ.reg y + σ.reg y ≤ σ.reg x * σ.reg y := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
      simp [St.setReg_apply, hd1, hd2, hxd.symm, hd, hτy, hxy.symm, h12]
      omega
    · simp [St.setReg_apply, hx1, hx2, hxd, hk]
    · simp [St.setReg_apply, hd1, hd2, hxd.symm, hd, hτy, hxy.symm, h12]
      rw [show σ.reg x - k = σ.reg x - (k + 1) + 1 by omega, Nat.succ_mul]
    · refine hfr.trans ?_
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [St.setReg_apply, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]

/-- `q := x / y; m := x % y` for `y ≥ 1` (destroys `x`; uses `rem` and `t`). -/
def divModR (x y q m rem t : Fin K) : Stmt K :=
  clear q ⨟ clear m ⨟ copy y rem t ⨟
    whileNZ x (.dec x ⨟ .inc m ⨟ .dec rem ⨟ .ite (.zero rem) (.inc q ⨟ clear m ⨟ copy y rem t) .skip)

lemma ach_divModR (x y q m rem t : Fin K) (hxy : x ≠ y) (hxq : x ≠ q) (hxm : x ≠ m)
    (hxr : x ≠ rem) (hxt : x ≠ t) (hyq : y ≠ q) (hym : y ≠ m) (hyr : y ≠ rem) (hyt : y ≠ t)
    (hqm : q ≠ m) (hqr : q ≠ rem) (hqt : q ≠ t) (hmr : m ≠ rem) (hmt : m ≠ t) (hrt : rem ≠ t)
    (σ : St K)
    (Q : St K → Prop) (hBx : σ.reg x ≤ B) (hBy : σ.reg y ≤ B) (hy : 1 ≤ σ.reg y)
    (h : ∀ τ : St K, τ.out = σ.out → τ.pos = σ.pos → τ.reg q = σ.reg x / σ.reg y →
      τ.reg m = σ.reg x % σ.reg y → RegFrame [x, q, m, rem, t] σ τ → Q τ) :
    Ach w B (divModR x y q m rem t) σ Q := by
  set X := σ.reg x
  set Y := σ.reg y
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_clear _ _ _ (ach_seq (ach_copy y rem t hyr hyt hrt
    _ _ (by simp [St.setReg_apply, hyq, hym]; omega) ?_)))))
  refine ach_loop (fun k τ => τ.reg x = k ∧ k ≤ X ∧ τ.reg q * Y + τ.reg m = X - k ∧
      τ.reg m < Y ∧ τ.reg rem = Y - τ.reg m ∧ τ.out = σ.out ∧ τ.pos = σ.pos ∧
      RegFrame [x, q, m, rem, t] σ τ) Q ?_ X _ ⟨?_, le_rfl, ?_, ?_, ?_, rfl, rfl, ?_⟩
  rotate_left
  · simp [St.setReg_apply, hxq, hxm, hxr, hxt, X]
  · simp [St.setReg_apply, hqm, hqr, hqt, hmr, hmt]
  · simp [St.setReg_apply, hmr, hmt]; omega
  · simp [St.setReg_apply, hmr, hmt, hrt, hyq, hym, Y]
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    simp [St.setReg_apply, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2]
  rintro k τ ⟨hk, hkX, hqm', hmY, hrem, ho, hp, hfr⟩
  have hτy : τ.reg y = Y := hfr y (by simp [hxy.symm, hyq, hym, hyr, hyt])
  rcases k with _ | k
  · left
    refine ⟨by simp [Cond.eval, hk], h τ ho hp ?_ ?_ hfr⟩
    · have : X = τ.reg m + Y * τ.reg q := by rw [mul_comm]; omega
      rw [this, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hmY, zero_add]
    · have : X = τ.reg m + Y * τ.reg q := by rw [mul_comm]; omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmY]
  · right
    refine ⟨by simp [Cond.eval, hk], ach_seq (ach_dec (ach_seq (ach_inc ?_ (ach_seq (ach_dec
      (ach_ite ?_))))))⟩
    · simp [St.setReg_apply, hxm.symm]; omega
    · set τ₁ := ((τ.setReg x (τ.reg x - 1)).setReg m
        ((τ.setReg x (τ.reg x - 1)).reg m + 1))
      have e1 : (τ₁.setReg rem (τ₁.reg rem - 1)).reg rem = Y - τ.reg m - 1 := by
        simp [τ₁, St.setReg_apply, hxr.symm, hmr.symm, hrem]
      by_cases hz : τ.reg m + 1 = Y
      · rw [if_pos (by simp [Cond.eval, e1]; omega)]
        refine ach_seq (ach_inc ?_ (ach_seq (ach_clear _ _ _ (ach_copy y rem t hyr hyt hrt _ _ ?_
          ⟨k, by omega, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩))))
        · simp [τ₁, St.setReg_apply, hqr, hqm, hxq.symm]
          have : (τ.reg q + 1) * Y ≤ X := by rw [Nat.succ_mul]; omega
          have : τ.reg q + 1 ≤ (τ.reg q + 1) * Y := Nat.le_mul_of_pos_right _ (by omega)
          omega
        · simp [τ₁, St.setReg_apply, hyq, hym, hyr, hxy.symm, hτy]; omega
        · simp [τ₁, St.setReg_apply, hxq, hxm, hxr, hxt, hk]
        · simp [τ₁, St.setReg_apply, hqm, hqr, hqt, hxq.symm, hmr, hmt]
          rw [Nat.succ_mul]; omega
        · simp [τ₁, St.setReg_apply, hmr, hmt]; omega
        · simp [τ₁, St.setReg_apply, hmr, hmt, hrt, hyq, hym, hτy, hyr, hxy.symm]
        · simp [τ₁, ho]
        · simp [τ₁, hp]
        · refine hfr.trans ?_
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
          simp [τ₁, St.setReg_apply, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1, hz.2.2.2.2]
      · rw [if_neg (by simp [Cond.eval, e1]; omega)]
        refine ach_skip ⟨k, by omega, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [τ₁, St.setReg_apply, hxm, hxr, hxm.symm, hxr.symm, hmr.symm, hk]
        · simp [τ₁, St.setReg_apply, hqm, hqr, hmr, hxq.symm, hxm.symm, hxr.symm, hmr.symm]; omega
        · simp [τ₁, St.setReg_apply, hmr, hxm.symm, hxr.symm, hmr.symm]; omega
        · simp [τ₁, St.setReg_apply, hmr, hxm.symm, hxr.symm, hmr.symm, hrem]; omega
        · simp [τ₁, ho]
        · simp [τ₁, hp]
        · refine hfr.trans ?_
          intro z hz
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
          simp [τ₁, St.setReg_apply, hz.1, hz.2.2.1, hz.2.2.2.1]

end LS

end PathChecking
