module

public import RequestProject.LTLPath.FE

/-!
# Uncapped semantics of functional expressions

`FE.ev` is the semantics of expressions without the cap: constants, additions, multiplications
and counts are exact.  `E.dg d δ e` is a syntactic degree: if the variables `x < d` are bounded by
`X ^ δ x` with `X = |w| + 2`, then every intermediate value of `e` is bounded by `X ^ dg`.
Hence, if `X ^ dg ≤ C`, the capped semantics agrees with the uncapped one (`eval_eq_ev`).
-/

@[expose] public section

namespace PathChecking

namespace FE

open LL

/-- Binary operations without cap. -/
def apU : BOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

/-- Counting without cap. -/
def cntU (N : ℕ) (f : ℕ → ℕ) : ℕ := (List.range N).countP (fun i => f i ≠ 0)

/-- Uncapped semantics. -/
def ev (w : Word) : ℕ → (ℕ → ℕ) → E → ℕ
  | _, _, .c k => k
  | _, ρ, .v x => ρ x
  | _, _, .len => w.length
  | d, ρ, .inp e => symNum (inputSym w (ev w d ρ e))
  | d, ρ, .bin o a b => apU o (ev w d ρ a) (ev w d ρ b)
  | d, ρ, .ite cnd a b => if ev w d ρ cnd ≠ 0 then ev w d ρ a else ev w d ρ b
  | d, ρ, .find n body => findF (ev w d ρ n) (fun i => ev w (d + 1) (Function.update ρ d i) body)
  | d, ρ, .count n body => cntU (ev w d ρ n) (fun i => ev w (d + 1) (Function.update ρ d i) body)
  | d, ρ, .lett a body => ev w (d + 1) (Function.update ρ d (ev w d ρ a)) body

/-- Degree of an operation. -/
def dgOp : BOp → ℕ → ℕ → ℕ
  | .add, a, b => max a b + 1
  | .mul, a, b => a + b
  | _, a, b => max a b

/-- Syntactic degree. -/
def E.dg : ℕ → (ℕ → ℕ) → E → ℕ
  | _, _, .c k => k
  | _, δ, .v x => δ x
  | _, _, .len => 1
  | d, δ, .inp e => max 2 (e.dg d δ)
  | d, δ, .bin o a b => dgOp o (a.dg d δ) (b.dg d δ)
  | d, δ, .ite cnd a b => max (cnd.dg d δ) (max (a.dg d δ) (b.dg d δ))
  | d, δ, .find n body => max (n.dg d δ) (body.dg (d + 1) (Function.update δ d (n.dg d δ)))
  | d, δ, .count n body => max (n.dg d δ) (body.dg (d + 1) (Function.update δ d (n.dg d δ)))
  | d, δ, .lett a body => max (a.dg d δ) (body.dg (d + 1) (Function.update δ d (a.dg d δ)))

lemma findF_le (N : ℕ) (f : ℕ → ℕ) : findF N f ≤ N := by
  unfold findF
  cases h : (List.range N).find? (fun i => f i ≠ 0) with
  | none => simp
  | some i =>
    have := List.mem_of_find?_eq_some h
    simp only [List.mem_range] at this
    simp; omega

lemma findF_congr {N : ℕ} {f g : ℕ → ℕ} (h : ∀ i < N, f i = g i) : findF N f = findF N g := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [findF_succ, findF_succ, ih (fun i hi => h i (by omega)), h N (by omega)]

lemma cntU_le (N : ℕ) (f : ℕ → ℕ) : cntU N f ≤ N := by
  unfold cntU
  exact (List.countP_le_length).trans (by simp)

lemma cntU_succ (N : ℕ) (f : ℕ → ℕ) : cntU (N + 1) f = cntU N f + if f N ≠ 0 then 1 else 0 := by
  unfold cntU
  rw [List.range_succ, List.countP_append]
  simp

lemma cntU_congr {N : ℕ} {f g : ℕ → ℕ} (h : ∀ i < N, f i = g i) : cntU N f = cntU N g := by
  induction N with
  | zero => rfl
  | succ N ih => rw [cntU_succ, cntU_succ, ih (fun i hi => h i (by omega)), h N (by omega)]

lemma countF_eq_cntU {C N : ℕ} (f : ℕ → ℕ) (hN : N ≤ C) : countF C N f = cntU N f := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [countF_succ, cntU_succ, ih (by omega)]
    have := cntU_le N f
    split_ifs <;> omega

lemma ev_congr (w : Word) : ∀ (e : E) (d : ℕ) (ρ ρ' : ℕ → ℕ), e.wf d = true →
    (∀ x < d, ρ x = ρ' x) → ev w d ρ e = ev w d ρ' e := by
  intro e
  induction e with
  | c k => intros; rfl
  | v x => intro d ρ ρ' hw h; simp only [E.wf, decide_eq_true_eq] at hw; exact h x hw
  | len => intros; rfl
  | inp e ih => intro d ρ ρ' hw h; simp only [ev]; rw [ih d ρ ρ' hw h]
  | bin o a b iha ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [ev]; rw [iha d ρ ρ' hw.1 h, ihb d ρ ρ' hw.2 h]
  | ite c a b ihc iha ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [ev]; rw [ihc d ρ ρ' hw.1.1 h, iha d ρ ρ' hw.1.2 h, ihb d ρ ρ' hw.2 h]
  | find n body ihn ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [ev]
    rw [ihn d ρ ρ' hw.1 h]
    congr 1; funext i
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)
  | count n body ihn ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [ev]
    rw [ihn d ρ ρ' hw.1 h]
    congr 1; funext i
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)
  | lett a body iha ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [ev]
    rw [iha d ρ ρ' hw.1 h]
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)

lemma le_pow_self {X : ℕ} (hX : 2 ≤ X) (k : ℕ) : k ≤ X ^ k :=
  (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hX k)

lemma pow_mono {X : ℕ} (hX : 2 ≤ X) {a b : ℕ} (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right (by omega) h

lemma symNum_le3 (x : Word) (p : ℕ) : symNum (inputSym x p) ≤ 3 := by
  unfold inputSym
  split_ifs
  · simp [symNum]
  · split
    · rename_i b _; cases b <;> simp [symNum]
    · simp [symNum]

lemma update_bound {X : ℕ} {ρ δ : ℕ → ℕ} {d : ℕ} (h : ∀ x < d, ρ x ≤ X ^ δ x) {i k : ℕ}
    (hi : i ≤ X ^ k) : ∀ x < d + 1, Function.update ρ d i x ≤ X ^ Function.update δ d k x := by
  intro x hx
  by_cases hxd : x = d
  · subst hxd; simpa using hi
  · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)

/-- **Cap elimination.** -/
theorem eval_eq_ev {w : Word} {C : ℕ} : ∀ (e : E) (d : ℕ) (ρ δ : ℕ → ℕ), e.wf d = true →
    (∀ x < d, ρ x ≤ (w.length + 2) ^ δ x) → (w.length + 2) ^ e.dg d δ ≤ C →
    eval w C d ρ e = ev w d ρ e ∧ ev w d ρ e ≤ (w.length + 2) ^ e.dg d δ := by
  have hX : 2 ≤ w.length + 2 := by omega
  set X := w.length + 2
  intro e
  induction e with
  | c k =>
    intro d ρ δ _ _ hC
    have := le_pow_self hX k
    simp only [eval, ev, E.dg] at *
    exact ⟨by omega, this⟩
  | v x =>
    intro d ρ δ hw hρ hC
    simp only [E.wf, decide_eq_true_eq] at hw
    exact ⟨rfl, hρ x hw⟩
  | len =>
    intro d ρ δ _ _ hC
    simp only [eval, ev, E.dg, pow_one] at *
    exact ⟨by omega, by omega⟩
  | inp e ih =>
    intro d ρ δ hw hρ hC
    simp only [E.wf] at hw
    simp only [E.dg] at hC
    obtain ⟨h1, -⟩ := ih d ρ δ hw hρ ((pow_mono hX (le_max_right _ _)).trans hC)
    simp only [eval, ev, E.dg, h1]
    refine ⟨trivial, (symNum_le3 _ _).trans ((show 3 ≤ X ^ 2 by nlinarith).trans
      (pow_mono hX (le_max_left _ _)))⟩
  | bin o a b iha ihb =>
    intro d ρ δ hw hρ hC
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.dg] at hC ⊢
    have hda : a.dg d δ ≤ dgOp o (a.dg d δ) (b.dg d δ) := by
      cases o <;> simp [dgOp]; omega
    have hdb : b.dg d δ ≤ dgOp o (a.dg d δ) (b.dg d δ) := by
      cases o <;> simp [dgOp]; omega
    obtain ⟨a1, a2⟩ := iha d ρ δ hw.1 hρ ((pow_mono hX hda).trans hC)
    obtain ⟨b1, b2⟩ := ihb d ρ δ hw.2 hρ ((pow_mono hX hdb).trans hC)
    simp only [eval, ev, a1, b1]
    set u := ev w d ρ a
    set v := ev w d ρ b
    have key : apU o u v ≤ X ^ dgOp o (a.dg d δ) (b.dg d δ) := by
      cases o with
      | add =>
        simp only [apU, dgOp, pow_succ]
        have := pow_mono hX (le_max_left (a.dg d δ) (b.dg d δ))
        have := pow_mono hX (le_max_right (a.dg d δ) (b.dg d δ))
        nlinarith
      | mul => simp only [apU, dgOp, pow_add]; exact Nat.mul_le_mul a2 b2
      | sub => exact (Nat.sub_le _ _).trans (a2.trans (pow_mono hX hda))
      | div => exact (Nat.div_le_self _ _).trans (a2.trans (pow_mono hX hda))
      | mod => exact (Nat.mod_le _ _).trans (a2.trans (pow_mono hX hda))
      | lt => simp only [apU]; split_ifs <;> simp [Nat.one_le_pow _ _ (by omega : 0 < X)]
      | eq => simp only [apU]; split_ifs <;> simp [Nat.one_le_pow _ _ (by omega : 0 < X)]
    refine ⟨?_, key⟩
    cases o <;> simp only [BOp.ap, apU] <;> first | rfl | (simp only [apU] at key; omega)
  | ite c a b ihc iha ihb =>
    intro d ρ δ hw hρ hC
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.dg] at hC ⊢
    obtain ⟨c1, -⟩ := ihc d ρ δ hw.1.1 hρ ((pow_mono hX (le_max_left _ _)).trans hC)
    obtain ⟨a1, a2⟩ := iha d ρ δ hw.1.2 hρ
      ((pow_mono hX ((le_max_left _ _).trans (le_max_right _ _))).trans hC)
    obtain ⟨b1, b2⟩ := ihb d ρ δ hw.2 hρ
      ((pow_mono hX ((le_max_right _ _).trans (le_max_right _ _))).trans hC)
    simp only [eval, ev, c1, a1, b1]
    refine ⟨trivial, ?_⟩
    split_ifs
    · exact a2.trans (pow_mono hX ((le_max_left _ _).trans (le_max_right _ _)))
    · exact b2.trans (pow_mono hX ((le_max_right _ _).trans (le_max_right _ _)))
  | find n body ihn ihb =>
    intro d ρ δ hw hρ hC
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.dg] at hC ⊢
    obtain ⟨n1, n2⟩ := ihn d ρ δ hw.1 hρ ((pow_mono hX (le_max_left _ _)).trans hC)
    simp only [eval, ev, n1]
    refine ⟨findF_congr fun i hi => ?_, (findF_le _ _).trans
      (n2.trans (pow_mono hX (le_max_left _ _)))⟩
    exact (ihb (d + 1) _ _ hw.2 (update_bound hρ (hi.le.trans n2))
      ((pow_mono hX (le_max_right _ _)).trans hC)).1
  | count n body ihn ihb =>
    intro d ρ δ hw hρ hC
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.dg] at hC ⊢
    obtain ⟨n1, n2⟩ := ihn d ρ δ hw.1 hρ ((pow_mono hX (le_max_left _ _)).trans hC)
    have hnC : ev w d ρ n ≤ C := n2.trans ((pow_mono hX (le_max_left _ _)).trans hC)
    simp only [eval, ev, n1]
    refine ⟨?_, (cntU_le _ _).trans (n2.trans (pow_mono hX (le_max_left _ _)))⟩
    rw [countF_eq_cntU _ hnC]
    exact cntU_congr fun i hi => (ihb (d + 1) _ _ hw.2 (update_bound hρ (hi.le.trans n2))
      ((pow_mono hX (le_max_right _ _)).trans hC)).1
  | lett a body iha ihb =>
    intro d ρ δ hw hρ hC
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.dg] at hC ⊢
    obtain ⟨a1, a2⟩ := iha d ρ δ hw.1 hρ ((pow_mono hX (le_max_left _ _)).trans hC)
    simp only [eval, ev, a1]
    obtain ⟨b1, b2⟩ := ihb (d + 1) _ _ hw.2 (update_bound hρ a2)
      ((pow_mono hX (le_max_right _ _)).trans hC)
    exact ⟨b1, b2.trans (pow_mono hX (le_max_right _ _))⟩

end FE

end PathChecking
