module

public import RequestProject.Logspace.VReal

/-!
# Closure properties of logspace computable functions

* `LogspaceComputable.append`: `x ↦ f x ++ g x`;
* `LogspaceComputable.pmap`: `x ↦` the concatenation, over all prefixes `x.take ℓ`
  (`ℓ ≤ |x|`), of `f (x.take ℓ)` with every bit `b` written as `[true, b]`, followed by
  `[false, false]`.
-/

@[expose] public section

namespace PathChecking

open Classical

/-- A bit `b` written as `[true, b]`. -/
def dupB (b : Bool) : List Bool := [true, b]

/-- The prefix map of `f`. -/
def pmapF (f : Word → Word) (x : Word) : Word :=
  (List.range (x.length + 1)).flatMap fun ℓ => (f (x.take ℓ)).flatMap dupB ++ [false, false]

namespace LS

open scoped LS

namespace VR

variable {x : Word} {B : ℕ}

/-- `r := |x|` (the head ends on the right end marker). -/
def setLen (r : Fin KR) : Stmt KR :=
  rewind ⨟ clear r ⨟ .loop (.not (.sym .rend)) (.right ⨟ .inc r)

lemma ach_setLen (r : Fin KR) (σ : St KR) (Q : St KR → Prop) (hB : x.length ≤ B)
    (h : ∀ τ : St KR, τ.reg r = x.length → τ.out = σ.out →
      (∀ y, y ≠ r → τ.reg y = σ.reg y) → Q τ) :
    Ach x B (setLen r) σ Q := by
  unfold setLen
  refine ach_seq (ach_rewind _ _ (ach_seq (ach_clear _ _ _ ?_)))
  refine ach_loop (fun n τ => n ≤ x.length ∧ τ.pos = x.length + 1 - n ∧
      τ.reg r = x.length - n ∧ τ.out = σ.out ∧ ∀ y, y ≠ r → τ.reg y = σ.reg y) _ ?_
    x.length _ ⟨le_rfl, by simp, by simp [St.setReg_apply], by simp,
      fun y hy => by simp [St.setReg_apply, hy]⟩
  rintro n τ ⟨hn, hpos, hr, hout, hy⟩
  rcases n with _ | n
  · left
    refine ⟨?_, h τ (by omega) hout hy⟩
    simp [Cond.eval, hpos, inputSym_eq_rend (w := x) (p := x.length + 1) (by omega) le_rfl]
  · right
    have hne : inputSym x τ.pos ≠ .rend := by
      rw [hpos]
      rcases Nat.eq_zero_or_pos (x.length + 1 - (n + 1)) with h0 | h0
      · rw [h0]; simp [inputSym]
      · rw [Ne, inputSym_eq_rend (by omega) (by omega)]; omega
    refine ⟨by simp [Cond.eval, hne], ach_seq (ach_right (ach_inc ?_ ⟨n, by omega, ?_⟩))⟩
    · simp [hr]; omega
    · refine ⟨by omega, ?_, by simp [St.setReg_apply, hr]; omega, by simp [hout], ?_⟩
      · simp [hpos]; omega
      · intro y hy'; simp [St.setReg_apply, hy', hy y hy']

end VR

open VR

/-- Space bounds on prefixes. -/
lemma space_take {M : TM} {c : ℕ} (hS : ∀ w t, (M.run w t).workPos ≤ c * (Nat.log 2 w.length + 1))
    (x : Word) (L : ℕ) (t : ℕ) :
    (M.run (x.take L) t).workPos ≤ c * (Nat.log 2 x.length + 1) := by
  refine (hS _ t).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right ?_ _))
  exact Nat.log_mono_right (by simp)

lemma len_two_pow (n : ℕ) : n + 2 ≤ 2 ^ (2 * (Nat.log 2 n + 1)) := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : 2 ≤ 2 ^ (Nat.log 2 n + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [two_mul, pow_add]; nlinarith

/-- The program for `x ↦ f x ++ g x`. -/
noncomputable def appendProg (M₁ M₂ : TM) : Stmt KR :=
  setLen rL ⨟ runPrefix (fun b => [b]) M₁ ⨟ runPrefix (fun b => [b]) M₂

lemma flatMap_single (l : List Bool) : l.flatMap (fun b => [b]) = l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

end LS

open LS LS.VR in
/-- **Concatenation of logspace computable functions.** -/
theorem LogspaceComputable.append {f g : Word → Word} (hf : LogspaceComputable f)
    (hg : LogspaceComputable g) : LogspaceComputable (fun x => f x ++ g x) := by
  obtain ⟨M₁, c₁, hM₁, hS₁⟩ := hf
  obtain ⟨M₂, c₂, hM₂, hS₂⟩ := hg
  let S₁ : Word → ℕ := fun x => c₁ * (Nat.log 2 x.length + 1)
  let S₂ : Word → ℕ := fun x => c₂ * (Nat.log 2 x.length + 1)
  let B : Word → ℕ := fun x => (M₁.nQ + S₁ x + 2 + M₁.nG ^ (S₁ x + 2)) +
    (M₂.nQ + S₂ x + 2 + M₂.nG ^ (S₂ x + 2)) + (x.length + 4)
  refine logspaceComputable_of_prog (appendProg M₁ M₂) _ B
    (M₁.nQ + c₁ + M₁.nG * (c₁ + 2) + M₂.nQ + c₂ * (2 + 1) + M₂.nG * (c₂ * (2 + 1) + 2) + 2 + 4)
    (fun x => ?_) (fun x => ?_)
  · have := register_bound M₁.nQ M₁.nG c₁ M₂.nQ M₂.nG c₂ 2 x.length x.length
      (len_two_pow x.length)
    refine lt_of_le_of_lt ?_ this
    simp only [B, S₁, S₂]
    have : c₂ * (Nat.log 2 x.length + 1) ≤ c₂ * (Nat.log 2 x.length + 1) := le_rfl
    omega
  · have key : Ach x (B x) (appendProg M₁ M₂) (St.init KR) (fun τ => τ.out = f x ++ g x) := by
      unfold appendProg
      refine ach_seq (ach_setLen _ _ _ (by simp only [B]; omega) ?_)
      intro τ hτL hτo _
      have hEx : ExtraOK (fun σ : St KR => σ.reg rL = x.length) :=
        fun σ τ h hy => by
          simp only at h ⊢; rw [hy rL (by decide) (by decide) (by decide)]; exact h
      refine ach_seq ((ach_runPrefix (fun b => [b]) M₁ f hM₁ τ (space_take hS₁ x _) hEx hτL
        (by omega) (by simp only [B, S₁]; omega)).mono ?_)
      rintro τ' ⟨ho', hL'⟩
      refine (ach_runPrefix (fun b => [b]) M₂ g hM₂ τ' (space_take hS₂ x _) hEx hL'
        (by omega) (by simp only [B, S₂]; omega)).mono ?_
      rintro τ'' ⟨ho'', -⟩
      rw [ho'', ho', hτo, hτL, hL', List.take_length, flatMap_single, flatMap_single]
      simp [St.init]
    obtain ⟨σ', h1, h2⟩ := key
    exact ⟨σ', h1, h2⟩

namespace LS

namespace VR

/-- The program for the prefix map. -/
noncomputable def pmapProg (M : TM) : Stmt KR :=
  setLen rN ⨟ clear rL ⨟ copy rN rK rT ⨟ .inc rK ⨟
    .loop (.not (.zero rK)) (runPrefix dupB M ⨟ emitBits [false, false] ⨟ .inc rL ⨟ .dec rK)

end VR

end LS

open LS LS.VR in
/-- **The prefix map of a logspace computable function is logspace computable.** -/
theorem LogspaceComputable.pmap {f : Word → Word} (hf : LogspaceComputable f) :
    LogspaceComputable (pmapF f) := by
  obtain ⟨M, c, hM, hS⟩ := hf
  let S : Word → ℕ := fun x => c * (Nat.log 2 x.length + 1)
  let B : Word → ℕ := fun x => (M.nQ + S x + 2 + M.nG ^ (S x + 2)) +
    (M.nQ + S x + 2 + M.nG ^ (S x + 2)) + (x.length + 4)
  refine logspaceComputable_of_prog (pmapProg M) _ B
    (M.nQ + c + M.nG * (c + 2) + M.nQ + c * (2 + 1) + M.nG * (c * (2 + 1) + 2) + 2 + 4)
    (fun x => ?_) (fun x => ?_)
  · have := register_bound M.nQ M.nG c M.nQ M.nG c 2 x.length x.length (len_two_pow x.length)
    refine lt_of_le_of_lt ?_ this
    simp only [B, S]
    omega
  · have hBx : M.nQ + S x + 2 + M.nG ^ (S x + 2) + x.length + 3 ≤ B x := by
      simp only [B]; omega
    have key : Ach x (B x) (pmapProg M) (St.init KR) (fun τ => τ.out = pmapF f x) := by
      unfold pmapProg
      refine ach_seq (ach_setLen _ _ _ (by simp only [B]; omega) ?_)
      intro τ hτN hτo _
      refine ach_seq (ach_clear _ _ _ (ach_seq (ach_copy _ _ _ (by decide) (by decide)
        (by decide) _ _ (by simp [St.setReg_apply, hτN]; simp only [B]; omega)
        (ach_seq (ach_inc ?_ ?_)))))
      · simp [St.setReg_apply, hτN]; simp only [B]; omega
      set σ₀ := ((((τ.setReg rL 0).setReg rK ((τ.setReg rL 0).reg rN)).setReg rT 0).setReg rK
        ((((τ.setReg rL 0).setReg rK ((τ.setReg rL 0).reg rN)).setReg rT 0).reg rK + 1))
        with hσ₀
      have e0N : σ₀.reg rN = x.length := by simp [hσ₀, St.setReg_apply, hτN]
      have e0L : σ₀.reg rL = 0 := by simp [hσ₀, St.setReg_apply]
      have e0K : σ₀.reg rK = x.length + 1 := by simp [hσ₀, St.setReg_apply, hτN]
      have e0o : σ₀.out = [] := by simp [hσ₀, hτo, St.init]
      let blk : ℕ → Word := fun ℓ => (f (x.take ℓ)).flatMap dupB ++ [false, false]
      refine ach_loop (fun n σ => n ≤ x.length + 1 ∧ σ.reg rK = n ∧
          σ.reg rL = x.length + 1 - n ∧ σ.reg rN = x.length ∧
          σ.out = (List.range (x.length + 1 - n)).flatMap blk) _ ?_ (x.length + 1) σ₀
        ⟨le_rfl, e0K, by rw [e0L]; omega, e0N, by simp [e0o]⟩
      rintro n σ ⟨hn, hK, hL, hN, ho⟩
      rcases n with _ | n
      · left
        refine ⟨by simp [Cond.eval, hK], ?_⟩
        rw [ho]; rfl
      · right
        refine ⟨by simp [Cond.eval, hK], ?_⟩
        have hEx : ExtraOK (fun τ : St KR => τ.reg rK = n + 1 ∧ τ.reg rL = x.length - n ∧
            τ.reg rN = x.length) := by
          intro σ' τ' h hy
          rw [hy rK (by decide) (by decide) (by decide), hy rL (by decide) (by decide)
            (by decide), hy rN (by decide) (by decide) (by decide)]
          exact h
        have hL' : σ.reg rL = x.length - n := by omega
        refine ach_seq ((ach_runPrefix dupB M f hM σ (space_take hS x _) hEx ⟨hK, hL', hN⟩
          (by omega) hBx).mono ?_)
        rintro τ' ⟨ho', hK', hL'', hN'⟩
        refine ach_seq (ach_emitBits _ _ _ (ach_seq (ach_inc ?_ (ach_dec ⟨n, by omega, ?_⟩))))
        · simp [hL'']; simp only [B]; omega
        · refine ⟨by omega, by simp [St.setReg_apply, hK'], by simp [St.setReg_apply, hL'']; omega,
            by simp [St.setReg_apply, hN'], ?_⟩
          simp only [ho', ho, hL']
          rw [show x.length + 1 - n = (x.length + 1 - (n + 1)) + 1 by omega, List.range_succ,
            List.flatMap_append]
          simp [blk, show x.length + 1 - (n + 1) = x.length - n by omega]
    obtain ⟨σ', h1, h2⟩ := key
    exact ⟨σ', h1, h2⟩

end PathChecking
