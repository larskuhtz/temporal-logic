module

public import RequestProject.Complexity

/-!
# Output length of logspace machines

A halting machine whose work head stays in the first `S` cells cannot repeat a
configuration (ignoring the output) before halting, so it halts within
`|Q| · (n+2) · (S+1) · |Γ|^(S+1)` steps.  In particular a logspace computable function has
polynomially long outputs.

## References

This is the standard configuration-counting argument; see for example Arora–Barak [AB09],
Chapter 4. Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

open Classical

attribute [instance] TM.finQ TM.finΓ

namespace TM

variable (M : TM) (w : Word)

lemma run_zero : M.run w 0 = M.init := rfl

lemma run_succ (t : ℕ) : M.run w (t + 1) = M.step w (M.run w t) := by
  simp only [TM.run, Function.iterate_succ_apply']

lemma step_output (c : M.Cfg) : ∃ l : List Bool, l.length ≤ 1 ∧ (M.step w c).output = c.output ++ l := by
  unfold TM.step
  split_ifs
  · exact ⟨[], by simp, by simp⟩
  · rcases M.δ c.state (inputSym w c.inPos) (c.tape c.workPos) with ⟨q', g, dw, di, o⟩
    refine ⟨o.toList, ?_, rfl⟩
    cases o <;> simp

lemma output_length_le (t : ℕ) : (M.run w t).output.length ≤ t := by
  induction t with
  | zero => simp [run_zero, TM.init]
  | succ t ih =>
    obtain ⟨l, hl, he⟩ := M.step_output w (M.run w t)
    rw [run_succ, he, List.length_append]; omega

lemma output_prefix {t t' : ℕ} (h : t ≤ t') : (M.run w t).output <+: (M.run w t').output := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih =>
    rename_i m _
    obtain ⟨l, -, he⟩ := M.step_output w (M.run w m)
    rw [run_succ, he]
    exact ih.trans (List.prefix_append _ _)

lemma step_halted (c : M.Cfg) (h : M.halt c.state = true) : M.step w c = c := by
  simp [TM.step, h]

lemma run_halted {t : ℕ} (h : M.halt (M.run w t).state = true) (k : ℕ) :
    M.run w (t + k) = M.run w t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← add_assoc, run_succ, ih, step_halted _ _ _ h]

lemma run_halted' {t t' : ℕ} (h : M.halt (M.run w t).state = true) (ht : t ≤ t') :
    M.run w t' = M.run w t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  exact run_halted _ _ h k

/-- If `M` halts at time `t` with output `o`, then `o` is the output at every later time. -/
lemma HaltsWith.output_eq {t t' : ℕ} {o : Word} (h : M.HaltsWith w t o) (ht : t ≤ t') :
    (M.run w t').output = o := by
  rw [run_halted' _ _ h.1 ht]; exact h.2

lemma inPos_le (t : ℕ) : (M.run w t).inPos ≤ w.length + 1 := by
  induction t with
  | zero => simp [run_zero, TM.init]
  | succ t ih =>
    rw [run_succ]
    unfold TM.step
    split_ifs
    · exact ih
    · rcases M.δ (M.run w t).state (inputSym w (M.run w t).inPos)
        ((M.run w t).tape (M.run w t).workPos) with ⟨q', g, dw, di, o⟩
      exact min_le_right _ _

lemma tape_blank {S : ℕ} (hS : ∀ t, (M.run w t).workPos ≤ S) (t j : ℕ) (hj : S < j) :
    (M.run w t).tape j = M.blank := by
  induction t with
  | zero => simp [run_zero, TM.init]
  | succ t ih =>
    rw [run_succ]
    unfold TM.step
    split_ifs
    · exact ih
    · rcases M.δ (M.run w t).state (inputSym w (M.run w t).inPos)
        ((M.run w t).tape (M.run w t).workPos) with ⟨q', g, dw, di, o⟩
      have := hS t
      simp only
      rw [Function.update_of_ne (by omega)]
      exact ih

/-- The part of a configuration that determines the future (everything but the output). -/
def key (c : M.Cfg) : M.Q × ℕ × (ℕ → M.Γ) × ℕ := (c.state, c.inPos, c.tape, c.workPos)

lemma key_step {c c' : M.Cfg} (h : M.key c = M.key c') : M.key (M.step w c) = M.key (M.step w c') := by
  obtain ⟨q, i, T, p, o⟩ := c
  obtain ⟨q', i', T', p', o'⟩ := c'
  simp only [key, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  unfold TM.step
  split_ifs
  · rfl
  · rcases M.δ q (inputSym w i) (T p) with ⟨q₁, g, dw, di, o₁⟩
    rfl

lemma key_run_add {t₁ t₂ : ℕ} (h : M.key (M.run w t₁) = M.key (M.run w t₂)) (k : ℕ) :
    M.key (M.run w (t₁ + k)) = M.key (M.run w (t₂ + k)) := by
  induction k with
  | zero => exact h
  | succ k ih => rw [← add_assoc, ← add_assoc, run_succ, run_succ]; exact M.key_step w ih

/-- Before the first halting time, keys are pairwise distinct. -/
lemma key_inj {T : ℕ} (hT : M.halt (M.run w T).state = true)
    (hmin : ∀ t < T, M.halt (M.run w t).state = false) {t₁ t₂ : ℕ} (h12 : t₁ < t₂)
    (h2 : t₂ ≤ T) : M.key (M.run w t₁) ≠ M.key (M.run w t₂) := by
  intro h
  have := M.key_run_add w h (T - t₂)
  rw [show t₂ + (T - t₂) = T by omega] at this
  have hs := congrArg Prod.fst this
  simp only [key] at hs
  have := hmin (t₁ + (T - t₂)) (by omega)
  rw [hs, hT] at this
  exact Bool.noConfusion this

/-- Halting time bound by counting configurations. -/
lemma halt_time_bound {S T : ℕ} (hS : ∀ t, (M.run w t).workPos ≤ S)
    (hT : M.halt (M.run w T).state = true)
    (hmin : ∀ t < T, M.halt (M.run w t).state = false) :
    T + 1 ≤ Fintype.card M.Q * (w.length + 2) * (S + 1) * Fintype.card M.Γ ^ (S + 1) := by
  let F : Fin (T + 1) → M.Q × Fin (w.length + 2) × Fin (S + 1) × (Fin (S + 1) → M.Γ) :=
    fun t => ((M.run w t).state, ⟨(M.run w t).inPos, by have := M.inPos_le w t; omega⟩,
      ⟨(M.run w t).workPos, by have := hS t; omega⟩, fun j => (M.run w t).tape j)
  have hF : Function.Injective F := by
    intro a b hab
    simp only [F, Prod.mk.injEq, Fin.mk.injEq] at hab
    obtain ⟨h1, h2, h3, h4⟩ := hab
    have hk : M.key (M.run w a) = M.key (M.run w b) := by
      simp only [key, Prod.mk.injEq]
      refine ⟨h1, h2, ?_, h3⟩
      funext j
      by_cases hj : j ≤ S
      · exact congrFun h4 ⟨j, by omega⟩
      · rw [M.tape_blank w hS _ _ (by omega), M.tape_blank w hS _ _ (by omega)]
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · exact M.key_inj w hT hmin h (by omega) hk
    · exact M.key_inj w hT hmin h (by omega) hk.symm
  have := Fintype.card_le_of_injective F hF
  simpa [Fintype.card_prod, Fintype.card_fun, mul_assoc] using this

end TM

/-- A logspace computable function has polynomially bounded output length; moreover the
witnessing machine can be chosen together with the output bound. -/
theorem LogspaceComputable.exists_bound {f : Word → Word} (hf : LogspaceComputable f) :
    ∃ (M : TM) (c e : ℕ), M.Computes f ∧
      (∀ w t, (M.run w t).workPos ≤ c * (Nat.log 2 w.length + 1)) ∧
      ∀ w, (f w).length + 2 ≤ 2 ^ (e * (Nat.log 2 w.length + 1)) := by
  obtain ⟨M, c, hM, hS⟩ := hf
  refine ⟨M, c, Fintype.card M.Q + 2 + (Fintype.card M.Γ + 1) * (c + 1) + 1, hM, hS, fun w => ?_⟩
  set L := Nat.log 2 w.length + 1 with hL
  have hL1 : 1 ≤ L := by omega
  set S := c * L
  -- minimal halting time
  have hex : ∃ T, M.halt (M.run w T).state = true := by
    obtain ⟨t, ht⟩ := hM w; exact ⟨t, ht.1⟩
  let T := Nat.find hex
  have hT : M.halt (M.run w T).state = true := Nat.find_spec hex
  have hmin : ∀ t < T, M.halt (M.run w t).state = false := fun t ht => by
    have := Nat.find_min hex ht; simpa using this
  have hTb := M.halt_time_bound w (S := S) (fun t => hS w t) hT hmin
  have hfw : (f w).length ≤ T := by
    obtain ⟨t, ht⟩ := hM w
    have hTt : T ≤ t := Nat.find_min' hex ht.1
    have := M.output_length_le w T
    rw [← M.run_halted' w hT hTt, ht.2] at this
    exact this
  -- bounding the factors
  set q := Fintype.card M.Q
  set g := Fintype.card M.Γ
  have hn : w.length < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) _
  have e1 : q ≤ 2 ^ (q * L) := (Nat.lt_two_pow_self).le.trans
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_of_pos_right _ hL1))
  have e2 : w.length + 2 ≤ 2 ^ (2 * L) := by
    have : 2 ^ (2 * L) = 2 ^ L * 2 ^ L := by rw [two_mul, pow_add]
    have h2 : 2 ≤ 2 ^ L := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
    rw [this]; nlinarith
  have e3 : S + 1 ≤ 2 ^ ((c + 1) * L) := by
    have : S + 1 < 2 ^ (S + 1) := Nat.lt_two_pow_self
    refine this.le.trans (Nat.pow_le_pow_right (by norm_num) ?_)
    simp only [S]; nlinarith
  have e4 : g ^ (S + 1) ≤ 2 ^ (g * ((c + 1) * L)) := by
    rw [pow_mul]
    refine (Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _).trans ?_
    rw [← pow_mul, ← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ ?_)
    simp only [S]; nlinarith
  have e5 : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL1
  have hprod : q * (w.length + 2) * (S + 1) * g ^ (S + 1) ≤
      2 ^ (q * L) * 2 ^ (2 * L) * 2 ^ ((c + 1) * L) * 2 ^ (g * ((c + 1) * L)) := by
    gcongr
  have hexp : 2 ^ (q * L) * 2 ^ (2 * L) * 2 ^ ((c + 1) * L) * 2 ^ (g * ((c + 1) * L)) * 2 ^ L =
      2 ^ ((q + 2 + (g + 1) * (c + 1) + 1) * L) := by
    rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
    congr 1; ring
  rw [← hexp]
  have : 2 ^ (q * L) * 2 ^ (2 * L) * 2 ^ ((c + 1) * L) * 2 ^ (g * ((c + 1) * L)) * 2 =
      2 ^ (q * L) * 2 ^ (2 * L) * 2 ^ ((c + 1) * L) * 2 ^ (g * ((c + 1) * L)) + 
      2 ^ (q * L) * 2 ^ (2 * L) * 2 ^ ((c + 1) * L) * 2 ^ (g * ((c + 1) * L)) := by ring
  have hpos : 1 ≤ 2 ^ (q * L) * 2 ^ (2 * L) * 2 ^ ((c + 1) * L) * 2 ^ (g * ((c + 1) * L)) :=
    Nat.one_le_iff_ne_zero.2 (by positivity)
  calc (f w).length + 2 ≤ T + 2 := by omega
    _ ≤ 2 ^ (q * L) * 2 ^ (2 * L) * 2 ^ ((c + 1) * L) * 2 ^ (g * ((c + 1) * L)) * 2 := by
        omega
    _ ≤ _ := Nat.mul_le_mul_left _ e5

end PathChecking
