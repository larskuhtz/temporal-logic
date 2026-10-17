module

public import RequestProject.LTLPath.Run

/-!
# Correctness of the global circuit

Given a semantics `sat p i` of the nodes of the formula tree on a lasso with stem `s` and loop
`ℓ` (`Sem`: the local recursion of the operators, polarities, and periodicity on the loop), the
`main` gate `(p, i)` computes `sat p i` (negated if `pol p`) for all `i` with `i + ℓ < W p`
(`gate_sem`).  For until, the gates compute the until bounded by the window, which agrees with
the unbounded until since a minimal witness on a lasso is less than `max i s + ℓ`.
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-- A semantics of the formula tree. -/
structure Sem (T : FT) (sat : ℕ → ℕ → Bool) : Prop where
  pol1 : ∀ p, T.nd p = true → 1 ≤ T.ar p → T.pol (p + 1) = (T.pol p ^^ decide (T.kd p = 2))
  pol2 : ∀ p, T.nd p = true → T.ar p = 2 → T.pol (T.c2 p) = T.pol p
  leaf : ∀ p i, T.nd p = true → T.kd p ≤ 1 → sat p i = T.lv p i
  neg : ∀ p i, T.nd p = true → T.kd p = 2 → sat p i = !sat (p + 1) i
  and : ∀ p i, T.nd p = true → T.kd p = 3 → sat p i = (sat (p + 1) i && sat (T.c2 p) i)
  X : ∀ p i, T.nd p = true → T.kd p = 4 → sat p i = sat (p + 1) (i + 1)
  U : ∀ p i, T.nd p = true → T.kd p = 5 →
    (sat p i = true ↔ ∃ k, sat (T.c2 p) (i + k) = true ∧ ∀ j < k, sat (p + 1) (i + j) = true)
  per : ∀ p i, T.nd p = true → T.s ≤ i → sat p (i + T.ℓ) = sat p i

lemma val_gateAt {p i t : ℕ} (hp : p < T.N) (hi : i < T.Wm) (ht : t ≤ 1) :
    GS.val T.gate (T.idx p i t) = (T.gateAt p i t).evalFn ∅ [] (GS.val T.gate) := by
  rw [GS.val_spec gate_ordered, gate_idx hp hi ht]

lemma evalFn_andOr2 (b : Bool) (v : ℕ → Bool) (x y : ℕ) :
    Gate.evalFn ∅ [] v ⟨andOr b, [x, y]⟩ = cond b (v x || v y) (v x && v y) := by
  cases b <;> simp [Gate.evalFn, andOr]

lemma evalFn_and1 (v : ℕ → Bool) (x : ℕ) : Gate.evalFn ∅ [] v ⟨.and, [x]⟩ = v x := by
  simp [Gate.evalFn]

lemma nd_lt_N {p : ℕ} (hp : T.nd p = true) : p < T.N := lt_of_lt_of_le (PT.lt_F hp) T.hN

/-- Minimal witnesses of until on a lasso. -/
lemma until_window {sat : ℕ → ℕ → Bool} (hS : T.Sem sat) {p i : ℕ} (hp : T.nd p = true)
    (h5 : T.kd p = 5) {k : ℕ} (hk : sat (T.c2 p) (i + k) = true)
    (hj : ∀ j < k, sat (p + 1) (i + j) = true) :
    ∃ k', i + k' < max i T.s + T.ℓ ∧ sat (T.c2 p) (i + k') = true ∧
      ∀ j < k', sat (p + 1) (i + j) = true := by
  have har : T.ar p = 2 := (ar_of_kd hp).2.2 (Or.inr h5)
  have hc2 := (child2_lt_N hp har).2.2
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hlt : i + k < max i T.s + T.ℓ
    · exact ⟨k, hlt, hk, hj⟩
    · have hℓ := T.hℓ
      refine ih (k - T.ℓ) (by omega) ?_ (fun j hjk => hj j (by omega))
      have := hS.per (T.c2 p) (i + (k - T.ℓ)) hc2 (by omega)
      rw [show i + (k - T.ℓ) + T.ℓ = i + k by omega] at this
      rw [← this]; exact hk

/-- **The global circuit computes the semantics.** -/
theorem gate_sem {sat : ℕ → ℕ → Bool} (hS : T.Sem sat) :
    ∀ p, T.nd p = true → ∀ i, i + T.ℓ < T.W p →
      GS.val T.gate (T.idx p i 1) = (sat p i ^^ T.pol p) := by
  intro p
  induction hm : T.F - p using Nat.strong_induction_on generalizing p with
  | _ m ih =>
    intro hp i hi
    subst hm
    have hpN := nd_lt_N hp
    have hWp := W_le_Wm (T := T) hpN
    have ha := ar_of_kd hp
    have hℓ := T.hℓ
    -- correctness of the children
    have ch1 : T.ar p ≠ 0 → ∀ j, j < T.W p →
        GS.val T.gate (T.idx (p + 1) j 1) = (sat (p + 1) j ^^ T.pol (p + 1)) := by
      intro har j hj
      have hc := child1_lt_N hp har
      refine ih (T.F - (p + 1)) (by have := PT.lt_F hc.2; omega) (p + 1) rfl hc.2 j ?_
      rw [W_succ]; omega
    have ch2 : T.ar p = 2 → ∀ j, j < T.W p →
        GS.val T.gate (T.idx (T.c2 p) j 1) = (sat (T.c2 p) j ^^ T.pol (T.c2 p)) := by
      intro har j hj
      have hc := child2_lt_N hp har
      refine ih (T.F - T.c2 p) (by have := PT.lt_F hc.2.2; omega) (T.c2 p) rfl hc.2.2 j ?_
      have := W_add (T := T) hc.1; omega
    rcases kd_cases hp with e | e | e | e | e
    · rw [val_gateAt hpN (by omega) le_rfl]; unfold gateAt; rw [if_pos ⟨hp, by omega⟩]
      rw [if_pos e, if_pos rfl, hS.leaf p i hp e]
      simp [Gate.evalFn]
    · rw [val_gateAt hpN (by omega) le_rfl]; unfold gateAt; rw [if_pos ⟨hp, by omega⟩]
      rw [if_neg (by omega), if_pos e, if_pos rfl, evalFn_and1,
        ch1 (by have := ha.2.1 (Or.inl e); omega) i (by omega), hS.neg p i hp e,
        hS.pol1 p hp (by have := ha.2.1 (Or.inl e); omega)]
      all_goals (cases sat (p + 1) i <;> cases T.pol p <;> simp [e])
    · have e2 := ha.2.2 (Or.inl e)
      rw [val_gateAt hpN (by omega) le_rfl]; unfold gateAt; rw [if_pos ⟨hp, by omega⟩]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e, if_pos rfl,
        evalFn_andOr2, ch1 (by omega) i (by omega), ch2 e2 i (by omega), hS.and p i hp e,
        hS.pol1 p hp (by omega), hS.pol2 p hp e2]
      all_goals (cases sat (p + 1) i <;> cases sat (T.c2 p) i <;> cases T.pol p <;> simp [e])
    · rw [val_gateAt hpN (by omega) le_rfl]; unfold gateAt; rw [if_pos ⟨hp, by omega⟩]
      rw [if_neg (by omega), if_neg (by omega), if_pos e, if_pos rfl, evalFn_and1,
        ch1 (by have := ha.2.1 (Or.inr e); omega) (i + 1) (by omega), hS.X p i hp e,
        hS.pol1 p hp (by have := ha.2.1 (Or.inr e); omega)]
      all_goals simp [e]
    · have e2 := ha.2.2 (Or.inr e)
      have hp1 : T.pol (p + 1) = T.pol p := by rw [hS.pol1 p hp (by omega)]; simp [e]
      have hp2 := hS.pol2 p hp e2
      -- the bounded until
      let bu : ℕ → Prop := fun j => ∃ m, j ≤ m ∧ m < T.W p ∧ sat (T.c2 p) m = true ∧
        ∀ m', j ≤ m' → m' < m → sat (p + 1) m' = true
      have key : ∀ d j, j + d + 1 = T.W p →
          GS.val T.gate (T.idx p j 1) = (decide (bu j) ^^ T.pol p) := by
        intro d
        induction d with
        | zero =>
          intro j hj
          rw [val_gateAt hpN (by omega) le_rfl]
          unfold gateAt
          rw [if_pos (show T.nd p = true ∧ j < T.W p from ⟨hp, by omega⟩), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos rfl, if_neg (by omega), evalFn_and1, ch2 e2 j (by omega),
            hp2]
          have hb : bu j ↔ sat (T.c2 p) j = true :=
            ⟨fun ⟨m, h1, h2, h3, _⟩ => by rwa [show j = m by omega],
              fun h => ⟨j, le_rfl, by omega, h, fun m' h1 h2 => by omega⟩⟩
          have hd : decide (bu j) = sat (T.c2 p) j := by
            cases hs : sat (T.c2 p) j
            · exact decide_eq_false (fun h => by rw [hb, hs] at h; exact absurd h (by simp))
            · exact decide_eq_true (hb.2 hs)
          rw [hd]
        | succ d ihd =>
          intro j hj
          rw [val_gateAt hpN (by omega) le_rfl]
          unfold gateAt
          rw [if_pos (show T.nd p = true ∧ j < T.W p from ⟨hp, by omega⟩), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_pos rfl, if_pos (by omega), evalFn_andOr2,
            val_gateAt (p := p) (i := j) (t := 0) hpN (by omega) (by omega)]
          unfold gateAt
          rw [if_pos (show T.nd p = true ∧ j < T.W p from ⟨hp, by omega⟩), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            if_neg (by omega), if_neg (by omega), if_pos (by omega), evalFn_andOr2,
            ch2 e2 j (by omega), ch1 (by omega) j (by omega), ihd (j + 1) (by omega), hp1, hp2]
          have hbu : bu j ↔ sat (T.c2 p) j = true ∨ (sat (p + 1) j = true ∧ bu (j + 1)) := by
            constructor
            · rintro ⟨m, h1, h2, h3, h4⟩
              by_cases hmj : m = j
              · left; rwa [← hmj]
              · right
                exact ⟨h4 j le_rfl (by omega), m, by omega, h2, h3,
                  fun m' a b => h4 m' (by omega) b⟩
            · rintro (h | ⟨h1, m, h2, h3, h4, h5⟩)
              · exact ⟨j, le_rfl, by omega, h, fun m' a b => by omega⟩
              · refine ⟨m, by omega, h3, h4, fun m' a b => ?_⟩
                by_cases hm' : m' = j
                · rw [hm']; exact h1
                · exact h5 m' (by omega) b
          have : decide (bu j) = (sat (T.c2 p) j || (sat (p + 1) j && decide (bu (j + 1)))) := by
            rw [Bool.eq_iff_iff]
            simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            exact hbu
          rw [this]
          cases sat (T.c2 p) j <;> cases sat (p + 1) j <;> cases decide (bu (j + 1)) <;>
            cases T.pol p <;> rfl
      rw [key (T.W p - 1 - i) i (by omega)]
      congr 1
      have hsat : sat p i = true ↔ bu i := by
        rw [hS.U p i hp e]
        constructor
        · rintro ⟨k, hk, hj⟩
          obtain ⟨k', hk', hc, hj'⟩ := until_window hS hp e hk hj
          refine ⟨i + k', by omega, ?_, hc, fun m' a b => ?_⟩
          · unfold W at hi ⊢; have : T.s + T.ℓ ≤ T.s + (p + 2) * T.ℓ := by nlinarith
            omega
          · have := hj' (m' - i) (by omega); rwa [show i + (m' - i) = m' by omega] at this
        · rintro ⟨m, h1, -, h3, h4⟩
          refine ⟨m - i, by rwa [show i + (m - i) = m by omega], fun j hj => h4 _ (by omega)
            (by omega)⟩
      rw [Bool.eq_iff_iff, decide_eq_true_eq]
      exact hsat.symm

end FT

end PathChecking
