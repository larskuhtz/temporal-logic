module

public import RequestProject.LogLang.Out

/-!
# Small verified routines of the loop language

* `powP`: `dst := base ^ k`;
* `findP`: the first index `j < bound` at which a predicate expression vanishes;
* `logP`: `⌊log₂ n⌋`.
-/

@[expose] public section

namespace PathChecking

namespace LL

variable {W : ℕ} {z : Word} {C : ℕ}

/-! ## Powers -/

/-- `dst := base ^ k` (loop counter `cnt`). -/
def powP (dst base cnt : Fin W) (k : ℕ) : Pr W :=
  .seq (.set dst (.c 1)) (.loop cnt (.c k) (.set dst (.bin .mul (.v dst) (.v base))))

lemma powP_wr (dst base cnt : Fin W) (k : ℕ) : (powP dst base cnt k).wr = [dst, cnt, dst] := rfl

lemma run_powP (dst base cnt : Fin W) (k : ℕ) (hdb : dst ≠ base) (hcb : cnt ≠ base) (hdc : dst ≠ cnt)
    (ρ : Fin W → ℕ) (hk : k ≤ C) (hC : 1 ≤ C) (hb : ρ base ^ k ≤ C) :
    ((powP dst base cnt k).run z C ρ).1 dst = ρ base ^ k ∧
      ((powP dst base cnt k).run z C ρ).2 = [] := by
  unfold powP
  simp only [run_seq, run_set, eval_c, min_eq_left hC, List.nil_append]
  have h := run_loop_spec (w := z) (C := C) cnt (.c k) (.set dst (.bin .mul (.v dst) (.v base)))
    (Function.update ρ dst 1)
    (fun j ρ' => ρ' dst = ρ base ^ j ∧ ρ' base = ρ base) (fun _ => [])
    ⟨by simp, by simp [Function.update_of_ne (Ne.symm hdb)]⟩ (by
      intro j hj ρ' ⟨h1, h2⟩
      simp only [eval_c, min_eq_left hk] at hj
      have hb' : (Function.update ρ' cnt j) base = ρ base := by
        rw [Function.update_of_ne (Ne.symm hcb)]; exact h2
      have hd' : (Function.update ρ' cnt j) dst = ρ base ^ j := by
        rw [Function.update_of_ne hdc]; exact h1
      refine ⟨⟨?_, ?_⟩, rfl⟩
      · simp only [run_set, Function.update_self, eval_bin, eval_v, ap_mul, hb', hd']
        rw [← pow_succ, min_eq_left]
        rcases Nat.eq_zero_or_pos (ρ base) with h0 | h0
        · rw [h0, zero_pow (by omega)]; omega
        · exact (Nat.pow_le_pow_right h0 (by omega)).trans hb
      · simp only [run_set]; rw [Function.update_of_ne (Ne.symm hdb), hb'])
  simp only [eval_c, min_eq_left hk] at h
  exact ⟨h.1.1, by rw [h.2]; simp⟩

/-! ## Finding the first zero of a predicate -/

/-- `res :=` the first `j < bound` with `P = 0` (flag `fd`). -/
def findP (res fd j : Fin W) (bound P : Ex W) : Pr W :=
  .seq (.set fd (.c 0)) (.loop j bound
    (.ite (.bin .eq (.bin .add (.v fd) P) (.c 0)) (.seq (.set fd (.c 1)) (.set res (.v j))) .skip))

lemma run_findP (res fd j : Fin W) (bound P : Ex W) (hrf : res ≠ fd) (hrj : res ≠ j)
    (hfj : fd ≠ j) (ρ : Fin W → ℕ) (p : ℕ → ℕ) (m : ℕ) (hC : 1 ≤ C)
    (hB : ∀ ρ', (∀ v, v ≠ res → v ≠ fd → v ≠ j → ρ' v = ρ v) → bound.eval z C ρ' = bound.eval z C ρ)
    (hP : ∀ i < bound.eval z C ρ, ∀ ρ', (∀ v, v ≠ res → v ≠ fd → v ≠ j → ρ' v = ρ v) →
      P.eval z C (Function.update ρ' j i) = p i)
    (hm : m < bound.eval z C ρ) (hpm : p m = 0) (hlt : ∀ i < m, p i ≠ 0) :
    ((findP res fd j bound P).run z C ρ).1 res = m ∧
      ((findP res fd j bound P).run z C ρ).2 = [] ∧
      ∀ v, v ≠ res → v ≠ fd → v ≠ j → ((findP res fd j bound P).run z C ρ).1 v = ρ v := by
  unfold findP
  simp only [run_seq, run_set, eval_c, min_eq_left (show 0 ≤ C by omega), List.nil_append]
  set ρ0 := Function.update ρ fd 0
  have hfr0 : ∀ v, v ≠ res → v ≠ fd → v ≠ j → ρ0 v = ρ v := fun v _ h2 _ => by
    simp [ρ0, Function.update_of_ne h2]
  have h := run_loop_spec (w := z) (C := C) j bound
    (.ite (.bin .eq (.bin .add (.v fd) P) (.c 0)) (.seq (.set fd (.c 1)) (.set res (.v j))) .skip) ρ0
    (fun i ρ' => (i ≤ m → ρ' fd = 0) ∧ (m < i → ρ' fd = 1 ∧ ρ' res = m) ∧
      ∀ v, v ≠ res → v ≠ fd → v ≠ j → ρ' v = ρ v) (fun _ => [])
    ⟨fun _ => by simp [ρ0], fun h => absurd h (by omega), hfr0⟩ (by
      intro i hi ρ' ⟨h1, h2, h3⟩
      have hPi := hP i (by rw [← hB ρ0 hfr0]; exact hi) ρ' h3
      have hfd : Function.update ρ' j i fd = ρ' fd := Function.update_of_ne hfj _ _
      rw [run_ite]
      simp only [eval_bin, eval_v, eval_c, ap_eq, ap_add, hPi, hfd, min_eq_left (show 0 ≤ C by omega)]
      have hmin : ∀ a, min a C = 0 ↔ a = 0 := fun a => by
        constructor
        · intro h; rcases le_total a C with h' | h'
          · rwa [min_eq_left h'] at h
          · rw [min_eq_right h'] at h; omega
        · intro h; rw [h]; simp
      have hval : min (ρ' fd + p i) C = 0 ↔ i = m := by
        rw [hmin]
        rcases Nat.lt_trichotomy i m with him | rfl | him
        · rw [h1 (by omega)]; have := hlt i him; omega
        · rw [h1 le_rfl, hpm]; simp
        · rw [(h2 him).1]; omega
      by_cases him : i = m
      · subst him
        rw [if_pos (by simp [hval])]
        simp only [run_seq, run_set, eval_c, eval_v, and_true, List.nil_append]
        refine ⟨fun h => absurd h (by omega), fun _ => ⟨?_, ?_⟩, fun v hv1 hv2 hv3 => ?_⟩
        · rw [Function.update_of_ne (Ne.symm hrf), Function.update_self, min_eq_left hC]
        · rw [Function.update_self, Function.update_of_ne (Ne.symm hfj), Function.update_self]
        · rw [Function.update_of_ne hv1, Function.update_of_ne hv2, Function.update_of_ne hv3]
          exact h3 v hv1 hv2 hv3
      · rw [if_neg (by simp [hval, him])]
        simp only [run_skip, and_true]
        refine ⟨fun h => ?_, fun h => ?_, fun v hv1 hv2 hv3 => ?_⟩
        · rw [Function.update_of_ne hfj]; exact h1 (by omega)
        · rw [Function.update_of_ne hfj, Function.update_of_ne hrj]; exact h2 (by omega)
        · rw [Function.update_of_ne hv3]; exact h3 v hv1 hv2 hv3)
  rw [hB ρ0 hfr0] at h
  obtain ⟨⟨-, h2, h3⟩, h4⟩ := h
  refine ⟨(h2 hm).2, by rw [h4]; simp, h3⟩

/-! ## Binary logarithm -/

/-- `lg := ⌊log₂ nv⌋` (temporaries `p2`, `j`). -/
def logP (lg p2 j nv : Fin W) : Pr W :=
  .seq (.set lg (.c 0)) (.seq (.set p2 (.c 1)) (.loop j (.v nv)
    (.ite (.bin .lt (.v nv) (.bin .add (.v p2) (.v p2))) .skip
      (.seq (.set p2 (.bin .add (.v p2) (.v p2))) (.set lg (.bin .add (.v lg) (.c 1)))))))

lemma logP_wr (lg p2 j nv : Fin W) : (logP lg p2 j nv).wr = [lg, p2, j, p2, lg] := rfl

lemma run_logP (lg p2 j nv : Fin W) (h1 : lg ≠ p2) (h2 : lg ≠ j) (h3 : lg ≠ nv) (h4 : p2 ≠ j)
    (h5 : p2 ≠ nv) (h6 : j ≠ nv) (ρ : Fin W → ℕ) (hC : 2 * ρ nv + 2 ≤ C) :
    ((logP lg p2 j nv).run z C ρ).1 lg = Nat.log 2 (ρ nv) ∧
      ((logP lg p2 j nv).run z C ρ).2 = [] := by
  unfold logP
  simp only [run_seq, run_set, eval_c, min_eq_left (show 0 ≤ C by omega),
    min_eq_left (show 1 ≤ C by omega), List.nil_append]
  set n := ρ nv
  set ρ0 := Function.update (Function.update ρ lg 0) p2 1
  have hn0 : ρ0 nv = n := by simp [ρ0, Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h5), n]
  have h := run_loop_spec (w := z) (C := C) j (.v nv)
    (.ite (.bin .lt (.v nv) (.bin .add (.v p2) (.v p2))) .skip
      (.seq (.set p2 (.bin .add (.v p2) (.v p2))) (.set lg (.bin .add (.v lg) (.c 1))))) ρ0
    (fun i ρ' => ρ' nv = n ∧ ρ' p2 = 2 ^ ρ' lg ∧ 2 ^ ρ' lg ≤ max n 1 ∧
      (ρ' lg = i ∨ n < 2 ^ (ρ' lg + 1))) (fun _ => [])
    ⟨hn0, by simp [ρ0, Function.update_of_ne h1], by simp [ρ0, Function.update_of_ne h1],
      Or.inl (by simp [ρ0, Function.update_of_ne h1])⟩ (by
      intro i hi ρ' ⟨k1, k2, k3, k4⟩
      simp only [eval_v, hn0] at hi
      set τ := Function.update ρ' j i
      have t1 : τ nv = n := by simp [τ, Function.update_of_ne (Ne.symm h6), k1]
      have t2 : τ p2 = ρ' p2 := by simp [τ, Function.update_of_ne h4]
      have t3 : τ lg = ρ' lg := by simp [τ, Function.update_of_ne h2]
      have hle : 2 ^ ρ' lg ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · omega
        · rwa [max_eq_left (show 1 ≤ n by omega)] at k3
      rw [run_ite]
      simp only [eval_bin, eval_v, ap_lt, ap_add, t1, t2, k2, min_eq_left (show 2 ^ ρ' lg + 2 ^ ρ' lg ≤ C by omega)]
      by_cases hc : n < 2 ^ ρ' lg + 2 ^ ρ' lg
      · rw [if_pos hc]
        simp only [ne_eq, one_ne_zero, not_false_eq_true, if_true, run_skip, and_true]
        refine ⟨t1, by rw [t2, t3, k2], by rw [t3]; exact k3, Or.inr ?_⟩
        rw [t3, pow_succ]; omega
      · rw [if_neg hc]
        simp only [ne_eq, not_true_eq_false, if_false, run_seq, run_set, eval_bin, eval_v, eval_c,
          ap_add, t2, k2, min_eq_left (show 2 ^ ρ' lg + 2 ^ ρ' lg ≤ C by omega), and_true,
          List.nil_append]
        have u1 : Function.update τ p2 (2 ^ ρ' lg + 2 ^ ρ' lg) lg = ρ' lg := by
          rw [Function.update_of_ne h1, t3]
        simp only [u1, min_eq_left (show 1 ≤ C by omega)]
        have hl1 : ρ' lg + 1 ≤ C := by
          have := Nat.lt_two_pow_self (n := ρ' lg); omega
        rw [min_eq_left hl1]
        refine ⟨by simp [Function.update_of_ne (Ne.symm h3), Function.update_of_ne (Ne.symm h5), t1],
          by simp [Function.update_of_ne (Ne.symm h1), pow_succ]; ring, ?_, ?_⟩
        · simp only [Function.update_self, pow_succ]; push_neg at hc
          rcases Nat.eq_zero_or_pos n with h0 | h0
          · omega
          · rw [max_eq_left (show 1 ≤ n by omega)]; omega
        · simp only [Function.update_self]
          rcases k4 with k4 | k4
          · left; omega
          · push_neg at hc; rw [pow_succ] at k4; omega)
  simp only [eval_v, hn0] at h
  obtain ⟨⟨-, -, k3, k4⟩, k5⟩ := h
  refine ⟨?_, by rw [k5]; simp⟩
  set l := ((Pr.loop j (Ex.v nv) _).run z C ρ0).1 lg
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · rw [h0] at k3 ⊢
    simp at k3
    rw [Nat.log_zero_right]
    rcases Nat.eq_zero_or_pos l with hl | hl
    · exact hl
    · have := Nat.one_lt_two_pow (n := l) (by omega); omega
  · rw [max_eq_left (show 1 ≤ n by omega)] at k3
    rcases k4 with k4 | k4
    · have := Nat.lt_two_pow_self (n := l); omega
    · exact (Nat.log_eq_of_pow_le_of_lt_pow k3 k4).symm

end LL

end PathChecking
