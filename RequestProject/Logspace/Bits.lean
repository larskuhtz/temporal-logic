module

public import Mathlib

/-!
# Bit-level facts about increment and decrement

Binary increment flips the trailing ones and the lowest zero; binary decrement flips the
trailing zeros and the lowest one.
-/

@[expose] public section

namespace PathChecking

namespace LS

lemma testBit_succ_of_trailing (v j : ℕ) (h1 : ∀ i < j, v.testBit i = true)
    (h0 : v.testBit j = false) (i : ℕ) :
    (v + 1).testBit i = if i < j then false else if i = j then true else v.testBit i := by
  induction j generalizing v i with
  | zero =>
    have hv : v % 2 = 0 := by
      rw [Nat.testBit_zero] at h0; simpa using h0
    rcases i with _ | i
    · simp [Nat.testBit_zero]; omega
    · simp only [Nat.testBit_succ, Nat.not_lt_zero, if_false, Nat.add_one_ne_zero]
      congr 1; omega
  | succ j ih =>
    have hv : v % 2 = 1 := by
      have := h1 0 (by omega); rw [Nat.testBit_zero] at this; simpa using this
    have e : (v + 1) / 2 = v / 2 + 1 := by omega
    rcases i with _ | i
    · simp [Nat.testBit_zero]; omega
    · rw [Nat.testBit_succ, e, ih (v / 2) (fun i hi => by
          have := h1 (i + 1) (by omega); rwa [Nat.testBit_succ] at this)
          (by rwa [Nat.testBit_succ] at h0) i, Nat.testBit_succ]
      simp only [Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

lemma testBit_pred_of_trailing (v j : ℕ) (h1 : ∀ i < j, v.testBit i = false)
    (h0 : v.testBit j = true) (i : ℕ) :
    (v - 1).testBit i = if i < j then true else if i = j then false else v.testBit i := by
  induction j generalizing v i with
  | zero =>
    have hv : v % 2 = 1 := by
      rw [Nat.testBit_zero] at h0; simpa using h0
    rcases i with _ | i
    · simp [Nat.testBit_zero]; omega
    · simp only [Nat.testBit_succ, Nat.not_lt_zero, if_false, Nat.add_one_ne_zero]
      congr 1; omega
  | succ j ih =>
    have hv : v % 2 = 0 := by
      have := h1 0 (by omega); rw [Nat.testBit_zero] at this; simpa using this
    have hpos : v / 2 ≠ 0 := by
      intro h
      have : v = 0 := by omega
      subst this; simp at h0
    have e : (v - 1) / 2 = v / 2 - 1 := by omega
    rcases i with _ | i
    · simp [Nat.testBit_zero]; omega
    · rw [Nat.testBit_succ, e, ih (v / 2) (fun i hi => by
          have := h1 (i + 1) (by omega); rwa [Nat.testBit_succ] at this)
          (by rwa [Nat.testBit_succ] at h0) i, Nat.testBit_succ]
      simp only [Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

lemma two_pow_le_of_testBit {v j : ℕ} (h : v.testBit j = true) : 2 ^ j ≤ v :=
  Nat.ge_two_pow_of_testBit h

lemma testBit_eq_false_of_lt_two_pow {v A j : ℕ} (hv : v < 2 ^ A) (hj : A ≤ j) :
    v.testBit j = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hj))

end LS

end PathChecking
