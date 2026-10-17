module

public import Mathlib

/-!
# Polynomially bounded functions and logarithm estimates
-/

@[expose] public section

namespace PathChecking

/-- Polynomially bounded functions. -/
def PolyB (f : ℕ → ℕ) : Prop := ∃ K, ∀ n, f n ≤ K * (n + 1) ^ K

namespace PolyB

lemma mono {f g : ℕ → ℕ} (hg : PolyB g) (h : ∀ n, f n ≤ g n) : PolyB f := by
  obtain ⟨K, hK⟩ := hg
  exact ⟨K, fun n => (h n).trans (hK n)⟩

lemma const (a : ℕ) : PolyB (fun _ => a) :=
  ⟨a, fun n => by
    have : 1 ≤ (n + 1) ^ a := Nat.one_le_pow _ _ (by omega)
    nlinarith⟩

lemma id' : PolyB (fun n => n) :=
  ⟨1, fun n => by simp⟩

lemma add {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB (fun n => f n + g n) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨M, hM⟩ := hg
  refine ⟨K + M, fun n => ?_⟩
  have h1 : (n + 1) ^ K ≤ (n + 1) ^ (K + M) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (n + 1) ^ M ≤ (n + 1) ^ (K + M) := Nat.pow_le_pow_right (by omega) (by omega)
  have := hK n; have := hM n
  nlinarith

lemma mul {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB (fun n => f n * g n) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨M, hM⟩ := hg
  refine ⟨K * M + K + M, fun n => ?_⟩
  have h1 : K * M ≤ (K * M + K + M) := by omega
  have h2 : (n + 1) ^ (K + M) ≤ (n + 1) ^ (K * M + K + M) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  calc f n * g n ≤ (K * (n + 1) ^ K) * (M * (n + 1) ^ M) := Nat.mul_le_mul (hK n) (hM n)
    _ = (K * M) * (n + 1) ^ (K + M) := by ring
    _ ≤ (K * M + K + M) * (n + 1) ^ (K * M + K + M) := Nat.mul_le_mul h1 h2

lemma pow {f : ℕ → ℕ} (hf : PolyB f) (a : ℕ) : PolyB (fun n => f n ^ a) := by
  induction a with
  | zero => simpa using const 1
  | succ a ih => simpa [pow_succ] using ih.mul hf

end PolyB

lemma log_add_one_le (n : ℕ) : Nat.log 2 n + 1 ≤ n + 1 := by
  have := Nat.log_le_self 2 n; omega

lemma two_pow_log_le (m : ℕ) : 2 ^ (Nat.log 2 m + 1) ≤ 2 * (m + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    rw [pow_succ]; omega

lemma succ_le_two_pow_log (n : ℕ) : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) :=
  Nat.lt_pow_succ_log_self (by norm_num) n

lemma log_mul_pow_le (A n : ℕ) :
    Nat.log 2 (A * (n + 1) ^ A) + 1 ≤ (2 * A + 1) * (Nat.log 2 n + 1) := by
  rcases Nat.eq_zero_or_pos A with rfl | hA
  · simp
  have hpos : A * (n + 1) ^ A ≠ 0 := by positivity
  have hlt : A * (n + 1) ^ A < 2 ^ (A + A * (Nat.log 2 n + 1)) := by
    rw [pow_add, pow_mul]
    have h1 : A < 2 ^ A := Nat.lt_two_pow_self
    have h2 : (n + 1) ^ A ≤ (2 ^ (Nat.log 2 n + 1)) ^ A :=
      Nat.pow_le_pow_left (succ_le_two_pow_log n) A
    have h3 : 0 < (n + 1) ^ A := by positivity
    calc A * (n + 1) ^ A < 2 ^ A * (n + 1) ^ A := Nat.mul_lt_mul_of_pos_right h1 h3
      _ ≤ 2 ^ A * (2 ^ (Nat.log 2 n + 1)) ^ A := Nat.mul_le_mul_left _ h2
      _ = 2 ^ A * (2 ^ A) ^ (Nat.log 2 n + 1) := by
        rw [← pow_mul, ← pow_mul, mul_comm (Nat.log 2 n + 1) A]
  have := Nat.log_lt_of_lt_pow hpos hlt
  nlinarith

end PathChecking
