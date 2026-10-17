module

public import RequestProject.ACRound.Gen.Main

/-!
# Uniformity of the round circuit family

The round circuit `(G.lay CB n).circ` is produced from `1ⁿ` by first computing the generator
input `GenI.zIn fB G.A (1ⁿ)` (which contains the encodings of the oracle circuits `CB ℓ`) and
then running the generator program `GenP.mainP G` on it.
-/

@[expose] public section

namespace PathChecking

namespace GCst

open LL GenP GenI

lemma cap_bound (K x n : ℕ) (hn : n + 1 ≤ x) : K * (n + 1) ^ K ≤ (x + 2) ^ (2 * K + 6) := by
  have h1 : K ≤ (x + 2) ^ K := (Nat.lt_pow_self (by omega : 1 < x + 2)).le
  have h2 : (n + 1) ^ K ≤ (x + 2) ^ K := Nat.pow_le_pow_left (by omega) _
  calc K * (n + 1) ^ K ≤ (x + 2) ^ K * (x + 2) ^ K := Nat.mul_le_mul h1 h2
    _ = (x + 2) ^ (2 * K) := by ring
    _ ≤ (x + 2) ^ (2 * K + 6) := Nat.pow_le_pow_right (by omega) (by omega)

lemma cap_bound_len (K x : ℕ) : 4 * x + 40 ≤ (x + 2) ^ (2 * K + 6) + 3 := by
  have h : (x + 2) ^ 6 ≤ (x + 2) ^ (2 * K + 6) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (x + 2) * 32 ≤ (x + 2) ^ 6 := by
    rw [show (x + 2) ^ 6 = (x + 2) * (x + 2) ^ 5 by ring]
    exact Nat.mul_le_mul_left _ (by
      have := Nat.pow_le_pow_left (show 2 ≤ x + 2 by omega) 5; simpa using this)
  omega

/-- **The round circuit family is logspace uniform.** -/
theorem lay_uniform (G : GCst) {CB : ℕ → Circuit} {fB : Word → Word}
    (hfB : LogspaceComputable fB) (hf : ∀ ℓ, fB (List.replicate ℓ true) = (CB ℓ).encode)
    (hsz : ∀ ℓ, (CB ℓ).length ≤ G.cB * (ℓ + 1) ^ G.cB) (hwf : ∀ ℓ, (CB ℓ).WellFormed ℓ) :
    LogspaceUniform (fun n => (G.lay CB n).circ) := by
  obtain ⟨K, hK⟩ := G.Mb_poly
  refine ⟨(mainP G).output (2 * K + 6) ∘ zIn fB G.A,
    (zIn_logspace hfB G.A).comp (logspaceComputable_of_output _ _ _ (fun _ => rfl)), fun n => ?_⟩
  set z := zIn fB G.A (List.replicate n true) with hz
  have hsep := zIn_sep G.A hf n
  have hzn : n < z.length := (List.getElem?_eq_some_iff.1 hsep).1
  simp only [Function.comp_apply, Pr.output]
  refine run_mainP G CB n _ (zIn_unary G.A hf n) hsep (fun ℓ hℓ => ?_) (fun ℓ _ => hwf ℓ)
    (fun ℓ hℓ => ?_) ?_ ?_
  · have hℓ' : ℓ ≤ G.A * (n + 1) ^ G.A := hℓ
    have hlen := segW_length CB ℓ
    refine ⟨fun j hj => ?_, fun j hj => ?_, ?_⟩
    · rw [zIn_seg G.A hf n ℓ (2 * j) hℓ' (by omega), segW_even CB ℓ j hj]
    · rw [show n + 1 + offW CB ℓ + 2 * j + 1 = n + 1 + offW CB ℓ + (2 * j + 1) by ring,
        zIn_seg G.A hf n ℓ (2 * j + 1) hℓ' (by omega), segW_odd CB ℓ j hj]
    · rw [zIn_seg G.A hf n ℓ _ hℓ' (by omega), segW_end]
  · refine ⟨(hwf ℓ).1, ?_⟩
    show (CB ℓ).length + 1 ≤ G.cB * (G.L n + 1) ^ G.cB + 1
    have := hsz ℓ
    have : (ℓ + 1) ^ G.cB ≤ (G.L n + 1) ^ G.cB :=
      Nat.pow_le_pow_left (by simpa [GCst.lay] using hℓ) _
    have : G.cB * (ℓ + 1) ^ G.cB ≤ G.cB * (G.L n + 1) ^ G.cB := Nat.mul_le_mul_left _ this
    omega
  · unfold capOf
    rw [← hz]
    have := cap_bound K z.length n (by omega)
    have := hK n
    omega
  · unfold capOf
    exact cap_bound_len K z.length

end GCst

end PathChecking
