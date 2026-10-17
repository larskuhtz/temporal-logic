module

public import RequestProject.ACRound.Build

/-!
# Case analysis on the gates of the round circuit
-/

@[expose] public section

namespace PathChecking

namespace Lay

variable {P : Lay}

lemma getElem_of_getElem?_eq {α : Type*} {l : List α} {i : ℕ} {g : α} (hi : i < l.length)
    (h : l[i]? = some g) : l[i] = g := by
  rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h

lemma W_pos : 0 < P.W := by unfold W; omega

lemma bb_eq (r q ℓ : ℕ) : P.bb r q ℓ = P.gb r q + (2 * (P.L + 1) + ℓ * P.S) := by
  unfold bb; omega

/-- **Case analysis on the gates of the round circuit.** -/
theorem circ_cases (h : P.SizeOk) (Pr : ℕ → Gate → Prop)
    (hpre : ∀ i < P.P0, ∀ g, P.prefixGates[i]? = some g → Pr i g)
    (hbit : ∀ r < P.R, ∀ q < P.Nq, ∀ i ≤ P.L, Pr (P.gb r q + i) (P.bitGate r q i))
    (hlen : ∀ r < P.R, ∀ q < P.Nq, ∀ i ≤ P.L, Pr (P.gb r q + (P.L + 1) + i) (P.lenGate r q i))
    (hcopy : ∀ r < P.R, ∀ q < P.Nq, ∀ ℓ ≤ P.L, ∀ (v : ℕ) (hv : v < (P.CB ℓ).length),
      Pr (P.bb r q ℓ + v) (copyGate (P.bb r q ℓ) (P.gb r q) (P.CB ℓ)[v]))
    (hpad : ∀ r < P.R, ∀ q < P.Nq, ∀ ℓ ≤ P.L, ∀ v, (P.CB ℓ).length ≤ v → v + 1 < P.S →
      Pr (P.bb r q ℓ + v) ⟨.const false, []⟩)
    (hsel : ∀ r < P.R, ∀ q < P.Nq, ∀ ℓ ≤ P.L, Pr (P.bb r q ℓ + (P.S - 1))
      ⟨.and, [P.gb r q + (P.L + 1) + ℓ, P.bb r q ℓ + (P.CB ℓ).length - 1]⟩)
    (hans : ∀ r < P.R, ∀ q < P.Nq, Pr (P.gb r q + (P.W - 1)) (P.ansGate r q))
    (hfin : ∀ t < 3, ∀ g, P.finalGates[t]? = some g → Pr (P.F0 + t) g) :
    ∀ i (hi : i < P.circ.length), Pr i P.circ[i] := by
  intro i hi
  have hlen' := circ_length h
  by_cases h1 : i < P.P0
  · exact hpre i h1 _ (by rw [← circ_get_prefix i h1, List.getElem?_eq_getElem hi])
  by_cases h2 : P.F0 ≤ i
  · obtain ⟨t, rfl⟩ : ∃ t, i = P.F0 + t := ⟨i - P.F0, by omega⟩
    exact hfin t (by omega) _ (by rw [← circ_get_final h t (by omega), List.getElem?_eq_getElem hi])
  have hW := W_pos (P := P)
  set k := (i - P.P0) / P.W with hk
  set t := (i - P.P0) % P.W with ht
  have hkt : i - P.P0 = k * P.W + t := by rw [hk, ht, mul_comm]; exact (Nat.div_add_mod _ _).symm
  have htW : t < P.W := Nat.mod_lt _ hW
  clear_value k t
  have hkR : k < P.R * P.Nq := by
    by_contra hc
    have : P.R * P.Nq * P.W ≤ k * P.W := Nat.mul_le_mul_right _ (by omega)
    unfold F0 at h2; omega
  have hNq : 0 < P.Nq := by
    rcases Nat.eq_zero_or_pos P.Nq with h0 | h0
    · rw [h0] at hkR; simp at hkR
    · exact h0
  set r := k / P.Nq with hr
  set q := k % P.Nq with hq
  have hrq : k = r * P.Nq + q := by rw [hr, hq, mul_comm]; exact (Nat.div_add_mod _ _).symm
  have hrR : r < P.R := by
    rw [hr]; exact (Nat.div_lt_iff_lt_mul hNq).2 hkR
  have hqN : q < P.Nq := Nat.mod_lt _ hNq
  clear_value r q
  have hi_eq : i = P.gb r q + t := by unfold gb; rw [← hrq]; omega
  have hget := circ_get_group h r q t hrR hqN htW
  rw [← hi_eq] at hget
  have key : ∀ g, (P.groupGates r q)[t]? = some g → Pr i g → Pr i P.circ[i] := by
    intro g hg hp
    rw [getElem_of_getElem?_eq hi (hget.trans hg)]; exact hp
  by_cases t1 : t < P.L + 1
  · exact key _ (groupGates_get_bit r q t (by omega)) (hi_eq ▸ hbit r hrR q hqN t (by omega))
  by_cases t2 : t < 2 * (P.L + 1)
  · obtain ⟨j, rfl⟩ : ∃ j, t = P.L + 1 + j := ⟨t - (P.L + 1), by omega⟩
    refine key _ (groupGates_get_len r q j (by omega)) ?_
    rw [hi_eq, ← Nat.add_assoc]; exact hlen r hrR q hqN j (by omega)
  have hWdef : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
  by_cases t3 : t < P.W - 1
  · obtain ⟨t', rfl⟩ : ∃ t', t = 2 * (P.L + 1) + t' := ⟨t - 2 * (P.L + 1), by omega⟩
    have hS : 0 < P.S := by
      rcases Nat.eq_zero_or_pos P.S with h0 | h0
      · rw [h0] at hWdef; omega
      · exact h0
    set ℓ := t' / P.S with hℓ
    set v := t' % P.S with hv
    have hℓv : t' = ℓ * P.S + v := by rw [hℓ, hv, mul_comm]; exact (Nat.div_add_mod _ _).symm
    have hvS : v < P.S := Nat.mod_lt _ hS
    have hℓL : ℓ ≤ P.L := by
      by_contra hc
      have : (P.L + 1) * P.S ≤ ℓ * P.S := Nat.mul_le_mul_right _ (by omega)
      omega
    have hgb := groupGates_get_block h r q ℓ v hℓL hvS
    rw [Nat.add_assoc, ← hℓv] at hgb
    have hib : i = P.bb r q ℓ + v := by rw [hi_eq, bb_eq]; omega
    by_cases v1 : v < (P.CB ℓ).length
    · refine key _ (hgb.trans (blockGates_get_copy r q ℓ v v1)) ?_
      rw [hib]; exact hcopy r hrR q hqN ℓ hℓL v v1
    by_cases v2 : v + 1 < P.S
    · refine key _ (hgb.trans (blockGates_get_pad r q ℓ v (by omega) v2)) ?_
      rw [hib]; exact hpad r hrR q hqN ℓ hℓL v (by omega) v2
    · have hv' : v = P.S - 1 := by omega
      rw [hv'] at hgb hib
      refine key _ (hgb.trans (blockGates_get_sel h r q ℓ hℓL)) ?_
      rw [hib]; exact hsel r hrR q hqN ℓ hℓL
  · obtain rfl : t = P.W - 1 := by omega
    refine key _ ((groupGates_get_ans h r q)) ?_
    rw [hi_eq]; exact hans r hrR q hqN

end Lay

end PathChecking
