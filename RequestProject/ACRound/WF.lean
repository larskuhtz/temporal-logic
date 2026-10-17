module

public import RequestProject.ACRound.Cases

/-!
# Well-formedness of the round circuit
-/

@[expose] public section

namespace PathChecking

namespace Lay

variable {P : Lay}

/-- The condition of `Circuit.WellFormed` for a single gate at index `i`. -/
def GateOk (n i : ℕ) (g : Gate) : Prop :=
  (∀ j ∈ g.args, j < i) ∧
    match g.kind with
    | .input k => k < n ∧ g.args = []
    | .const _ => g.args = []
    | .not => g.args.length = 1
    | _ => True

lemma ans_lt (r q : ℕ) (hq : q < P.Nq) : P.ans r q < P.P0 + r * P.Nq * P.W := by
  rcases r with _ | r
  · simp [ans, P0]
  · simp only [ans, gb]
    have hW := W_pos (P := P)
    have : (r * P.Nq + q) * P.W + P.W ≤ (r + 1) * P.Nq * P.W := by
      have : (r * P.Nq + q + 1) * P.W ≤ ((r + 1) * P.Nq) * P.W :=
        Nat.mul_le_mul_right _ (by nlinarith)
      nlinarith
    omega

lemma qArgs_lt (t b : Bool) (i r q : ℕ) :
    ∀ j ∈ P.qArgs t b i r q, j < P.P0 + r * P.Nq * P.W := by
  intro j hj
  have h2 : 2 ≤ P.P0 := by simp [P0]
  simp only [qArgs, packArgs, List.mem_append, List.mem_cons, List.mem_replicate,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hj
  have hb : ∀ c, bitIdx c ≤ 1 := fun c => by cases c <;> simp [bitIdx]
  rcases hj with ((((h | h | h) | ⟨-, h⟩) | h | (((((⟨-, h⟩ | h) | ⟨k, hk, h⟩) | ⟨k, hk, h⟩) |
    ⟨-, h⟩) | ⟨-, h⟩)))
  all_goals first
    | (subst h; have := hb t; have := hb b; omega)
    | (have := hb t; have := hb b; omega)
    | (subst h; simp [P0] at hk ⊢; omega)
    | (subst h; exact ans_lt r k hk)

lemma gb_ge (r q : ℕ) : P.P0 + r * P.Nq * P.W ≤ P.gb r q := by
  unfold gb; nlinarith

lemma copyGate_ok (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ) (r q ℓ v : ℕ) (hℓ : ℓ ≤ P.L)
    (hv : v < (P.CB ℓ).length) :
    GateOk P.n (P.bb r q ℓ + v) (copyGate (P.bb r q ℓ) (P.gb r q) (P.CB ℓ)[v]) := by
  obtain ⟨hargs, hk⟩ := (hwf ℓ hℓ).2 v hv
  have hbb := bb_eq (P := P) r q ℓ
  unfold copyGate GateOk
  revert hk
  rcases hg : (P.CB ℓ)[v].kind with k | c | _ | _ | _ | _ <;> intro hk <;>
    simp only [hg] at hk ⊢
  · refine ⟨fun j hj => ?_, trivial⟩
    simp only [List.mem_singleton] at hj
    subst hj; omega
  · refine ⟨fun j hj => ?_, by simp [hk]⟩
    simp only [List.mem_map] at hj
    obtain ⟨j', hj', rfl⟩ := hj
    have := hargs j' hj'; omega
  · refine ⟨fun j hj => ?_, by simp [hk]⟩
    simp only [List.mem_map] at hj
    obtain ⟨j', hj', rfl⟩ := hj
    have := hargs j' hj'; omega
  all_goals
    refine ⟨fun j hj => ?_, trivial⟩
    simp only [List.mem_map, List.mem_cons] at hj
    first
      | (rcases hj with rfl | ⟨j', hj', rfl⟩
         · omega
         · have := hargs j' hj'; omega)
      | (obtain ⟨j', hj', rfl⟩ := hj; have := hargs j' hj'; omega)

/-- **Well-formedness of the round circuit.** -/
theorem circ_wf (h : P.SizeOk) (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ) :
    P.circ.WellFormed P.n := by
  refine ⟨?_, ?_⟩
  · intro he
    have := circ_length h
    rw [he] at this; simp at this
  · intro i hi
    show GateOk P.n i P.circ[i]
    have hW := W_pos (P := P)
    refine circ_cases h (fun i g => GateOk P.n i g) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hi
    · intro i hi g hg
      simp only [prefixGates] at hg
      rcases i with _ | _ | i
      · simp at hg; subst hg; simp [GateOk]
      · simp at hg; subst hg; simp [GateOk]
      · simp only [List.cons_append, List.getElem?_cons_succ, List.nil_append, List.getElem?_map,
          List.getElem?_range (show i < P.n by simp [P0] at hi; omega), Option.map_some,
          Option.some.injEq] at hg
        subst hg; simp [GateOk]; simp [P0] at hi; omega
    · intro r hr q hq i hi
      refine ⟨fun j hj => ?_, trivial⟩
      have := qArgs_lt false false i r q j hj
      have := gb_ge (P := P) r q
      omega
    · intro r hr q hq i hi
      refine ⟨fun j hj => ?_, trivial⟩
      have := qArgs_lt false true i r q j hj
      have := gb_ge (P := P) r q
      omega
    · intro r hr q hq ℓ hℓ v hv
      exact copyGate_ok hwf r q ℓ v hℓ hv
    · intro r hr q hq ℓ hℓ v _ _
      simp [GateOk]
    · intro r hr q hq ℓ hℓ
      obtain ⟨hne, hs⟩ := h ℓ hℓ
      have := List.length_pos_of_ne_nil hne
      have hbb := bb_eq (P := P) r q ℓ
      refine ⟨fun j hj => ?_, trivial⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl <;> omega
    · intro r hr q hq
      refine ⟨fun j hj => ?_, trivial⟩
      simp only [ansGate, List.mem_map, List.mem_range] at hj
      obtain ⟨ℓ, hℓ, rfl⟩ := hj
      have hbb := bb_eq (P := P) r q ℓ
      have : ℓ * P.S + P.S ≤ (P.L + 1) * P.S := by nlinarith
      have hWd : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
      omega
    · intro t ht g hg
      have h2 : 2 ≤ P.P0 := by simp [P0]
      rcases t with _ | _ | _ | t
      · simp [finalGates] at hg; subst hg
        refine ⟨fun j hj => ?_, trivial⟩
        have := qArgs_lt true false 0 P.R 0 j hj
        simp only [F0]; omega
      · simp [finalGates] at hg; subst hg
        refine ⟨fun j hj => ?_, trivial⟩
        have := qArgs_lt true true 1 P.R 0 j hj
        simp only [F0]; omega
      · simp [finalGates] at hg; subst hg
        refine ⟨fun j hj => ?_, trivial⟩
        simp at hj; omega
      · omega

end Lay

end PathChecking
