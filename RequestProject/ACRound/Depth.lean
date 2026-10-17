module

public import RequestProject.ACRound.EvalMain

/-!
# Depth of the round circuit
-/

@[expose] public section

namespace PathChecking

lemma le_foldl_max_of_mem (l : List ℕ) (a x : ℕ) (hx : x ∈ l) : x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y l ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · have : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b := by
        intro l; induction l with
        | nil => intro b; simp
        | cons z l ih' => intro b; simp only [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih' _)
      exact le_trans (le_max_right _ _) (this l _)
    · exact ih _ hx

lemma Circuit.depths_le_depth (C : Circuit) (v : ℕ) (hv : v < C.length) :
    C.depths[v]'(by simp [Circuit.depths_length, hv]) ≤ C.depth :=
  le_foldl_max_of_mem _ _ _ (List.getElem_mem _)

lemma Circuit.depths_arg (C : Circuit) (v : ℕ) (hv : v < C.length)
    (hargs : ∀ j ∈ C[v].args, j < v)
    (hk1 : ∀ k, C[v].kind ≠ .input k) (hk2 : ∀ b, C[v].kind ≠ .const b) (j : ℕ)
    (hj : j ∈ C[v].args) :
    C.depths[j]'(by have := hargs j hj; simp [Circuit.depths_length]; omega) + 1 ≤
      C.depths[v]'(by simp [Circuit.depths_length, hv]) := by
  have hjv := hargs j hj
  rw [Circuit.depths_getElem C v hv]
  have key : C.depths[j]'(by simp [Circuit.depths_length]; omega) ≤
      (C[v].args.map fun j => (C.depths.take v).getD j 0).foldl max 0 := by
    apply le_foldl_max_of_mem
    simp only [List.mem_map]
    refine ⟨j, hj, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hjv,
      List.getElem?_eq_getElem (by simp [Circuit.depths_length]; omega)]
    rfl
  unfold gateDepth
  rcases hk : C[v].kind with k | b | _ | _ | _ | _
  · exact absurd hk (hk1 k)
  · exact absurd hk (hk2 b)
  all_goals simp only []; omega

namespace Lay

variable (P : Lay) (DB : ℕ)

/-- Depth potential of the gates of a group. -/
def grpDep (r t : ℕ) : ℕ :=
  if t < 2 * (P.L + 1) then r * (DB + 4) + 1
  else if t < P.W - 1 then
    if (t - 2 * (P.L + 1)) % P.S < (P.CB ((t - 2 * (P.L + 1)) / P.S)).length then
      r * (DB + 4) + 2 + (P.CB ((t - 2 * (P.L + 1)) / P.S)).depths.getD ((t - 2 * (P.L + 1)) % P.S) 0
    else if (t - 2 * (P.L + 1)) % P.S + 1 < P.S then r * (DB + 4) + 2
    else r * (DB + 4) + 3 + DB
  else r * (DB + 4) + 4 + DB

/-- Depth potential of all gates. -/
def dep (i : ℕ) : ℕ :=
  if i < P.P0 then 0
  else if i < P.F0 then P.grpDep DB ((i - P.P0) / P.W / P.Nq) ((i - P.P0) % P.W)
  else if i < P.F0 + 2 then P.R * (DB + 4) + 1
  else P.R * (DB + 4) + 2

variable {P DB}

lemma dep_gb (r q t : ℕ) (hr : r < P.R) (hq : q < P.Nq) (ht : t < P.W) :
    P.dep DB (P.gb r q + t) = P.grpDep DB r t := by
  have hge := gb_ge (P := P) r q
  have hlt : P.gb r q + t < P.F0 := by
    unfold gb F0
    have : (r * P.Nq + q + 1) * P.W ≤ P.R * P.Nq * P.W :=
      Nat.mul_le_mul_right _ (by nlinarith)
    nlinarith
  have hW := W_pos (P := P)
  have e1 : P.gb r q + t - P.P0 = (r * P.Nq + q) * P.W + t := by unfold gb; omega
  have e2 : ((r * P.Nq + q) * P.W + t) / P.W = r * P.Nq + q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt ht, Nat.zero_add]
  have e3 : ((r * P.Nq + q) * P.W + t) % P.W = t := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]
  have hN : 0 < P.Nq := by omega
  have e4 : (r * P.Nq + q) / P.Nq = r := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hq, Nat.zero_add]
  unfold dep
  rw [if_neg (by omega), if_pos hlt, e1, e2, e3, e4]

lemma dep_block (r q ℓ v : ℕ) (hr : r < P.R) (hq : q < P.Nq) (hℓ : ℓ ≤ P.L) (hv : v < P.S) :
    P.dep DB (P.bb r q ℓ + v) =
      if v < (P.CB ℓ).length then r * (DB + 4) + 2 + (P.CB ℓ).depths.getD v 0
      else if v + 1 < P.S then r * (DB + 4) + 2
      else r * (DB + 4) + 3 + DB := by
  have hlt : 2 * (P.L + 1) + ℓ * P.S + v < P.W := by
    have : ℓ * P.S + v < (P.L + 1) * P.S := by nlinarith
    unfold W; omega
  rw [bb_eq, Nat.add_assoc, dep_gb r q _ hr hq hlt]
  have hS : 0 < P.S := by omega
  have e1 : 2 * (P.L + 1) + ℓ * P.S + v - 2 * (P.L + 1) = ℓ * P.S + v := by omega
  have e2 : (ℓ * P.S + v) / P.S = ℓ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hv, Nat.zero_add]
  have e3 : (ℓ * P.S + v) % P.S = v := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
  have hlt' : 2 * (P.L + 1) + ℓ * P.S + v < P.W - 1 := by
    have : ℓ * P.S + v < (P.L + 1) * P.S := by nlinarith
    unfold W; omega
  unfold grpDep
  rw [if_neg (by omega), if_pos hlt', e1, e2, e3]

lemma dep_ans (r q : ℕ) (hr : r ≤ P.R) (hq : q < P.Nq) : P.dep DB (P.ans r q) = r * (DB + 4) := by
  rcases r with _ | r
  · simp [ans, dep, P0]
  · have hW := W_pos (P := P)
    simp only [ans]
    rw [Nat.add_sub_assoc (by omega), dep_gb r q _ (by omega) hq (by omega)]
    unfold grpDep
    have hWd : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
    rw [if_neg (by omega), if_neg (by omega)]
    ring

lemma dep_qArgs (t b : Bool) (i r q : ℕ) (hr : r ≤ P.R) :
    ∀ j ∈ P.qArgs t b i r q, P.dep DB j ≤ r * (DB + 4) := by
  intro j hj
  have h2 : 2 ≤ P.P0 := by simp [P0]
  have hb : ∀ c, bitIdx c ≤ 1 := fun c => by cases c <;> simp [bitIdx]
  have d0 : ∀ j, j < P.P0 → P.dep DB j = 0 := fun j hj => by simp [dep, hj]
  simp only [qArgs, packArgs, List.mem_append, List.mem_cons, List.mem_replicate,
    List.mem_map, List.mem_range, List.not_mem_nil, or_false] at hj
  rcases hj with ((((h | h | h) | ⟨-, h⟩) | h | (((((⟨-, h⟩ | h) | ⟨k, hk, h⟩) | ⟨k, hk, h⟩) |
    ⟨-, h⟩) | ⟨-, h⟩)))
  all_goals first
    | (subst h; rw [d0 _ (by have := hb t; have := hb b; omega)]; omega)
    | (subst h; rw [d0 _ (by simp [P0] at hk ⊢; omega)]; omega)
    | (subst h; rw [dep_ans r k hr hk])

/-- **Depth of the round circuit.** -/
theorem circ_depth (h : P.SizeOk) (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ)
    (hDB : ∀ ℓ ≤ P.L, (P.CB ℓ).depth ≤ DB) :
    P.circ.depth ≤ P.R * (DB + 4) + 2 := by
  have hargs := fun i hi => ((circ_wf h hwf).2 i hi).1
  have hspec := Circuit.depths_le_spec P.circ (P.dep DB) hargs ?_ ?_
  · refine Circuit.depth_le_of _ _ fun i hi => le_trans (hspec i hi) ?_
    refine circ_cases h (fun i _ => P.dep DB i ≤ P.R * (DB + 4) + 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ i hi
    · intro i hi _ _; simp [dep, hi]
    · intro r hr q hq i hi
      rw [dep_gb r q i hr hq (by unfold W; omega)]
      unfold grpDep; rw [if_pos (by omega)]
      have : (r + 1) * (DB + 4) ≤ P.R * (DB + 4) := Nat.mul_le_mul_right _ hr
      have : 1 ≤ (DB + 4) := by omega
      nlinarith
    · intro r hr q hq i hi
      rw [Nat.add_assoc, dep_gb r q _ hr hq (by unfold W; omega)]
      unfold grpDep; rw [if_pos (by omega)]
      have : (r + 1) * (DB + 4) ≤ P.R * (DB + 4) := Nat.mul_le_mul_right _ hr
      have : 1 ≤ (DB + 4) := by omega
      nlinarith
    · intro r hr q hq ℓ hℓ v hv
      obtain ⟨hne, hs⟩ := h ℓ hℓ
      rw [dep_block r q ℓ v hr hq hℓ (by omega), if_pos hv]
      have hd := Circuit.depths_le_depth _ v hv
      rw [List.getD_eq_getElem _ _ (by simp [Circuit.depths_length, hv])]
      have := hDB ℓ hℓ
      have : (r + 1) * (DB + 4) ≤ P.R * (DB + 4) := Nat.mul_le_mul_right _ hr
      nlinarith
    · intro r hr q hq ℓ hℓ v hv1 hv2
      rw [dep_block r q ℓ v hr hq hℓ (by omega), if_neg (by omega), if_pos hv2]
      have : (r + 1) * (DB + 4) ≤ P.R * (DB + 4) := Nat.mul_le_mul_right _ hr
      nlinarith
    · intro r hr q hq ℓ hℓ
      obtain ⟨hne, hs⟩ := h ℓ hℓ
      rw [dep_block r q ℓ _ hr hq hℓ (by omega), if_neg (by omega), if_neg (by omega)]
      have : (r + 1) * (DB + 4) ≤ P.R * (DB + 4) := Nat.mul_le_mul_right _ hr
      nlinarith
    · intro r hr q hq
      have hW := W_pos (P := P)
      rw [dep_gb r q _ hr hq (by omega)]
      have hWd : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
      unfold grpDep; rw [if_neg (by omega), if_neg (by omega)]
      have : (r + 1) * (DB + 4) ≤ P.R * (DB + 4) := Nat.mul_le_mul_right _ hr
      nlinarith
    · intro t ht _ _
      have h2 : 2 ≤ P.P0 := by simp [P0]
      have hF : P.P0 ≤ P.F0 := by unfold F0; omega
      unfold dep
      rw [if_neg (by omega), if_neg (by omega)]
      split_ifs <;> omega
  · -- every wire increases the potential
    refine circ_cases h (fun i g => ∀ j ∈ g.args, P.dep DB j + 1 ≤ P.dep DB i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi g hg
      simp only [prefixGates] at hg
      rcases i with _ | _ | i
      · simp at hg; subst hg; simp
      · simp at hg; subst hg; simp
      · simp only [List.cons_append, List.getElem?_cons_succ, List.nil_append, List.getElem?_map,
          List.getElem?_range (show i < P.n by simp [P0] at hi; omega), Option.map_some,
          Option.some.injEq] at hg
        subst hg; simp
    · intro r hr q hq i hi j hj
      have := dep_qArgs (DB := DB) false false i r q (by omega) j hj
      rw [dep_gb r q i hr hq (by unfold W; omega)]
      unfold grpDep; rw [if_pos (by omega)]; omega
    · intro r hr q hq i hi j hj
      have := dep_qArgs (DB := DB) false true i r q (by omega) j hj
      rw [Nat.add_assoc, dep_gb r q _ hr hq (by unfold W; omega)]
      unfold grpDep; rw [if_pos (by omega)]; omega
    · intro r hr q hq ℓ hℓ v hv j hj
      obtain ⟨hne, hs⟩ := h ℓ hℓ
      obtain ⟨hargsv, hk⟩ := (hwf ℓ hℓ).2 v hv
      rw [dep_block r q ℓ v hr hq hℓ (by omega), if_pos hv,
        List.getD_eq_getElem _ _ (by simp [Circuit.depths_length, hv])]
      have hbbj : ∀ j' ∈ (P.CB ℓ)[v].args, P.dep DB (P.bb r q ℓ + j') + 1 ≤
          r * (DB + 4) + 2 + (P.CB ℓ).depths[v]'(by simp [Circuit.depths_length, hv]) := by
        intro j' hj'
        have hj'v := hargsv j' hj'
        rw [dep_block r q ℓ j' hr hq hℓ (by omega), if_pos (by omega),
          List.getD_eq_getElem _ _ (by simp [Circuit.depths_length]; omega)]
        have := Circuit.depths_arg _ v hv hargsv (fun k hk' => by rw [hk'] at hk; simp_all)
          (fun b hb => by rw [hb] at hk; simp_all) j' hj'
        omega
      unfold copyGate at hj
      revert hj hk hbbj
      rcases hg : (P.CB ℓ)[v].kind with k | c | _ | _ | _ | _ <;> intro hj hk hbbj
      · simp only [List.mem_singleton] at hj
        subst hj
        rw [dep_gb r q k hr hq (by have := hk.1; unfold W; omega)]
        unfold grpDep; rw [if_pos (by have := hk.1; omega)]; omega
      · simp [hk] at hj
      · simp only [List.mem_map] at hj; obtain ⟨j', hj', rfl⟩ := hj; exact hbbj j' hj'
      · simp only [List.mem_map] at hj; obtain ⟨j', hj', rfl⟩ := hj; exact hbbj j' hj'
      · simp only [List.mem_map] at hj; obtain ⟨j', hj', rfl⟩ := hj; exact hbbj j' hj'
      · rcases List.mem_cons.1 hj with rfl | hj
        · rw [show P.dep DB 0 = 0 by simp [dep, P0]]; omega
        · simp only [List.mem_map] at hj; obtain ⟨j', hj', rfl⟩ := hj; exact hbbj j' hj'
    · intro r hr q hq ℓ hℓ v _ _ j hj
      simp at hj
    · intro r hr q hq ℓ hℓ j hj
      obtain ⟨hne, hs⟩ := h ℓ hℓ
      have hpos := List.length_pos_of_ne_nil hne
      rw [dep_block r q ℓ _ hr hq hℓ (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · rw [Nat.add_assoc, dep_gb r q _ hr hq (by unfold W; omega)]
        unfold grpDep; rw [if_pos (by omega)]; omega
      · rw [Nat.add_sub_assoc (by omega), dep_block r q ℓ _ hr hq hℓ (by omega),
          if_pos (by omega), List.getD_eq_getElem _ _ (by simp [Circuit.depths_length]; omega)]
        have := Circuit.depths_le_depth (P.CB ℓ) ((P.CB ℓ).length - 1) (by omega)
        have := hDB ℓ hℓ
        omega
    · intro r hr q hq j hj
      have hW := W_pos (P := P)
      simp only [ansGate, List.mem_map, List.mem_range] at hj
      obtain ⟨ℓ, hℓ, rfl⟩ := hj
      obtain ⟨hne, hs⟩ := h ℓ (by omega)
      rw [dep_gb r q _ hr hq (by omega), Nat.add_sub_assoc (by omega),
        dep_block r q ℓ _ hr hq (by omega) (by omega), if_neg (by omega), if_neg (by omega)]
      have hWd : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
      unfold grpDep; rw [if_neg (by omega), if_neg (by omega)]; omega
    · intro t ht g hg j hj
      have h2 : 2 ≤ P.P0 := by simp [P0]
      have hF : P.P0 ≤ P.F0 := by unfold F0; omega
      rcases t with _ | _ | _ | t
      · simp [finalGates] at hg; subst hg
        have := dep_qArgs (DB := DB) true false 0 P.R 0 le_rfl j hj
        rw [show P.dep DB (P.F0 + 0) = P.R * (DB + 4) + 1 by unfold dep; split_ifs <;> omega]
        omega
      · simp [finalGates] at hg; subst hg
        have := dep_qArgs (DB := DB) true true 1 P.R 0 le_rfl j hj
        rw [show P.dep DB (P.F0 + (0 + 1)) = P.R * (DB + 4) + 1 by unfold dep; split_ifs <;> omega]
        omega
      · simp [finalGates] at hg; subst hg
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        simp only [dep]
        rcases hj with rfl | rfl <;> split_ifs <;> omega
      · omega
  · -- non-input, non-constant gates have positive potential
    refine circ_cases h (fun i g => (∀ k, g.kind ≠ .input k) → (∀ b, g.kind ≠ .const b) →
      1 ≤ P.dep DB i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro i hi g hg h1 h2
      simp only [prefixGates] at hg
      rcases i with _ | _ | i
      · simp at hg; subst hg; exact absurd rfl (h2 false)
      · simp at hg; subst hg; exact absurd rfl (h2 true)
      · simp only [List.cons_append, List.getElem?_cons_succ, List.nil_append, List.getElem?_map,
          List.getElem?_range (show i < P.n by simp [P0] at hi; omega), Option.map_some,
          Option.some.injEq] at hg
        subst hg; exact absurd rfl (h1 i)
    · intro r hr q hq i hi _ _
      rw [dep_gb r q i hr hq (by unfold W; omega)]
      unfold grpDep; rw [if_pos (by omega)]; omega
    · intro r hr q hq i hi _ _
      rw [Nat.add_assoc, dep_gb r q _ hr hq (by unfold W; omega)]
      unfold grpDep; rw [if_pos (by omega)]; omega
    · intro r hr q hq ℓ hℓ v hv _ _
      obtain ⟨hne, hs⟩ := h ℓ hℓ
      rw [dep_block r q ℓ v hr hq hℓ (by omega), if_pos hv]; omega
    · intro r hr q hq ℓ hℓ v _ _ _ h2
      exact absurd rfl (h2 false)
    · intro r hr q hq ℓ hℓ _ _
      obtain ⟨hne, hs⟩ := h ℓ hℓ
      rw [dep_block r q ℓ _ hr hq hℓ (by omega), if_neg (by omega), if_neg (by omega)]; omega
    · intro r hr q hq _ _
      have hW := W_pos (P := P)
      rw [dep_gb r q _ hr hq (by omega)]
      unfold grpDep; split_ifs <;> omega
    · intro t ht g hg _ _
      have h2 : 2 ≤ P.P0 := by simp [P0]
      have hF : P.P0 ≤ P.F0 := by unfold F0; omega
      unfold dep
      rw [if_neg (by omega), if_neg (by omega)]
      split_ifs <;> omega

end Lay

end PathChecking
