module

public import RequestProject.ACRound.Eval

/-!
# Correctness of the round circuit
-/

@[expose] public section

namespace PathChecking

open Classical

namespace Lay

variable {P : Lay} {B Bc : Language} {Q D : Word → Word} {w : Word}

lemma val_final (t : ℕ) (ht : t < 3) :
    P.val B Bc Q D w (P.F0 + t) =
      if t = 0 then (D (pack w 0 (roundAns B Q P.Nq w P.R))).getD 0 false
      else if t = 1 then decide ((D (pack w 0 (roundAns B Q P.Nq w P.R))).length = 1)
      else decide (D (pack w 0 (roundAns B Q P.Nq w P.R)) = [true]) := by
  have h2 := P0_ge (P := P)
  have hF : P.P0 ≤ P.F0 := by unfold F0; omega
  unfold val
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rcases t with _ | _ | _ | t
  · simp
  · simp
  · simp
  · omega

lemma val_bit (r q i : ℕ) (hr : r < P.R) (hq : q < P.Nq) (hi : i ≤ P.L) :
    P.val B Bc Q D w (P.gb r q + i) = (Q (pack w q (roundAns B Q P.Nq w r))).getD i false := by
  rw [val_gb r q i hr hq (by unfold W; omega)]
  unfold grpVal; simp only; rw [if_pos (by omega)]

lemma val_len (r q i : ℕ) (hr : r < P.R) (hq : q < P.Nq) (hi : i ≤ P.L) :
    P.val B Bc Q D w (P.gb r q + (P.L + 1) + i) =
      decide ((Q (pack w q (roundAns B Q P.Nq w r))).length = i) := by
  rw [Nat.add_assoc, val_gb r q _ hr hq (by unfold W; omega)]
  unfold grpVal; simp only; rw [if_neg (by omega), if_pos (by omega)]
  congr 2; omega

/-- **The round circuit satisfies its gate equations.** -/
theorem circ_evalFn (h : P.SizeOk) (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ)
    (hn : P.n = w.length)
    (hCB : ∀ u : Word, u.length ≤ P.L → ((P.CB u.length).eval Bc u = true ↔ u ∈ B))
    (hQ : ∀ r < P.R, ∀ q < P.Nq, (Q (pack w q (roundAns B Q P.Nq w r))).length ≤ P.L) :
    ∀ i (hi : i < P.circ.length),
      P.circ[i].evalFn (tagU Bc (tagU (LangF Q) (LangF D))) w (P.val B Bc Q D w) =
        P.val B Bc Q D w i := by
  refine circ_cases h (fun i g => g.evalFn (tagU Bc (tagU (LangF Q) (LangF D))) w
    (P.val B Bc Q D w) = P.val B Bc Q D w i) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i hi g hg
    simp only [prefixGates] at hg
    rcases i with _ | _ | i
    · simp at hg; subst hg; simp [Gate.evalFn, val]
    · simp at hg; subst hg; simp [Gate.evalFn, val]
    · simp only [List.cons_append, List.getElem?_cons_succ, List.nil_append, List.getElem?_map,
        List.getElem?_range (show i < P.n by simp [P0] at hi; omega), Option.map_some,
        Option.some.injEq] at hg
      subst hg
      simp only [Gate.evalFn, val]
      rw [if_neg (by omega), if_neg (by omega), if_pos hi]
      rfl
  · intro r hr q hq i hi
    simp only [bitGate, Gate.evalFn]
    simp only [map_val_qArgs hn false false i r q (by omega) (by omega), oracle_query,
      val_bit r q i hr hq hi]
    simp
  · intro r hr q hq i hi
    simp only [lenGate, Gate.evalFn]
    simp only [map_val_qArgs hn false true i r q (by omega) (by omega), oracle_query,
      val_len r q i hr hq hi]
    simp
  · intro r hr q hq ℓ hℓ v hv
    obtain ⟨hne, hs⟩ := h ℓ hℓ
    obtain ⟨hargs, hk⟩ := (hwf ℓ hℓ).2 v hv
    set x := Q (pack w q (roundAns B Q P.Nq w r))
    rw [val_block r q ℓ v hr hq hℓ (by omega)]
    simp only [if_pos hv]
    rw [Circuit.values_getD_evalFn Bc x _ v hv hargs]
    refine copyGate_evalFn _ (tagU (LangF Q) (LangF D)) rfl _ x _ _ _ ℓ v _ hargs ?_ ?_ ?_ ?_
    · intro k hk'
      revert hk; rw [hk']; exact fun h => h.1
    · simp [val]
    · intro k hkℓ
      exact val_bit r q k hr hq (by omega)
    · intro j hj
      rw [val_block r q ℓ j hr hq hℓ (by omega)]
      simp only [if_pos (show j < (P.CB ℓ).length by omega)]
      try rfl
  · intro r hr q hq ℓ hℓ v hv1 hv2
    rw [val_block r q ℓ v hr hq hℓ (by omega)]
    simp only [if_neg (show ¬ v < (P.CB ℓ).length by omega), if_pos hv2]
    rfl
  · intro r hr q hq ℓ hℓ
    obtain ⟨hne, hs⟩ := h ℓ hℓ
    have hpos := List.length_pos_of_ne_nil hne
    rw [val_block r q ℓ _ hr hq hℓ (by omega)]
    simp only [if_neg (show ¬ P.S - 1 < (P.CB ℓ).length by omega),
      if_neg (show ¬ P.S - 1 + 1 < P.S by omega)]
    simp only [Gate.evalFn, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true]
    rw [val_len r q ℓ hr hq hℓ, Nat.add_sub_assoc (by omega),
      val_block r q ℓ _ hr hq hℓ (by omega), if_pos (by omega),
      Circuit.eval_eq_getElem _ _ _ hne, List.getD_eq_getElem]
  · intro r hr q hq
    have hW := W_pos (P := P)
    set x := Q (pack w q (roundAns B Q P.Nq w r))
    rw [val_gb r q _ hr hq (by omega)]
    have hWd : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
    unfold grpVal
    simp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp only [ansGate, Gate.evalFn, List.map_map]
    have hxL : x.length ≤ P.L := hQ r hr q hq
    rw [Bool.eq_iff_iff, List.any_eq_true]
    simp only [List.mem_map, List.mem_range, Function.comp_apply, id, decide_eq_true_iff]
    constructor
    · rintro ⟨_, ⟨ℓ, hℓ, rfl⟩, hb⟩
      obtain ⟨hne, hs⟩ := h ℓ (by omega)
      rw [Nat.add_sub_assoc (by omega), val_block r q ℓ _ hr hq (by omega) (by omega)] at hb
      simp only [if_neg (show ¬ P.S - 1 < (P.CB ℓ).length by omega),
        if_neg (show ¬ P.S - 1 + 1 < P.S by omega), Bool.and_eq_true, decide_eq_true_iff] at hb
      obtain ⟨rfl, hb⟩ := hb
      exact (hCB x hxL).1 hb
    · intro hx
      refine ⟨_, ⟨x.length, by omega, rfl⟩, ?_⟩
      obtain ⟨hne, hs⟩ := h x.length hxL
      rw [Nat.add_sub_assoc (by omega), val_block r q _ _ hr hq hxL (by omega)]
      simp only [if_neg (show ¬ P.S - 1 < (P.CB x.length).length by omega),
        if_neg (show ¬ P.S - 1 + 1 < P.S by omega)]
      simp only [Bool.and_eq_true, decide_eq_true_iff]
      exact ⟨rfl, (hCB x hxL).2 hx⟩
  · intro t ht g hg
    rw [val_final t ht]
    rcases t with _ | _ | _ | t
    · simp [finalGates] at hg; subst hg
      simp only [Gate.evalFn]
      simp only [map_val_qArgs hn true false 0 P.R 0 le_rfl (by omega), oracle_query]
      simp
    · simp [finalGates] at hg; subst hg
      simp only [Gate.evalFn]
      simp only [map_val_qArgs hn true true 1 P.R 0 le_rfl (by omega), oracle_query]
      simp
    · simp [finalGates] at hg; subst hg
      simp only [Gate.evalFn, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
        Bool.and_true]
      rw [show P.F0 = P.F0 + 0 from rfl, val_final 0 (by omega), val_final 1 (by omega)]
      simpa using getD_eq_true_and_length
    · omega

/-- **Correctness of the round circuit.** -/
theorem circ_eval (h : P.SizeOk) (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ)
    (hn : P.n = w.length)
    (hCB : ∀ u : Word, u.length ≤ P.L → ((P.CB u.length).eval Bc u = true ↔ u ∈ B))
    (hQ : ∀ r < P.R, ∀ q < P.Nq, (Q (pack w q (roundAns B Q P.Nq w r))).length ≤ P.L) :
    P.circ.eval (tagU Bc (tagU (LangF Q) (LangF D))) w =
      decide (D (pack w 0 (roundAns B Q P.Nq w P.R)) = [true]) := by
  have hl := circ_length h
  have hne : P.circ ≠ [] := by intro he; rw [he] at hl; simp at hl
  rw [Circuit.eval_eq_getElem _ _ _ hne]
  have := Circuit.values_spec (tagU Bc (tagU (LangF Q) (LangF D))) w P.circ (P.val B Bc Q D w)
    (fun i hi => ((circ_wf h hwf).2 i hi).1) (circ_evalFn h hwf hn hCB hQ)
    (P.circ.length - 1) (by omega)
  rw [this, hl, show P.F0 + 3 - 1 = P.F0 + 2 by omega, val_final 2 (by omega)]
  simp

end Lay

end PathChecking
