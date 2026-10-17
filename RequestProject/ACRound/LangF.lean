module

public import RequestProject.ACRound.Build
public import RequestProject.ACRound.LLBasic

/-!
# The bit/length languages of logspace functions are in `L`

`LangF f` (for a logspace function `f`) is decided by a logspace function: the input
`x = b :: 1^i 0 u` is mapped to `x.flatMap dupB ++ [false, false] ++ f u`, which is then
checked by a program of the loop language.
-/

@[expose] public section

namespace PathChecking

open Classical

/-! ## Pure part -/

/-- The suffix `u` of `x = b :: 1^i 0 u` (empty if there is no `0` after the head). -/
def sfxF (x : Word) : Word :=
  if false ∈ x.tail then x.tail.drop (x.tail.idxOf false + 1) else []

lemma take_idxOf_false (t : List Bool) : t.take (t.idxOf false) = List.replicate (t.idxOf false) true := by
  induction t with
  | nil => simp
  | cons a t ih =>
    cases a
    · simp
    · simp [List.idxOf_cons_ne _ (show true ≠ false by decide), List.replicate_succ, ih]

lemma idxOf_replicate_append (i : ℕ) (u : Word) :
    (List.replicate i true ++ false :: u).idxOf false = i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.replicate_succ, List.cons_append, List.idxOf_cons_ne _ (by decide), ih]

lemma mem_LangF_iff (f : Word → Word) (x : Word) :
    x ∈ LangF f ↔ ∃ b t, x = b :: t ∧ false ∈ t ∧
      (if b then (f (sfxF x)).length = t.idxOf false
        else (f (sfxF x)).getD (t.idxOf false) false = true) := by
  constructor
  · rintro ⟨i, u, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · refine ⟨false, _, rfl, by simp, ?_⟩
      have hs : sfxF (false :: (List.replicate i true ++ false :: u)) = u := by
        simp [sfxF, idxOf_replicate_append, List.drop_append]
      simpa [hs, idxOf_replicate_append] using h
    · refine ⟨true, _, rfl, by simp, ?_⟩
      have hs : sfxF (true :: (List.replicate i true ++ false :: u)) = u := by
        simp [sfxF, idxOf_replicate_append, List.drop_append]
      simpa [hs, idxOf_replicate_append] using h
  · rintro ⟨b, t, rfl, ht, h⟩
    have hlt : t.idxOf false < t.length := List.idxOf_lt_length_iff.2 ht
    have hget : t[t.idxOf false] = false := List.getElem_idxOf hlt
    have ht' : t = List.replicate (t.idxOf false) true ++ false :: t.drop (t.idxOf false + 1) := by
      conv_lhs => rw [← List.take_append_drop (t.idxOf false) t]
      rw [take_idxOf_false, List.drop_eq_getElem_cons hlt, hget]
    have hs : sfxF (b :: t) = t.drop (t.idxOf false + 1) := by simp [sfxF, ht]
    rw [hs] at h
    rw [ht', mem_LangF]
    exact h

/-! ## The suffix program -/

namespace LL

/-- Read bit `e` (0-based) of the input. -/
def rd {V : ℕ} (e : Ex V) : Ex V := .inp (.bin .add e (.c 1))

/-- The suffix program.  Variables: `0` position, `1` "zero seen". -/
def sfxProg : Pr 2 :=
  .loop 0 .len (.ite (.bin .eq (.v 0) (.c 0)) .skip
    (.ite (.v 1) (.out (.bin .eq (rd (.v 0)) (.c 1)))
      (.ite (.bin .eq (rd (.v 0)) (.c 0)) (.set 1 (.c 1)) .skip)))

lemma eval_rd {V : ℕ} (z : Word) (C : ℕ) (ρ : Fin V → ℕ) (e : Ex V) (k : ℕ)
    (he : e.eval z C ρ = k) (hC : k + 1 ≤ C) : (rd e).eval z C ρ = bitCode z[k]? := by
  simp only [rd, eval_inp, eval_bin, ap_add, he, eval_c]
  rw [min_eq_left (show 1 ≤ C by omega), min_eq_left hC, symNum_inputSym_succ]

lemma take_succ_tail_mem (x : Word) (p : ℕ) (hp : 1 ≤ p) (hpx : p < x.length) :
    (false ∈ (x.take (p + 1)).tail ↔ false ∈ (x.take p).tail ∨ x[p] = false) := by
  rw [List.take_succ_eq_append_getElem hpx]
  rcases x with _ | ⟨a, x⟩
  · simp at hpx
  · obtain ⟨p, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [List.take_succ_cons, List.cons_append, List.tail_cons, List.mem_append,
      List.mem_singleton, List.getElem_cons_succ]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.symm

lemma sfx_pure (t : List Bool) :
    (List.range t.length).flatMap (fun q => if false ∈ t.take q then [t.getD q false] else []) =
      if false ∈ t then t.drop (t.idxOf false + 1) else [] := by
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t c ih =>
    have hmap : ∀ q ∈ List.range t.length,
        (if false ∈ (t ++ [c]).take q then [(t ++ [c]).getD q false] else []) =
        (if false ∈ t.take q then [t.getD q false] else []) := by
      intro q hq
      simp only [List.mem_range] at hq
      rw [List.take_append_of_le_length (by omega)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hq]
    rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
      List.flatMap_congr hmap, ih]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [show (t ++ [c]).take t.length = t by simp,
      show (t ++ [c]).getD t.length false = c by simp [List.getD_eq_getElem?_getD]]
    by_cases ht : false ∈ t
    · have hidx : (t ++ [c]).idxOf false = t.idxOf false := by
        rw [List.idxOf_append_of_mem ht]
      have hlt : t.idxOf false < t.length := List.idxOf_lt_length_iff.2 ht
      simp only [ht, if_true, List.mem_append, true_or, hidx]
      rw [List.drop_append_of_le_length (by omega)]
    · simp only [ht, if_false, List.nil_append, List.mem_append, false_or, List.mem_singleton]
      by_cases hc : false = c
      · subst hc
        simp [List.idxOf_append_of_notMem ht]
      · simp [hc]

lemma sfxProg_output (x : Word) : sfxProg.output 2 x = sfxF x := by
  have hC := len_lt_cap2 x
  unfold Pr.output sfxProg
  set C := capOf 2 x
  have h := run_loop_spec (V := 2) (w := x) (C := C) 0 .len
    (.ite (.bin .eq (.v 0) (.c 0)) .skip
      (.ite (.v 1) (.out (.bin .eq (rd (.v 0)) (.c 1)))
        (.ite (.bin .eq (rd (.v 0)) (.c 0)) (.set 1 (.c 1)) .skip)))
    (fun _ => 0) (fun p ρ => ρ 1 = if false ∈ (x.take p).tail then 1 else 0)
    (fun p => if 1 ≤ p ∧ false ∈ (x.take p).tail then [x.getD p false] else [])
    (by simp) (by
      intro p hp ρ' h1
      simp only [eval_len] at hp
      have hp' : p < x.length := by omega
      have e1 : (Function.update ρ' 0 p) 1 = ρ' 1 := by
        rw [Function.update_of_ne (by decide)]
      have hrd : (rd (.v 0) : Ex 2).eval x C (Function.update ρ' 0 p) = bitCode x[p]? :=
        eval_rd x C _ _ p (by simp) (by omega)
      rw [run_ite]
      simp only [eval_bin, ap_eq, eval_v, Function.update_self, eval_c]
      rw [min_eq_left (show 0 ≤ C by omega)]
      by_cases hp0 : p = 0
      · subst hp0
        simp only [ne_eq, one_ne_zero, not_false_eq_true, if_true, run_skip]
        refine ⟨?_, by simp⟩
        rw [e1, h1]
        rcases x with _ | ⟨a, x⟩ <;> simp
      · rw [if_neg (by simp [hp0])]
        rw [run_ite]
        simp only [eval_v, e1, h1]
        have hmem := take_succ_tail_mem x p (by omega) hp'
        by_cases hs : false ∈ (x.take p).tail
        · simp only [hs, if_true, ne_eq, one_ne_zero, not_false_eq_true, run_out, eval_bin, ap_eq,
            hrd, eval_c]
          rw [min_eq_left (show 1 ≤ C by omega)]
          refine ⟨?_, ?_⟩
          · rw [e1, h1, if_pos hs, if_pos (hmem.2 (Or.inl hs))]
          · rw [if_pos (show 1 ≤ p ∧ True from ⟨by omega, trivial⟩), List.getElem?_eq_getElem hp',
              List.getD_eq_getElem _ _ hp']
            rcases x[p] with _ | _ <;> simp [bitCode]
        · simp only [hs, if_false, ne_eq, not_true_eq_false]
          rw [run_ite]
          simp only [eval_bin, ap_eq, hrd, eval_c]
          rw [min_eq_left (show 0 ≤ C by omega)]
          rw [List.getElem?_eq_getElem hp']
          cases hx : x[p]
          · simp only [bitCode, if_true, ne_eq, one_ne_zero, not_false_eq_true, run_set]
            refine ⟨?_, ?_⟩
            · simp [hmem.2 (Or.inr hx), min_eq_left (show 1 ≤ C by omega)]
            · simp [hs]
          · simp only [bitCode, Nat.one_ne_zero, if_false, ne_eq, not_true_eq_false, run_skip]
            refine ⟨?_, ?_⟩
            · simp only [e1] at *
              rw [h1, if_neg hs, if_neg]
              rw [hmem]; simp [hs, hx]
            · simp [hs])
  rw [h.2]
  simp only [eval_len]
  rw [min_eq_left (by omega)]
  -- the pure part
  rcases x with _ | ⟨a, t⟩
  · simp [sfxF]
  · rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rw [if_neg (by omega), List.nil_append,
      List.flatMap_congr (g := fun q => if false ∈ t.take q then [t.getD q false] else [])
        (fun q _ => by simp)]
    unfold sfxF
    simp only [List.tail_cons]
    exact sfx_pure t

end LL

end PathChecking
