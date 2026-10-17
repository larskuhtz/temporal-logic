module

public import RequestProject.ACRound.LLBasic
public import RequestProject.ACRound.DPDA

/-!
# `LogDCFL` is closed under tagged unions

The reduction maps `b :: y` to `b :: f_b y`, where `f_false`, `f_true` are the reductions of
the two languages.  It is the composition of the logspace function
`x ↦ [x ≠ [], head x] ++ dup (f₁ (tail x)) ++ [false, false] ++ dup (f₂ (tail x))`
(`dup` writes every bit `c` as `[true, c]`) with a selection program in the loop language.
-/

@[expose] public section

namespace PathChecking

/-- The tagged map: `b :: y ↦ b :: f_b y`. -/
def tagMapF (f₁ f₂ : Word → Word) : Word → Word
  | [] => []
  | b :: y => b :: (if b then f₂ y else f₁ y)

namespace LL

lemma dup_get_even (l : List Bool) (i : ℕ) :
    (l.flatMap dupB)[2 * i]? = if i < l.length then some true else none := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    rcases i with _ | i
    · simp [dupB]
    · rw [List.flatMap_cons, show 2 * (i + 1) = 2 * i + 2 by ring,
        List.getElem?_append_right (by simp [dupB])]
      simp [dupB, ih]

lemma dup_get_odd (l : List Bool) (i : ℕ) : (l.flatMap dupB)[2 * i + 1]? = l[i]? := by
  induction l generalizing i with
  | nil => simp
  | cons a l ih =>
    rcases i with _ | i
    · simp [dupB]
    · rw [List.flatMap_cons, show 2 * (i + 1) + 1 = (2 * i + 1) + 2 by ring,
        List.getElem?_append_right (by simp [dupB])]
      simp [dupB, ih]

lemma dup_length (l : List Bool) : (l.flatMap dupB).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [dupB, ih]; ring

/-- The position `2 i + 3` of the marker of pair `i`. -/
def selP : Ex 3 := .bin .add (.bin .add (.v 0) (.v 0)) (.c 3)

/-- The body of the selection loop. -/
def selBody : Pr 3 :=
  .ite (.bin .eq (.inp selP) (.c 1))
    (.ite (.bin .eq (.v 2) (.v 1)) (.out (.bin .eq (.inp (.bin .add selP (.c 1))) (.c 1))) .skip)
    (.ite (.bin .eq (.inp selP) (.c 0)) (.set 2 (.c 1)) .skip)

/-- The selection program. Variables: `0` loop counter, `1` tag, `2` separator seen. -/
def selProg : Pr 3 :=
  .ite (.bin .eq (.inp (.c 1)) (.c 1))
    (.seq (.set 1 (.inp (.c 2))) (.seq (.out (.v 1)) (.seq (.set 2 (.c 0))
      (.loop 0 .len selBody))))
    .skip

lemma selBody_run (z : Word) (C : ℕ) (ρ : Fin 3 → ℕ) (i : ℕ) (h0 : ρ 0 = i)
    (hC : 2 * i + 5 ≤ C) :
    selBody.run z C ρ =
      if bitCode z[2 * i + 2]? = 1 then
        (if ρ 2 = ρ 1 then (ρ, [decide (bitCode z[2 * i + 3]? = 1)]) else (ρ, []))
      else if bitCode z[2 * i + 2]? = 0 then (Function.update ρ 2 1, []) else (ρ, []) := by
  have hP : selP.eval z C ρ = 2 * i + 2 + 1 := by
    simp only [selP, eval_bin, ap_add, eval_v, h0, eval_c]
    rw [min_eq_left (show 3 ≤ C by omega), min_eq_left (by omega), min_eq_left (by omega)]
    omega
  have hP1 : (Ex.bin .add selP (.c 1)).eval z C ρ = 2 * i + 3 + 1 := by
    simp only [eval_bin, ap_add, hP, eval_c]
    rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega)]
  have e1 : min 1 C = 1 := min_eq_left (by omega)
  have e0 : min 0 C = 0 := min_eq_left (by omega)
  have hi1 : (Ex.inp selP).eval z C ρ = bitCode z[2 * i + 2]? := by
    rw [eval_inp, hP, symNum_inputSym_succ]
  have hi2 : (Ex.inp (.bin .add selP (.c 1))).eval z C ρ = bitCode z[2 * i + 3]? := by
    rw [eval_inp, hP1, symNum_inputSym_succ]
  unfold selBody
  rw [run_ite]
  simp only [eval_bin, ap_eq, hi1, eval_c, e1, e0]
  by_cases ha : bitCode z[2 * i + 2]? = 1
  · simp only [ha, if_true, ne_eq, one_ne_zero, not_false_eq_true]
    rw [run_ite]
    simp only [eval_bin, ap_eq, eval_v]
    by_cases hb : ρ 2 = ρ 1
    · simp only [hb, if_true, ne_eq, one_ne_zero, not_false_eq_true, run_out, eval_bin, ap_eq,
        hi2, eval_c, e1]
      by_cases hc : bitCode z[2 * i + 3]? = 1 <;> simp [hc]
    · simp [hb]
  · simp only [ha, if_false, ne_eq, not_true_eq_false]
    rw [run_ite]
    simp only [eval_bin, ap_eq, hi1, eval_c, e0]
    by_cases hb : bitCode z[2 * i + 2]? = 0
    · simp [hb, eval_c, e1]
    · simp [hb]

/-- The word read by the selection program. -/
def selIn (b : Bool) (u v : Word) : Word :=
  [true, b] ++ ((u.flatMap dupB ++ [false, false]) ++ (v.flatMap dupB ++ []))

lemma selIn_get (b : Bool) (u v : Word) (i : ℕ) :
    ((selIn b u v)[2 * i + 2]? = if i < u.length then some true else if i = u.length then
      some false else if i < u.length + 1 + v.length then some true else none) ∧
    ((selIn b u v)[2 * i + 3]? = if i < u.length then u[i]? else if i = u.length then
      some false else v[i - u.length - 1]?) := by
  have hu := dup_length u
  have hv := dup_length v
  simp only [selIn, List.append_nil]
  refine ⟨?_, ?_⟩
  · rw [List.getElem?_append_right (by simp), show 2 * i + 2 - [true, b].length = 2 * i by simp]
    by_cases h1 : i < u.length
    · rw [List.append_assoc, List.getElem?_append_left (by rw [hu]; omega), dup_get_even,
        if_pos h1, if_pos h1]
    · rw [List.append_assoc, List.getElem?_append_right (by rw [hu]; omega), hu, if_neg h1]
      by_cases h2 : i = u.length
      · subst h2; simp
      · rw [if_neg h2, List.getElem?_append_right (by simp; omega),
          show 2 * i - 2 * u.length - [false, false].length = 2 * (i - u.length - 1) by
            simp; omega, dup_get_even]
        by_cases h3 : i - u.length - 1 < v.length
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3, if_neg (by omega)]
  · rw [List.getElem?_append_right (by simp), show 2 * i + 3 - [true, b].length = 2 * i + 1 by
      simp]
    by_cases h1 : i < u.length
    · rw [List.append_assoc, List.getElem?_append_left (by rw [hu]; omega), dup_get_odd,
        if_pos h1]
    · rw [List.append_assoc, List.getElem?_append_right (by rw [hu]; omega), hu, if_neg h1]
      by_cases h2 : i = u.length
      · subst h2; simp
      · rw [if_neg h2, List.getElem?_append_right (by simp; omega),
          show 2 * i + 1 - 2 * u.length - [false, false].length = 2 * (i - u.length - 1) + 1 by
            simp; omega, dup_get_odd]

lemma selIn_length (b : Bool) (u v : Word) :
    (selIn b u v).length = 2 * u.length + 2 * v.length + 4 := by
  simp only [selIn, List.length_append, dup_length, List.length_cons, List.length_nil]; omega

/-- Per-iteration output of the selection loop. -/
def selO (b : Bool) (u v : Word) (i : ℕ) : List Bool :=
  if i < u.length then (if b then [] else [u[i]?.getD false])
  else if i = u.length then [] else (if b then (v[i - u.length - 1]?).toList else [])

lemma selO_flatMap (b : Bool) (u v : Word) (N : ℕ) (hN : u.length + 1 + v.length ≤ N) :
    (List.range N).flatMap (selO b u v) = if b then v else u := by
  obtain ⟨k, rfl⟩ : ∃ k, N = u.length + (1 + (v.length + k)) := ⟨N - u.length - 1 - v.length,
    by omega⟩
  rw [List.range_add, List.flatMap_append, List.range_add, List.flatMap_map, List.flatMap_append,
    List.range_add, List.flatMap_map, List.flatMap_append, List.flatMap_map]
  have e1 : (List.range u.length).flatMap (selO b u v) = if b then [] else u := by
    rw [show (if b = true then [] else u) = u.flatMap (fun c => if b then [] else [c]) by
      cases b <;> simp, ← flatMap_range_getD u _ false]
    refine List.flatMap_congr fun i hi => ?_
    simp only [List.mem_range] at hi
    simp only [selO, if_pos hi]
  have e2 : (List.range 1).flatMap (fun i => selO b u v (u.length + i)) = [] := by
    simp [selO]
  have e3 : (List.range v.length).flatMap (fun i => selO b u v (u.length + (1 + i))) =
      if b then v else [] := by
    rw [show (if b = true then v else []) = v.flatMap (fun c => if b then [c] else []) by
      cases b <;> simp, ← flatMap_range_getD v _ false]
    refine List.flatMap_congr fun i hi => ?_
    simp only [List.mem_range] at hi
    simp only [selO, if_neg (show ¬ u.length + (1 + i) < u.length by omega),
      if_neg (show u.length + (1 + i) ≠ u.length by omega),
      show u.length + (1 + i) - u.length - 1 = i by omega, List.getElem?_eq_getElem hi]
    cases b <;> simp
  have e4 : (List.range k).flatMap (fun i => selO b u v (u.length + (1 + (v.length + i)))) = [] := by
    refine List.flatMap_eq_nil_iff.2 fun i _ => ?_
    simp only [selO, if_neg (show ¬ u.length + (1 + (v.length + i)) < u.length by omega),
      if_neg (show u.length + (1 + (v.length + i)) ≠ u.length by omega),
      List.getElem?_eq_none (show v.length ≤ u.length + (1 + (v.length + i)) - u.length - 1 by
        omega)]
    simp
  rw [e1, e2, e3, e4]
  cases b <;> simp

lemma selProg_output_b (b : Bool) (u v : Word) :
    selProg.output 2 (selIn b u v) = b :: (if b then v else u) := by
  set z := selIn b u v with hz
  have hC := len_lt_cap2 z
  have hzl := selIn_length b u v
  rw [← hz] at hzl
  unfold Pr.output selProg
  set C := capOf 2 z
  have e1 : min 1 C = 1 := min_eq_left (by omega)
  have e2 : min 2 C = 2 := min_eq_left (by omega)
  have e0 : min 0 C = 0 := min_eq_left (by omega)
  have hz1 : symNum (inputSym z 1) = 1 := by simp [hz, selIn, inputSym, symNum]
  have hz2 : symNum (inputSym z 2) = if b then 1 else 0 := by
    cases b <;> simp [hz, selIn, inputSym, symNum]
  rw [run_ite_pos (by simp [e1, hz1])]
  simp only [run_seq, run_set, run_out, eval_inp, eval_c, eval_v, e2, e0, hz2,
    Function.update_self]
  set bb : ℕ := if b then 1 else 0 with hbb
  set ρ₀ : Fin 3 → ℕ := Function.update (Function.update (fun _ => 0) 1 bb) 2 0
  have h := run_loop_spec (V := 3) (w := z) (C := C) 0 .len selBody ρ₀
    (fun i ρ => ρ 1 = bb ∧ ρ 2 = (if u.length < i then 1 else 0))
    (selO b u v) ⟨by simp [ρ₀], by simp [ρ₀]⟩ (by
      intro i hi ρ' ⟨h1, h2⟩
      simp only [eval_len] at hi
      have hi' : i < z.length := by omega
      obtain ⟨g0, g1⟩ := selIn_get b u v i
      rw [← hz] at g0 g1
      rw [selBody_run z C _ i (by simp) (by omega)]
      have hs1 : (Function.update ρ' 0 i) 1 = bb := by
        rw [Function.update_of_ne (by decide)]; exact h1
      have hs2 : (Function.update ρ' 0 i) 2 = (if u.length < i then 1 else 0) := by
        rw [Function.update_of_ne (by decide)]; exact h2
      rw [hs1, hs2, g0, g1]
      rcases Nat.lt_trichotomy i u.length with hu | hu | hu
      · simp only [if_pos hu, bitCode, if_true, if_neg (show ¬ u.length < i by omega)]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · split <;> simp [h1]
        · split <;> simp [h2, if_neg (show ¬ u.length < i by omega)] <;> omega
        · cases b
          · simp only [hbb, Bool.false_eq_true, if_false, if_true, selO, if_pos hu]
            rw [List.getElem?_eq_getElem hu]; cases u[i] <;> simp
          · simp [hbb, selO, hu]
      · subst hu
        simp only [lt_irrefl, if_false, if_true, bitCode]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp [h1]
        · simp
        · simp [selO]
      · simp only [if_neg (show ¬ i < u.length by omega), if_neg (show i ≠ u.length by omega),
          if_pos hu]
        by_cases hv : i < u.length + 1 + v.length
        · simp only [if_pos hv, bitCode, if_true]
          have hv' : i - u.length - 1 < v.length := by omega
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · split <;> simp [h1]
          · split <;> simp [h2, hu, show u.length < i + 1 by omega]
          · simp only [selO, if_neg (show ¬ i < u.length by omega),
              if_neg (show i ≠ u.length by omega), List.getElem?_eq_getElem hv']
            cases b
            · simp [hbb]
            · simp only [hbb, if_true]; cases v[i - u.length - 1] <;> simp [bitCode]
        · simp only [if_neg hv, bitCode]
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · simp [h1]
          · simp [h2, hu]; omega
          · simp only [selO, if_neg (show ¬ i < u.length by omega),
              if_neg (show i ≠ u.length by omega),
              List.getElem?_eq_none (show v.length ≤ i - u.length - 1 by omega)]
            simp)
  rw [h.2]
  simp only [eval_len]
  rw [min_eq_left (by omega), selO_flatMap b u v _ (by omega)]
  cases b <;> simp [hbb]

lemma selProg_output_nil (z : Word) (h : z[0]? = some false) : selProg.output 2 z = [] := by
  have hC := len_lt_cap2 z
  unfold Pr.output selProg
  rw [run_ite_neg]
  · rfl
  · simp only [eval_bin, ap_eq, eval_inp, eval_c]
    rw [min_eq_left (show 1 ≤ capOf 2 z by omega), symNum_inputSym_succ, h]
    simp [bitCode]

/-- The word fed to the selection program. -/
def tagMapPre (f₁ f₂ : Word → Word) (x : Word) : Word :=
  head2 x ++ ((f₁ x.tail).flatMap dupB ++ [false, false]) ++ ((f₂ x.tail).flatMap dupB ++ [])

lemma selProg_tagMapPre (f₁ f₂ : Word → Word) (x : Word) :
    selProg.output 2 (tagMapPre f₁ f₂ x) = tagMapF f₁ f₂ x := by
  rcases x with _ | ⟨b, y⟩
  · exact selProg_output_nil _ (by simp [tagMapPre, head2])
  · have : tagMapPre f₁ f₂ (b :: y) = selIn b (f₁ y) (f₂ y) := by
      simp [tagMapPre, head2, selIn]
    rw [this, selProg_output_b]
    rfl

end LL

open LL

/-- The tagged map of two logspace functions is logspace computable. -/
theorem LogspaceComputable.tagMap {f₁ f₂ : Word → Word} (h₁ : LogspaceComputable f₁)
    (h₂ : LogspaceComputable f₂) : LogspaceComputable (tagMapF f₁ f₂) := by
  have hpre : LogspaceComputable (tagMapPre f₁ f₂) := by
    have a1 := (LogspaceComputable.tail.comp h₁).comp (LogspaceComputable.bitMap dupB [false, false])
    have a2 := (LogspaceComputable.tail.comp h₂).comp (LogspaceComputable.bitMap dupB [])
    exact (LogspaceComputable.head2.append a1).append a2
  have hsel : LogspaceComputable (selProg.output 2) :=
    logspaceComputable_of_output 2 selProg _ (fun _ => rfl)
  have := hpre.comp hsel
  refine (funext fun x => ?_ : (selProg.output 2 ∘ tagMapPre f₁ f₂) = tagMapF f₁ f₂) ▸ this
  exact selProg_tagMapPre f₁ f₂ x

/-- `LogDCFL` is closed under tagged unions. -/
theorem LogDCFL_tagU {A₁ A₂ : Language} (h₁ : A₁ ∈ LogDCFL) (h₂ : A₂ ∈ LogDCFL) :
    tagU A₁ A₂ ∈ LogDCFL := by
  obtain ⟨D₁, hD₁, f₁, hf₁, e₁⟩ := h₁
  obtain ⟨D₂, hD₂, f₂, hf₂, e₂⟩ := h₂
  refine ⟨tagU D₁ D₂, DCFL_tagU hD₁ hD₂, tagMapF f₁ f₂, hf₁.tagMap hf₂, fun x => ?_⟩
  rcases x with _ | ⟨b, y⟩
  · simp [tagMapF, nil_not_mem_tagU]
  · simp only [tagMapF, cons_mem_tagU]
    cases b <;> simp [e₁, e₂]

end PathChecking
