module

public import RequestProject.ACRound.Self

/-!
# Generic lemmas on circuit values and depths

`Circuit.values_spec`: if a function `val` satisfies the gate equations of a circuit (in the
form `Gate.evalFn`), then it is the value function of the circuit.  `Circuit.depths_le_spec`:
if a function `dep` increases along every wire, it bounds the depth of every gate.
-/

@[expose] public section

namespace PathChecking

open Classical

/-- Value of a gate when the values of all gates are given by a function. -/
noncomputable def Gate.evalFn (B : Language) (x : Word) (val : ℕ → Bool) (g : Gate) : Bool :=
  match g.kind with
  | .input i => x.getD i false
  | .const b => b
  | .not => !((g.args.map val).headD false)
  | .and => (g.args.map val).all id
  | .or => (g.args.map val).any id
  | .oracle => decide (g.args.map val ∈ B)

lemma Gate.eval_range_map (B : Language) (x : Word) (val : ℕ → Bool) (g : Gate) (i : ℕ)
    (h : ∀ j ∈ g.args, j < i) : g.eval B x ((List.range i).map val) = g.evalFn B x val := by
  have e : g.args.map (fun j => ((List.range i).map val).getD j false) = g.args.map val := by
    refine List.map_congr_left fun j hj => ?_
    have := h j hj
    simp [List.getD_eq_getElem?_getD, this]
  unfold Gate.eval Gate.evalFn
  simp only [e]
  rcases g.kind <;> rfl

lemma Circuit.values_snoc (B : Language) (x : Word) (C : Circuit) (g : Gate) :
    Circuit.values B x (C ++ [g]) = C.values B x ++ [g.eval B x (C.values B x)] := by
  unfold Circuit.values; rw [List.foldl_append]; rfl

@[simp] lemma Circuit.values_nil (B : Language) (x : Word) : Circuit.values B x [] = [] := rfl

lemma Circuit.values_length (B : Language) (x : Word) (C : Circuit) :
    (C.values B x).length = C.length := by
  induction C using List.reverseRecOn with
  | nil => rfl
  | append_singleton C g ih => simp [Circuit.values_snoc, ih]

lemma Circuit.values_append_take (B : Language) (x : Word) (C D : Circuit) :
    ((C ++ D).values B x).take C.length = C.values B x := by
  induction D using List.reverseRecOn with
  | nil => simp [← Circuit.values_length B x C]
  | append_singleton D g ih =>
    rw [← List.append_assoc, Circuit.values_snoc, List.take_append_of_le_length
      (by simp [Circuit.values_length]), ih]

lemma Circuit.values_take (B : Language) (x : Word) (C : Circuit) (i : ℕ) :
    (C.values B x).take i = Circuit.values B x (C.take i) := by
  by_cases hi : i ≤ C.length
  · conv_lhs => rw [← List.take_append_drop i C]
    have := Circuit.values_append_take B x (C.take i) (C.drop i)
    rwa [List.length_take, min_eq_left hi] at this
  · rw [List.take_of_length_le (by simp [Circuit.values_length]; omega),
      List.take_of_length_le (by omega)]

lemma Circuit.values_getElem (B : Language) (x : Word) (C : Circuit) (i : ℕ)
    (h : i < C.length) :
    (C.values B x)[i]'(by simp [Circuit.values_length, h]) =
      C[i].eval B x ((C.values B x).take i) := by
  have e1 := Circuit.values_take B x C (i + 1)
  rw [List.take_succ_eq_append_getElem h, Circuit.values_snoc, ← Circuit.values_take,
    List.take_succ_eq_append_getElem (by simp [Circuit.values_length, h])] at e1
  have := List.append_cancel_left e1
  simpa using this

/-- **Values from a specification.** -/
theorem Circuit.values_spec (B : Language) (x : Word) (C : Circuit) (val : ℕ → Bool)
    (hargs : ∀ i (h : i < C.length), ∀ j ∈ C[i].args, j < i)
    (hval : ∀ i (h : i < C.length), C[i].evalFn B x val = val i) :
    ∀ i (h : i < C.length), (C.values B x)[i]'(by simp [Circuit.values_length, h]) = val i := by
  have key : ∀ i, i ≤ C.length → (C.values B x).take i = (List.range i).map val := by
    intro i
    induction i with
    | zero => intro; simp
    | succ i ih =>
      intro hi
      rw [List.take_succ_eq_append_getElem (by simp [Circuit.values_length]; omega), ih (by omega),
        Circuit.values_getElem B x C i (by omega), ih (by omega),
        Gate.eval_range_map B x val _ i (hargs i (by omega)), hval i (by omega),
        List.range_succ, List.map_append, List.map_singleton]
  intro i h
  have := key (i + 1) h
  rw [List.take_succ_eq_append_getElem (by simp [Circuit.values_length]; omega), key i (by omega),
    List.range_succ, List.map_append, List.map_singleton] at this
  simpa using this

lemma Circuit.eval_eq_getElem (B : Language) (x : Word) (C : Circuit) (h : C ≠ []) :
    C.eval B x = (C.values B x)[C.length - 1]'(by
      simp [Circuit.values_length]; exact List.length_pos_of_ne_nil h) := by
  unfold Circuit.eval
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
  simp [Circuit.values_length, List.length_pos_of_ne_nil h]

/-! ## Depths -/

lemma Circuit.depths_length (C : Circuit) : C.depths.length = C.length := by
  induction C using List.reverseRecOn with
  | nil => rfl
  | append_singleton C g ih => simp [Circuit.depths_snoc, ih]

lemma Circuit.depths_append_take (C D : Circuit) :
    (C ++ D).depths.take C.length = C.depths := by
  induction D using List.reverseRecOn with
  | nil => simp [← Circuit.depths_length C]
  | append_singleton D g ih =>
    rw [← List.append_assoc, Circuit.depths_snoc, List.take_append_of_le_length
      (by simp [Circuit.depths_length]), ih]

lemma Circuit.depths_take (C : Circuit) (i : ℕ) : C.depths.take i = Circuit.depths (C.take i) := by
  by_cases hi : i ≤ C.length
  · conv_lhs => rw [← List.take_append_drop i C]
    have := Circuit.depths_append_take (C.take i) (C.drop i)
    rwa [List.length_take, min_eq_left hi] at this
  · rw [List.take_of_length_le (by simp [Circuit.depths_length]; omega),
      List.take_of_length_le (by omega)]

lemma Circuit.depths_getElem (C : Circuit) (i : ℕ) (h : i < C.length) :
    C.depths[i]'(by simp [Circuit.depths_length, h]) = gateDepth (C.depths.take i) C[i] := by
  have e1 := Circuit.depths_take C (i + 1)
  rw [List.take_succ_eq_append_getElem h, Circuit.depths_snoc, ← Circuit.depths_take,
    List.take_succ_eq_append_getElem (by simp [Circuit.depths_length, h])] at e1
  have := List.append_cancel_left e1
  simpa using this

/-- **Depth bounds from a potential.** -/
theorem Circuit.depths_le_spec (C : Circuit) (dep : ℕ → ℕ)
    (hargs : ∀ i (h : i < C.length), ∀ j ∈ C[i].args, j < i)
    (hdep : ∀ i (h : i < C.length), ∀ j ∈ C[i].args, dep j + 1 ≤ dep i)
    (hpos : ∀ i (h : i < C.length), (∀ k, C[i].kind ≠ .input k) → (∀ b, C[i].kind ≠ .const b) →
      1 ≤ dep i) :
    ∀ i (h : i < C.length), C.depths[i]'(by simp [Circuit.depths_length, h]) ≤ dep i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro h
    rw [Circuit.depths_getElem C i h]
    have hb : 1 ≤ dep i →
        (C[i].args.map fun j => (C.depths.take i).getD j 0).foldl max 0 + 1 ≤ dep i := by
      intro hd
      have := foldl_max_le (C[i].args.map fun j => (C.depths.take i).getD j 0) 0 (dep i - 1)
        (by omega) (by
          intro y hy
          simp only [List.mem_map] at hy
          obtain ⟨j, hj, rfl⟩ := hy
          have hji := hargs i h j hj
          have := ih j hji (by omega)
          have := hdep i h j hj
          rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hji,
            List.getElem?_eq_getElem (by simp [Circuit.depths_length]; omega)]
          simp only [Option.getD_some]
          omega)
      omega
    rcases hk : C[i].kind with k | b | _ | _ | _ | _ <;> simp only [gateDepth, hk]
    · omega
    · omega
    all_goals (have := hb (hpos i h (by simp [hk]) (by simp [hk])); omega)

lemma Circuit.depth_le_of (C : Circuit) (D : ℕ)
    (h : ∀ i (hi : i < C.length), C.depths[i]'(by simp [Circuit.depths_length, hi]) ≤ D) :
    C.depth ≤ D := by
  unfold Circuit.depth
  refine foldl_max_le _ _ _ (Nat.zero_le _) fun y hy => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
  exact h i (by simpa [Circuit.depths_length] using hi)

end PathChecking
