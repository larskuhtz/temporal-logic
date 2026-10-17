module

public import RequestProject.LogLang.Out

/-!
# Every language is in `AC⁰` relative to itself

The circuit `selfCirc n` on `n` inputs consists of the `n` input gates followed by a single
oracle gate reading all of them (`ACOracle_self_zero`).  Hence `LogDCFL ⊆ AC⁰[LogDCFL]`
(`LogDCFL_subset_ACOracle_zero`).
-/

@[expose] public section

namespace PathChecking

open LL

/-- The circuit `[x₀, …, x_{n-1}, B(x₀ … x_{n-1})]`. -/
def selfCirc (n : ℕ) : Circuit :=
  (List.range n).map (fun i => ⟨.input i, []⟩) ++ [⟨.oracle, List.range n⟩]

lemma foldl_max_le (l : List ℕ) (a b : ℕ) (ha : a ≤ b) (hl : ∀ x ∈ l, x ≤ b) :
    l.foldl max a ≤ b := by
  induction l generalizing a with
  | nil => simpa using ha
  | cons x l ih =>
    simp only [List.foldl_cons]
    exact ih _ (max_le ha (hl x (by simp))) (fun y hy => hl y (by simp [hy]))

/-- Depth of a gate given the depths of the previous gates. -/
def gateDepth (ds : List ℕ) (g : Gate) : ℕ :=
  match g.kind with
  | .input _ => 0
  | .const _ => 0
  | _ => 1 + (g.args.map fun j => ds.getD j 0).foldl max 0

lemma Circuit.depths_snoc (C : Circuit) (g : Gate) :
    Circuit.depths (C ++ [g]) = C.depths ++ [gateDepth C.depths g] := by
  unfold Circuit.depths; rw [List.foldl_append]; rfl

lemma selfCirc_depths_inputs (n : ℕ) :
    Circuit.depths ((List.range n).map (fun i => (⟨.input i, []⟩ : Gate))) =
      List.replicate n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, Circuit.depths_snoc, ih]
    simp [List.replicate_succ', gateDepth]

lemma selfCirc_depth (n : ℕ) : (selfCirc n).depth ≤ 1 := by
  unfold Circuit.depth selfCirc
  rw [Circuit.depths_snoc, selfCirc_depths_inputs]
  apply foldl_max_le _ _ _ (by omega)
  intro x hx
  simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at hx
  rcases hx with ⟨_, rfl⟩ | rfl
  · omega
  · have : (List.map (fun j => (List.replicate n 0).getD j 0) (List.range n)).foldl max 0 ≤ 0 :=
      foldl_max_le _ _ _ le_rfl (fun y hy => by
        simp only [List.mem_map] at hy
        obtain ⟨j, _, rfl⟩ := hy
        simp [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split_ifs <;> rfl)
    simp only [gateDepth]
    omega

lemma selfCirc_values_inputs (B : Language) (x : Word) (n : ℕ) (vals : List Bool) :
    ((List.range n).map (fun i => (⟨.input i, []⟩ : Gate))).foldl
      (fun vals g => vals ++ [g.eval B x vals]) vals =
      vals ++ (List.range n).map (fun i => x.getD i false) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp [Gate.eval]

lemma selfCirc_eval (B : Language) (x : Word) :
    (selfCirc x.length).eval B x = true ↔ x ∈ B := by
  unfold Circuit.eval Circuit.values selfCirc
  rw [List.foldl_append, selfCirc_values_inputs]
  simp only [List.nil_append, List.foldl_cons, List.foldl_nil, List.getLastD_eq_getLast?,
    List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.getD_some]
  simp only [Gate.eval, decide_eq_true_iff]
  suffices h : (List.map (fun j => ((List.range x.length).map (fun i => x.getD i false)).getD j
      false) (List.range x.length)) = x by rw [h]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp at h1
  simp [List.getD_eq_getElem?_getD, h1]

lemma selfCirc_wf (n : ℕ) : (selfCirc n).WellFormed n := by
  refine ⟨by simp [selfCirc], fun i hi => ?_⟩
  simp only [selfCirc, List.length_append, List.length_map, List.length_range,
    List.length_singleton] at hi
  by_cases h : i < n
  · have e : (selfCirc n)[i]'(by simp [selfCirc]; omega) = ⟨.input i, []⟩ := by
      simp [selfCirc, List.getElem_append_left (by simpa using h : i < ((List.range n).map
        (fun i => (⟨.input i, []⟩ : Gate))).length)]
    simp only [e]; simp [h]
  · have hi' : i = n := by omega
    subst hi'
    have e : (selfCirc i)[i]'(by simp [selfCirc]) = ⟨.oracle, List.range i⟩ := by
      simp [selfCirc, List.getElem_append_right]
    simp only [e]; simp

/-- The token encoding of `selfCirc n`. -/
lemma selfCirc_toks (n : ℕ) : (selfCirc n).flatMap Gate.toks =
    (List.range n).flatMap (fun i => Tok.tag 0 :: natToks i ++ [Tok.lpar, Tok.rpar]) ++
      (Tok.tag 6 :: Tok.lpar :: ((List.range n).flatMap natToks ++ [Tok.rpar])) := by
  simp [selfCirc, Gate.toks, List.flatMap_map]

/-- The generator program of `selfCirc`. Variables: `0` loop counter, `1`, `2` temporaries. -/
def selfGen : Pr 3 :=
  .seq (.loop 0 .len (.seq (outToks [Tok.tag 0]) (.seq (emitNat 0 1 2)
      (outToks [Tok.lpar, Tok.rpar]))))
    (.seq (outToks [Tok.tag 6, Tok.lpar]) (.seq (.loop 0 .len (emitNat 0 1 2))
      (outToks [Tok.rpar])))

lemma selfGen_output (w : Word) : selfGen.output 1 w = (selfCirc w.length).encode := by
  have hC : 2 ≤ capOf 1 w := by unfold capOf; omega
  have hlen : min w.length (capOf 1 w) = w.length := by unfold capOf; simp; omega
  unfold Pr.output Circuit.encode
  rw [selfCirc_toks]
  simp only [selfGen, run_seq, run_outToks]
  set C := capOf 1 w
  have h1 := run_loop_spec (V := 3) (w := w) (C := C) 0 .len
    (.seq (outToks [Tok.tag 0]) (.seq (emitNat 0 1 2) (outToks [Tok.lpar, Tok.rpar])))
    (fun _ => 0) (fun _ _ => True)
    (fun i => encodeToks (Tok.tag 0 :: natToks i ++ [Tok.lpar, Tok.rpar])) trivial
    (fun i _ ρ' _ => by
      refine ⟨trivial, ?_⟩
      simp only [run_seq, run_outToks]
      rw [(run_emitNat 0 1 2 (by decide) hC _).1]
      simp [encodeToks])
  have h2 := fun ρ => run_loop_spec (V := 3) (w := w) (C := C) 0 .len (emitNat 0 1 2) ρ
    (fun _ _ => True) (fun i => encodeToks (natToks i)) trivial
    (fun i _ ρ' _ => ⟨trivial, by rw [(run_emitNat 0 1 2 (by decide) hC _).1]; simp⟩)
  rw [h1.2, (h2 _).2]
  simp only [eval_len, hlen]
  simp [encodeToks, List.flatMap_assoc]

lemma selfCirc_uniform : LogspaceUniform selfCirc :=
  ⟨fun w => (selfCirc w.length).encode,
    logspaceComputable_of_output 1 selfGen _ selfGen_output, fun n => by simp⟩

/-- Every language is in `AC⁰` relative to itself (a single oracle gate reading all inputs). -/
theorem ACOracle_self_zero (B : Language) : B ∈ ACOracle 0 {B} := by
  refine ⟨B, rfl, selfCirc, 1, selfCirc_uniform, fun n => ⟨selfCirc_wf n, ?_, ?_⟩, fun w => ?_⟩
  · simp [Circuit.size, selfCirc]
  · have := selfCirc_depth n; simp only [pow_zero, mul_one]; omega
  · exact selfCirc_eval B w

/-- Every language in `LogDCFL` is in `AC⁰[LogDCFL]`. -/
theorem LogDCFL_subset_ACOracle_zero {B : Language} (hB : B ∈ LogDCFL) :
    B ∈ ACOracle 0 LogDCFL := by
  obtain ⟨B', hB', C, c, hu, hC, he⟩ := ACOracle_self_zero B
  exact ⟨B', by rw [Set.mem_singleton_iff.1 hB']; exact hB, C, c, hu, hC, he⟩

end PathChecking
