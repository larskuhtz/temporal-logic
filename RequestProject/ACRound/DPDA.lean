module

public import RequestProject.Complexity

/-!
# Two closure properties of deterministic context-free languages

* `DCFL_single`: the language `{[true]}` is deterministic context-free;
* `DCFL_tagU`: if `D₁` and `D₂` are deterministic context-free, then so is the tagged union
  `tagU D₁ D₂ = {false :: y | y ∈ D₁} ∪ {true :: y | y ∈ D₂}`.
-/

@[expose] public section

namespace PathChecking

/-- The tagged union of two languages. -/
def tagU (D₁ D₂ : Language) : Language :=
  {x | ∃ y, (x = false :: y ∧ y ∈ D₁) ∨ (x = true :: y ∧ y ∈ D₂)}

lemma nil_not_mem_tagU (D₁ D₂ : Language) : [] ∉ tagU D₁ D₂ := by
  rintro ⟨y, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> simp at h

lemma cons_mem_tagU (D₁ D₂ : Language) (b : Bool) (y : Word) :
    b :: y ∈ tagU D₁ D₂ ↔ y ∈ (if b then D₂ else D₁) := by
  constructor
  · rintro ⟨y', ⟨h, h'⟩ | ⟨h, h'⟩⟩ <;> simp only [List.cons.injEq] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> simpa using h'
  · intro h
    cases b
    · exact ⟨y, Or.inl ⟨rfl, by simpa using h⟩⟩
    · exact ⟨y, Or.inr ⟨rfl, by simpa using h⟩⟩

namespace DPDA

/-! ## The language `{[true]}` -/

/-- Transition of the automaton for `{[true]}`: state `0` initial, `1` accepting, `2` dead. -/
def oneNext : Fin 3 → Bool → Fin 3
  | 0, true => 1
  | _, _ => 2

/-- The automaton for `{[true]}`. -/
def single : DPDA where
  Q := Fin 3
  S := Unit
  start := 0
  bottom := ()
  accept := {1}
  δ q a _ := a.map fun b => (oneNext q b, [()])
  deterministic := by intro q Z h; simp at h

lemma single_reach (w : Word) : ∀ (q q' : Fin 3) (γ : List Unit),
    Relation.ReflTransGen single.Step ⟨q, w, [()]⟩ ⟨q', [], γ⟩ → q' = w.foldl oneNext q := by
  induction w with
  | nil =>
    intro q q' γ h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hst, -⟩
    · simp only [Cfg.mk.injEq] at h; simp [h.1]
    · cases hst with
      | eps hδ => simp [single] at hδ
  | cons a w ih =>
    intro q q' γ h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hst, hrest⟩
    · simp at h
    · cases hst with
      | read hδ =>
        simp only [single, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hδ
        obtain ⟨rfl, rfl⟩ := hδ
        simpa using ih _ _ _ hrest
      | eps hδ => simp [single] at hδ

lemma single_accepts (w : Word) : single.Accepts w ↔ w = [true] := by
  constructor
  · rintro ⟨q, γ, hq, h⟩
    have e := single_reach w _ _ _ h
    change q = (1 : Fin 3) at hq
    subst hq
    rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩
    · simp [single] at e
    · change (1 : Fin 3) = oneNext 0 a at e
      cases a
      · exact absurd e (by decide)
      · rfl
    · exfalso
      have : ∀ (l : Word), l.foldl oneNext 2 = 2 := by
        intro l; induction l with
        | nil => rfl
        | cons x l ih => simpa [oneNext] using ih
      have h2 : oneNext (oneNext single.start a) b = 2 := by
        cases a <;> cases b <;> rfl
      simp only [List.foldl_cons, h2, this] at e
      exact absurd e (by decide)
  · rintro rfl
    refine ⟨(1 : Fin 3), [()], rfl, Relation.ReflTransGen.single ?_⟩
    exact Step.read (M := single) (q := (0 : Fin 3)) (a := true) (Z := ()) (γ := []) (w := [])
      (q' := (1 : Fin 3)) (α := [()]) rfl

end DPDA

namespace DPDA

/-! ## Tagged unions -/

section Tag

variable (P₁ P₂ : DPDA)

/-- Transition function of the automaton for the tagged union. -/
def tagδ : Option (P₁.Q ⊕ P₂.Q) → Option Bool → Option (P₁.S ⊕ P₂.S) →
    Option (Option (P₁.Q ⊕ P₂.Q) × List (Option (P₁.S ⊕ P₂.S)))
  | none, some false, none => some (some (.inl P₁.start), [some (.inl P₁.bottom)])
  | none, some true, none => some (some (.inr P₂.start), [some (.inr P₂.bottom)])
  | some (.inl q), a, some (.inl Z) =>
      (P₁.δ q a Z).map fun r => (some (.inl r.1), r.2.map (some ∘ Sum.inl))
  | some (.inr q), a, some (.inr Z) =>
      (P₂.δ q a Z).map fun r => (some (.inr r.1), r.2.map (some ∘ Sum.inr))
  | _, _, _ => none

lemma tagδ_det (q : Option (P₁.Q ⊕ P₂.Q)) (Z : Option (P₁.S ⊕ P₂.S))
    (h : (tagδ P₁ P₂ q none Z).isSome) (a : Bool) : tagδ P₁ P₂ q (some a) Z = none := by
  rcases q with _ | q₁ | q₂ <;> rcases Z with _ | Z₁ | Z₂ <;> simp [tagδ] at h ⊢
  · rw [P₁.deterministic q₁ Z₁ (by simpa using h) a]
  · rw [P₂.deterministic q₂ Z₂ (by simpa using h) a]

/-- The automaton for the tagged union. -/
def tagDPDA : DPDA :=
  letI := P₁.finQ; letI := P₂.finQ; letI := P₁.finS; letI := P₂.finS
  { Q := Option (P₁.Q ⊕ P₂.Q)
    S := Option (P₁.S ⊕ P₂.S)
    start := none
    bottom := none
    accept := {q | ∃ q₁ ∈ P₁.accept, q = some (.inl q₁)} ∪
      {q | ∃ q₂ ∈ P₂.accept, q = some (.inr q₂)}
    δ := tagδ P₁ P₂
    deterministic := tagδ_det P₁ P₂ }

/-- Embedding of the configurations of `P₁`. -/
def emb₁ (c : P₁.Cfg) : (tagDPDA P₁ P₂).Cfg :=
  ⟨some (.inl c.state), c.input, c.stack.map (some ∘ Sum.inl)⟩

/-- Embedding of the configurations of `P₂`. -/
def emb₂ (c : P₂.Cfg) : (tagDPDA P₁ P₂).Cfg :=
  ⟨some (.inr c.state), c.input, c.stack.map (some ∘ Sum.inr)⟩

lemma step_emb₁ {c c' : P₁.Cfg} (h : P₁.Step c c') : (tagDPDA P₁ P₂).Step (emb₁ P₁ P₂ c)
    (emb₁ P₁ P₂ c') := by
  cases h with
  | read hδ =>
    simp only [emb₁, List.map_cons, List.map_append]
    exact Step.read (M := tagDPDA P₁ P₂) (by simp [tagDPDA, tagδ, hδ])
  | eps hδ =>
    simp only [emb₁, List.map_cons, List.map_append]
    exact Step.eps (M := tagDPDA P₁ P₂) (by simp [tagDPDA, tagδ, hδ])

lemma step_emb₂ {c c' : P₂.Cfg} (h : P₂.Step c c') : (tagDPDA P₁ P₂).Step (emb₂ P₁ P₂ c)
    (emb₂ P₁ P₂ c') := by
  cases h with
  | read hδ =>
    simp only [emb₂, List.map_cons, List.map_append]
    exact Step.read (M := tagDPDA P₁ P₂) (by simp [tagDPDA, tagδ, hδ])
  | eps hδ =>
    simp only [emb₂, List.map_cons, List.map_append]
    exact Step.eps (M := tagDPDA P₁ P₂) (by simp [tagDPDA, tagδ, hδ])

lemma emb₁_step {c : P₁.Cfg} {d : (tagDPDA P₁ P₂).Cfg} (h : (tagDPDA P₁ P₂).Step
    (emb₁ P₁ P₂ c) d) : ∃ c', P₁.Step c c' ∧ d = emb₁ P₁ P₂ c' := by
  obtain ⟨q, w, γ⟩ := c
  rcases γ with _ | ⟨Z, γ⟩
  · cases h
  · cases h with
    | read hδ =>
      rename_i a w q' α
      have hδ' : (P₁.δ q (some a) Z).map (fun r => (some (Sum.inl r.1),
          r.2.map (some ∘ Sum.inl))) = some (q', α) := hδ
      rcases e : P₁.δ q (some a) Z with _ | ⟨q₁, α₁⟩
      · simp [e] at hδ'
      · simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hδ'
        obtain ⟨rfl, rfl⟩ := hδ'
        exact ⟨⟨q₁, w, α₁ ++ γ⟩, Step.read e, by simp [emb₁]⟩
    | eps hδ =>
      rename_i q' α
      have hδ' : (P₁.δ q none Z).map (fun r => (some (Sum.inl r.1),
          r.2.map (some ∘ Sum.inl))) = some (q', α) := hδ
      rcases e : P₁.δ q none Z with _ | ⟨q₁, α₁⟩
      · simp [e] at hδ'
      · simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hδ'
        obtain ⟨rfl, rfl⟩ := hδ'
        exact ⟨⟨q₁, w, α₁ ++ γ⟩, Step.eps e, by simp [emb₁]⟩

lemma emb₂_step {c : P₂.Cfg} {d : (tagDPDA P₁ P₂).Cfg} (h : (tagDPDA P₁ P₂).Step
    (emb₂ P₁ P₂ c) d) : ∃ c', P₂.Step c c' ∧ d = emb₂ P₁ P₂ c' := by
  obtain ⟨q, w, γ⟩ := c
  rcases γ with _ | ⟨Z, γ⟩
  · cases h
  · cases h with
    | read hδ =>
      rename_i a w q' α
      have hδ' : (P₂.δ q (some a) Z).map (fun r => (some (Sum.inr r.1),
          r.2.map (some ∘ Sum.inr))) = some (q', α) := hδ
      rcases e : P₂.δ q (some a) Z with _ | ⟨q₁, α₁⟩
      · simp [e] at hδ'
      · simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hδ'
        obtain ⟨rfl, rfl⟩ := hδ'
        exact ⟨⟨q₁, w, α₁ ++ γ⟩, Step.read e, by simp [emb₂]⟩
    | eps hδ =>
      rename_i q' α
      have hδ' : (P₂.δ q none Z).map (fun r => (some (Sum.inr r.1),
          r.2.map (some ∘ Sum.inr))) = some (q', α) := hδ
      rcases e : P₂.δ q none Z with _ | ⟨q₁, α₁⟩
      · simp [e] at hδ'
      · simp only [e, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hδ'
        obtain ⟨rfl, rfl⟩ := hδ'
        exact ⟨⟨q₁, w, α₁ ++ γ⟩, Step.eps e, by simp [emb₂]⟩

lemma reach_emb₁ {c : P₁.Cfg} {d : (tagDPDA P₁ P₂).Cfg}
    (h : Relation.ReflTransGen (tagDPDA P₁ P₂).Step (emb₁ P₁ P₂ c) d) :
    ∃ c', Relation.ReflTransGen P₁.Step c c' ∧ d = emb₁ P₁ P₂ c' := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail _ hst ih =>
    obtain ⟨c', h1, rfl⟩ := ih
    obtain ⟨c'', h2, rfl⟩ := emb₁_step P₁ P₂ hst
    exact ⟨c'', h1.tail h2, rfl⟩

lemma reach_emb₂ {c : P₂.Cfg} {d : (tagDPDA P₁ P₂).Cfg}
    (h : Relation.ReflTransGen (tagDPDA P₁ P₂).Step (emb₂ P₁ P₂ c) d) :
    ∃ c', Relation.ReflTransGen P₂.Step c c' ∧ d = emb₂ P₁ P₂ c' := by
  induction h with
  | refl => exact ⟨c, .refl, rfl⟩
  | tail _ hst ih =>
    obtain ⟨c', h1, rfl⟩ := ih
    obtain ⟨c'', h2, rfl⟩ := emb₂_step P₁ P₂ hst
    exact ⟨c'', h1.tail h2, rfl⟩

lemma emb₁_reach {c c' : P₁.Cfg} (h : Relation.ReflTransGen P₁.Step c c') :
    Relation.ReflTransGen (tagDPDA P₁ P₂).Step (emb₁ P₁ P₂ c) (emb₁ P₁ P₂ c') := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (step_emb₁ P₁ P₂ hst)

lemma emb₂_reach {c c' : P₂.Cfg} (h : Relation.ReflTransGen P₂.Step c c') :
    Relation.ReflTransGen (tagDPDA P₁ P₂).Step (emb₂ P₁ P₂ c) (emb₂ P₁ P₂ c') := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih => exact ih.tail (step_emb₂ P₁ P₂ hst)

lemma tag_accepts_nil : ¬ (tagDPDA P₁ P₂).Accepts [] := by
  rintro ⟨q, γ, hq, h⟩
  rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hst, -⟩
  · simp only [Cfg.mk.injEq] at h
    rw [← h.1] at hq
    rcases hq with ⟨q₁, -, e⟩ | ⟨q₂, -, e⟩ <;> simp [tagDPDA] at e
  · cases hst with
    | eps hδ => simp [tagDPDA, tagδ] at hδ

lemma tag_accepts_false (y : Word) : (tagDPDA P₁ P₂).Accepts (false :: y) ↔ P₁.Accepts y := by
  constructor
  · rintro ⟨q, γ, hq, h⟩
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hst, hrest⟩
    · simp at h
    · cases hst with
      | read hδ =>
        simp only [tagDPDA, tagδ, Option.some.injEq, Prod.mk.injEq] at hδ
        obtain ⟨rfl, rfl⟩ := hδ
        obtain ⟨c', h1, e⟩ := reach_emb₁ P₁ P₂ (c := ⟨P₁.start, y, [P₁.bottom]⟩) hrest
        simp only [emb₁, Cfg.mk.injEq] at e
        obtain ⟨rfl, he, rfl⟩ := e
        rcases hq with ⟨q₁, hq₁, e⟩ | ⟨q₂, -, e⟩
        · simp only [Option.some.injEq, Sum.inl.injEq] at e
          obtain ⟨q₀, i₀, γ₀⟩ := c'
          simp only at e he
          subst e
          subst he
          exact ⟨q₀, γ₀, hq₁, h1⟩
        · simp at e
      | eps hδ => simp [tagDPDA, tagδ] at hδ
  · rintro ⟨q, γ, hq, h⟩
    refine ⟨some (.inl q), γ.map (some ∘ Sum.inl), Or.inl ⟨q, hq, rfl⟩, ?_⟩
    refine Relation.ReflTransGen.head (Step.read (M := tagDPDA P₁ P₂) (Z := none) (γ := [])
      (q := none) (a := false) (w := y) (q' := some (.inl P₁.start))
      (α := [some (.inl P₁.bottom)]) rfl) ?_
    exact emb₁_reach P₁ P₂ (c := ⟨P₁.start, y, [P₁.bottom]⟩) (c' := ⟨q, [], γ⟩) h

lemma tag_accepts_true (y : Word) : (tagDPDA P₁ P₂).Accepts (true :: y) ↔ P₂.Accepts y := by
  constructor
  · rintro ⟨q, γ, hq, h⟩
    rcases Relation.ReflTransGen.cases_head h with h | ⟨c, hst, hrest⟩
    · simp at h
    · cases hst with
      | read hδ =>
        simp only [tagDPDA, tagδ, Option.some.injEq, Prod.mk.injEq] at hδ
        obtain ⟨rfl, rfl⟩ := hδ
        obtain ⟨c', h1, e⟩ := reach_emb₂ P₁ P₂ (c := ⟨P₂.start, y, [P₂.bottom]⟩) hrest
        simp only [emb₂, Cfg.mk.injEq] at e
        obtain ⟨rfl, he, rfl⟩ := e
        rcases hq with ⟨q₁, -, e⟩ | ⟨q₂, hq₂, e⟩
        · simp at e
        · simp only [Option.some.injEq, Sum.inr.injEq] at e
          obtain ⟨q₀, i₀, γ₀⟩ := c'
          simp only at e he
          subst e
          subst he
          exact ⟨q₀, γ₀, hq₂, h1⟩
      | eps hδ => simp [tagDPDA, tagδ] at hδ
  · rintro ⟨q, γ, hq, h⟩
    refine ⟨some (.inr q), γ.map (some ∘ Sum.inr), Or.inr ⟨q, hq, rfl⟩, ?_⟩
    refine Relation.ReflTransGen.head (Step.read (M := tagDPDA P₁ P₂) (Z := none) (γ := [])
      (q := none) (a := true) (w := y) (q' := some (.inr P₂.start))
      (α := [some (.inr P₂.bottom)]) rfl) ?_
    exact emb₂_reach P₁ P₂ (c := ⟨P₂.start, y, [P₂.bottom]⟩) (c' := ⟨q, [], γ⟩) h

end Tag

end DPDA

/-- The language `{[true]}` is deterministic context-free. -/
theorem DCFL_single : ({[true]} : Language) ∈ DCFL :=
  ⟨DPDA.single, fun w => by rw [DPDA.single_accepts]; rfl⟩

/-- Deterministic context-free languages are closed under tagged unions. -/
theorem DCFL_tagU {D₁ D₂ : Language} (h₁ : D₁ ∈ DCFL) (h₂ : D₂ ∈ DCFL) : tagU D₁ D₂ ∈ DCFL := by
  obtain ⟨P₁, hP₁⟩ := h₁
  obtain ⟨P₂, hP₂⟩ := h₂
  refine ⟨DPDA.tagDPDA P₁ P₂, fun w => ?_⟩
  rcases w with _ | ⟨b, y⟩
  · simp only [nil_not_mem_tagU, false_iff]; exact DPDA.tag_accepts_nil P₁ P₂
  · rw [cons_mem_tagU]
    cases b
    · simp only [Bool.false_eq_true, if_false]; rw [DPDA.tag_accepts_false, hP₁]
    · simp only [if_true]; rw [DPDA.tag_accepts_true, hP₂]

/-- Every logspace language is in `LogDCFL`. -/
theorem ClassL_subset_LogDCFL {A : Language} (hA : A ∈ ClassL) : A ∈ LogDCFL :=
  ⟨{[true]}, DCFL_single, charWord A, hA, fun w => by
    simp [charWord, Set.mem_singleton_iff]⟩

end PathChecking
