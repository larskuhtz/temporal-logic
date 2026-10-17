module

public import Mathlib

/-!
# Layered monotone planar circuits

An abstract description of a stratified monotone planar circuit in standard (layered) form, in
the style of [BLMS99, Section 2].  Gates are natural numbers.  The gates of layer `l` are the
numbers in `[bd l, bd (l + 1))`; layer `0` is the input layer.  A gate `i` of a layer `l ≥ 1` is
an `AND` gate (`isAnd i = true`) or an `OR` gate with arguments `lo i ≤ hi i` (a `COPY` gate is a
gate with `lo i = hi i`).  Planarity: if `i < i'` are gates of the same layer, then
`hi i ≤ lo i'`.

`ev l S` is the set of true gates of layer `l` when the set of true input gates is `S`, and
`out S` says that some gate of the last layer `D` is true.

We prove the basic facts about one evaluation step used in the analysis of the algorithm of
[BLMS99, Section 5]: monotonicity, the image of a convex set is convex, a gate whose arguments
enclose a set kills it, and the right (left) end of the image of a convex set bounds the image of
everything to its left (right).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

open Set

/-- A layered monotone circuit. -/
structure LC where
  isAnd : ℕ → Bool
  lo : ℕ → ℕ
  hi : ℕ → ℕ
  bd : ℕ → ℕ
  D : ℕ

namespace LC

variable (c : LC)

/-- Value of gate `i` if the set of true gates of the previous layer is `S`. -/
def gval (S : Set ℕ) (i : ℕ) : Prop :=
  if c.isAnd i = true then c.lo i ∈ S ∧ c.hi i ∈ S else c.lo i ∈ S ∨ c.hi i ∈ S

/-- The gates of layer `l + 1`. -/
def gates (l : ℕ) : Set ℕ := Ico (c.bd (l + 1)) (c.bd (l + 2))

/-- One evaluation step: from layer `l` to layer `l + 1`. -/
def step (l : ℕ) (S : Set ℕ) : Set ℕ := {i | i ∈ c.gates l ∧ c.gval S i}

/-- The true gates of layer `l`. -/
def ev : ℕ → Set ℕ → Set ℕ
  | 0, S => S
  | l + 1, S => c.step l (ev l S)

/-- The circuit accepts the input `S` if some gate of the last layer is true. -/
def out (S : Set ℕ) : Prop := (c.ev c.D S).Nonempty

/-- Planarity (and `lo ≤ hi`) of all layers. -/
structure Planar : Prop where
  le : ∀ l < c.D, ∀ i ∈ c.gates l, c.lo i ≤ c.hi i
  mono : ∀ l < c.D, ∀ i ∈ c.gates l, ∀ i' ∈ c.gates l, i < i' → c.hi i ≤ c.lo i'

variable {c}

@[simp] lemma ev_zero (S : Set ℕ) : c.ev 0 S = S := rfl
@[simp] lemma ev_succ (l : ℕ) (S : Set ℕ) : c.ev (l + 1) S = c.step l (c.ev l S) := rfl

lemma gval_mono {S T : Set ℕ} (h : S ⊆ T) {i : ℕ} (hi : c.gval S i) : c.gval T i := by
  unfold gval at *
  split_ifs at * with hA
  · exact ⟨h hi.1, h hi.2⟩
  · rcases hi with hi | hi
    · exact Or.inl (h hi)
    · exact Or.inr (h hi)

lemma step_mono {S T : Set ℕ} (h : S ⊆ T) (l : ℕ) : c.step l S ⊆ c.step l T :=
  fun _ hi => ⟨hi.1, gval_mono h hi.2⟩

lemma ev_mono {S T : Set ℕ} (h : S ⊆ T) : ∀ l, c.ev l S ⊆ c.ev l T
  | 0 => h
  | l + 1 => step_mono (ev_mono h l) l

lemma step_empty (l : ℕ) : c.step l ∅ = ∅ := by
  ext i; simp only [step, gval, mem_setOf_eq, mem_empty_iff_false, or_self,
    ite_self, and_false]

lemma ev_empty : ∀ l, c.ev l ∅ = ∅
  | 0 => rfl
  | l + 1 => by rw [ev_succ, ev_empty l, step_empty]

/-- `ev` from layer `l` on only depends on the value at layer `l`. -/
lemma ev_congr {S T : Set ℕ} {l : ℕ} (h : c.ev l S = c.ev l T) : ∀ k, l ≤ k → c.ev k S = c.ev k T
  | k, hk => by
    induction k with
    | zero =>
      have : l = 0 := by omega
      subst this; exact h
    | succ k ih =>
      rcases Nat.lt_or_ge l (k + 1) with h1 | h1
      · rw [ev_succ, ev_succ, ih (by omega)]
      · have : l = k + 1 := by omega
        subst this; exact h

lemma out_mono {S T : Set ℕ} (h : S ⊆ T) (hS : c.out S) : c.out T :=
  hS.mono (ev_mono h _)

lemma out_empty : ¬ c.out ∅ := by
  simp [out, ev_empty]

lemma ev_succ_subset_gates (l : ℕ) (S : Set ℕ) : c.ev (l + 1) S ⊆ c.gates l :=
  fun _ hi => hi.1

/-- If no `AND` gate has its arguments split between `S` and `T`, then evaluation commutes with
union. -/
lemma step_union {S T : Set ℕ} {l : ℕ}
    (h : ∀ i ∈ c.gates l, c.isAnd i = true → c.lo i ∈ S ∪ T → c.hi i ∈ S ∪ T →
      (c.lo i ∈ S ∧ c.hi i ∈ S) ∨ (c.lo i ∈ T ∧ c.hi i ∈ T)) :
    c.step l (S ∪ T) = c.step l S ∪ c.step l T := by
  ext i
  simp only [step, mem_union, mem_setOf_eq, gval]
  constructor
  · rintro ⟨hg, hv⟩
    split_ifs at hv with hA
    · rcases h i hg hA hv.1 hv.2 with h' | h'
      · exact Or.inl ⟨hg, by simp [hA, h']⟩
      · exact Or.inr ⟨hg, by simp [hA, h']⟩
    · simp only [hA] at *
      rcases hv with (hv | hv) | (hv | hv)
      · exact Or.inl ⟨hg, by simp [hv]⟩
      · exact Or.inr ⟨hg, by simp [hv]⟩
      · exact Or.inl ⟨hg, by simp [hv]⟩
      · exact Or.inr ⟨hg, by simp [hv]⟩
  · rintro (⟨hg, hv⟩ | ⟨hg, hv⟩) <;> refine ⟨hg, ?_⟩ <;> split_ifs at hv ⊢ <;> tauto

section Planar

variable (hP : c.Planar) {l : ℕ} (hl : l < c.D)
include hP hl

/-- A gate whose arguments enclose `X` kills `X`. -/
lemma step_eq_empty_of_span {X : Set ℕ} {i : ℕ} (hi : i ∈ c.gates l)
    (hX : X ⊆ Ioo (c.lo i) (c.hi i)) : c.step l X = ∅ := by
  ext j
  simp only [step, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
  intro hj hv
  have hlo : c.lo j ∉ X ∧ c.hi j ∉ X := by
    rcases lt_trichotomy j i with h | rfl | h
    · have h1 := hP.mono l hl j hj i hi h
      have h2 := hP.le l hl j hj
      constructor <;> intro hx <;> have := hX hx <;> simp at this <;> omega
    · constructor <;> intro hx <;> have := hX hx <;> simp at this
    · have h1 := hP.mono l hl i hi j hj h
      have h2 := hP.le l hl j hj
      constructor <;> intro hx <;> have := hX hx <;> simp at this <;> omega
  unfold gval at hv
  split_ifs at hv <;> tauto

/-- The image of a convex set is convex. -/
lemma step_ordConnected {X : Set ℕ} (hX : X.OrdConnected) : (c.step l X).OrdConnected := by
  refine ⟨fun a ha b hb z hz => ?_⟩
  obtain ⟨haz, hzb⟩ := hz
  have hzg : z ∈ c.gates l := ⟨le_trans ha.1.1 haz, lt_of_le_of_lt hzb hb.1.2⟩
  rcases eq_or_lt_of_le haz with rfl | haz'
  · exact ha
  rcases eq_or_lt_of_le hzb with rfl | hzb'
  · exact hb
  have h1 := hP.mono l hl a ha.1 z hzg haz'
  have h2 := hP.mono l hl z hzg b hb.1 hzb'
  have hla := hP.le l hl a ha.1
  have hlz := hP.le l hl z hzg
  have hlb := hP.le l hl b hb.1
  have hxa : ∃ x ∈ X, x ≤ c.lo z := by
    have := ha.2; unfold gval at this
    split_ifs at this
    · exact ⟨c.hi a, this.2, h1⟩
    · rcases this with h | h
      · exact ⟨c.lo a, h, by omega⟩
      · exact ⟨c.hi a, h, h1⟩
  have hxb : ∃ x ∈ X, c.hi z ≤ x := by
    have := hb.2; unfold gval at this
    split_ifs at this
    · exact ⟨c.lo b, this.1, h2⟩
    · rcases this with h | h
      · exact ⟨c.lo b, h, h2⟩
      · exact ⟨c.hi b, h, by omega⟩
  obtain ⟨x, hx, hxz⟩ := hxa
  obtain ⟨y, hy, hzy⟩ := hxb
  have hlo : c.lo z ∈ X := hX.out hx hy ⟨hxz, by omega⟩
  have hhi : c.hi z ∈ X := hX.out hx hy ⟨by omega, hzy⟩
  exact ⟨hzg, by unfold gval; split_ifs <;> simp [hlo, hhi]⟩

/-- Right bound: if every element of `S` is at most some element of the convex set `X`, then
every element of the image of `S` is at most some element of the (nonempty) image of `X`. -/
lemma step_right_bound {X S : Set ℕ} (hX : X.OrdConnected) (hne : (c.step l X).Nonempty)
    (hS : ∀ z ∈ S, ∃ x ∈ X, z ≤ x) : ∀ z ∈ c.step l S, ∃ y ∈ c.step l X, z ≤ y := by
  intro z hz
  obtain ⟨m, hm⟩ := hne
  rcases le_or_gt z m with h | h
  · exact ⟨m, hm, h⟩
  refine ⟨z, ?_, le_rfl⟩
  have h1 := hP.mono l hl m hm.1 z hz.1 h
  have hlz := hP.le l hl z hz.1
  have hlm := hP.le l hl m hm.1
  have hxm : ∃ x ∈ X, x ≤ c.hi m := by
    have := hm.2; unfold gval at this
    split_ifs at this
    · exact ⟨c.hi m, this.2, le_rfl⟩
    · rcases this with h | h
      · exact ⟨c.lo m, h, hlm⟩
      · exact ⟨c.hi m, h, le_rfl⟩
  obtain ⟨x, hx, hxm⟩ := hxm
  refine ⟨hz.1, ?_⟩
  have hv := hz.2
  unfold gval at hv ⊢
  split_ifs at hv ⊢
  · obtain ⟨y, hy, hhy⟩ := hS _ hv.2
    exact ⟨hX.out hx hy ⟨by omega, by omega⟩, hX.out hx hy ⟨by omega, hhy⟩⟩
  · rcases hv with hv | hv
    · obtain ⟨y, hy, hhy⟩ := hS _ hv
      exact Or.inl (hX.out hx hy ⟨by omega, hhy⟩)
    · obtain ⟨y, hy, hhy⟩ := hS _ hv
      exact Or.inr (hX.out hx hy ⟨by omega, hhy⟩)

/-- Left bound: the mirror image of `step_right_bound`. -/
lemma step_left_bound {X S : Set ℕ} (hX : X.OrdConnected) (hne : (c.step l X).Nonempty)
    (hS : ∀ z ∈ S, ∃ x ∈ X, x ≤ z) : ∀ z ∈ c.step l S, ∃ y ∈ c.step l X, y ≤ z := by
  intro z hz
  obtain ⟨m, hm⟩ := hne
  rcases le_or_gt m z with h | h
  · exact ⟨m, hm, h⟩
  refine ⟨z, ?_, le_rfl⟩
  have h1 := hP.mono l hl z hz.1 m hm.1 h
  have hlz := hP.le l hl z hz.1
  have hlm := hP.le l hl m hm.1
  have hxm : ∃ x ∈ X, c.lo m ≤ x := by
    have := hm.2; unfold gval at this
    split_ifs at this
    · exact ⟨c.lo m, this.1, le_rfl⟩
    · rcases this with h | h
      · exact ⟨c.lo m, h, le_rfl⟩
      · exact ⟨c.hi m, h, hlm⟩
  obtain ⟨x, hx, hxm⟩ := hxm
  refine ⟨hz.1, ?_⟩
  have hv := hz.2
  unfold gval at hv ⊢
  split_ifs at hv ⊢
  · obtain ⟨y, hy, hhy⟩ := hS _ hv.1
    exact ⟨hX.out hy hx ⟨hhy, by omega⟩, hX.out hy hx ⟨by omega, by omega⟩⟩
  · rcases hv with hv | hv
    · obtain ⟨y, hy, hhy⟩ := hS _ hv
      exact Or.inl (hX.out hy hx ⟨hhy, by omega⟩)
    · obtain ⟨y, hy, hhy⟩ := hS _ hv
      exact Or.inr (hX.out hy hx ⟨hhy, by omega⟩)

end Planar

lemma ev_ordConnected (hP : c.Planar) {X : Set ℕ} (hX : X.OrdConnected) :
    ∀ l, l ≤ c.D → (c.ev l X).OrdConnected
  | 0, _ => hX
  | l + 1, h => step_ordConnected hP (by omega) (ev_ordConnected hP hX l (by omega))

end LC

end BLMS

end PathChecking
