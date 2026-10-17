module

public import Mathlib

/-!
# Positional trees

A *positional tree* describes the syntax tree of a formula written in prefix notation by its
token positions: `nd p` says that a subformula starts at position `p`, `fe p` is the position
just after it and `ar p ∈ {0,1,2}` is its arity.  The children of a node `p` are `p + 1` (arity
`≥ 1`) and `fe (p + 1)` (arity `2`).  The root is position `1` and `[1, F)` is the formula.

We develop the combinatorics needed for tree contraction: nesting of subtrees, ancestors,
leaf indices (`lix`), the leaves of a subtree (`Cont`), for a set `S` of leaves the alive nodes
and the `down` map (the deepest descendant with the same `S`-leaves).
-/

@[expose] public section

namespace PathChecking

/-- A positional tree. -/
structure PT where
  F : ℕ
  nd : ℕ → Bool
  ar : ℕ → ℕ
  fe : ℕ → ℕ
  nd_one : nd 1 = true
  fe_one : fe 1 = F
  nd_ge : ∀ p, nd p = true → 1 ≤ p
  lt_fe : ∀ p, nd p = true → p < fe p
  fe_le : ∀ p, nd p = true → fe p ≤ F
  ar_le : ∀ p, nd p = true → ar p ≤ 2
  leaf_nd : ∀ p, nd p = true → ar p = 0 → ∀ q, p < q → q < fe p → nd q = false
  un : ∀ p, nd p = true → ar p = 1 → nd (p + 1) = true ∧ fe (p + 1) = fe p
  bin : ∀ p, nd p = true → ar p = 2 →
    nd (p + 1) = true ∧ nd (fe (p + 1)) = true ∧ fe (fe (p + 1)) = fe p

namespace PT

variable (T : PT)

/-- Second child. -/
def c2 (p : ℕ) : ℕ := T.fe (p + 1)

/-- Leaves. -/
def leaf (p : ℕ) : Bool := T.nd p && T.ar p == 0

variable {T}

lemma lt_F {p : ℕ} (h : T.nd p = true) : p < T.F := lt_of_lt_of_le (T.lt_fe p h) (T.fe_le p h)

/-- **Nesting of subtrees.** -/
theorem nest : ∀ m p, T.fe p - p = m → T.nd p = true → ∀ q, T.nd q = true → p < q → q < T.fe p →
    T.fe q ≤ T.fe p := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hm hp q hq hpq hqf
    have har := T.ar_le p hp
    rcases (show T.ar p = 0 ∨ T.ar p = 1 ∨ T.ar p = 2 by omega) with h0 | h1 | h2
    · exact absurd hq (by rw [T.leaf_nd p hp h0 q hpq hqf]; simp)
    · obtain ⟨hc, hfe⟩ := T.un p hp h1
      by_cases hq1 : q = p + 1
      · subst hq1; rw [hfe]
      · rw [← hfe]
        exact ih _ (by have := T.lt_fe p hp; omega) (p + 1) rfl hc q hq (by omega) (by omega)
    · obtain ⟨hc, hc2, hfe⟩ := T.bin p hp h2
      have l1 := T.lt_fe (p + 1) hc
      have l2 := T.lt_fe _ hc2
      by_cases hq1 : q = p + 1
      · subst hq1; omega
      by_cases hq2 : q < T.fe (p + 1)
      · have := ih _ (by omega) (p + 1) rfl hc q hq (by omega) hq2; omega
      by_cases hq3 : q = T.fe (p + 1)
      · subst hq3; omega
      · rw [← hfe]
        exact ih _ (by omega) _ rfl hc2 q hq (by omega) (by omega)

lemma fe_le_fe {p q : ℕ} (hp : T.nd p = true) (hq : T.nd q = true) (hpq : p ≤ q)
    (hqf : q < T.fe p) : T.fe q ≤ T.fe p := by
  rcases eq_or_lt_of_le hpq with rfl | h
  · exact le_rfl
  · exact nest _ p rfl hp q hq h hqf

/-- `p` is an ancestor of `q` (or `p = q`). -/
def Anc (p q : ℕ) : Prop := T.nd p = true ∧ T.nd q = true ∧ p ≤ q ∧ q < T.fe p

lemma Anc.refl {p : ℕ} (hp : T.nd p = true) : T.Anc p p := ⟨hp, hp, le_rfl, T.lt_fe p hp⟩

lemma Anc.trans {p q r : ℕ} (h1 : T.Anc p q) (h2 : T.Anc q r) : T.Anc p r := by
  refine ⟨h1.1, h2.2.1, le_trans h1.2.2.1 h2.2.2.1, ?_⟩
  have := fe_le_fe h1.1 h1.2.1 h1.2.2.1 h1.2.2.2
  exact lt_of_lt_of_le h2.2.2.2 this

lemma Anc.fe_le {p q : ℕ} (h : T.Anc p q) : T.fe q ≤ T.fe p :=
  fe_le_fe h.1 h.2.1 h.2.2.1 h.2.2.2

/-- Ancestors of a node form a chain. -/
lemma Anc.chain {p p' q : ℕ} (h : T.Anc p q) (h' : T.Anc p' q) (hpp : p ≤ p') : T.Anc p p' :=
  ⟨h.1, h'.1, hpp, by have := h.2.2.2; have := h'.2.2.1; omega⟩

/-- Two subtrees are nested or disjoint. -/
lemma nested_or_disjoint {p q : ℕ} (hp : T.nd p = true) (hq : T.nd q = true) (hpq : p ≤ q) :
    T.Anc p q ∨ T.fe p ≤ q := by
  by_cases h : q < T.fe p
  · exact Or.inl ⟨hp, hq, hpq, h⟩
  · exact Or.inr (by omega)

/-- A proper descendant lies below one of the children. -/
lemma desc_cases {p q : ℕ} (hp : T.nd p = true) (hq : T.nd q = true) (hpq : p < q)
    (hqf : q < T.fe p) :
    (T.ar p = 1 ∨ T.ar p = 2) ∧ T.Anc (p + 1) q ∨ T.ar p = 2 ∧ T.Anc (T.c2 p) q := by
  have har := T.ar_le p hp
  rcases (show T.ar p = 0 ∨ T.ar p = 1 ∨ T.ar p = 2 by omega) with h0 | h1 | h2
  · exact absurd hq (by rw [T.leaf_nd p hp h0 q hpq hqf]; simp)
  · obtain ⟨hc, hfe⟩ := T.un p hp h1
    exact Or.inl ⟨Or.inl h1, hc, hq, by omega, by rw [hfe]; exact hqf⟩
  · obtain ⟨hc, hc2, hfe⟩ := T.bin p hp h2
    by_cases hq2 : q < T.fe (p + 1)
    · exact Or.inl ⟨Or.inr h2, hc, hq, by omega, hq2⟩
    · exact Or.inr ⟨h2, hc2, hq, by unfold c2; omega, by unfold c2; rw [hfe]; exact hqf⟩

/-! ## Leaves and leaf indices -/

/-- Every subtree contains a leaf. -/
theorem exists_leaf : ∀ m p, T.fe p - p = m → T.nd p = true →
    ∃ q, T.leaf q = true ∧ T.Anc p q := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hm hp
    have har := T.ar_le p hp
    rcases (show T.ar p = 0 ∨ 1 ≤ T.ar p by omega) with h0 | h1
    · exact ⟨p, by simp [leaf, hp, h0], Anc.refl hp⟩
    · have hc : T.nd (p + 1) = true ∧ T.fe (p + 1) ≤ T.fe p := by
        rcases (show T.ar p = 1 ∨ T.ar p = 2 by omega) with e | e
        · exact ⟨(T.un p hp e).1, (T.un p hp e).2.le⟩
        · obtain ⟨a, b, c⟩ := T.bin p hp e
          exact ⟨a, by have := T.lt_fe _ b; omega⟩
      have := T.lt_fe (p + 1) hc.1
      obtain ⟨q, hq, ha⟩ := ih _ (by omega) (p + 1) rfl hc.1
      exact ⟨q, hq, (show T.Anc p (p + 1) from ⟨hp, hc.1, by omega, by omega⟩).trans ha⟩

/-- Number of leaves before position `p`. -/
def lix (p : ℕ) : ℕ := ((List.range p).filter fun q => T.leaf q).length

lemma lix_succ (p : ℕ) : T.lix (p + 1) = T.lix p + if T.leaf p then 1 else 0 := by
  unfold lix
  rw [List.range_succ, List.filter_append]
  by_cases h : T.leaf p <;> simp [h]

lemma lix_mono {p q : ℕ} (h : p ≤ q) : T.lix p ≤ T.lix q := by
  induction q with
  | zero => have : p = 0 := by omega
            subst this; rfl
  | succ q ih =>
    rcases eq_or_lt_of_le h with rfl | h'
    · rfl
    · have := ih (by omega); rw [lix_succ]; omega

lemma lix_lt_of_leaf {p q : ℕ} (hp : T.leaf p = true) (hpq : p < q) : T.lix p < T.lix q := by
  have := lix_mono (T := T) (show p + 1 ≤ q by omega)
  rw [lix_succ, if_pos hp] at this; omega

lemma leaf_nd' {p : ℕ} (h : T.leaf p = true) : T.nd p = true := by
  simp [leaf] at h; exact h.1

lemma leaf_ar {p : ℕ} (h : T.leaf p = true) : T.ar p = 0 := by
  simp [leaf] at h; exact h.2

lemma lix_fe_leaf {p : ℕ} (hp : T.leaf p = true) : T.lix (T.fe p) = T.lix p + 1 := by
  have hn := leaf_nd' hp
  have key : ∀ j, p + 1 + j ≤ T.fe p → T.lix (p + 1 + j) = T.lix p + 1 := by
    intro j
    induction j with
    | zero => intro; rw [Nat.add_zero, lix_succ, if_pos hp]
    | succ j ih =>
      intro hj
      rw [show p + 1 + (j + 1) = (p + 1 + j) + 1 by omega, lix_succ, ih (by omega)]
      have : T.leaf (p + 1 + j) = false := by
        simp [leaf, T.leaf_nd p hn (leaf_ar hp) (p + 1 + j) (by omega) (by omega)]
      simp [this]
  have := key (T.fe p - (p + 1)) (by have := T.lt_fe p hn; omega)
  rwa [show p + 1 + (T.fe p - (p + 1)) = T.fe p by have := T.lt_fe p hn; omega] at this

/-- `y` contains the leaf with index `k`. -/
def Cont (y k : ℕ) : Prop := T.lix y ≤ k ∧ k < T.lix (T.fe y)

lemma lix_lt_fe {p : ℕ} (hp : T.nd p = true) : T.lix p < T.lix (T.fe p) := by
  obtain ⟨q, hq, ha⟩ := exists_leaf _ p rfl hp
  have h1 := lix_mono (T := T) ha.2.2.1
  have h2 := lix_lt_of_leaf hq ha.2.2.2
  omega

/-- A leaf `q` is contained in `y` iff `y` is an ancestor of `q`. -/
lemma cont_leaf_iff {y q : ℕ} (hy : T.nd y = true) (hq : T.leaf q = true) :
    T.Cont y (T.lix q) ↔ T.Anc y q := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hy, leaf_nd' hq, ?_, ?_⟩
    · by_contra h
      have := lix_lt_of_leaf hq (show q < y by omega); omega
    · by_contra h
      have := lix_mono (T := T) (show T.fe y ≤ q by omega); omega
  · rintro ⟨-, -, h1, h2⟩
    refine ⟨lix_mono h1, ?_⟩
    have := lix_mono (T := T) (show q + 1 ≤ T.fe y by omega)
    rw [lix_succ, if_pos hq] at this; omega

/-- Total number of leaves. -/
def L : ℕ := T.lix T.F

/-- Every leaf index below `L` belongs to a leaf. -/
theorem exists_leaf_of_lt {k : ℕ} (hk : k < T.L) : ∃ q, T.leaf q = true ∧ T.lix q = k := by
  -- the first position `p` with `k < lix (p+1)`
  have hex : ∃ p, k < T.lix (p + 1) := ⟨T.F, lt_of_lt_of_le hk (lix_mono (by omega))⟩
  classical
  let p := Nat.find hex
  have hp : k < T.lix (p + 1) := Nat.find_spec hex
  have hmin : ¬ k < T.lix p := by
    intro h
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0] at h; simp [lix] at h
    · have := Nat.find_min hex (show p - 1 < p by omega)
      rw [show p - 1 + 1 = p by omega] at this; exact this h
  rw [lix_succ] at hp
  by_cases hl : T.leaf p = true
  · exact ⟨p, hl, by rw [if_pos hl] at hp; omega⟩
  · rw [if_neg hl] at hp; exact absurd hp hmin

lemma lix_inj_leaf {p q : ℕ} (hp : T.leaf p = true) (hq : T.leaf q = true)
    (h : T.lix p = T.lix q) : p = q := by
  rcases lt_trichotomy p q with h' | h' | h'
  · have := lix_lt_of_leaf hp h'; omega
  · exact h'
  · have := lix_lt_of_leaf hq h'; omega

lemma lix_lt_L_of_leaf {q : ℕ} (hq : T.leaf q = true) : T.lix q < T.L :=
  lix_lt_of_leaf hq (lt_F (leaf_nd' hq))

/-- Containment of leaf indices is an interval, nested along ancestors. -/
lemma Anc.cont {p q k : ℕ} (h : T.Anc p q) (hk : T.Cont q k) : T.Cont p k :=
  ⟨le_trans (lix_mono h.2.2.1) hk.1, lt_of_lt_of_le hk.2 (lix_mono h.fe_le)⟩

/-- Leaves of the children. -/
lemma cont_un {p k : ℕ} (hp : T.nd p = true) (h1 : T.ar p = 1) :
    T.Cont p k ↔ T.Cont (p + 1) k := by
  have hnl : T.leaf p = false := by simp [leaf, h1]
  unfold Cont
  rw [lix_succ, if_neg (by simp [hnl]), (T.un p hp h1).2]; simp

lemma cont_bin {p k : ℕ} (hp : T.nd p = true) (h2 : T.ar p = 2) :
    T.Cont p k ↔ T.Cont (p + 1) k ∨ T.Cont (T.c2 p) k := by
  have hnl : T.leaf p = false := by simp [leaf, h2]
  obtain ⟨hc1, hc2, hfe⟩ := T.bin p hp h2
  have e1 : T.lix (p + 1) = T.lix p := by rw [lix_succ, if_neg (by simp [hnl])]; simp
  have m1 : T.lix (p + 1) ≤ T.lix (T.fe (p + 1)) := lix_mono (le_of_lt (T.lt_fe _ hc1))
  have m2 : T.lix (T.fe (p + 1)) ≤ T.lix (T.fe p) :=
    lix_mono (by rw [← hfe]; exact le_of_lt (T.lt_fe _ hc2))
  unfold Cont c2; rw [hfe]; omega

lemma cont_c2_not_c1 {p k : ℕ} (hp : T.nd p = true) (h2 : T.ar p = 2) :
    ¬ (T.Cont (p + 1) k ∧ T.Cont (T.c2 p) k) := by
  rintro ⟨⟨_, a⟩, ⟨b, _⟩⟩
  unfold c2 at b; omega

end PT

end PathChecking
