module

public import RequestProject.LTLPath.Tree

/-!
# Alive nodes, the `down` map and compressed parents

For a set `S` of leaf indices (a predicate on `ℕ`):

* `alive S y`: the subtree of `y` contains a leaf of `S`;
* `down S y`: the deepest descendant `z` of `y` whose subtree contains the same `S`-leaves;
* `par S k`: the deepest node containing the leaf `k` and another leaf of `S` (the parent of `k`
  in the tree compressed to `S`).

Main facts: `down` of a node with two alive children is the node itself (`down_branch`), `down`
of a node with exactly one alive child is `down` of that child (`down_single`), and `down` of a
leaf is the leaf.  The merge lemma `merge_dead`: if a child of a node `y` alive in `S \ D` loses
all its `S`-leaves, then `y` is the compressed parent of a leaf of `D` (provided the leaves of `D`
are separated by leaves of `S \ D`).
-/

@[expose] public section

namespace PathChecking

namespace PT

variable {T : PT}

open Classical

/-- `c` is a child of `y`. -/
def IsChild (T : PT) (y c : ℕ) : Prop :=
  T.nd y = true ∧ ((1 ≤ T.ar y ∧ c = y + 1) ∨ (T.ar y = 2 ∧ c = T.c2 y))

/-- The subtree of `y` contains a leaf of `S`. -/
def alive (T : PT) (S : ℕ → Prop) (y : ℕ) : Prop := ∃ k, S k ∧ T.Cont y k

/-- `y` and `z` contain the same leaves of `S`. -/
def SameS (T : PT) (S : ℕ → Prop) (y z : ℕ) : Prop := ∀ k, S k → (T.Cont y k ↔ T.Cont z k)

/-- The deepest descendant of `y` with the same `S`-leaves. -/
noncomputable def down (T : PT) (S : ℕ → Prop) (y : ℕ) : ℕ :=
  Nat.findGreatest (fun z => T.Anc y z ∧ T.SameS S y z) T.F

lemma IsChild.nd {y c : ℕ} (h : T.IsChild y c) : T.nd c = true := by
  rcases h with ⟨hy, ⟨_, rfl⟩ | ⟨h2, rfl⟩⟩
  · rcases (show T.ar y = 1 ∨ T.ar y = 2 by have := T.ar_le y hy; omega) with e | e
    · exact (T.un y hy e).1
    · exact (T.bin y hy e).1
  · exact (T.bin y hy h2).2.1

lemma IsChild.anc {y c : ℕ} (h : T.IsChild y c) : T.Anc y c := by
  have hc := h.nd
  rcases h with ⟨hy, ⟨h1, rfl⟩ | ⟨h2, rfl⟩⟩
  · refine ⟨hy, hc, by omega, ?_⟩
    rcases (show T.ar y = 1 ∨ T.ar y = 2 by have := T.ar_le y hy; omega) with e | e
    · rw [← (T.un y hy e).2]; exact T.lt_fe _ hc
    · obtain ⟨a, b, c⟩ := T.bin y hy e
      have := T.lt_fe _ a; have := T.lt_fe _ b; rw [c] at this; omega
  · obtain ⟨a, b, c⟩ := T.bin y hy h2
    have := T.lt_fe _ a; have := T.lt_fe _ b
    refine ⟨hy, hc, by unfold c2; omega, by unfold c2; rw [c] at this; omega⟩

lemma IsChild.lt {y c : ℕ} (h : T.IsChild y c) : y < c := by
  rcases h with ⟨hy, ⟨_, rfl⟩ | ⟨h2, rfl⟩⟩
  · omega
  · have := T.lt_fe _ (T.bin y hy h2).1; unfold c2; omega

lemma down_prop {S : ℕ → Prop} {y : ℕ} (hy : T.nd y = true) :
    T.Anc y (T.down S y) ∧ T.SameS S y (T.down S y) :=
  Nat.findGreatest_spec (P := fun z => T.Anc y z ∧ T.SameS S y z) (m := y) (lt_F hy).le
    ⟨Anc.refl hy, fun _ _ => Iff.rfl⟩

lemma le_down {S : ℕ → Prop} {y z : ℕ} (hz : T.Anc y z) (hs : T.SameS S y z) :
    z ≤ T.down S y :=
  Nat.le_findGreatest (P := fun z => T.Anc y z ∧ T.SameS S y z) (lt_F hz.2.1).le ⟨hz, hs⟩

/-- Characterisation of `down`. -/
lemma down_eq_iff {S : ℕ → Prop} {y z : ℕ} (hy : T.nd y = true) :
    T.down S y = z ↔ T.Anc y z ∧ T.SameS S y z ∧
      ∀ z', T.Anc y z' → T.SameS S y z' → z' ≤ z := by
  constructor
  · rintro rfl
    exact ⟨(down_prop hy).1, (down_prop hy).2, fun z' h1 h2 => le_down h1 h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact le_antisymm (h3 _ (down_prop hy).1 (down_prop hy).2) (le_down h1 h2)

/-- The children of a node cover its leaves. -/
lemma cont_child_cases {y k : ℕ} (hy : T.nd y = true) (hk : T.Cont y k) (hl : T.leaf y = false) :
    (T.IsChild y (y + 1) ∧ T.Cont (y + 1) k) ∨ (T.IsChild y (T.c2 y) ∧ T.Cont (T.c2 y) k) := by
  have har := T.ar_le y hy
  have h0 : T.ar y ≠ 0 := by intro h; simp [leaf, hy, h] at hl
  rcases (show T.ar y = 1 ∨ T.ar y = 2 by omega) with e | e
  · exact Or.inl ⟨⟨hy, Or.inl ⟨by omega, rfl⟩⟩, (cont_un hy e).1 hk⟩
  · rcases (cont_bin hy e).1 hk with h | h
    · exact Or.inl ⟨⟨hy, Or.inl ⟨by omega, rfl⟩⟩, h⟩
    · exact Or.inr ⟨⟨hy, Or.inr ⟨e, rfl⟩⟩, h⟩

/-- A proper descendant lies below a child. -/
lemma desc_child {y z : ℕ} (h : T.Anc y z) (hne : y ≠ z) : ∃ c, T.IsChild y c ∧ T.Anc c z := by
  rcases desc_cases h.1 h.2.1 (by have := h.2.2.1; omega) h.2.2.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨y + 1, ⟨h.1, Or.inl ⟨by omega, rfl⟩⟩, h2⟩
  · exact ⟨T.c2 y, ⟨h.1, Or.inr ⟨h1, rfl⟩⟩, h2⟩

/-- Different children have disjoint leaves. -/
lemma child_disjoint {y c c' k : ℕ} (hc : T.IsChild y c) (hc' : T.IsChild y c') (hne : c ≠ c')
    (h1 : T.Cont c k) (h2 : T.Cont c' k) : False := by
  rcases hc with ⟨hy, ⟨_, rfl⟩ | ⟨e, rfl⟩⟩ <;> rcases hc' with ⟨_, ⟨_, rfl⟩ | ⟨e', rfl⟩⟩
  · exact hne rfl
  · exact cont_c2_not_c1 hy e' ⟨h1, h2⟩
  · exact cont_c2_not_c1 hy e ⟨h2, h1⟩
  · exact hne rfl

/-- Children of a node are contained in it. -/
lemma IsChild.cont {y c k : ℕ} (h : T.IsChild y c) (hk : T.Cont c k) : T.Cont y k :=
  h.anc.cont hk

lemma child_unique_of_anc {y c c' z : ℕ} (hc : T.IsChild y c) (hc' : T.IsChild y c')
    (h1 : T.Anc c z) (h2 : T.Anc c' z) : c = c' := by
  by_contra hne
  obtain ⟨q, hq, ha⟩ := exists_leaf _ z rfl h1.2.1
  have k1 := (cont_leaf_iff hc.nd hq).2 (h1.trans ha)
  have k2 := (cont_leaf_iff hc'.nd hq).2 (h2.trans ha)
  exact child_disjoint hc hc' hne k1 k2

/-! ## `down` of branching and non-branching nodes -/

/-- **`down` of a node with two alive children.** -/
theorem down_branch {S : ℕ → Prop} {y c c' : ℕ} (hc : T.IsChild y c) (hc' : T.IsChild y c')
    (hne : c ≠ c') (ha : T.alive S c) (ha' : T.alive S c') : T.down S y = y := by
  have hy := hc.1
  rw [down_eq_iff hy]
  refine ⟨Anc.refl hy, fun _ _ => Iff.rfl, fun z hz hs => ?_⟩
  by_contra hlt
  obtain ⟨d, hd, hdz⟩ := desc_child hz (by omega)
  -- the child `d` misses the leaves of the other child
  obtain ⟨k, hkS, hk⟩ := ha
  obtain ⟨k', hkS', hk'⟩ := ha'
  have e1 := (hs k hkS).1 (hc.cont hk)
  have e2 := (hs k' hkS').1 (hc'.cont hk')
  have f1 := hdz.cont e1
  have f2 := hdz.cont e2
  have g1 : d = c := by
    by_contra h; exact child_disjoint hd hc h f1 hk
  have g2 : d = c' := by
    by_contra h; exact child_disjoint hd hc' h f2 hk'
  exact hne (g1.symm.trans g2)

lemma Cont.lt_L {y k : ℕ} (hy : T.nd y = true) (h : T.Cont y k) : k < T.L :=
  lt_of_lt_of_le h.2 (lix_mono (T.fe_le y hy))

/-- Two nodes containing the same leaf are comparable. -/
lemma anc_of_cont {y z k : ℕ} (hy : T.nd y = true) (hz : T.nd z = true) (h1 : T.Cont y k)
    (h2 : T.Cont z k) (hyz : y ≤ z) : T.Anc y z := by
  obtain ⟨q, hq, rfl⟩ := exists_leaf_of_lt (h1.lt_L hy)
  exact Anc.chain ((cont_leaf_iff hy hq).1 h1) ((cont_leaf_iff hz hq).1 h2) hyz

/-- **`down` of a node with a single alive child.** -/
theorem down_single {S : ℕ → Prop} {y c : ℕ} (hc : T.IsChild y c) (ha : T.alive S c)
    (hd : ∀ c', T.IsChild y c' → c' ≠ c → ¬ T.alive S c') : T.down S y = T.down S c := by
  have hy := hc.1
  have hcn := hc.nd
  have hsame : T.SameS S y c := by
    intro k hk
    refine ⟨fun h => ?_, fun h => hc.cont h⟩
    have hl : T.leaf y = false := by
      by_contra hl'
      have := hc.lt; have := hc.anc.2.2.2
      have := T.leaf_nd y hy (leaf_ar (by simpa using hl')) c (by omega) this
      rw [hcn] at this; exact absurd this (by simp)
    rcases cont_child_cases hy h hl with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · by_cases e : y + 1 = c
      · rwa [← e]
      · exact absurd ⟨k, hk, h2⟩ (hd _ h1 e)
    · by_cases e : T.c2 y = c
      · rwa [← e]
      · exact absurd ⟨k, hk, h2⟩ (hd _ h1 e)
  obtain ⟨d1, d2⟩ := down_prop (S := S) hcn
  rw [down_eq_iff hy]
  refine ⟨hc.anc.trans d1, fun k hk => (hsame k hk).trans (d2 k hk), fun z hz hs => ?_⟩
  by_cases hzy : z = y
  · subst hzy; have := hc.lt; have := d1.2.2.1; omega
  obtain ⟨d, hd', hdz⟩ := desc_child hz (Ne.symm hzy)
  obtain ⟨k, hk, hkc⟩ := ha
  have hkz := (hs k hk).1 (hc.cont hkc)
  have hdc : d = c := by
    by_contra h; exact child_disjoint hd' hc h (hdz.cont hkz) hkc
  subst hdc
  exact le_down hdz (fun k' hk' => (hsame k' hk').symm.trans (hs k' hk'))

/-- `down` of a leaf. -/
lemma down_leaf {S : ℕ → Prop} {y : ℕ} (hy : T.leaf y = true) : T.down S y = y := by
  have hn := leaf_nd' hy
  rw [down_eq_iff hn]
  refine ⟨Anc.refl hn, fun _ _ => Iff.rfl, fun z hz _ => ?_⟩
  by_contra h
  have := T.leaf_nd y hn (leaf_ar hy) z (by omega) hz.2.2.2
  rw [hz.2.1] at this; exact absurd this (by simp)

/-- `down` is idempotent. -/
lemma down_down {S : ℕ → Prop} {y : ℕ} (hy : T.nd y = true) :
    T.down S (T.down S y) = T.down S y := by
  obtain ⟨d1, d2⟩ := down_prop (S := S) hy
  rw [down_eq_iff d1.2.1]
  refine ⟨Anc.refl d1.2.1, fun _ _ => Iff.rfl, fun z hz hs => ?_⟩
  exact le_down (d1.trans hz) (fun k hk => (d2 k hk).trans (hs k hk))

lemma alive_of_same {S : ℕ → Prop} {y z : ℕ} (h : T.SameS S y z) (ha : T.alive S y) :
    T.alive S z := by
  obtain ⟨k, hk, hc⟩ := ha; exact ⟨k, hk, (h k hk).1 hc⟩

lemma alive_down {S : ℕ → Prop} {y : ℕ} (hy : T.nd y = true) (ha : T.alive S y) :
    T.alive S (T.down S y) := alive_of_same (down_prop hy).2 ha

/-- `down` of an alive node is a leaf or has two alive children. -/
theorem down_shape {S : ℕ → Prop} {y : ℕ} (hy : T.nd y = true) (ha : T.alive S y) :
    T.leaf (T.down S y) = true ∨ ∃ c c', T.IsChild (T.down S y) c ∧ T.IsChild (T.down S y) c' ∧
      c ≠ c' ∧ T.alive S c ∧ T.alive S c' := by
  set d := T.down S y
  have hd := (down_prop (S := S) hy).1.2.1
  have had := alive_down hy ha
  by_cases hl : T.leaf d = true
  · exact Or.inl hl
  right
  obtain ⟨k, hk, hkd⟩ := had
  obtain ⟨c, hc, hkc⟩ : ∃ c, T.IsChild d c ∧ T.Cont c k := by
    rcases cont_child_cases hd hkd (by simpa using hl) with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  by_contra hno
  have hsingle : ∀ c', T.IsChild d c' → c' ≠ c → ¬ T.alive S c' := by
    intro c' hc' hne ha'
    exact hno ⟨c, c', hc, hc', hne.symm, ⟨k, hk, hkc⟩, ha'⟩
  have e := down_single hc ⟨k, hk, hkc⟩ hsingle
  have e2 : T.down S d = d := down_down hy
  have := (down_prop (S := S) hc.nd).1.2.2.1
  have := hc.lt
  omega

/-! ## Compressed parents and the merge lemma -/

/-- The compressed parent of the leaf `k`: the deepest node containing `k` and another leaf of
`S`. -/
noncomputable def par (T : PT) (S : ℕ → Prop) (k : ℕ) : ℕ :=
  Nat.findGreatest (fun z => T.nd z = true ∧ T.Cont z k ∧ ∃ k', S k' ∧ k' ≠ k ∧ T.Cont z k') T.F

lemma le_par {S : ℕ → Prop} {k z k' : ℕ} (hz : T.nd z = true) (h1 : T.Cont z k) (h2 : S k')
    (h3 : k' ≠ k) (h4 : T.Cont z k') : z ≤ T.par S k :=
  Nat.le_findGreatest (P := fun z => T.nd z = true ∧ T.Cont z k ∧ ∃ k', S k' ∧ k' ≠ k ∧
    T.Cont z k') (lt_F hz).le ⟨hz, h1, k', h2, h3, h4⟩

lemma par_prop {S : ℕ → Prop} {k z k' : ℕ} (hz : T.nd z = true) (h1 : T.Cont z k) (h2 : S k')
    (h3 : k' ≠ k) (h4 : T.Cont z k') :
    T.nd (T.par S k) = true ∧ T.Cont (T.par S k) k ∧
      ∃ k', S k' ∧ k' ≠ k ∧ T.Cont (T.par S k) k' :=
  Nat.findGreatest_spec (P := fun z => T.nd z = true ∧ T.Cont z k ∧ ∃ k', S k' ∧ k' ≠ k ∧
    T.Cont z k') (lt_F hz).le ⟨hz, h1, k', h2, h3, h4⟩

/-- Leaves of `D` are separated by leaves of `S` outside `D`. -/
def Sep (S D : ℕ → Prop) : Prop :=
  ∀ k₁ k₂, D k₁ → D k₂ → k₁ < k₂ → ∃ m, S m ∧ ¬ D m ∧ k₁ < m ∧ m < k₂

/-- **Merge lemma.** If a child `c` of a node `y` that is alive in `S \ D` loses all its
`S`-leaves, then `c` contains exactly one leaf `k` of `S`, `k ∈ D`, and `y = par S k`. -/
theorem merge_dead {S D : ℕ → Prop} (hDS : ∀ k, D k → S k) (hsep : Sep S D) {y c : ℕ}
    (hc : T.IsChild y c) (hy : T.alive (fun k => S k ∧ ¬ D k) y) (hcS : T.alive S c)
    (hcS' : ¬ T.alive (fun k => S k ∧ ¬ D k) c) :
    ∃ k, D k ∧ T.Cont c k ∧ (∀ k', S k' → T.Cont c k' → k' = k) ∧ T.par S k = y := by
  obtain ⟨k, hkS, hkc⟩ := hcS
  have allD : ∀ k', S k' → T.Cont c k' → D k' := by
    intro k' h1 h2; by_contra h3; exact hcS' ⟨k', ⟨h1, h3⟩, h2⟩
  have huniq : ∀ k', S k' → T.Cont c k' → k' = k := by
    intro k' h1 h2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hsep k' k (allD k' h1 h2) (allD k hkS hkc) hlt
      exact hcS' ⟨m, ⟨hm1, hm2⟩, by have := h2.1; have := hkc.2; exact ⟨by omega, by omega⟩⟩
    · obtain ⟨m, hm1, hm2, hm3, hm4⟩ := hsep k k' (allD k hkS hkc) (allD k' h1 h2) hlt
      exact hcS' ⟨m, ⟨hm1, hm2⟩, by have := hkc.1; have := h2.2; exact ⟨by omega, by omega⟩⟩
  have hkD := allD k hkS hkc
  refine ⟨k, hkD, hkc, huniq, ?_⟩
  obtain ⟨k', ⟨hk'S, hk'D⟩, hk'y⟩ := hy
  have hne : k' ≠ k := by rintro rfl; exact hk'D hkD
  have hy' := hc.1
  have hky := hc.cont hkc
  have hle := le_par hy' hky hk'S hne hk'y
  obtain ⟨p1, p2, k'', p3, p4, p5⟩ := par_prop (S := S) hy' hky hk'S hne hk'y
  refine le_antisymm ?_ hle
  by_contra hlt
  have ha := anc_of_cont hy' p1 hky p2 hle
  obtain ⟨d, hd, hdz⟩ := desc_child ha (by omega)
  have hdc : d = c := by
    by_contra h; exact child_disjoint hd hc h (hdz.cont p2) hkc
  subst hdc
  exact p4 (huniq k'' p3 (hdz.cont p5))

/-! ## Regions and frontiers across a merge -/

/-- `z` lies in the region of `y`. -/
def InReg (T : PT) (S : ℕ → Prop) (y z : ℕ) : Prop :=
  T.alive S z ∧ T.leaf z = false ∧ T.down S z = T.down S y

/-- Rows that are *not* frontier rows for the gates of `y`: `y` itself, dead rows and rows of
the region of `y`. -/
def NF (T : PT) (S : ℕ → Prop) (y c : ℕ) : Prop := c = y ∨ ¬ T.alive S c ∨ T.InReg S y c

/-- Compressed parents of the leaves of `D`. -/
def PSet (T : PT) (S D : ℕ → Prop) (p : ℕ) : Prop := ∃ k, D k ∧ T.par S k = p

/-- The child of a compressed parent containing `k` has no other leaf of `S`. -/
lemma par_child_only {S : ℕ → Prop} {k c : ℕ} (hc : T.IsChild (T.par S k) c) (hkc : T.Cont c k) :
    ∀ k', S k' → T.Cont c k' → k' = k := by
  intro k' hk' hck'
  by_contra hne
  have := le_par hc.nd hkc hk' hne hck'
  have := hc.lt
  omega

/-- A compressed parent has two alive children. -/
lemma par_branch {S : ℕ → Prop} {k z k' : ℕ} (hz : T.nd z = true) (h1 : T.Cont z k) (h2 : S k')
    (h3 : k' ≠ k) (h4 : T.Cont z k') (hk : S k) : T.down S (T.par S k) = T.par S k := by
  obtain ⟨p1, p2, k'', p3, p4, p5⟩ := par_prop (S := S) hz h1 h2 h3 h4
  have hl : T.leaf (T.par S k) = false := by
    by_contra hl'
    have hl'' : T.leaf (T.par S k) = true := by simpa using hl'
    have e1 := lix_fe_leaf hl''
    have := p2.1; have := p2.2; have := p5.1; have := p5.2
    omega
  obtain ⟨c, hc, hkc⟩ : ∃ c, T.IsChild (T.par S k) c ∧ T.Cont c k := by
    rcases cont_child_cases p1 p2 hl with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  obtain ⟨c', hc', hkc'⟩ : ∃ c', T.IsChild (T.par S k) c' ∧ T.Cont c' k'' := by
    rcases cont_child_cases p1 p5 hl with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  have hne : c ≠ c' := by
    rintro rfl; exact p4 (par_child_only hc hkc k'' p3 hkc')
  exact down_branch hc hc' hne ⟨k, hk, hkc⟩ ⟨k'', p3, hkc'⟩

/-- If the region of `y` changes, `y` has two alive children. -/
lemma two_alive_of_down_ne {S : ℕ → Prop} {y c : ℕ} (hc : T.IsChild y c) (hcS : T.alive S c)
    (hne : T.down S c ≠ T.down S y) :
    ∃ c', T.IsChild y c' ∧ c' ≠ c ∧ T.alive S c' := by
  by_contra h
  push_neg at h
  exact hne (down_single hc hcS h).symm

section Merge

variable {S D : ℕ → Prop} (hDS : ∀ k, D k → S k) (hsep : Sep S D)
include hDS hsep

/-- Outside of the regions of compressed parents, children alive in `S` stay alive. -/
lemma alive_merge {y c : ℕ} (hc : T.IsChild y c) (hy : T.alive (fun k => S k ∧ ¬ D k) y)
    (hP : ¬ T.PSet S D (T.down S y)) (hcS : T.alive S c) :
    T.alive (fun k => S k ∧ ¬ D k) c := by
  by_contra h
  obtain ⟨k, hkD, hkc, -, hpar⟩ := merge_dead hDS hsep hc hy hcS h
  obtain ⟨k', ⟨hk'S, hk'D⟩, hk'y⟩ := hy
  have hne : k' ≠ k := by rintro rfl; exact hk'D hkD
  have := par_branch hc.1 (hc.cont hkc) hk'S hne hk'y (hDS k hkD)
  rw [hpar] at this
  exact hP ⟨k, hkD, by rw [this, hpar]⟩

/-- A node outside the regions of compressed parents with two alive children keeps them. -/
lemma down_merge_branch {y : ℕ} (hy : T.alive (fun k => S k ∧ ¬ D k) y)
    (hP : ¬ T.PSet S D (T.down S y)) {c c' : ℕ} (hc : T.IsChild y c) (hc' : T.IsChild y c')
    (hne : c ≠ c') (ha : T.alive S c) (ha' : T.alive S c') :
    T.down (fun k => S k ∧ ¬ D k) y = y :=
  down_branch hc hc' hne (alive_merge hDS hsep hc hy hP ha) (alive_merge hDS hsep hc' hy hP ha')

/-- **Frontier rows persist across a merge** (outside the regions of compressed parents):
a row that is not a frontier row after the merge was not one before. -/
lemma nf_merge {y c : ℕ} (hy : T.alive (fun k => S k ∧ ¬ D k) y)
    (hP : ¬ T.PSet S D (T.down S y)) (hc : c = y ∨ T.IsChild y c) :
    T.NF (fun k => S k ∧ ¬ D k) y c → T.NF S y c := by
  rintro (h | h | ⟨ha', hl, hd⟩)
  · exact Or.inl h
  · rcases hc with rfl | hc
    · exact Or.inl rfl
    by_cases ha : T.alive S c
    · exact absurd (alive_merge hDS hsep hc hy hP ha) h
    · exact Or.inr (Or.inl ha)
  · rcases hc with rfl | hc
    · exact Or.inl rfl
    obtain ⟨k, ⟨hk, -⟩, hkc⟩ := ha'
    have ha : T.alive S c := ⟨k, hk, hkc⟩
    refine Or.inr (Or.inr ⟨ha, hl, ?_⟩)
    by_contra hne
    obtain ⟨c', hc', hne', ha''⟩ := two_alive_of_down_ne hc ha hne
    have e := down_merge_branch hDS hsep hy hP hc hc' (Ne.symm hne') ha ha''
    rw [e] at hd
    have := (down_prop (S := fun k => S k ∧ ¬ D k) hc.nd).1.2.2.1
    have := hc.lt
    omega

end Merge

end PT

end PathChecking
