module

public import RequestProject.MCVP.Construction

/-!
# P-hardness on trees with a single fork: the semantic core

This file adapts the reduction of `RequestProject/MCVP/Construction.lean` from the monotone
circuit value problem to CTL* tree checking, so that the tree is a path with **one single
branching node**, whose two children are leaves.

For a circuit `C = g₀, …, g_{n-1}` the tree `forkTree C` is the path of *registers*
`R_{n-1}, R_{n-2}, …, R_0` (from the root downwards), and `R_0` has exactly two children, the
leaves `self` and `walk`. So the tree has `n + 2` nodes, exactly two leaves, and only one node
(namely `R_0`) with more than one child.

Every node `R_g` has two paths: the *self path* (down the spine into the leaf `self`) and the
*walk path* (down the spine into the leaf `walk`). The path formulas `F self` and `F walk` tell
these two paths apart at every position, which replaces the dummy nodes and side leaves of the
caterpillar construction. At level `k`:

    θ_k(p) = (act_k ∨ F self) ∧ (F walk U ((in_k ∨ (¬act_k ∧ F self)) ∧ p))

* a register `R_g` with `g ≠ k` must take its self path (to satisfy `act_k ∨ F self`), along
  which `F walk` never holds, so `p` is read at offset `0`, i.e. at `R_g` itself;
* the active register `R_k` cannot read at offset `0` (it carries `act_k` and not `in_k`), so
  it takes the walk path, along which `F self` is false, and reads `p` exactly at the nodes
  labelled `in_k`, the registers of the two inputs of gate `k`.

As before, `Φ_0 = init`, `Φ_{k+1} = E θ_k(Φ_k)` for `∨` gates and `¬E θ_k(¬Φ_k)` for `∧`
gates, and `Φ_{k+1} = Φ_k` for constant gates. The main result is `forkFormula_correct`.

## References

We know of no published source for this construction and have not checked the literature
for one. It reduces from MCVP, which is P-complete by Goldschlager [Gol77] (see also Ladner
[Lad75]). CTL* was introduced by Emerson–Halpern [EH86]. Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

/-! ## Trees consisting of a path ending in a single fork -/

/-- `LTree.forkPath ls r a b` is the path whose nodes carry the labels `ls` (from the root
downwards), followed by a node labelled `r` with exactly two children, the leaves labelled
`a` and `b`. -/
def LTree.forkPath (r a b : Finset ℕ) : List (Finset ℕ) → LTree
  | [] => .node r [.node a [], .node b []]
  | l :: ls => .node l [LTree.forkPath r a b ls]

/-- A tree is a *single-fork tree* if it is a path ending in one node with exactly two
children, both of which are leaves. Equivalently: a path with a single extra (side) leaf
attached to its last inner node. Such a tree has exactly two leaves, and exactly one node with
more than one child. -/
def LTree.IsSingleFork (t : LTree) : Prop := ∃ ls r a b, t = LTree.forkPath r a b ls

/-- **CTL* tree checking restricted to single-fork trees**: encodings of pairs `(φ, t)` of a
CTL* formula and a single-fork tree `t` (a path ending in a node with exactly two leaf
children) such that `t ⊨ φ`. -/
def CTLStarSingleForkTreeChecking : Language :=
  {x | ∃ (φ : CTLStar) (t : LTree),
    x = encodeToks (Tok.lpar :: (φ.toks ++ (Tok.rpar :: t.toks))) ∧ t.IsSingleFork ∧
      CTLStar.TreeSat t φ}

lemma CTLStarSingleForkTreeChecking_subset :
    CTLStarSingleForkTreeChecking ⊆ CTLStarTreeChecking := by
  rintro x ⟨φ, t, hx, -, hsat⟩
  exact ⟨φ, t, hx, hsat⟩

namespace MCVPReduction

/-! ## The tree -/

/-- Atomic proposition marking the leaf `self`. -/
def aSelf : ℕ := 0
/-- Atomic proposition marking the leaf `walk`. -/
def aWalk : ℕ := 2

/-- The leaf `self`. -/
def selfLeaf : LTree := .node {aSelf} []
/-- The leaf `walk`. -/
def walkLeaf : LTree := .node {aWalk} []

/-- The spine of the fork tree, indexed from the bottom: `fspine C g = R_g`. -/
def fspine (C : List MGate) : ℕ → LTree
  | 0 => .node (regLabel C 0) [selfLeaf, walkLeaf]
  | g + 1 => .node (regLabel C (g + 1)) [fspine C g]

/-- The tree of the reduction: rooted at the register of the output gate. -/
def forkTree (C : List MGate) : LTree := fspine C (C.length - 1)

lemma fspine_eq_forkPath (C : List MGate) (g : ℕ) :
    fspine C g = LTree.forkPath (regLabel C 0) {aSelf} {aWalk}
      ((List.range g).reverse.map (fun h => regLabel C (h + 1))) := by
  induction g with
  | zero => rfl
  | succ g ih => simp [fspine, ih, List.range_succ, LTree.forkPath]

/-- The tree of the reduction is a single-fork tree. -/
theorem forkTree_isSingleFork (C : List MGate) : (forkTree C).IsSingleFork :=
  ⟨_, _, _, _, fspine_eq_forkPath C _⟩

/-! ## The formula -/

/-- Eventually: `F φ = true U φ`. -/
def cF (φ : CTLStar) : CTLStar := .U .tt φ

/-- The path formula reading `p` at the positions selected at level `k`:
`(act_k ∨ F self) ∧ (F walk U ((in_k ∨ (¬act_k ∧ F self)) ∧ p))`. -/
def forkTheta (k : ℕ) (p : CTLStar) : CTLStar :=
  .and (cOr (.ap (aAct k)) (cF (.ap aSelf)))
    (.U (cF (.ap aWalk))
      (.and (cOr (.ap (aIn k)) (.and (.neg (.ap (aAct k))) (cF (.ap aSelf)))) p))

/-- Level `k` of the formula, for gate `G`. -/
def forkWrap (k : ℕ) : MGate → CTLStar → CTLStar
  | .input _, p => p
  | .or _ _, p => .E (forkTheta k p)
  | .and _ _, p => .neg (.E (forkTheta k (.neg p)))

/-- The formulas `Φ_k`. -/
def forkLevel (C : List MGate) : ℕ → CTLStar
  | 0 => .ap aInit
  | k + 1 => forkWrap k (gateAt C k) (forkLevel C k)

/-- The formula of the reduction. -/
def forkFormula (C : List MGate) : CTLStar := forkLevel C C.length

/-! ## Paths in the fork tree -/

section Paths

variable (C : List MGate)

lemma fspine_label (g : ℕ) : (fspine C g).label = regLabel C g := by
  cases g <;> rfl

lemma aSelf_not_mem_regLabel (g : ℕ) : aSelf ∉ regLabel C g := by
  rw [mem_regLabel]; unfold aSelf aAct aIn aInit; rintro (h | ⟨k, -, h⟩ | ⟨-, h⟩) <;> omega

lemma aWalk_not_mem_regLabel (g : ℕ) : aWalk ∉ regLabel C g := by
  rw [mem_regLabel]; unfold aWalk aAct aIn aInit; rintro (h | ⟨k, -, h⟩ | ⟨-, h⟩) <;> omega

lemma fspine_child (g : ℕ) : fspine C g ∈ (fspine C (g + 1)).children := by
  simp [fspine, LTree.children]

/-- The canonical path from `R_g` down into the leaf `ℓ`. -/
def downTo (g : ℕ) (ℓ : LTree) (i : ℕ) : LTree := if i ≤ g then fspine C (g - i) else ℓ

lemma downTo_path (g : ℕ) (ℓ : LTree) (hℓ : ℓ = selfLeaf ∨ ℓ = walkLeaf) :
    IsTreePath (downTo C g ℓ) := by
  intro i
  unfold downTo
  by_cases hi : i + 1 ≤ g
  · left
    rw [if_pos hi, if_pos (by omega), show g - i = (g - (i + 1)) + 1 by omega]
    exact fspine_child C _
  · by_cases hi' : i ≤ g
    · left
      rw [if_pos hi', if_neg hi, show g - i = 0 by omega]
      rcases hℓ with rfl | rfl <;> simp [fspine, LTree.children]
    · right
      rw [if_neg hi', if_neg hi]
      rcases hℓ with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- Every path starting at `R_g` is one of the two canonical paths. -/
lemma path_eq_downTo {π : ℕ → LTree} (hπ : IsTreePath π) {g : ℕ} (h0 : π 0 = fspine C g) :
    (π (g + 1) = selfLeaf ∨ π (g + 1) = walkLeaf) ∧ π = downTo C g (π (g + 1)) := by
  have hspine : ∀ i ≤ g, π i = fspine C (g - i) := by
    intro i hi
    induction i with
    | zero => simpa using h0
    | succ i ih =>
      have ih := ih (by omega)
      rcases hπ i with h | ⟨h, -⟩
      · rw [ih, show g - i = (g - (i + 1)) + 1 by omega] at h
        simpa [fspine, LTree.children] using h
      · rw [ih, show g - i = (g - (i + 1)) + 1 by omega] at h
        simp [fspine, LTree.children] at h
  have hleaf : π (g + 1) = selfLeaf ∨ π (g + 1) = walkLeaf := by
    rcases hπ g with h | ⟨h, -⟩
    · rw [hspine g le_rfl, Nat.sub_self] at h; simpa [fspine, LTree.children] using h
    · rw [hspine g le_rfl, Nat.sub_self] at h; simp [fspine, LTree.children] at h
  refine ⟨hleaf, ?_⟩
  have hstay : ∀ s, π (g + 1 + s) = π (g + 1) := by
    intro s
    induction s with
    | zero => rfl
    | succ s ih =>
      rcases hπ (g + 1 + s) with h | ⟨-, h⟩
      · rw [ih] at h
        rcases hleaf with hl | hl <;> rw [hl] at h <;>
          simp [selfLeaf, walkLeaf, LTree.children] at h
      · rw [← add_assoc, h, ih]
  funext i
  unfold downTo
  split_ifs with hi
  · exact hspine i hi
  · have := hstay (i - (g + 1)); rwa [show g + 1 + (i - (g + 1)) = i by omega] at this

lemma downTo_label_self (g : ℕ) (ℓ : LTree) (hℓ : ℓ = selfLeaf ∨ ℓ = walkLeaf) (i : ℕ) :
    aSelf ∈ (downTo C g ℓ i).label ↔ g < i ∧ ℓ = selfLeaf := by
  unfold downTo
  split_ifs with hi
  · simp [fspine_label, aSelf_not_mem_regLabel]; omega
  · rcases hℓ with rfl | rfl <;> simp [selfLeaf, walkLeaf, LTree.label, aSelf, aWalk]
    omega

lemma downTo_label_walk (g : ℕ) (ℓ : LTree) (hℓ : ℓ = selfLeaf ∨ ℓ = walkLeaf) (i : ℕ) :
    aWalk ∈ (downTo C g ℓ i).label ↔ g < i ∧ ℓ = walkLeaf := by
  unfold downTo
  split_ifs with hi
  · simp [fspine_label, aWalk_not_mem_regLabel]; omega
  · rcases hℓ with rfl | rfl <;> simp [selfLeaf, walkLeaf, LTree.label, aSelf, aWalk]
    omega

lemma holds_F_self (g : ℕ) (ℓ : LTree) (hℓ : ℓ = selfLeaf ∨ ℓ = walkLeaf) (t : ℕ) :
    CTLStar.Holds (cF (.ap aSelf)) (fun i => downTo C g ℓ (i + t)) ↔ ℓ = selfLeaf := by
  simp only [cF, CTLStar.Holds, zero_add, downTo_label_self C g ℓ hℓ]
  constructor
  · rintro ⟨m, h, -⟩; exact h.2
  · intro h; exact ⟨g + 1, ⟨by omega, h⟩, fun _ _ => trivial⟩

lemma holds_F_walk (g : ℕ) (ℓ : LTree) (hℓ : ℓ = selfLeaf ∨ ℓ = walkLeaf) (t : ℕ) :
    CTLStar.Holds (cF (.ap aWalk)) (fun i => downTo C g ℓ (i + t)) ↔ ℓ = walkLeaf := by
  simp only [cF, CTLStar.Holds, zero_add, downTo_label_walk C g ℓ hℓ]
  constructor
  · rintro ⟨m, h, -⟩; exact h.2
  · intro h; exact ⟨g + 1, ⟨by omega, h⟩, fun _ _ => trivial⟩

lemma selfLeaf_ne_walkLeaf : selfLeaf ≠ walkLeaf := by
  simp [selfLeaf, walkLeaf, aSelf, aWalk]

end Paths

/-! ## The two key facts -/

section Semantics

variable (C : List MGate)

lemma holds_forkTheta (k g : ℕ) (ℓ : LTree) (hℓ : ℓ = selfLeaf ∨ ℓ = walkLeaf) (p : CTLStar) :
    CTLStar.Holds (forkTheta k p) (downTo C g ℓ) ↔
      (aAct k ∈ (fspine C g).label ∨ ℓ = selfLeaf) ∧
      ∃ t, ((aIn k ∈ (downTo C g ℓ t).label ∨
          (aAct k ∉ (downTo C g ℓ t).label ∧ ℓ = selfLeaf)) ∧
        CTLStar.Holds p (fun i => downTo C g ℓ (i + t))) ∧
        ∀ j < t, ℓ = walkLeaf := by
  have e0 : downTo C g ℓ 0 = fspine C g := by simp [downTo]
  have hs0 : CTLStar.Holds (cF (.ap aSelf)) (downTo C g ℓ) ↔ ℓ = selfLeaf := by
    simpa using holds_F_self C g ℓ hℓ 0
  simp only [forkTheta, cOr, CTLStar.Holds, holds_F_self C g ℓ hℓ, holds_F_walk C g ℓ hℓ, hs0,
    zero_add, e0]
  exact and_congr (by tauto) (exists_congr fun t => and_congr (and_congr (by tauto) Iff.rfl) Iff.rfl)

/-- The paths from `R_g` are exactly the self path and the walk path. -/
lemma fork_exists_path (g : ℕ) (θ : CTLStar) :
    (∃ π, IsTreePath π ∧ π 0 = fspine C g ∧ CTLStar.Holds θ π) ↔
      ∃ ℓ, (ℓ = selfLeaf ∨ ℓ = walkLeaf) ∧ CTLStar.Holds θ (downTo C g ℓ) := by
  constructor
  · rintro ⟨π, hπ, h0, hθ⟩
    obtain ⟨hℓ, he⟩ := path_eq_downTo C hπ h0
    exact ⟨_, hℓ, he ▸ hθ⟩
  · rintro ⟨ℓ, hℓ, hθ⟩
    exact ⟨_, downTo_path C g ℓ hℓ, by simp [downTo], hθ⟩

variable (P : LTree → Prop) (p : CTLStar) (hp : ∀ π, CTLStar.Holds p π ↔ P (π 0))
include hp

/-- At level `k`, a register `R_g` with `g ≠ k` reads exactly itself. -/
lemma fork_copy_read (k g : ℕ) (hkg : k ≠ g) :
    (∃ ℓ, (ℓ = selfLeaf ∨ ℓ = walkLeaf) ∧ CTLStar.Holds (forkTheta k p) (downTo C g ℓ)) ↔
      P (fspine C g) := by
  have e0 : downTo C g selfLeaf 0 = fspine C g := by simp [downTo]
  constructor
  · rintro ⟨ℓ, hℓ, hθ⟩
    rw [holds_forkTheta C k g ℓ hℓ] at hθ
    obtain ⟨h1, t, ⟨-, hP⟩, hj⟩ := hθ
    rw [fspine_label, aAct_mem_regLabel] at h1
    have hs : ℓ = selfLeaf := h1.resolve_left hkg
    subst hs
    obtain rfl : t = 0 := by
      by_contra ht
      exact selfLeaf_ne_walkLeaf (hj 0 (by omega))
    rw [hp] at hP
    simpa [e0] using hP
  · intro hP
    refine ⟨selfLeaf, Or.inl rfl, ?_⟩
    rw [holds_forkTheta C k g _ (Or.inl rfl)]
    refine ⟨Or.inr rfl, 0, ⟨Or.inr ⟨?_, rfl⟩, ?_⟩, by simp⟩
    · rw [e0, fspine_label, aAct_mem_regLabel]; exact hkg
    · rw [hp]; simpa [e0] using hP

/-- At level `k`, the register `R_k` reads exactly the registers of the inputs of gate `k`. -/
lemma fork_active_read (k a b : ℕ) (hk : k < C.length) (ha : a < k) (hb : b < k)
    (hreads : ∀ h, (gateAt C k).reads h ↔ h = a ∨ h = b) :
    (∃ ℓ, (ℓ = selfLeaf ∨ ℓ = walkLeaf) ∧ CTLStar.Holds (forkTheta k p) (downTo C k ℓ)) ↔
      P (fspine C a) ∨ P (fspine C b) := by
  have reach : ∀ h, h < k → (gateAt C k).reads h → P (fspine C h) →
      ∃ ℓ, (ℓ = selfLeaf ∨ ℓ = walkLeaf) ∧ CTLStar.Holds (forkTheta k p) (downTo C k ℓ) := by
    intro h hh hr hP
    have eh : downTo C k walkLeaf (k - h) = fspine C h := by
      simp only [downTo, if_pos (Nat.sub_le k h)]; congr 1; omega
    refine ⟨walkLeaf, Or.inr rfl, ?_⟩
    rw [holds_forkTheta C k k _ (Or.inr rfl)]
    refine ⟨Or.inl ?_, k - h, ⟨Or.inl ?_, ?_⟩, fun _ _ => rfl⟩
    · rw [fspine_label, aAct_mem_regLabel]
    · rw [eh, fspine_label, aIn_mem_regLabel]; exact ⟨hk, hr⟩
    · rw [hp]; simpa [eh] using hP
  constructor
  · rintro ⟨ℓ, hℓ, hθ⟩
    rw [holds_forkTheta C k k ℓ hℓ] at hθ
    obtain ⟨-, t, ⟨h2, hP⟩, hj⟩ := hθ
    rw [hp] at hP
    simp only [zero_add] at hP
    rcases t with _ | t
    · exfalso
      have e0 : downTo C k ℓ 0 = fspine C k := by simp [downTo]
      rw [e0, fspine_label, aIn_mem_regLabel, aAct_mem_regLabel] at h2
      rcases h2 with ⟨-, hr⟩ | ⟨h, -⟩
      · rcases (hreads k).1 hr with rfl | rfl <;> omega
      · exact h rfl
    · have hw : ℓ = walkLeaf := hj 0 (by omega)
      subst hw
      have hin : aIn k ∈ (downTo C k walkLeaf (t + 1)).label := by
        rcases h2 with h | ⟨-, h⟩
        · exact h
        · exact absurd h.symm selfLeaf_ne_walkLeaf
      unfold downTo at hin hP
      split_ifs at hin hP with hle
      · rw [fspine_label, aIn_mem_regLabel] at hin
        rcases (hreads _).1 hin.2 with h | h <;> rw [h] at hP
        · exact Or.inl hP
        · exact Or.inr hP
      · simp [walkLeaf, LTree.label, aIn, aWalk] at hin
  · rintro (hP | hP)
    · exact reach a ha ((hreads a).2 (Or.inl rfl)) hP
    · exact reach b hb ((hreads b).2 (Or.inr rfl)) hP

end Semantics

section Main

variable (C : List MGate)

/-- `Φ_k` is a state formula: its truth only depends on the first node of a path. -/
lemma forkLevel_state (k : ℕ) (π π' : ℕ → LTree) (h : π 0 = π' 0) :
    CTLStar.Holds (forkLevel C k) π ↔ CTLStar.Holds (forkLevel C k) π' := by
  induction k with
  | zero => simp [forkLevel, CTLStar.Holds, h]
  | succ k ih =>
    simp only [forkLevel]
    cases gateAt C k <;> simp [forkWrap, CTLStar.Holds, h, ih]

/-- Truth of `Φ_k` at a node. -/
def ForkLevelSat (k : ℕ) (v : LTree) : Prop := CTLStar.Holds (forkLevel C k) (fun _ => v)

lemma holds_forkLevel (k : ℕ) (π : ℕ → LTree) :
    CTLStar.Holds (forkLevel C k) π ↔ ForkLevelSat C k (π 0) :=
  forkLevel_state C k _ _ rfl

/-- The invariant of the construction. -/
lemma forkLevelSat_iff (hC : WellFormed C) (k g : ℕ)
    (hg : g < k ∨ ∃ b, gateAt C g = .input b) :
    ForkLevelSat C k (fspine C g) ↔ val C g = true := by
  induction k generalizing g with
  | zero =>
    obtain ⟨b, hb⟩ := hg.resolve_left (Nat.not_lt_zero _)
    simp only [ForkLevelSat, forkLevel, CTLStar.Holds, fspine_label, aInit_mem_regLabel]
    rw [val, hb]; cases b <;> simp [MGate.isTrue]
  | succ k ih =>
    have hg' : g ≠ k → g < k ∨ ∃ b, gateAt C g = .input b := by
      intro hne; rcases hg with hg | hg
      · exact Or.inl (by omega)
      · exact Or.inr hg
    rcases hG : gateAt C k with b | ⟨i, j⟩ | ⟨i, j⟩
    · simp only [ForkLevelSat, forkLevel, hG, forkWrap]
      by_cases hgk : g = k
      · subst hgk; exact ih g (Or.inr ⟨b, hG⟩)
      · exact ih g (hg' hgk)
    · have hij := hC k i j (Or.inl hG)
      have hk := lt_length_of_gate C (Or.inl hG)
      simp only [ForkLevelSat, forkLevel, hG, forkWrap, CTLStar.Holds]
      rw [fork_exists_path]
      have hp : ∀ π, CTLStar.Holds (.neg (forkLevel C k)) π ↔
          (fun v => ¬ ForkLevelSat C k v) (π 0) := by
        intro π; simp [CTLStar.Holds, holds_forkLevel]
      by_cases hgk : g = k
      · subst hgk
        rw [fork_active_read C (fun v => ¬ ForkLevelSat C g v) _ hp g i j hk hij.1 hij.2
          (by rw [hG]; intro h; rfl), ih i (Or.inl hij.1), ih j (Or.inl hij.2)]
        conv_rhs => rw [val, hG]
        simp [hij.1, hij.2]
      · rw [fork_copy_read C (fun v => ¬ ForkLevelSat C k v) _ hp k g (Ne.symm hgk)]
        simpa using ih g (hg' hgk)
    · have hij := hC k i j (Or.inr hG)
      have hk := lt_length_of_gate C (Or.inr hG)
      simp only [ForkLevelSat, forkLevel, hG, forkWrap, CTLStar.Holds]
      rw [fork_exists_path]
      have hp : ∀ π, CTLStar.Holds (forkLevel C k) π ↔ ForkLevelSat C k (π 0) :=
        holds_forkLevel C k
      by_cases hgk : g = k
      · subst hgk
        rw [fork_active_read C _ _ hp g i j hk hij.1 hij.2 (by rw [hG]; intro h; rfl),
          ih i (Or.inl hij.1), ih j (Or.inl hij.2)]
        conv_rhs => rw [val, hG]
        simp [hij.1, hij.2]
      · rw [fork_copy_read C _ _ hp k g (Ne.symm hgk)]
        exact ih g (hg' hgk)

end Main

/-- **Correctness of the single-fork reduction.** For a well-formed monotone circuit `C`, the
single-fork tree `forkTree C` satisfies the CTL* formula `forkFormula C` iff `C` evaluates to
true. -/
theorem forkFormula_correct (C : List MGate) (hC : WellFormed C) :
    CTLStar.TreeSat (forkTree C) (forkFormula C) ↔ eval C = true := by
  have key : ForkLevelSat C C.length (forkTree C) ↔ eval C = true := by
    unfold forkTree eval
    apply forkLevelSat_iff C hC
    rcases Nat.eq_zero_or_pos C.length with h | h
    · right; refine ⟨false, ?_⟩; simp [gateAt, List.length_eq_zero_iff.mp h]
    · left; omega
  rw [← key]
  constructor
  · intro h
    have := h _ (downTo_path C (C.length - 1) selfLeaf (Or.inl rfl)) (by simp [downTo, forkTree])
    exact (holds_forkLevel C _ _).1 this
  · intro h π _ hπ0
    exact (holds_forkLevel C _ _).2 (hπ0 ▸ h)


end MCVPReduction

end PathChecking
