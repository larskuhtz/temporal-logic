module

public import RequestProject.Logics

/-!
# A reduction from the monotone circuit value problem to CTL* tree checking

This file contains the semantic core of a logspace reduction from the monotone circuit value
problem (MCVP) to CTL* tree checking.

Given a monotone circuit `C = g₀, …, g_{n-1}` (each gate is a constant or an `∧`/`∨` of two
earlier gates), we build

* a *caterpillar* tree: a spine `R_{n-1}, D_{n-1}, R_{n-2}, D_{n-2}, …, R_0, D_0` (from the root
  downwards), where every *register* node `R_g` additionally has a leaf child `side`;
* a CTL* formula `Φ_n` defined by `Φ_0 = init` and `Φ_{k+1} = wrap_k Φ_k`, where `Φ_k` occurs
  exactly **once** in `wrap_k Φ_k`, so that `|Φ_n| = O(n log n)`.

The invariant is: after level `k`, `Φ_k` holds at register `R_g` iff gate `g` evaluates to
true (for all gates `g < k` and all constant gates).  At level `k` every register except
`R_k` copies its old value (its only "readable" position is itself, reached by stepping into
its side leaf), whereas `R_k` reads exactly the registers of the two inputs of gate `k`,
by a two-phase until: first step into the dummy node `D_k`, then walk down the spine to a node
labelled `in_k`.

The main result is `reductionFormula_correct`: the tree satisfies the formula iff the
circuit evaluates to true.

## References

We know of no published source for this construction and have not checked the literature
for one. It reduces from MCVP, which is P-complete by Goldschlager [Gol77] (see also Ladner
[Lad75]). CTL* was introduced by Emerson–Halpern [EH86]. Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

/-! ## Monotone circuits -/

/-- Gates of a monotone circuit: constants and binary `∧`/`∨` gates whose inputs are given
as indices of (earlier) gates. -/
inductive MGate
  | input (b : Bool)
  | and (i j : ℕ)
  | or (i j : ℕ)

/-- The `k`-th gate of a circuit (a `false` constant outside the circuit). -/
def gateAt (C : List MGate) (k : ℕ) : MGate := C.getD k (.input false)

/-- A circuit is well formed if every gate only reads earlier gates. -/
def WellFormed (C : List MGate) : Prop :=
  ∀ k i j, gateAt C k = .and i j ∨ gateAt C k = .or i j → i < k ∧ j < k

/-- Value of gate `k` of a circuit (references to non-earlier gates read `false`). -/
def val (C : List MGate) (k : ℕ) : Bool :=
  match gateAt C k with
  | .input b => b
  | .and i j => (if _ : i < k then val C i else false) && (if _ : j < k then val C j else false)
  | .or i j => (if _ : i < k then val C i else false) || (if _ : j < k then val C j else false)
termination_by k

/-- The value of a circuit: the value of its last gate. -/
def eval (C : List MGate) : Bool := val C (C.length - 1)

/-! ## The tree -/

/-- Atomic proposition marking side leaves. -/
def aSide : ℕ := 0
/-- Atomic proposition marking constant-`true` gates. -/
def aInit : ℕ := 4
/-- Atomic proposition marking register `R_k` (active at level `k`). -/
def aAct (k : ℕ) : ℕ := 4 * k + 1
/-- Atomic proposition marking the dummy node `D_k`. -/
def aDum (k : ℕ) : ℕ := 4 * k + 2
/-- Atomic proposition marking the registers read by gate `k`. -/
def aIn (k : ℕ) : ℕ := 4 * k + 3

/-- Does gate `G` read gate `g`? -/
def MGate.reads : MGate → ℕ → Prop
  | .input _, _ => False
  | .and i j, g => g = i ∨ g = j
  | .or i j, g => g = i ∨ g = j

instance (G : MGate) (g : ℕ) : Decidable (G.reads g) := by
  cases G <;> unfold MGate.reads <;> infer_instance

/-- Is `G` the constant `true`? -/
def MGate.isTrue : MGate → Prop
  | .input b => b = true
  | _ => False

instance (G : MGate) : Decidable G.isTrue := by
  cases G <;> unfold MGate.isTrue <;> infer_instance

/-- Label of register `R_g`. -/
def regLabel (C : List MGate) (g : ℕ) : Finset ℕ :=
  insert (aAct g)
    (((Finset.range C.length).filter (fun k => (gateAt C k).reads g)).image aIn ∪
      (if (gateAt C g).isTrue then {aInit} else ∅))

/-- The side leaf. -/
def sideLeaf : LTree := .node {aSide} []

/-- The spine, indexed from the bottom: `spine (2g) = D_g`, `spine (2g+1) = R_g`. -/
def spine (C : List MGate) : ℕ → LTree
  | 0 => .node {aDum 0} []
  | n + 1 => if n % 2 = 0 then .node (regLabel C (n / 2)) [sideLeaf, spine C n]
      else .node {aDum ((n + 1) / 2)} [spine C n]

/-- The tree of the reduction: rooted at the register of the output gate. -/
def reductionTree (C : List MGate) : LTree := spine C (2 * (C.length - 1) + 1)

/-! ## The formula -/

/-- Disjunction. -/
def cOr (φ ψ : CTLStar) : CTLStar := .neg (.and (.neg φ) (.neg ψ))

/-- `β₁ = (X side ∧ ¬act_k) ∨ dum_k`: end of the first phase. -/
def beta1 (k : ℕ) : CTLStar :=
  cOr (.and (.X (.ap aSide)) (.neg (.ap (aAct k)))) (.ap (aDum k))

/-- `γ₂ = ¬ X X side ∧ ¬ side`: invariant of the second phase. -/
def gamma2 : CTLStar := .and (.neg (.X (.X (.ap aSide)))) (.neg (.ap aSide))

/-- `β₂ = (X side ∨ in_k) ∧ ¬side ∧ ¬dum_k`: end of the second phase (the read position). -/
def beta2 (k : ℕ) : CTLStar :=
  .and (.and (cOr (.X (.ap aSide)) (.ap (aIn k))) (.neg (.ap aSide))) (.neg (.ap (aDum k)))

/-- The path formula reading `p` at the positions selected at level `k`:
`act_k U (β₁ ∧ (γ₂ U (β₂ ∧ p)))`. -/
def theta (k : ℕ) (p : CTLStar) : CTLStar :=
  .U (.ap (aAct k)) (.and (beta1 k) (.U gamma2 (.and (beta2 k) p)))

/-- Level `k` of the formula, for gate `G`. -/
def wrap (k : ℕ) : MGate → CTLStar → CTLStar
  | .input _, p => p
  | .or _ _, p => .E (theta k p)
  | .and _ _, p => .neg (.E (theta k (.neg p)))

/-- The formulas `Φ_k`. -/
def levelFormula (C : List MGate) : ℕ → CTLStar
  | 0 => .ap aInit
  | k + 1 => wrap k (gateAt C k) (levelFormula C k)

/-- The formula of the reduction. -/
def reductionFormula (C : List MGate) : CTLStar := levelFormula C C.length

/-! ## Correctness -/

section Basic

variable (C : List MGate)

lemma mem_regLabel (x g : ℕ) : x ∈ regLabel C g ↔ x = aAct g ∨
    (∃ k, (k < C.length ∧ (gateAt C k).reads g) ∧ aIn k = x) ∨
    ((gateAt C g).isTrue ∧ x = aInit) := by
  unfold regLabel; split_ifs with h <;> simp [h]; exact or_congr_right or_comm

lemma aSide_not_mem_regLabel (g : ℕ) : aSide ∉ regLabel C g := by
  rw [mem_regLabel]; unfold aSide aAct aIn aInit; rintro (h | ⟨k, -, h⟩ | ⟨-, h⟩) <;> omega

lemma aDum_not_mem_regLabel (k g : ℕ) : aDum k ∉ regLabel C g := by
  rw [mem_regLabel]; unfold aDum aAct aIn aInit; rintro (h | ⟨k, -, h⟩ | ⟨-, h⟩) <;> omega

lemma aAct_mem_regLabel (k g : ℕ) : aAct k ∈ regLabel C g ↔ k = g := by
  rw [mem_regLabel]; unfold aAct aIn aInit
  constructor
  · rintro (h | ⟨k, -, h⟩ | ⟨-, h⟩) <;> omega
  · rintro rfl; exact Or.inl rfl

lemma aIn_mem_regLabel (k g : ℕ) :
    aIn k ∈ regLabel C g ↔ k < C.length ∧ (gateAt C k).reads g := by
  rw [mem_regLabel]; unfold aAct aIn aInit
  constructor
  · rintro (h | ⟨k', h', h⟩ | ⟨-, h⟩)
    · omega
    · obtain rfl : k' = k := by omega
      exact h'
    · omega
  · intro h; exact Or.inr (Or.inl ⟨k, h, rfl⟩)

lemma aInit_mem_regLabel (g : ℕ) : aInit ∈ regLabel C g ↔ (gateAt C g).isTrue := by
  rw [mem_regLabel]; unfold aAct aIn aInit
  constructor
  · rintro (h | ⟨k', h', h⟩ | ⟨h, -⟩)
    · omega
    · omega
    · exact h
  · intro h; exact Or.inr (Or.inr ⟨h, rfl⟩)

lemma spine_odd (g : ℕ) :
    spine C (2 * g + 1) = .node (regLabel C g) [sideLeaf, spine C (2 * g)] := by
  rw [spine, if_pos (by omega)]; congr 2; omega

lemma spine_even (g : ℕ) :
    spine C (2 * g + 2) = .node {aDum (g + 1)} [spine C (2 * g + 1)] := by
  rw [spine, if_neg (by omega)]; congr 3; omega

lemma spine_zero : spine C 0 = .node {aDum 0} [] := rfl

lemma spine_cases (i : ℕ) :
    (∃ g, i = 2 * g + 1 ∧ spine C i = .node (regLabel C g) [sideLeaf, spine C (2 * g)]) ∨
    (∃ g, i = 2 * g ∧ ((g = 0 ∧ spine C i = .node {aDum 0} []) ∨
      (∃ h, g = h + 1 ∧ spine C i = .node {aDum g} [spine C (2 * h + 1)]))) := by
  obtain ⟨g, rfl | rfl⟩ := Nat.even_or_odd' i
  · rcases g with _ | h
    · exact Or.inr ⟨0, rfl, Or.inl ⟨rfl, rfl⟩⟩
    · refine Or.inr ⟨h + 1, rfl, Or.inr ⟨h, rfl, ?_⟩⟩
      rw [show 2 * (h + 1) = 2 * h + 2 by ring, spine_even]
  · exact Or.inl ⟨g, rfl, spine_odd C g⟩

lemma aSide_not_mem_spine (i : ℕ) : aSide ∉ (spine C i).label := by
  rcases spine_cases C i with ⟨g, -, h⟩ | ⟨g, -, ⟨-, h⟩ | ⟨_, -, h⟩⟩ <;> rw [h] <;>
    simp only [LTree.label] <;> first | exact aSide_not_mem_regLabel C g |
      simp [aSide, aDum]

lemma sideLeaf_label : sideLeaf.label = {aSide} := rfl

lemma spine_reg_label (g : ℕ) : (spine C (2 * g + 1)).label = regLabel C g := by
  rw [spine_odd]; rfl

lemma spine_dum_label (g : ℕ) : (spine C (2 * g)).label = {aDum g} := by
  rcases g with _ | h
  · rfl
  · rw [show 2 * (h + 1) = 2 * h + 2 by ring, spine_even]; rfl

/-- Nodes of the caterpillar. -/
def Good (v : LTree) : Prop := v = sideLeaf ∨ ∃ i, v = spine C i

lemma good_child {v c : LTree} (hv : Good C v) (hc : c ∈ v.children) : Good C c := by
  rcases hv with rfl | ⟨i, rfl⟩
  · simp [sideLeaf, LTree.children] at hc
  · rcases spine_cases C i with ⟨g, -, h⟩ | ⟨g, -, ⟨-, h⟩ | ⟨k, -, h⟩⟩ <;>
      rw [h] at hc <;> simp [LTree.children] at hc
    · rcases hc with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨_, rfl⟩
    · exact Or.inr ⟨_, hc⟩

lemma good_path {π : ℕ → LTree} (hπ : IsTreePath π) (h0 : Good C (π 0)) (t : ℕ) :
    Good C (π t) := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    rcases hπ t with h | ⟨-, h⟩
    · exact good_child C ih h
    · rw [h]; exact ih

lemma good_side {v : LTree} (hv : Good C v) (h : aSide ∈ v.label) : v = sideLeaf := by
  rcases hv with rfl | ⟨i, rfl⟩
  · rfl
  · exact absurd h (aSide_not_mem_spine C i)

lemma good_aIn {v : LTree} {k : ℕ} (hv : Good C v) (h : aIn k ∈ v.label) :
    ∃ g, v = spine C (2 * g + 1) ∧ k < C.length ∧ (gateAt C k).reads g := by
  rcases hv with rfl | ⟨i, rfl⟩
  · simp [sideLeaf, LTree.label, aIn, aSide] at h
  · rcases spine_cases C i with ⟨g, rfl, hs⟩ | ⟨g, -, ⟨-, hs⟩ | ⟨_, -, hs⟩⟩ <;>
      rw [hs] at h <;> simp [LTree.label, aIn, aDum] at h
    · exact ⟨g, rfl, (aIn_mem_regLabel C k g).1 (by simpa [LTree.label] using h)⟩
    all_goals omega

lemma side_stutter {π : ℕ → LTree} (hπ : IsTreePath π) {t : ℕ} (ht : π t = sideLeaf)
    (s : ℕ) : π (t + s) = sideLeaf := by
  induction s with
  | zero => exact ht
  | succ s ih =>
    rcases hπ (t + s) with h | ⟨-, h⟩
    · rw [ih] at h; simp [sideLeaf, LTree.children] at h
    · rw [← add_assoc, h, ih]

lemma spine_child (m : ℕ) : spine C m ∈ (spine C (m + 1)).children := by
  rw [spine]; split_ifs <;> simp [LTree.children]

/-- The path going down the spine from `spine s`. -/
lemma down_path (s : ℕ) : IsTreePath (fun i => spine C (s - i)) := by
  intro i
  rcases Nat.eq_zero_or_pos (s - i) with h | h
  · right; simp [h, show s - (i + 1) = 0 by omega, spine, LTree.children]
  · left; obtain ⟨m, hm⟩ : ∃ m, s - i = m + 1 := ⟨s - i - 1, by omega⟩
    simp only [hm, show s - (i + 1) = m by omega]; exact spine_child C m

end Basic

section Semantics

variable (C : List MGate)

lemma holds_beta1 (k : ℕ) (π : ℕ → LTree) : CTLStar.Holds (beta1 k) π ↔
    (aSide ∈ (π 1).label ∧ aAct k ∉ (π 0).label) ∨ aDum k ∈ (π 0).label := by
  simp [beta1, cOr, CTLStar.Holds]; tauto

lemma holds_gamma2 (π : ℕ → LTree) : CTLStar.Holds gamma2 π ↔
    aSide ∉ (π 2).label ∧ aSide ∉ (π 0).label := by
  simp [gamma2, CTLStar.Holds]

lemma holds_beta2 (k : ℕ) (π : ℕ → LTree) : CTLStar.Holds (beta2 k) π ↔
    (aSide ∈ (π 1).label ∨ aIn k ∈ (π 0).label) ∧ aSide ∉ (π 0).label ∧
      aDum k ∉ (π 0).label := by
  simp [beta2, cOr, CTLStar.Holds]; tauto

lemma holds_theta (k : ℕ) (p : CTLStar) (π : ℕ → LTree) : CTLStar.Holds (theta k p) π ↔
    ∃ t₁, (CTLStar.Holds (beta1 k) (fun i => π (i + t₁)) ∧
      ∃ t₂, (CTLStar.Holds (beta2 k) (fun i => π (i + t₂ + t₁)) ∧
          CTLStar.Holds p (fun i => π (i + t₂ + t₁))) ∧
        ∀ j < t₂, CTLStar.Holds gamma2 (fun i => π (i + j + t₁))) ∧
      ∀ j < t₁, aAct k ∈ (π j).label := by
  simp [theta, CTLStar.Holds]

variable (P : LTree → Prop) (p : CTLStar) (hp : ∀ π, CTLStar.Holds p π ↔ P (π 0))
include hp

/-- At level `k`, a register `R_g` with `g ≠ k` reads exactly itself. -/
lemma copy_read (k g : ℕ) (hkg : k ≠ g) :
    (∃ π, IsTreePath π ∧ π 0 = spine C (2 * g + 1) ∧ CTLStar.Holds (theta k p) π) ↔
      P (spine C (2 * g + 1)) := by
  have hlab : (spine C (2 * g + 1)).label = regLabel C g := by rw [spine_odd]; rfl
  constructor
  · rintro ⟨π, hπ, h0, hθ⟩
    rw [holds_theta] at hθ
    obtain ⟨t₁, ⟨hb1, t₂, ⟨hb2, hpt⟩, hγ⟩, hact⟩ := hθ
    obtain rfl : t₁ = 0 := by
      by_contra hne
      have := hact 0 (by omega)
      rw [h0, hlab, aAct_mem_regLabel] at this
      exact hkg this
    rw [holds_beta1] at hb1
    simp only [add_zero, h0, hlab] at hb1 hb2 hpt
    have h1 : π 1 = sideLeaf := by
      rcases hb1 with ⟨h, -⟩ | h
      · exact good_side C (good_path C hπ (Or.inr ⟨_, h0⟩) 1) h
      · exact absurd h (aDum_not_mem_regLabel C k g)
    rcases t₂ with _ | t₂
    · rw [hp] at hpt; simpa [h0] using hpt
    · exfalso
      rw [holds_beta2] at hb2
      have := side_stutter hπ h1 t₂
      have h2 : π (t₂ + 1) = sideLeaf := by rw [add_comm]; exact this
      simp only [zero_add, h2, sideLeaf_label] at hb2
      exact hb2.2.1 (Finset.mem_singleton_self _)
  · intro hP
    refine ⟨fun i => if i = 0 then spine C (2 * g + 1) else sideLeaf, ?_, rfl, ?_⟩
    · intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · left; simp [spine_odd, LTree.children]
      · right; simp [show i ≠ 0 by omega, sideLeaf, LTree.children]
    · rw [holds_theta]
      refine ⟨0, ⟨?_, 0, ⟨?_, ?_⟩, by simp⟩, by simp⟩
      · rw [holds_beta1]; left
        simp [hlab, aAct_mem_regLabel, hkg, sideLeaf_label, aSide]
      · rw [holds_beta2]
        simp [hlab, aSide_not_mem_regLabel, aDum_not_mem_regLabel, sideLeaf_label]
      · rw [hp]; simpa using hP

/-- At level `k`, the register `R_k` reads exactly the registers of the inputs of gate `k`. -/
lemma active_read (k a b : ℕ) (hk : k < C.length) (ha : a < k) (hb : b < k)
    (hreads : ∀ h, (gateAt C k).reads h ↔ h = a ∨ h = b) :
    (∃ π, IsTreePath π ∧ π 0 = spine C (2 * k + 1) ∧ CTLStar.Holds (theta k p) π) ↔
      P (spine C (2 * a + 1)) ∨ P (spine C (2 * b + 1)) := by
  have hlab : (spine C (2 * k + 1)).label = regLabel C k := by rw [spine_odd]; rfl
  -- reading any input register `R_h` (with `h < k`) along the spine
  have reach : ∀ h, h < k → (gateAt C k).reads h → P (spine C (2 * h + 1)) →
      ∃ π, IsTreePath π ∧ π 0 = spine C (2 * k + 1) ∧ CTLStar.Holds (theta k p) π := by
    intro h hh hr hP
    refine ⟨fun i => spine C (2 * k + 1 - i), down_path C _, by simp, ?_⟩
    rw [holds_theta]
    refine ⟨1, ⟨?_, 2 * k - 2 * h - 1, ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [holds_beta1]; right
      simp only [zero_add, show 2 * k + 1 - 1 = 2 * k by omega, spine_dum_label]
      exact Finset.mem_singleton_self _
    · rw [holds_beta2]
      simp only [zero_add, show 2 * k + 1 - (2 * k - 2 * h - 1 + 1) = 2 * h + 1 by omega]
      refine ⟨Or.inr ?_, aSide_not_mem_spine C _, ?_⟩
      · rw [spine_reg_label, aIn_mem_regLabel]; exact ⟨hk, hr⟩
      · rw [spine_reg_label]; exact aDum_not_mem_regLabel C k h
    · rw [hp]
      simp only [zero_add, show 2 * k + 1 - (2 * k - 2 * h - 1 + 1) = 2 * h + 1 by omega]
      exact hP
    · intro j _
      rw [holds_gamma2]
      exact ⟨aSide_not_mem_spine C _, aSide_not_mem_spine C _⟩
    · intro j hj
      obtain rfl : j = 0 := by omega
      simp [hlab, aAct_mem_regLabel]
  constructor
  · rintro ⟨π, hπ, h0, hθ⟩
    have h1 : π 1 = sideLeaf ∨ π 1 = spine C (2 * k) := by
      rcases hπ 0 with h | ⟨h, -⟩
      · rw [h0, spine_odd] at h; simpa [LTree.children] using h
      · rw [h0, spine_odd] at h; simp [LTree.children] at h
    rw [holds_theta] at hθ
    obtain ⟨t₁, ⟨hb1, t₂, ⟨hb2, hpt⟩, hγ⟩, hact⟩ := hθ
    rcases t₁ with _ | _ | t₁
    · exfalso
      rw [holds_beta1] at hb1
      simp [h0, hlab, aAct_mem_regLabel, aDum_not_mem_regLabel] at hb1
    swap
    · exfalso
      have := hact 1 (by omega)
      rcases h1 with h1 | h1 <;> rw [h1] at this
      · simp [sideLeaf_label, aAct, aSide] at this
      · rw [spine_dum_label] at this; simp [aAct, aDum] at this
    rcases h1 with h1 | h1
    · exfalso
      have h2 : π (t₂ + 1) = sideLeaf := by rw [add_comm]; exact side_stutter hπ h1 t₂
      rw [holds_beta2] at hb2
      simp only [zero_add, h2, sideLeaf_label] at hb2
      exact hb2.2.1 (Finset.mem_singleton_self _)
    rcases t₂ with _ | s
    · exfalso
      rw [holds_beta2] at hb2
      simp only [zero_add, h1, spine_dum_label] at hb2
      exact hb2.2.2 (Finset.mem_singleton_self _)
    rw [holds_beta2] at hb2
    simp only [zero_add] at hb2
    rcases hb2.1 with hs | hin
    · exfalso
      have := hγ s (by omega)
      rw [holds_gamma2] at this
      exact this.1 (by rw [show 2 + s + 1 = 1 + (s + 1) + 1 by omega]; exact hs)
    · obtain ⟨h, hh, -, hr⟩ := good_aIn C (good_path C hπ (Or.inr ⟨_, h0⟩) _) hin
      rw [hp] at hpt
      simp only [zero_add, hh] at hpt
      rcases (hreads h).1 hr with rfl | rfl
      · exact Or.inl hpt
      · exact Or.inr hpt
  · rintro (hP | hP)
    · exact reach a ha ((hreads a).2 (Or.inl rfl)) hP
    · exact reach b hb ((hreads b).2 (Or.inr rfl)) hP

end Semantics

section Main

variable (C : List MGate)

/-- `Φ_k` is a state formula: its truth only depends on the first node of a path. -/
lemma levelFormula_state (k : ℕ) (π π' : ℕ → LTree) (h : π 0 = π' 0) :
    CTLStar.Holds (levelFormula C k) π ↔ CTLStar.Holds (levelFormula C k) π' := by
  induction k with
  | zero => simp [levelFormula, CTLStar.Holds, h]
  | succ k ih =>
    simp only [levelFormula]
    cases gateAt C k <;> simp [wrap, CTLStar.Holds, h, ih]

/-- Truth of `Φ_k` at a node. -/
def LevelSat (k : ℕ) (v : LTree) : Prop := CTLStar.Holds (levelFormula C k) (fun _ => v)

lemma holds_levelFormula (k : ℕ) (π : ℕ → LTree) :
    CTLStar.Holds (levelFormula C k) π ↔ LevelSat C k (π 0) :=
  levelFormula_state C k _ _ rfl

lemma lt_length_of_gate {k i j : ℕ} (h : gateAt C k = .and i j ∨ gateAt C k = .or i j) :
    k < C.length := by
  by_contra hk
  simp [gateAt, List.getElem?_eq_none (by omega : C.length ≤ k)] at h

/-- The invariant of the construction. -/
lemma levelSat_iff (hC : WellFormed C) (k g : ℕ) (hg : g < k ∨ ∃ b, gateAt C g = .input b) :
    LevelSat C k (spine C (2 * g + 1)) ↔ val C g = true := by
  induction k generalizing g with
  | zero =>
    obtain ⟨b, hb⟩ := hg.resolve_left (Nat.not_lt_zero _)
    simp only [LevelSat, levelFormula, CTLStar.Holds, spine_odd, LTree.label, aInit_mem_regLabel]
    rw [val, hb]; cases b <;> simp [MGate.isTrue]
  | succ k ih =>
    have hg' : g ≠ k → g < k ∨ ∃ b, gateAt C g = .input b := by
      intro hne; rcases hg with hg | hg
      · exact Or.inl (by omega)
      · exact Or.inr hg
    rcases hG : gateAt C k with b | ⟨i, j⟩ | ⟨i, j⟩
    · simp only [LevelSat, levelFormula, hG, wrap]
      by_cases hgk : g = k
      · subst hgk; exact ih g (Or.inr ⟨b, hG⟩)
      · exact ih g (hg' hgk)
    · have hij := hC k i j (Or.inl hG)
      have hk := lt_length_of_gate C (Or.inl hG)
      simp only [LevelSat, levelFormula, hG, wrap, CTLStar.Holds]
      have hp : ∀ π, CTLStar.Holds (.neg (levelFormula C k)) π ↔
          (fun v => ¬ LevelSat C k v) (π 0) := by
        intro π; simp [CTLStar.Holds, holds_levelFormula]
      by_cases hgk : g = k
      · subst hgk
        rw [active_read C (fun v => ¬ LevelSat C g v) _ hp g i j hk hij.1 hij.2
          (by rw [hG]; intro h; rfl), ih i (Or.inl hij.1), ih j (Or.inl hij.2)]
        conv_rhs => rw [val, hG]
        simp [hij.1, hij.2]
      · rw [copy_read C (fun v => ¬ LevelSat C k v) _ hp k g (Ne.symm hgk)]
        simpa using ih g (hg' hgk)
    · have hij := hC k i j (Or.inr hG)
      have hk := lt_length_of_gate C (Or.inr hG)
      simp only [LevelSat, levelFormula, hG, wrap, CTLStar.Holds]
      have hp : ∀ π, CTLStar.Holds (levelFormula C k) π ↔ LevelSat C k (π 0) :=
        holds_levelFormula C k
      by_cases hgk : g = k
      · subst hgk
        rw [active_read C _ _ hp g i j hk hij.1 hij.2 (by rw [hG]; intro h; rfl),
          ih i (Or.inl hij.1), ih j (Or.inl hij.2)]
        conv_rhs => rw [val, hG]
        simp [hij.1, hij.2]
      · rw [copy_read C _ _ hp k g (Ne.symm hgk)]
        exact ih g (hg' hgk)

end Main

/-- **Correctness of the reduction.** For a well-formed monotone circuit `C`, the caterpillar
tree `reductionTree C` satisfies the CTL* formula `reductionFormula C` iff `C` evaluates to
true. -/
theorem reductionFormula_correct (C : List MGate) (hC : WellFormed C) :
    CTLStar.TreeSat (reductionTree C) (reductionFormula C) ↔ eval C = true := by
  have key : LevelSat C C.length (reductionTree C) ↔ eval C = true := by
    unfold reductionTree eval
    apply levelSat_iff C hC
    rcases Nat.eq_zero_or_pos C.length with h | h
    · right; refine ⟨false, ?_⟩; simp [gateAt, List.length_eq_zero_iff.mp h]
    · left; omega
  rw [← key]
  constructor
  · intro h
    have := h _ (down_path C (2 * (C.length - 1) + 1)) (by simp [reductionTree])
    exact (holds_levelFormula C _ _).1 this
  · intro h π _ hπ0
    exact (holds_levelFormula C _ _).2 (hπ0 ▸ h)

/-! ## Size of the formula -/

lemma natToks_length_le (n : ℕ) : (natToks n).length ≤ n + 1 := by
  have : (Nat.bits n).length ≤ n := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.2 (Nat.lt_two_pow_self)
  simp [natToks]; omega

lemma wrap_toks_length (k : ℕ) (G : MGate) (p : CTLStar) :
    (wrap k G p).toks.length ≤ p.toks.length + 100 * (k + 1) := by
  have h1 := natToks_length_le (aAct k)
  have h2 := natToks_length_le (aDum k)
  have h3 := natToks_length_le (aIn k)
  have h4 := natToks_length_le aSide
  cases G <;>
  simp [wrap, theta, beta1, beta2, gamma2, cOr, CTLStar.toks, aAct, aDum, aIn, aSide] at * <;>
  omega

lemma levelFormula_toks_length (C : List MGate) (k : ℕ) :
    (levelFormula C k).toks.length ≤ 100 * (k + 1) ^ 2 := by
  induction k with
  | zero => simp [levelFormula, CTLStar.toks, natToks, aInit, Nat.bits, Nat.binaryRec]
  | succ k ih =>
    have := wrap_toks_length k (gateAt C k) (levelFormula C k)
    simp only [levelFormula]; nlinarith

/-- The formula of the reduction has polynomial (quadratic) size in the number of gates, even
though its nesting depth is linear: the previous level occurs only once in each new level. -/
theorem reductionFormula_toks_length (C : List MGate) :
    (reductionFormula C).toks.length ≤ 100 * (C.length + 1) ^ 2 :=
  levelFormula_toks_length C C.length

end MCVPReduction

end PathChecking
