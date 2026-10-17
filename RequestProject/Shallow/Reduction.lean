module

public import RequestProject.Logics

/-!
# CTL* tree checking on trees with shallow branching, reduced to LTL path checking

A tree has *branching depth at most `d`* (`ShallowBranching d t`) if every node with two or
more children lies at depth `< d`.  Below depth `d` the tree consists of disjoint simple paths
(each ending in a leaf, which loops to itself).

This file gives an adaptive reduction of CTL* tree checking on such trees to LTL path checking
(`LTLPathChecking`, over lasso paths) that uses `d + 1` rounds of queries.  The reduction is
the function `Shallow.vals`, which is parameterised by an arbitrary LTL path-checking oracle
`O : LTL → LassoPath → Bool`.  Its correctness is `Shallow.treeSat_iff_vals`.

* **Tail round** (`tailLasso`, `erase`): below the branching region every node has exactly one
  path, so `E ψ` is equivalent to `ψ` there; the whole formula becomes an LTL formula
  (`erase`, which deletes every `E`) checked on the lasso `stem · leaf^ω` of the unique path
  (`holds_iff_erase`).
* **Branching rounds** (`roundLasso`, `tr`): at a node `v`, let `p₀, …, p_{k-1}` be the paths
  starting at `v` (one per leaf below `v`).  Assume that for every relevant subformula `ψ` the
  truth value of `ψ` on every tail `pⱼ[1..]` is known.  Write these values, as fresh atomic
  propositions `nm φ ψ` (odd numbers `≤ 2|φ| + 1`; original propositions `a` become `2a`),
  into the letters of the *cyclic* word `(L₀ L₁ ⋯ L_{k-1})^ω`.  Then the value of
  any subformula `χ` on `pⱼ` is the LTL path-checking answer for `tr χ` on this word, started at
  position `j` (`round_correct`).  Here `tr` replaces `X ψ` and the "next" part of `φ U ψ` by the
  fresh propositions and translates `E ψ` to `F (tr ψ)`: since the word is cyclic, `F` sees every
  path through `v`.  `tr χ` is linear in the size of `χ`.

Applying a branching round at each depth `d-1, …, 0` and the tail round at depth `d` decides
the formula with `d + 1` rounds of parallel LTL path-checking queries.

## References

We know of no published source for this reduction and have not checked the literature for
one. The target problem, LTL path checking, is in `AC¹(LogDCFL)` by Kuhtz–Finkbeiner
[KF09, Theorem 1], [KF12, Theorem 1] for finite paths, and by [Kuh10, Corollary 4] for
ultimately periodic paths. Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

namespace Shallow

/-! ## Trees and their paths -/

/-- Prepend a node to an infinite path. -/
def pcons (v : LTree) (p : ℕ → LTree) : ℕ → LTree
  | 0 => v
  | i + 1 => p i

/-- The list of all paths starting at a node, one per leaf below it (in left-to-right order). -/
def treePaths : LTree → List (ℕ → LTree)
  | .node l [] => [fun _ => .node l []]
  | .node l cs => cs.flatMap fun c => (treePaths c).map (pcons (.node l cs))

/-- A *linear* tree: every node has at most one child, i.e. the tree is a simple path. -/
inductive Linear : LTree → Prop
  | leaf (l : Finset ℕ) : Linear (.node l [])
  | cons (l : Finset ℕ) (c : LTree) : Linear c → Linear (.node l [c])

/-- `ShallowBranching d t`: every node of `t` with at least two children lies at depth `< d`.
(Equivalently: every subtree rooted at depth `d` is linear.) -/
inductive ShallowBranching : ℕ → LTree → Prop
  | lin {n : ℕ} {t : LTree} : Linear t → ShallowBranching n t
  | step {n : ℕ} {l : Finset ℕ} {cs : List LTree} :
      (∀ c ∈ cs, ShallowBranching n c) → ShallowBranching (n + 1) (.node l cs)

/-- Boolean test for linearity. -/
def isLin : LTree → Bool
  | .node _ [] => true
  | .node _ [c] => isLin c
  | _ => false

/-! ## The tail round -/

/-- Delete every path quantifier, turning a CTL* formula into an LTL formula. -/
def erase : CTLStar → LTL
  | .ap a => .ap a
  | .tt => .tt
  | .neg φ => .neg (erase φ)
  | .and φ ψ => .and (erase φ) (erase ψ)
  | .X φ => .X (erase φ)
  | .U φ ψ => .U (erase φ) (erase ψ)
  | .E φ => erase φ

/-- Labels of a linear tree, except the final leaf (first child taken in general). -/
def tailStem : LTree → List (Finset ℕ)
  | .node _ [] => []
  | .node l (c :: _) => l :: tailStem c

/-- Label of the final leaf of a linear tree (first child taken in general). -/
def tailLeaf : LTree → Finset ℕ
  | .node l [] => l
  | .node _ (c :: _) => tailLeaf c

/-- The lasso `stem · leaf^ω` of the unique path of a linear tree. -/
def tailLasso (v : LTree) : LassoPath := ⟨tailStem v, [tailLeaf v], by simp⟩

/-! ## A branching round -/

/-- The subformulas whose value one step later is needed: arguments of `X` and the
`U`-subformulas themselves. -/
def pieces : CTLStar → List CTLStar
  | .ap _ => []
  | .tt => []
  | .neg φ => pieces φ
  | .and φ ψ => pieces φ ++ pieces ψ
  | .X φ => φ :: pieces φ
  | .U φ ψ => .U φ ψ :: (pieces φ ++ pieces ψ)
  | .E φ => pieces φ

deriving instance DecidableEq for CTLStar

/-- Name of the fresh proposition carrying the value of the piece `ψ` of `φ₀` one step later:
`2 * i + 1`, where `i` is the position of `ψ` in `pieces φ₀`. -/
def nm (φ₀ ψ : CTLStar) : ℕ := 2 * (pieces φ₀).idxOf ψ + 1

/-- Translation used in a branching round for the input formula `φ₀`.  Original propositions
`a` become `2a`; the value of a piece `ψ` one step later is the fresh proposition `nm φ₀ ψ`;
`E ψ` becomes `F (tr ψ) = tt U tr ψ`; `φ U ψ` becomes `ψ ∨ (φ ∧ next(φ U ψ))`. -/
def tr (φ₀ : CTLStar) : CTLStar → LTL
  | .ap a => .ap (2 * a)
  | .tt => .tt
  | .neg φ => .neg (tr φ₀ φ)
  | .and φ ψ => .and (tr φ₀ φ) (tr φ₀ ψ)
  | .X φ => .ap (nm φ₀ φ)
  | .U φ ψ => .neg (.and (.neg (tr φ₀ ψ))
      (.neg (.and (tr φ₀ φ) (.ap (nm φ₀ (CTLStar.U φ ψ))))))
  | .E φ => .U .tt (tr φ₀ φ)

/-- Letter of the cyclic word for one path: the node label (doubled) and the fresh
propositions of those pieces of `φ` that hold one step later on this path. -/
def roundLetter (φ : CTLStar) (lab : Finset ℕ) (b : CTLStar → Bool) : Finset ℕ :=
  lab.image (2 * ·) ∪ (((pieces φ).filter (fun ψ => b ψ)).map
    (nm φ)).toFinset

/-- The cyclic word `(L₀ ⋯ L_{k-1})^ω` of a branching round, rotated to start at path `j`. -/
def roundLasso (φ : CTLStar) (lab : Finset ℕ) (bs : List (CTLStar → Bool)) (j : ℕ) :
    LassoPath :=
  ⟨[], if bs = [] then [∅] else (bs.map (roundLetter φ lab)).rotate j, by
    split_ifs with h <;> simp [h]⟩

/-! ## The reduction -/

/-- **The reduction.**  `vals O φ n v` lists, for every path `p` starting at `v` (in the order of
`treePaths v`), a table of truth values of subformulas of `φ` on `p`, computed only from
answers of the LTL path-checking oracle `O`.  The parameter `n` bounds the branching depth of
`v`; the recursion depth, i.e. the number of query rounds, is at most `n + 1`. -/
def vals (O : LTL → LassoPath → Bool) (φ : CTLStar) : ℕ → LTree → List (CTLStar → Bool)
  | 0, v => [fun χ => O (erase χ) (tailLasso v)]
  | n + 1, v =>
    if isLin v then [fun χ => O (erase χ) (tailLasso v)] else
      let next := v.children.flatMap (vals O φ n)
      (List.range next.length).map fun j χ => O (tr φ χ) (roundLasso φ v.label next j)

/-! ## Correctness -/

/-- The paths of `treePaths v` are exactly the tree paths starting at `v`. -/
theorem mem_treePaths : ∀ (v : LTree) (π : ℕ → LTree),
    π ∈ treePaths v ↔ IsTreePath π ∧ π 0 = v
  | .node l [], π => by
    simp only [treePaths, List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨fun i => Or.inr ⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨hπ, h0⟩
      funext i
      induction i with
      | zero => exact h0
      | succ i ih =>
        rcases hπ i with h | h
        · rw [ih] at h
          simp [LTree.children] at h
        · rw [h.2, ih]
  | .node l (c :: cs), π => by
    have key : ∀ c' ∈ c :: cs, ∀ p, p ∈ treePaths c' ↔ IsTreePath p ∧ p 0 = c' :=
      fun c' hc' p => mem_treePaths c' p
    simp only [treePaths]
    rw [List.mem_flatMap]
    constructor
    · rintro ⟨c', hc', hp⟩
      obtain ⟨p, hp', rfl⟩ := List.mem_map.1 hp
      obtain ⟨hpp, hp0⟩ := (key c' hc' p).1 hp'
      refine ⟨?_, rfl⟩
      intro i
      cases i with
      | zero => left; simpa [pcons, LTree.children, hp0] using hc'
      | succ i => simpa [pcons] using hpp i
    · rintro ⟨hπ, h0⟩
      have h1 : π 1 ∈ c :: cs := by
        rcases hπ 0 with h | h <;> simp_all [LTree.children]
      refine ⟨π 1, h1, List.mem_map.2 ⟨fun i => π (i + 1),
        (key _ h1 _).2 ⟨fun i => hπ (i + 1), rfl⟩, ?_⟩⟩
      funext i
      cases i <;> simp [pcons, h0]
termination_by v => sizeOf v
decreasing_by
  have := List.sizeOf_lt_of_mem hc'
  have h2 : sizeOf (c :: cs) = 1 + sizeOf c + sizeOf cs := rfl
  simp_wf
  omega

/-- Tail round: on a path starting at a linear node, a CTL* formula holds iff its erasure holds
on the label sequence. -/
theorem linear_child {v c : LTree} (hv : Linear v) (hc : c ∈ v.children) : Linear c := by
  cases hv with
  | leaf l => simp [LTree.children] at hc
  | cons l c' hc' => simp [LTree.children] at hc; rw [hc]; exact hc'

theorem linear_children_eq {v c c' : LTree} (hv : Linear v) (hc : c ∈ v.children)
    (hc' : c' ∈ v.children) : c = c' := by
  cases hv with
  | leaf l => simp [LTree.children] at hc
  | cons l d hd => simp [LTree.children] at hc hc'; rw [hc, hc']

theorem linear_path (π : ℕ → LTree) (hπ : IsTreePath π) (hlin : Linear (π 0)) :
    ∀ i, Linear (π i) := by
  intro i
  induction i with
  | zero => exact hlin
  | succ i ih =>
    rcases hπ i with h | h
    · exact linear_child ih h
    · rw [h.2]; exact ih

theorem path_unique (π π' : ℕ → LTree) (hπ : IsTreePath π) (hπ' : IsTreePath π')
    (h0 : π 0 = π' 0) (hlin : Linear (π 0)) : π = π' := by
  have hl := linear_path π hπ hlin
  funext i
  induction i with
  | zero => exact h0
  | succ i ih =>
    have hi' := hπ' i
    rw [← ih] at hi'
    rcases hπ i with h | h <;> rcases hi' with h' | h'
    · exact linear_children_eq (hl i) h h'
    · rw [h'.1] at h; simp at h
    · rw [h.1] at h'; simp at h'
    · rw [h.2, h'.2, ih]

theorem ltl_sat_shift (w : ℕ → Finset ℕ) (ψ : LTL) (i k : ℕ) :
    LTL.Sat w ψ (i + k) ↔ LTL.Sat (fun n => w (n + k)) ψ i := by
  induction ψ generalizing i with
  | ap a => rfl
  | tt => rfl
  | neg φ ih => simp only [LTL.Sat, ih]
  | and φ ψ ih1 ih2 => simp only [LTL.Sat, ih1, ih2]
  | X φ ih =>
    simp only [LTL.Sat]
    rw [show i + k + 1 = (i + 1) + k by omega, ih]
  | U φ ψ ih1 ih2 =>
    simp only [LTL.Sat]
    constructor
    · rintro ⟨m, hm, hj⟩
      refine ⟨m, ?_, fun j hj' => ?_⟩
      · rw [← ih2, show i + m + k = i + k + m by omega]; exact hm
      · rw [← ih1, show i + j + k = i + k + j by omega]; exact hj j hj'
    · rintro ⟨m, hm, hj⟩
      refine ⟨m, ?_, fun j hj' => ?_⟩
      · rw [show i + k + m = i + m + k by omega, ih2]; exact hm
      · rw [show i + k + j = i + j + k by omega, ih1]; exact hj j hj'

theorem isTreePath_shift (π : ℕ → LTree) (hπ : IsTreePath π) (k : ℕ) :
    IsTreePath (fun i => π (i + k)) := by
  intro i
  have := hπ (i + k)
  rw [show i + k + 1 = i + 1 + k by omega] at this
  exact this

theorem holds_iff_erase (χ : CTLStar) (π : ℕ → LTree) (hπ : IsTreePath π)
    (hlin : Linear (π 0)) :
    CTLStar.Holds χ π ↔ LTL.Sat (fun i => (π i).label) (erase χ) 0 := by
  induction χ generalizing π with
  | ap a => rfl
  | tt => simp [CTLStar.Holds, erase, LTL.Sat]
  | neg φ ih => simp only [CTLStar.Holds, erase, LTL.Sat, ih π hπ hlin]
  | and φ ψ ih1 ih2 => simp only [CTLStar.Holds, erase, LTL.Sat, ih1 π hπ hlin, ih2 π hπ hlin]
  | X φ ih =>
    simp only [CTLStar.Holds, erase, LTL.Sat]
    rw [ih _ (isTreePath_shift π hπ 1) (linear_path π hπ hlin 1)]
    exact (ltl_sat_shift (fun i => (π i).label) _ 0 1).symm
  | U φ ψ ih1 ih2 =>
    simp only [CTLStar.Holds, erase, LTL.Sat, zero_add]
    have h1 := fun k => ih1 _ (isTreePath_shift π hπ k) (by simpa using linear_path π hπ hlin k)
    have h2 := fun k => ih2 _ (isTreePath_shift π hπ k) (by simpa using linear_path π hπ hlin k)
    simp only [h1, h2]
    refine exists_congr fun k => and_congr ?_ (forall_congr' fun j => imp_congr_right fun _ => ?_)
    · simpa using (ltl_sat_shift (fun i => (π i).label) (erase ψ) 0 k).symm
    · simpa using (ltl_sat_shift (fun i => (π i).label) (erase φ) 0 j).symm
  | E φ ih =>
    simp only [CTLStar.Holds, erase]
    rw [← ih π hπ hlin]
    constructor
    · rintro ⟨π', hπ', h0, h⟩
      rwa [path_unique π π' hπ hπ' h0.symm hlin]
    · intro h
      exact ⟨π, hπ, rfl, h⟩

/-- Letters of the tail lasso are the labels along the unique path of a linear tree. -/
theorem tailLasso_letter (v : LTree) (hv : Linear v) (π : ℕ → LTree) (hπ : π ∈ treePaths v)
    (i : ℕ) : (tailLasso v).letter i = (π i).label := by
  induction hv generalizing π i with
  | leaf l =>
    simp only [treePaths, List.mem_singleton] at hπ
    subst hπ
    simp [tailLasso, LassoPath.letter, tailStem, tailLeaf, LTree.label, Nat.mod_one]
  | cons l c hc ih =>
    simp only [treePaths, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_map] at hπ
    obtain ⟨p, hp, rfl⟩ := hπ
    cases i with
    | zero => simp [tailLasso, LassoPath.letter, tailStem, pcons, LTree.label]
    | succ i =>
      rw [show pcons (LTree.node l [c]) p (i + 1) = p i from rfl, ← ih p hp i]
      simp only [tailLasso, LassoPath.letter, tailStem, tailLeaf, List.length_cons]
      split_ifs with h1 h2 h2
      · simp
      · omega
      · omega
      · congr 2
        omega

theorem pieces_closed (χ : CTLStar) : ∀ ψ ∈ pieces χ, pieces ψ ⊆ pieces χ := by
  induction χ with
  | ap a => simp [pieces]
  | tt => simp [pieces]
  | neg φ ih => simpa [pieces] using ih
  | and φ ψ ih1 ih2 =>
    intro θ hθ
    simp only [pieces, List.mem_append] at hθ ⊢
    rcases hθ with h | h
    · exact (ih1 θ h).trans (List.subset_append_left _ _)
    · exact (ih2 θ h).trans (List.subset_append_right _ _)
  | X φ ih =>
    intro θ hθ
    simp only [pieces, List.mem_cons] at hθ ⊢
    rcases hθ with rfl | h
    · exact List.subset_cons_self _ _
    · exact (ih θ h).trans (List.subset_cons_self _ _)
  | U φ ψ ih1 ih2 =>
    intro θ hθ
    simp only [pieces, List.mem_cons, List.mem_append] at hθ
    rcases hθ with rfl | h | h
    · exact List.Subset.refl _
    · exact ((ih1 θ h).trans (List.subset_append_left _ _)).trans (List.subset_cons_self _ _)
    · exact ((ih2 θ h).trans (List.subset_append_right _ _)).trans (List.subset_cons_self _ _)
  | E φ ih => simpa [pieces] using ih

/-- The expansion law of until. -/
theorem holds_U_iff (φ ψ : CTLStar) (π : ℕ → LTree) :
    CTLStar.Holds (.U φ ψ) π ↔ CTLStar.Holds ψ π ∨
      (CTLStar.Holds φ π ∧ CTLStar.Holds (.U φ ψ) (fun i => π (i + 1))) := by
  simp only [CTLStar.Holds]
  constructor
  · rintro ⟨k, hk, hj⟩
    cases k with
    | zero => left; simpa using hk
    | succ k =>
      right
      refine ⟨by simpa using hj 0 (Nat.succ_pos k), k, ?_, fun j hj' => ?_⟩
      · convert hk using 2
      · convert hj (j + 1) (by omega) using 2
  · rintro (h | ⟨h1, k, hk, hj⟩)
    · exact ⟨0, by simpa using h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    · refine ⟨k + 1, ?_, fun j hj' => ?_⟩
      · convert hk using 2
      · cases j with
        | zero => simpa using h1
        | succ j => convert hj j (by omega) using 2

theorem mem_roundLetter_even (φ : CTLStar) (lab : Finset ℕ) (b : CTLStar → Bool) (a : ℕ) :
    2 * a ∈ roundLetter φ lab b ↔ a ∈ lab := by
  simp only [roundLetter, Finset.mem_union, Finset.mem_image, List.mem_toFinset, List.mem_map,
    nm]
  constructor
  · rintro (⟨x, hx, h⟩ | ⟨ψ, _, h⟩)
    · rwa [show x = a by omega] at hx
    · omega
  · intro h
    exact Or.inl ⟨a, h, rfl⟩

theorem mem_roundLetter_odd (φ : CTLStar) (lab : Finset ℕ) (b : CTLStar → Bool) (ψ : CTLStar)
    (hψ : ψ ∈ pieces φ) :
    nm φ ψ ∈ roundLetter φ lab b ↔ b ψ = true := by
  simp only [roundLetter, Finset.mem_union, Finset.mem_image, List.mem_toFinset, List.mem_map,
    List.mem_filter, nm]
  constructor
  · rintro (⟨x, _, h⟩ | ⟨θ, ⟨hθ, hb⟩, h⟩)
    · omega
    · rwa [(List.idxOf_inj hθ).1 (show (pieces φ).idxOf θ = (pieces φ).idxOf ψ by
        omega)] at hb
  · intro h
    exact Or.inr ⟨ψ, ⟨hψ, h⟩, rfl⟩

theorem getElem_congr_idx' {α : Type*} (l : List α) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i] = l[j] := by
  subst h; rfl

/-- Branching round on the (unrotated) cyclic word `W`, at every position `n`. -/
theorem round_cyclic (φ : CTLStar) (v : LTree) (ps : List (ℕ → LTree))
    (bs : List (CTLStar → Bool))
    (hps : ∀ π, π ∈ ps ↔ IsTreePath π ∧ π 0 = v) (hlen : bs.length = ps.length)
    (hk : 0 < ps.length)
    (hb : ∀ j (h1 : j < bs.length) (h2 : j < ps.length), ∀ ψ ∈ pieces φ,
      bs[j] ψ = true ↔ CTLStar.Holds ψ (fun i => ps[j] (i + 1)))
    (χ : CTLStar) (hχ : pieces χ ⊆ pieces φ) (n : ℕ) :
    CTLStar.Holds χ (ps[n % ps.length]'(Nat.mod_lt _ hk)) ↔
      LTL.Sat (fun m => ((bs.map (roundLetter φ v.label))[m % ps.length]?).getD ∅)
        (tr φ χ) n := by
  have hW : ∀ m, ((bs.map (roundLetter φ v.label))[m % ps.length]?).getD ∅ =
      roundLetter φ v.label (bs[m % ps.length]'(by rw [hlen]; exact Nat.mod_lt _ hk)) := by
    intro m
    rw [List.getElem?_map, List.getElem?_eq_getElem (by rw [hlen]; exact Nat.mod_lt _ hk)]
    rfl
  have hps0 : ∀ j (h : j < ps.length), ps[j] 0 = v := fun j h =>
    ((hps _).1 (List.getElem_mem h)).2
  induction χ generalizing n with
  | ap a =>
    simp only [CTLStar.Holds, tr, LTL.Sat]
    rw [hW, mem_roundLetter_even, hps0]
  | tt => simp [CTLStar.Holds, tr, LTL.Sat]
  | neg ψ ih => simp only [CTLStar.Holds, tr, LTL.Sat, ih hχ n]
  | and ψ₁ ψ₂ ih1 ih2 =>
    simp only [pieces] at hχ
    simp only [CTLStar.Holds, tr, LTL.Sat,
      ih1 ((List.subset_append_left _ _).trans hχ) n,
      ih2 ((List.subset_append_right _ _).trans hχ) n]
  | X ψ ih =>
    simp only [pieces] at hχ
    have hψ : ψ ∈ pieces φ := hχ List.mem_cons_self
    simp only [CTLStar.Holds, tr, LTL.Sat]
    rw [hW, mem_roundLetter_odd _ _ _ _ hψ, hb _ _ _ ψ hψ]
  | U ψ₁ ψ₂ ih1 ih2 =>
    simp only [pieces] at hχ
    have hU : CTLStar.U ψ₁ ψ₂ ∈ pieces φ := hχ List.mem_cons_self
    have h1 : pieces ψ₁ ⊆ pieces φ :=
      ((List.subset_append_left _ _).trans (List.subset_cons_self _ _)).trans hχ
    have h2 : pieces ψ₂ ⊆ pieces φ :=
      ((List.subset_append_right _ _).trans (List.subset_cons_self _ _)).trans hχ
    rw [holds_U_iff]
    simp only [tr, LTL.Sat, ← ih1 h1 n, ← ih2 h2 n]
    rw [hW, mem_roundLetter_odd _ _ _ _ hU, hb _ _ _ _ hU]
    tauto
  | E ψ ih =>
    simp only [pieces] at hχ
    simp only [CTLStar.Holds, tr, LTL.Sat]
    have hv := hps0 _ (Nat.mod_lt n hk)
    constructor
    · rintro ⟨π', hπ', h0, h⟩
      have hmem : π' ∈ ps := (hps π').2 ⟨hπ', h0.trans hv⟩
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hmem
      set k := ps.length with hkdef
      have hnk : n % k < k := Nat.mod_lt n hk
      refine ⟨(m + k - n % k) % k, ?_⟩
      have hmod : (n + (m + k - n % k) % k) % k = m := by
        have hn := Nat.mod_add_div n k
        rw [Nat.add_mod_mod,
          show n + (m + k - n % k) = m + k * (n / k + 1) by rw [Nat.mul_succ]; omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]
      exact ⟨(ih hχ _).1 (by rw [getElem_congr_idx' ps _ hm hmod]; exact h), fun _ _ => trivial⟩
    · rintro ⟨t, ht, -⟩
      replace ht := (ih hχ (n + t)).2 ht
      exact ⟨_, ((hps _).1 (List.getElem_mem _)).1,
        (hps0 _ (Nat.mod_lt _ hk)).trans hv.symm, ht⟩

/-- Letters of the rotated cyclic word. -/
theorem roundLasso_letter (φ : CTLStar) (lab : Finset ℕ) (bs : List (CTLStar → Bool))
    (hbs : bs ≠ []) (j m : ℕ) :
    (roundLasso φ lab bs j).letter m =
      ((bs.map (roundLetter φ lab))[(m + j) % bs.length]?).getD ∅ := by
  have hpos : 0 < bs.length := List.length_pos_of_ne_nil hbs
  simp only [roundLasso, LassoPath.letter, hbs, if_false, List.length_nil,
    Nat.not_lt_zero, Nat.sub_zero, List.length_rotate, List.length_map, List.getD_eq_getElem?_getD]
  rw [List.getElem?_rotate (by simpa using Nat.mod_lt m hpos), List.length_map, Nat.mod_add_mod]

/-- Branching round: correctness of the translation `tr` on the cyclic word. -/
theorem round_correct (φ : CTLStar) (v : LTree) (ps : List (ℕ → LTree))
    (bs : List (CTLStar → Bool))
    (hps : ∀ π, π ∈ ps ↔ IsTreePath π ∧ π 0 = v) (hlen : bs.length = ps.length)
    (hne : ps ≠ [])
    (hb : ∀ j (h1 : j < bs.length) (h2 : j < ps.length), ∀ ψ ∈ pieces φ,
      bs[j] ψ = true ↔ CTLStar.Holds ψ (fun i => ps[j] (i + 1)))
    (χ : CTLStar) (hχ : pieces χ ⊆ pieces φ) (j : ℕ) (hj : j < ps.length) :
    CTLStar.Holds χ ps[j] ↔ LTL.Sat (roundLasso φ v.label bs j).letter (tr φ χ) 0 := by
  have hk : 0 < ps.length := List.length_pos_of_ne_nil hne
  have hbs : bs ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  set W := fun m => ((bs.map (roundLetter φ v.label))[m % ps.length]?).getD ∅ with hWdef
  have hlet : (roundLasso φ v.label bs j).letter = fun m => W (m + j) := by
    funext m
    rw [roundLasso_letter _ _ _ hbs, hlen]
  have hs := ltl_sat_shift W (tr φ χ) 0 j
  rw [zero_add] at hs
  rw [hlet, ← hs, ← round_cyclic φ v ps bs hps hlen hk hb χ hχ j,
    getElem_congr_idx' ps _ hj (Nat.mod_eq_of_lt hj)]

theorem forall₂_exists_left {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (H : List.Forall₂ R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction H with
  | nil => simp at ha
  | cons h _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨b, hb, hr⟩ := ih ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem forall₂_exists_right {α β : Type*} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (H : List.Forall₂ R l₁ l₂) {b : β} (hb : b ∈ l₂) : ∃ a ∈ l₁, R a b := by
  induction H with
  | nil => simp at hb
  | cons h _ ih =>
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hr⟩ := ih hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

theorem isLin_iff : ∀ v : LTree, isLin v = true ↔ Linear v
  | .node l [] => by simpa [isLin] using Linear.leaf l
  | .node l [c] => by
    rw [isLin, isLin_iff c]
    constructor
    · exact Linear.cons l c
    · intro h
      cases h
      assumption
  | .node l (c :: d :: cs) => by
    simp only [isLin, Bool.false_eq_true, false_iff]
    intro h
    cases h

theorem linear_treePaths {v : LTree} (hv : Linear v) : ∃ p, treePaths v = [p] := by
  induction hv with
  | leaf l => exact ⟨fun _ => .node l [], by simp only [treePaths]⟩
  | cons l c hc ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨pcons (.node l [c]) p, by simp [treePaths, hp]⟩

theorem exists_treePath (v : LTree) : ∃ π, π ∈ treePaths v := by
  refine ⟨fun i => (Nat.rec (motive := fun _ => LTree) v
    (fun _ u => match u.children with | [] => u | c :: _ => c) i), ?_⟩
  rw [mem_treePaths]
  refine ⟨fun i => ?_, rfl⟩
  simp only
  generalize (Nat.rec (motive := fun _ => LTree) v
    (fun _ u => match u.children with | [] => u | c :: _ => c) i) = u
  cases h : u.children with
  | nil => right; exact ⟨rfl, by simp⟩
  | cons c cs => left; simp

theorem forall₂_flatMap {α β γ : Type*} {R : β → γ → Prop} (cs : List α)
    {f : α → List β} {g : α → List γ} (h : ∀ c ∈ cs, List.Forall₂ R (f c) (g c)) :
    List.Forall₂ R (cs.flatMap f) (cs.flatMap g) := by
  induction cs with
  | nil => exact List.Forall₂.nil
  | cons c cs ih =>
    simp only [List.flatMap_cons]
    exact List.rel_append (h c List.mem_cons_self)
      (ih fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

theorem tail_forall₂ (O : LTL → LassoPath → Bool)
    (hO : ∀ ψ p, O ψ p = true ↔ LTL.Sat p.letter ψ 0) (φ : CTLStar) (v : LTree)
    (hv : Linear v) :
    List.Forall₂ (fun f p => ∀ χ, pieces χ ⊆ pieces φ → (f χ = true ↔ CTLStar.Holds χ p))
      [fun χ => O (erase χ) (tailLasso v)] (treePaths v) := by
  obtain ⟨p, hp⟩ := linear_treePaths hv
  have hmem : p ∈ treePaths v := by rw [hp]; exact List.mem_singleton_self p
  obtain ⟨hpath, h0⟩ := (mem_treePaths v p).1 hmem
  rw [hp]
  refine List.Forall₂.cons (fun χ _ => ?_) List.Forall₂.nil
  rw [hO, holds_iff_erase χ p hpath (h0 ▸ hv),
    show (tailLasso v).letter = fun i => (p i).label from funext (tailLasso_letter v hv p hmem)]

/-- Correctness of the reduction, path by path. -/
theorem vals_correct (O : LTL → LassoPath → Bool)
    (hO : ∀ ψ p, O ψ p = true ↔ LTL.Sat p.letter ψ 0) (φ : CTLStar) :
    ∀ n v, ShallowBranching n v →
      List.Forall₂ (fun f p => ∀ χ, pieces χ ⊆ pieces φ → (f χ = true ↔ CTLStar.Holds χ p))
        (vals O φ n v) (treePaths v) := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have hlin : Linear v := by cases hv with | lin h => exact h
    exact tail_forall₂ O hO φ v hlin
  | succ n ih =>
    intro v hv
    by_cases hlin : Linear v
    · simp only [vals, (isLin_iff v).2 hlin, if_true]
      exact tail_forall₂ O hO φ v hlin
    · have hfalse : isLin v = false := by
        cases h : isLin v
        · rfl
        · exact absurd ((isLin_iff v).1 h) hlin
      simp only [vals, hfalse, Bool.false_eq_true, if_false]
      obtain ⟨l, cs, rfl, hcs⟩ : ∃ l cs, v = .node l cs ∧ ∀ c ∈ cs, ShallowBranching n c := by
        cases hv with
        | lin h => exact absurd h hlin
        | step h => exact ⟨_, _, rfl, h⟩
      have hne : cs ≠ [] := by
        rintro rfl
        exact hlin (Linear.leaf l)
      have hnext := forall₂_flatMap cs (fun c hc => ih c (hcs c hc))
      have hps_eq : treePaths (.node l cs) =
          (cs.flatMap treePaths).map (pcons (.node l cs)) := by
        cases cs with
        | nil => exact absurd rfl hne
        | cons c cs' => simp only [treePaths]; rw [List.map_flatMap]
      simp only [LTree.children, LTree.label]
      set next := cs.flatMap (vals O φ n) with hnextdef
      have hlenQ := hnext.length_eq
      have hlen : next.length = (treePaths (.node l cs)).length := by
        rw [hps_eq, List.length_map]; exact hlenQ
      have hpsne : treePaths (.node l cs) ≠ [] := by
        intro h
        obtain ⟨π, hπ⟩ := exists_treePath (.node l cs)
        rw [h] at hπ
        simp at hπ
      have hb : ∀ j (h1 : j < next.length) (h2 : j < (treePaths (.node l cs)).length),
          ∀ ψ ∈ pieces φ, next[j] ψ = true ↔
            CTLStar.Holds ψ (fun i => (treePaths (.node l cs))[j] (i + 1)) := by
        intro j h1 h2 ψ hψ
        have h3 : j < (cs.flatMap treePaths).length := hlenQ ▸ h1
        have hpj : (treePaths (.node l cs))[j] = pcons (.node l cs) (cs.flatMap treePaths)[j] := by
          simp only [hps_eq, List.getElem_map]
        rw [hpj]
        exact (List.forall₂_iff_get.1 hnext).2 j h1 h3 ψ (pieces_closed φ ψ hψ)
      rw [List.forall₂_iff_get]
      refine ⟨by simpa using hlen, fun i h1 h2 χ hχ => ?_⟩
      simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
      rw [hO]
      exact (round_correct φ (.node l cs) (treePaths (.node l cs)) next
        (fun π => mem_treePaths _ π) hlen hpsne hb χ hχ i h2).symm

/-- **Main theorem.**  For a tree `t` whose branching nodes all lie at depth `< d`, `t ⊨ φ`
iff all tables produced by the reduction `vals O φ d t` (which uses `d + 1` rounds of
LTL path-checking queries) report `φ` true. -/
theorem treeSat_iff_vals (O : LTL → LassoPath → Bool)
    (hO : ∀ ψ p, O ψ p = true ↔ LTL.Sat p.letter ψ 0) (d : ℕ) (t : LTree)
    (ht : ShallowBranching d t) (φ : CTLStar) :
    CTLStar.TreeSat t φ ↔ ∀ f ∈ vals O φ d t, f φ = true := by
  have H := vals_correct O hO φ d t ht
  constructor
  · intro h f hf
    obtain ⟨p, hp, hfp⟩ := forall₂_exists_left H hf
    exact (hfp φ (List.Subset.refl _)).2 (h p ((mem_treePaths t p).1 hp).1 ((mem_treePaths t p).1 hp).2)
  · intro h π hπ h0
    obtain ⟨f, hf, hfp⟩ := forall₂_exists_right H ((mem_treePaths t π).2 ⟨hπ, h0⟩)
    exact (hfp φ (List.Subset.refl _)).1 (h f hf)

/-- The main theorem instantiated with the semantic LTL path-checking oracle
`O ψ p = decide (p ⊨ ψ)` (the characteristic function of LTL path checking). -/
theorem treeSat_iff_ltlChecks (d : ℕ) (t : LTree) (ht : ShallowBranching d t) (φ : CTLStar) :
    CTLStar.TreeSat t φ ↔
      ∀ f ∈ vals (fun ψ p => @decide (LTL.Sat p.letter ψ 0) (Classical.dec _)) φ d t,
        f φ = true :=
  treeSat_iff_vals _ (fun _ _ => @decide_eq_true_iff _ (Classical.dec _)) d t ht φ

/-! ## Size of the queries -/

/-- Number of operators and atoms of a CTL* formula. -/
def fsize : CTLStar → ℕ
  | .ap _ => 1
  | .tt => 1
  | .neg φ => fsize φ + 1
  | .and φ ψ => fsize φ + fsize ψ + 1
  | .X φ => fsize φ + 1
  | .U φ ψ => fsize φ + fsize ψ + 1
  | .E φ => fsize φ + 1

/-- Number of operators and atoms of an LTL formula. -/
def lsize : LTL → ℕ
  | .ap _ => 1
  | .tt => 1
  | .neg φ => lsize φ + 1
  | .and φ ψ => lsize φ + lsize ψ + 1
  | .X φ => lsize φ + 1
  | .U φ ψ => lsize φ + lsize ψ + 1

/-- The queries of a branching round have linear size. -/
theorem lsize_tr_le (χ : CTLStar) : lsize (tr φ χ) ≤ 6 * fsize χ := by
  induction χ <;> simp only [tr, lsize, fsize] at * <;> omega

/-- The queries of the tail round have at most the size of the formula. -/
theorem lsize_erase_le (χ : CTLStar) : lsize (erase χ) ≤ fsize χ := by
  induction χ <;> simp only [erase, lsize, fsize] at * <;> omega

theorem pieces_length_le (φ : CTLStar) : (pieces φ).length ≤ fsize φ := by
  induction φ <;> simp only [pieces, fsize, List.length_append, List.length_cons,
    List.length_nil] at * <;> omega

/-- The fresh propositions are small numbers: at most `2 |φ| + 1`. -/
theorem nm_le (φ ψ : CTLStar) : nm φ ψ ≤ 2 * fsize φ + 1 := by
  have h1 := List.idxOf_le_length (a := ψ) (l := pieces φ)
  have h2 := pieces_length_le φ
  simp only [nm]
  omega

/-- The cyclic word of a branching round has one letter per path from the node. -/
theorem roundLasso_loop_length (φ : CTLStar) (lab : Finset ℕ) (bs : List (CTLStar → Bool))
    (hbs : bs ≠ []) (j : ℕ) : (roundLasso φ lab bs j).loop.length = bs.length := by
  simp [roundLasso, hbs]

end Shallow

end PathChecking
