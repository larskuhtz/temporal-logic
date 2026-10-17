module

public import RequestProject.Shallow.Reduction

/-!
# Semantics of CTL on finite trees: state formulas and expansion laws

`CSat s χ` says that the CTL formula `χ` holds at the root of the tree `s` (via the CTL*
semantics of `RequestProject/Logics.lean`).  CTL formulas are state formulas: their truth on a
tree path only depends on the first node (`holds_iff_csat`).  The expansion laws express
`EX`, `EU` and `AU` at a node through the children of the node.
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open Shallow

/-- `χ` holds at the root of `s`. -/
def CSat (s : LTree) (χ : CTL) : Prop := CTLStar.TreeSat s χ.toCTLStar

/-- One step of the leftmost path. -/
def stepL (t : LTree) : LTree :=
  match t.children with
  | [] => t
  | c :: _ => c

lemma isTreePath_iter (s : LTree) : IsTreePath (fun n => stepL^[n] s) := by
  intro i
  simp only [Function.iterate_succ_apply']
  generalize stepL^[i] s = t
  obtain ⟨l, cs⟩ := t
  cases cs with
  | nil => right; simp [stepL, LTree.children]
  | cons c cs => left; simp [stepL, LTree.children]

lemma exists_path (s : LTree) : ∃ π, IsTreePath π ∧ π 0 = s :=
  ⟨_, isTreePath_iter s, rfl⟩

/-- Prepending a node to a path starting at one of its children. -/
def consP (s : LTree) (π : ℕ → LTree) : ℕ → LTree := fun n => if n = 0 then s else π (n - 1)

lemma isTreePath_consP {s : LTree} {π : ℕ → LTree} (hπ : IsTreePath π) (h0 : π 0 ∈ s.children) :
    IsTreePath (consP s π) := by
  intro i
  cases i with
  | zero => left; simpa [consP] using h0
  | succ i => simpa [consP] using hπ i

lemma consP_shift (s : LTree) (π : ℕ → LTree) : (fun i => consP s π (i + 1)) = π := by
  funext i; simp [consP]

/-- Truth of the CTL* translation of a CTL formula depends only on the first node. -/
lemma holds_dep (χ : CTL) : ∀ π π' : ℕ → LTree, π 0 = π' 0 →
    (CTLStar.Holds χ.toCTLStar π ↔ CTLStar.Holds χ.toCTLStar π') := by
  induction χ with
  | ap a => intro π π' h; simp [CTL.toCTLStar, CTLStar.Holds, h]
  | tt => intro π π' h; simp [CTL.toCTLStar, CTLStar.Holds]
  | neg φ ih => intro π π' h; simp only [CTL.toCTLStar, CTLStar.Holds, ih π π' h]
  | and φ ψ ih1 ih2 => intro π π' h; simp only [CTL.toCTLStar, CTLStar.Holds, ih1 π π' h, ih2 π π' h]
  | EX φ ih => intro π π' h; simp only [CTL.toCTLStar, CTLStar.Holds, h]
  | EU φ ψ ih1 ih2 => intro π π' h; simp only [CTL.toCTLStar, CTLStar.Holds, h]
  | AU φ ψ ih1 ih2 => intro π π' h; simp only [CTL.toCTLStar, CTLStar.Holds, h]

/-- **CTL formulas are state formulas.** -/
lemma holds_iff_csat (χ : CTL) {π : ℕ → LTree} (hπ : IsTreePath π) :
    CTLStar.Holds χ.toCTLStar π ↔ CSat (π 0) χ := by
  constructor
  · intro h π' _ h0
    exact (holds_dep χ π π' h0.symm).1 h
  · intro h
    exact h π hπ rfl

lemma csat_iff_exists (χ : CTL) (s : LTree) :
    CSat s χ ↔ ∃ π, IsTreePath π ∧ π 0 = s ∧ CTLStar.Holds χ.toCTLStar π := by
  constructor
  · intro h
    obtain ⟨π, hπ, h0⟩ := exists_path s
    exact ⟨π, hπ, h0, h π hπ h0⟩
  · rintro ⟨π, hπ, h0, h⟩
    rw [holds_iff_csat χ hπ, h0] at h
    exact h

lemma csat_ap (a : ℕ) (s : LTree) : CSat s (.ap a) ↔ a ∈ s.label := by
  rw [csat_iff_exists]
  constructor
  · rintro ⟨π, -, h0, h⟩; simpa [CTL.toCTLStar, CTLStar.Holds, h0] using h
  · intro h
    obtain ⟨π, hπ, h0⟩ := exists_path s
    exact ⟨π, hπ, h0, by simpa [CTL.toCTLStar, CTLStar.Holds, h0] using h⟩

lemma csat_tt (s : LTree) : CSat s .tt := fun _ _ _ => trivial

lemma csat_neg (φ : CTL) (s : LTree) : CSat s (.neg φ) ↔ ¬ CSat s φ := by
  obtain ⟨π, hπ, h0⟩ := exists_path s
  rw [← h0, ← holds_iff_csat _ hπ, ← holds_iff_csat _ hπ]
  rfl

lemma csat_and (φ ψ : CTL) (s : LTree) : CSat s (.and φ ψ) ↔ CSat s φ ∧ CSat s ψ := by
  obtain ⟨π, hπ, h0⟩ := exists_path s
  rw [← h0, ← holds_iff_csat _ hπ, ← holds_iff_csat _ hπ, ← holds_iff_csat _ hπ]
  rfl

/-- The second node of a path is a child, or the node itself at a leaf. -/
lemma path_one {π : ℕ → LTree} (hπ : IsTreePath π) :
    π 1 ∈ (π 0).children ∨ ((π 0).children = [] ∧ π 1 = π 0) := hπ 0

/-- A path starting at a leaf stays there. -/
lemma path_leaf {π : ℕ → LTree} (hπ : IsTreePath π) (hl : (π 0).children = []) :
    ∀ n, π n = π 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases hπ n with h | h
    · rw [ih, hl] at h; simp at h
    · rw [h.2, ih]

lemma const_path {s : LTree} (hl : s.children = []) : IsTreePath (fun _ => s) :=
  fun _ => Or.inr ⟨hl, rfl⟩

/-- **Expansion law of `EX`.** -/
lemma csat_EX (φ : CTL) (s : LTree) :
    CSat s (.EX φ) ↔ (s.children = [] ∧ CSat s φ) ∨ ∃ c ∈ s.children, CSat c φ := by
  rw [csat_iff_exists]
  simp only [CTL.toCTLStar, CTLStar.Holds]
  constructor
  · rintro ⟨π, -, h0, π', hπ', h0', h⟩
    have hs := isTreePath_shift π' hπ' 1
    rw [holds_iff_csat φ hs] at h
    simp only [zero_add] at h
    rcases path_one hπ' with h1 | h1
    · exact Or.inr ⟨_, by rw [h0', h0] at h1; exact h1, h⟩
    · left; rw [h0', h0] at h1; rw [h1.2] at h; exact ⟨h1.1, h⟩
  · rintro (⟨hl, h⟩ | ⟨c, hc, h⟩)
    · refine ⟨_, const_path hl, rfl, _, const_path hl, rfl, ?_⟩
      exact (holds_iff_csat φ (const_path hl)).2 h
    · obtain ⟨π, hπ, h0⟩ := exists_path c
      have hp := isTreePath_consP hπ (by rw [h0]; exact hc)
      refine ⟨_, hp, rfl, _, hp, rfl, ?_⟩
      rw [consP_shift]
      exact (holds_iff_csat φ hπ).2 (by rw [h0]; exact h)

/-- The CTL* until of two CTL formulas on a path, in terms of the nodes. -/
lemma holds_U_nodes (φ ψ : CTL) {π : ℕ → LTree} (hπ : IsTreePath π) :
    CTLStar.Holds (.U φ.toCTLStar ψ.toCTLStar) π ↔
      ∃ k, CSat (π k) ψ ∧ ∀ j < k, CSat (π j) φ := by
  simp only [CTLStar.Holds]
  refine exists_congr fun k => and_congr ?_ (forall_congr' fun j => imp_congr_right fun _ => ?_)
  · rw [holds_iff_csat ψ (isTreePath_shift π hπ k)]; simp
  · rw [holds_iff_csat φ (isTreePath_shift π hπ j)]; simp

/-- **Expansion law of `EU`.** -/
lemma csat_EU (φ ψ : CTL) (s : LTree) :
    CSat s (.EU φ ψ) ↔ CSat s ψ ∨ (CSat s φ ∧ s.children ≠ [] ∧
      ∃ c ∈ s.children, CSat c (.EU φ ψ)) := by
  have key : ∀ t : LTree, CSat t (.EU φ ψ) ↔ ∃ π, IsTreePath π ∧ π 0 = t ∧
      ∃ k, CSat (π k) ψ ∧ ∀ j < k, CSat (π j) φ := by
    intro t
    rw [csat_iff_exists]
    simp only [CTL.toCTLStar, CTLStar.Holds]
    constructor
    · rintro ⟨π, -, h0, π', hπ', h0', h⟩
      exact ⟨π', hπ', h0'.trans h0, (holds_U_nodes φ ψ hπ').1 h⟩
    · rintro ⟨π, hπ, h0, h⟩
      exact ⟨π, hπ, h0, π, hπ, rfl, (holds_U_nodes φ ψ hπ).2 h⟩
  rw [key]
  constructor
  · rintro ⟨π, hπ, h0, k, hk, hj⟩
    cases k with
    | zero => left; rw [← h0]; exact hk
    | succ k =>
      by_cases hl : s.children = []
      · left
        have := path_leaf hπ (by rw [h0]; exact hl) (k + 1)
        rw [this, h0] at hk; exact hk
      · right
        refine ⟨by rw [← h0]; exact hj 0 (by omega), hl, π 1, ?_, ?_⟩
        · rcases path_one hπ with h1 | h1
          · rw [h0] at h1; exact h1
          · rw [h0] at h1; exact absurd h1.1 hl
        · rw [key]
          refine ⟨_, isTreePath_shift π hπ 1, by simp, k, by simpa using hk, fun j hj' => ?_⟩
          simpa using hj (j + 1) (by omega)
  · rintro (h | ⟨h1, -, c, hc, h2⟩)
    · obtain ⟨π, hπ, h0⟩ := exists_path s
      exact ⟨π, hπ, h0, 0, by rw [h0]; exact h, fun j hj => absurd hj (by omega)⟩
    · rw [key] at h2
      obtain ⟨π, hπ, h0, k, hk, hj⟩ := h2
      refine ⟨consP s π, isTreePath_consP hπ (by rw [h0]; exact hc), rfl, k + 1,
        by simpa [consP] using hk, fun j hj' => ?_⟩
      cases j with
      | zero => simpa [consP] using h1
      | succ j => simpa [consP] using hj j (by omega)

/-- **Expansion law of `AU`.** -/
lemma csat_AU (φ ψ : CTL) (s : LTree) :
    CSat s (.AU φ ψ) ↔ CSat s ψ ∨ (CSat s φ ∧ s.children ≠ [] ∧
      ∀ c ∈ s.children, CSat c (.AU φ ψ)) := by
  have key : ∀ t : LTree, CSat t (.AU φ ψ) ↔ ∀ π, IsTreePath π → π 0 = t →
      ∃ k, CSat (π k) ψ ∧ ∀ j < k, CSat (π j) φ := by
    intro t
    have e : CSat t (.AU φ ψ) ↔ ¬ ∃ π, IsTreePath π ∧ π 0 = t ∧
        ¬ CTLStar.Holds (.U φ.toCTLStar ψ.toCTLStar) π := by
      obtain ⟨π₀, hπ₀, h₀⟩ := exists_path t
      rw [← h₀, ← holds_iff_csat _ hπ₀, h₀]
      simp only [CTL.toCTLStar, CTLStar.Holds]
      constructor
      · rintro h ⟨π, hπ, h0, hn⟩; exact h ⟨π, hπ, h0.trans h₀.symm, hn⟩
      · rintro h ⟨π, hπ, h0, hn⟩; exact h ⟨π, hπ, h0.trans h₀, hn⟩
    rw [e]
    constructor
    · intro h π hπ h0
      by_contra hc
      exact h ⟨π, hπ, h0, fun hu => hc ((holds_U_nodes φ ψ hπ).1 hu)⟩
    · rintro h ⟨π, hπ, h0, hn⟩
      exact hn ((holds_U_nodes φ ψ hπ).2 (h π hπ h0))
  rw [key]
  constructor
  · intro h
    by_cases hψ : CSat s ψ
    · exact Or.inl hψ
    · right
      obtain ⟨π₀, hπ₀, h₀⟩ := exists_path s
      obtain ⟨k₀, hk₀, hj₀⟩ := h π₀ hπ₀ h₀
      have hk0 : k₀ ≠ 0 := by rintro rfl; rw [h₀] at hk₀; exact hψ hk₀
      have hφ : CSat s φ := by rw [← h₀]; exact hj₀ 0 (by omega)
      by_cases hl : s.children = []
      · exfalso
        have := path_leaf hπ₀ (by rw [h₀]; exact hl) k₀
        rw [this, h₀] at hk₀; exact hψ hk₀
      · refine ⟨hφ, hl, fun c hc => ?_⟩
        rw [key]
        intro π hπ h0
        obtain ⟨k, hk, hj⟩ := h (consP s π) (isTreePath_consP hπ (by rw [h0]; exact hc)) rfl
        have hk' : k ≠ 0 := by rintro rfl; exact hψ (by simpa [consP] using hk)
        refine ⟨k - 1, ?_, fun j hj' => ?_⟩
        · have := hk; simp only [consP, if_neg hk'] at this; exact this
        · have := hj (j + 1) (by omega); simpa [consP] using this
  · rintro (h | ⟨h1, hl, h2⟩) π hπ h0
    · exact ⟨0, by rw [h0]; exact h, fun j hj => absurd hj (by omega)⟩
    · have hc : π 1 ∈ s.children := by
        rcases path_one hπ with h' | h'
        · rw [h0] at h'; exact h'
        · rw [h0] at h'; exact absurd h'.1 hl
      have := h2 _ hc
      rw [key] at this
      obtain ⟨k, hk, hj⟩ := this _ (isTreePath_shift π hπ 1) (by simp)
      refine ⟨k + 1, by simpa using hk, fun j hj' => ?_⟩
      cases j with
      | zero => rw [h0]; exact h1
      | succ j => simpa using hj j (by omega)

/-- At a leaf, `AU` and `EU` reduce to their second argument. -/
lemma csat_AU_leaf (φ ψ : CTL) {s : LTree} (hl : s.children = []) :
    CSat s (.AU φ ψ) ↔ CSat s ψ := by
  rw [csat_AU]; simp [hl]

lemma csat_EU_leaf (φ ψ : CTL) {s : LTree} (hl : s.children = []) :
    CSat s (.EU φ ψ) ↔ CSat s ψ := by
  rw [csat_EU]; simp [hl]

end CTLT

end PathChecking
