module

public import RequestProject.MCVP.Defs
public import RequestProject.Shallow.Reduction

/-!
# The shallow-branching reduction with the language `LTLPathChecking` as oracle

`Shallow.vals` is parameterised by an abstract oracle `O : LTL → LassoPath → Bool`.  Here the
oracle is the language `LTLPathChecking` itself: a query `(ψ, p)` is written as the binary word
`ltlQuery ψ p` (the encoding used in the definition of `LTLPathChecking`) and the oracle answers
whether this word belongs to the language.  Unique decodability of the encoding shows that this
oracle is an LTL path-checking oracle (`ltlQuery_mem_iff`), so the reduction is correct with
membership queries to `LTLPathChecking` (`treeSat_iff_vals_LTLPathChecking`).
-/

@[expose] public section

namespace PathChecking

namespace Shallow

open MCVPReduction

lemma LTL.toks_append_eq {φ ψ : LTL} {l l' : List Tok}
    (h : φ.toks ++ l = ψ.toks ++ l') : φ = ψ ∧ l = l' := by
  induction φ generalizing ψ l l' with
  | ap a =>
    cases ψ <;> simp [LTL.toks] at h
    obtain ⟨rfl, rfl⟩ := natToks_append_eq h
    exact ⟨rfl, rfl⟩
  | tt => cases ψ <;> simp_all [LTL.toks]
  | neg φ ih =>
    cases ψ <;> simp [LTL.toks] at h
    obtain ⟨rfl, rfl⟩ := ih h
    exact ⟨rfl, rfl⟩
  | and φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp [LTL.toks] at h
    obtain ⟨e1, h2⟩ := ih₁ h
    obtain ⟨e2, e3⟩ := ih₂ h2
    exact ⟨by rw [e1, e2], e3⟩
  | X φ ih =>
    cases ψ <;> simp [LTL.toks] at h
    obtain ⟨rfl, rfl⟩ := ih h
    exact ⟨rfl, rfl⟩
  | U φ₁ φ₂ ih₁ ih₂ =>
    cases ψ <;> simp [LTL.toks] at h
    obtain ⟨e1, h2⟩ := ih₁ h
    obtain ⟨e2, e3⟩ := ih₂ h2
    exact ⟨by rw [e1, e2], e3⟩

lemma finsets_rpar_eq {xs ys : List (Finset ℕ)} {l l' : List Tok}
    (h : xs.flatMap finsetToks ++ Tok.rpar :: l = ys.flatMap finsetToks ++ Tok.rpar :: l') :
    xs = ys ∧ l = l' := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simpa using h
    | cons y ys => simp [finsetToks] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [finsetToks] at h
    | cons y ys =>
      simp only [List.flatMap_cons, List.append_assoc] at h
      obtain ⟨e1, h2⟩ := finsetToks_append_eq h
      obtain ⟨e2, e3⟩ := ih h2
      exact ⟨by rw [e1, e2], e3⟩

lemma LassoPath.toks_inj {p q : LassoPath} (h : p.toks = q.toks) :
    p.stem = q.stem ∧ p.loop = q.loop := by
  simp only [LassoPath.toks, List.cons.injEq, true_and] at h
  obtain ⟨h1, h2⟩ := finsets_rpar_eq h
  simp only [List.cons.injEq, true_and] at h2
  exact ⟨h1, (finsets_rpar_eq (l := []) (l' := []) (by simpa using h2)).1⟩

/-- The binary word encoding the LTL path-checking query `(ψ, p)`; this is exactly the
instance format of `LTLPathChecking`. -/
def ltlQuery (ψ : LTL) (p : LassoPath) : Word :=
  encodeToks (Tok.lpar :: (ψ.toks ++ (Tok.rpar :: p.toks)))

/-- The encoded query belongs to `LTLPathChecking` iff the lasso satisfies the formula. -/
theorem ltlQuery_mem_iff (ψ : LTL) (p : LassoPath) :
    ltlQuery ψ p ∈ LTLPathChecking ↔ LTL.Sat p.letter ψ 0 := by
  constructor
  · rintro ⟨ψ', p', hx, hs⟩
    have h' := encodeToks_injective hx
    simp only [List.cons.injEq, true_and] at h'
    obtain ⟨rfl, h''⟩ := LTL.toks_append_eq h'
    simp only [List.cons.injEq, true_and] at h''
    obtain ⟨h1, h2⟩ := LassoPath.toks_inj h''
    have : p.letter = p'.letter := by
      funext i; simp only [LassoPath.letter, h1, h2]
    rwa [this]
  · intro h
    exact ⟨ψ, p, rfl, h⟩

/-- The oracle that answers a query `(ψ, p)` by a membership query of its encoding to the
language `B`. -/
noncomputable def langOracle (B : Language) (ψ : LTL) (p : LassoPath) : Bool :=
  @decide (ltlQuery ψ p ∈ B) (Classical.dec _)

/-- Membership queries to `LTLPathChecking` form an LTL path-checking oracle. -/
theorem langOracle_LTLPathChecking (ψ : LTL) (p : LassoPath) :
    langOracle LTLPathChecking ψ p = true ↔ LTL.Sat p.letter ψ 0 := by
  rw [langOracle, @decide_eq_true_iff _ (Classical.dec _), ltlQuery_mem_iff]

/-- **The reduction with `LTLPathChecking` as oracle.**  If every branching node of `t` lies at
depth `< d`, then `t ⊨ φ` iff all truth tables computed by `vals` — asking `d + 1` rounds of
membership queries `ltlQuery ψ p ∈ LTLPathChecking` — report `φ` true. -/
theorem treeSat_iff_vals_LTLPathChecking (d : ℕ) (t : LTree) (ht : ShallowBranching d t)
    (φ : CTLStar) :
    CTLStar.TreeSat t φ ↔ ∀ f ∈ vals (langOracle LTLPathChecking) φ d t, f φ = true :=
  treeSat_iff_vals _ langOracle_LTLPathChecking d t ht φ

end Shallow

end PathChecking
