module

public import RequestProject.CTLStarP.EvalProof
public import RequestProject.Shallow.Reduction

/-!
# A positional variant of the branching round

For the logspace implementation of the reduction, subformulas of the input formula are named
by their *token positions* in the encoded instance.  In a branching round at a node `v`, the
fresh proposition `k + 1` carries the value, one step later, of the subformula occurrence
starting at token position `k`; an original proposition `a` is renamed to
`gm m a = a · 2^m + (2^m - 1)` (for `m` large, these names are larger than all fresh names).

The translation `trP m χ j` of the occurrence `χ` at position `j` replaces
* `X ψ` (at `j`) by a formula equivalent to the fresh proposition `j + 2` (the name of `ψ`),
  which still contains the translation of `ψ` (so that the translation can be produced
  token by token);
* `ψ₁ U ψ₂` (at `j`) by `(j + 1 ∧ ψ₁) ∨ ψ₂`, written `¬(¬(j + 1 ∧ ψ₁) ∧ ¬ψ₂)`;
* `E ψ` by `tt U ψ`.

`roundP_cyclic` is the correctness of this translation on a cyclic word with one letter per
path starting at `v` (letters may repeat).
-/

@[expose] public section

namespace PathChecking

namespace ShallowP

open CTLP

/-- Renaming of original propositions: `a ↦ a · 2^m + (2^m - 1)`. -/
def gm (m a : ℕ) : ℕ := a * 2 ^ m + (2 ^ m - 1)

/-- Positional translation of the occurrence `χ` at token position `j`. -/
def trP (m : ℕ) : CTLStar → ℕ → LTL
  | .ap a, _ => .ap (gm m a)
  | .tt, _ => .tt
  | .neg ψ, j => .neg (trP m ψ (j + 1))
  | .and ψ₁ ψ₂, j => .and (trP m ψ₁ (j + 1)) (trP m ψ₂ (j + 1 + ψ₁.toks.length))
  | .X ψ, j => .neg (.and (.neg (.ap (j + 2))) (.neg (.and (.ap (j + 2)) (trP m ψ (j + 1)))))
  | .U ψ₁ ψ₂, j => .neg (.and (.neg (.and (.ap (j + 1)) (trP m ψ₁ (j + 1))))
      (.neg (trP m ψ₂ (j + 1 + ψ₁.toks.length))))
  | .E ψ, j => .U .tt (trP m ψ (j + 1))

lemma drop_toks_cons {ts : List Tok} {j : ℕ} {t : Tok} {l R : List Tok}
    (h : ts.drop j = (t :: l) ++ R) : ts.drop (j + 1) = l ++ R := by
  rw [← List.drop_drop, h]; rfl

/-- **Correctness of the positional translation on a cyclic word.** -/
theorem roundP_cyclic (ts : List Tok) (m : ℕ) (v : LTree) (ps : List (ℕ → LTree))
    (Ls : List (Finset ℕ)) (hlen : Ls.length = ps.length) (hk : 0 < ps.length)
    (hps : ∀ π, π ∈ ps ↔ IsTreePath π ∧ π 0 = v)
    (hg : ∀ i (h : i < Ls.length) a, gm m a ∈ Ls[i] ↔ a ∈ v.label)
    (hfr : ∀ i (h1 : i < Ls.length) (h2 : i < ps.length) k (ψ : CTLStar) R,
      ts.drop k = ψ.toks ++ R → (k + 1 ∈ Ls[i] ↔ CTLStar.Holds ψ (fun t => ps[i] (t + 1))))
    (χ : CTLStar) : ∀ j R, ts.drop j = χ.toks ++ R → ∀ n,
      CTLStar.Holds χ (ps[n % ps.length]'(Nat.mod_lt _ hk)) ↔
        LTL.Sat (fun t => (Ls[t % ps.length]?).getD ∅) (trP m χ j) n := by
  have hW : ∀ t, (Ls[t % ps.length]?).getD ∅ =
      Ls[t % ps.length]'(by rw [hlen]; exact Nat.mod_lt _ hk) := by
    intro t; rw [List.getElem?_eq_getElem]; rfl
  have hps0 : ∀ i (h : i < ps.length), ps[i] 0 = v := fun i h =>
    ((hps _).1 (List.getElem_mem h)).2
  induction χ with
  | ap a =>
    intro j R hj n
    simp only [CTLStar.Holds, trP, LTL.Sat]
    rw [hW, hg, hps0]
  | tt => intro j R hj n; simp [CTLStar.Holds, trP, LTL.Sat]
  | neg ψ ih =>
    intro j R hj n
    simp only [CTLStar.Holds, trP, LTL.Sat, ih (j + 1) R (drop_toks_cons hj) n]
  | and ψ₁ ψ₂ ih1 ih2 =>
    intro j R hj n
    have h1 : ts.drop (j + 1) = ψ₁.toks ++ (ψ₂.toks ++ R) := by
      have := drop_toks_cons (l := ψ₁.toks ++ ψ₂.toks) hj; simpa using this
    have h2 := drop_append_of_drop h1
    simp only [CTLStar.Holds, trP, LTL.Sat, ih1 _ _ h1 n, ih2 _ _ h2 n]
  | X ψ ih =>
    intro j R hj n
    have h1 : ts.drop (j + 1) = ψ.toks ++ R := drop_toks_cons hj
    simp only [CTLStar.Holds, trP, LTL.Sat]
    rw [hW, hfr _ _ (Nat.mod_lt _ hk) _ _ _ h1]
    tauto
  | U ψ₁ ψ₂ ih1 ih2 =>
    intro j R hj n
    have h1 : ts.drop (j + 1) = ψ₁.toks ++ (ψ₂.toks ++ R) := by
      have := drop_toks_cons (l := ψ₁.toks ++ ψ₂.toks) hj; simpa using this
    have h2 := drop_append_of_drop h1
    rw [holds_U_iff]
    simp only [trP, LTL.Sat, ← ih1 _ _ h1 n, ← ih2 _ _ h2 n]
    rw [hW, hfr _ _ (Nat.mod_lt _ hk) _ _ _ hj]
    tauto
  | E ψ ih =>
    intro j R hj n
    have h1 : ts.drop (j + 1) = ψ.toks ++ R := drop_toks_cons hj
    simp only [CTLStar.Holds, trP, LTL.Sat]
    have hv := hps0 _ (Nat.mod_lt n hk)
    constructor
    · rintro ⟨π', hπ', h0, h⟩
      have hmem : π' ∈ ps := (hps π').2 ⟨hπ', h0.trans hv⟩
      obtain ⟨m', hm, rfl⟩ := List.getElem_of_mem hmem
      set k := ps.length with hkdef
      have hnk : n % k < k := Nat.mod_lt n hk
      refine ⟨(m' + k - n % k) % k, ?_⟩
      have hmod : (n + (m' + k - n % k) % k) % k = m' := by
        have hn := Nat.mod_add_div n k
        rw [Nat.add_mod_mod,
          show n + (m' + k - n % k) = m' + k * (n / k + 1) by rw [Nat.mul_succ]; omega,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm]
      exact ⟨(ih _ _ h1 _).1 (by rw [Shallow.getElem_congr_idx' ps _ hm hmod]; exact h),
        fun _ _ => trivial⟩
    · rintro ⟨t, ht, -⟩
      replace ht := (ih _ _ h1 (n + t)).2 ht
      exact ⟨_, ((hps _).1 (List.getElem_mem _)).1,
        (hps0 _ (Nat.mod_lt _ hk)).trans hv.symm, ht⟩

/-- The lasso `[] · Ls^ω` (a default letter if `Ls` is empty). -/
def cycLasso (Ls : List (Finset ℕ)) : LassoPath :=
  ⟨[], if Ls = [] then [∅] else Ls, by split_ifs with h <;> simp [h]⟩

lemma cycLasso_letter (Ls : List (Finset ℕ)) (hne : Ls ≠ []) (t : ℕ) :
    (cycLasso Ls).letter t = (Ls[t % Ls.length]?).getD ∅ := by
  simp [cycLasso, LassoPath.letter, hne, List.getD_eq_getElem?_getD]

/-- **Branching round, positional version**: the path `ps[0]` satisfies `χ` iff the cyclic
word of the letters `Ls` satisfies the translation. -/
theorem roundP_correct (ts : List Tok) (m : ℕ) (v : LTree) (ps : List (ℕ → LTree))
    (Ls : List (Finset ℕ)) (hlen : Ls.length = ps.length) (hk : 0 < ps.length)
    (hps : ∀ π, π ∈ ps ↔ IsTreePath π ∧ π 0 = v)
    (hg : ∀ i (h : i < Ls.length) a, gm m a ∈ Ls[i] ↔ a ∈ v.label)
    (hfr : ∀ i (h1 : i < Ls.length) (h2 : i < ps.length) k (ψ : CTLStar) R,
      ts.drop k = ψ.toks ++ R → (k + 1 ∈ Ls[i] ↔ CTLStar.Holds ψ (fun t => ps[i] (t + 1))))
    (χ : CTLStar) (j : ℕ) (R : List Tok) (hj : ts.drop j = χ.toks ++ R) :
    CTLStar.Holds χ (ps[0]'hk) ↔ LTL.Sat (cycLasso Ls).letter (trP m χ j) 0 := by
  have hne : Ls ≠ [] := by
    intro h; rw [h] at hlen; simp at hlen; omega
  have := roundP_cyclic ts m v ps Ls hlen hk hps hg hfr χ j R hj 0
  simp only [Nat.zero_mod] at this
  rw [this]
  have e : (cycLasso Ls).letter = fun t => (Ls[t % ps.length]?).getD ∅ := by
    funext t; rw [cycLasso_letter _ hne, hlen]
  rw [e]

end ShallowP

end PathChecking
