module

public import RequestProject.Shallow.TSpec
public import RequestProject.Shallow.Oracle

/-!
# The queries of the positional reduction and their correctness

`QP ts r₀ d m N u ℓ j A` is the token list of the LTL query asked in a round for the triple
(node position `u`, target position `ℓ`, formula position `j`), where `A c ℓ' k` are the answers
of the previous round:

* if the node at `u` is a leaf or lies at depth `≥ d` (tail case), the query is `erase χ` on the
  tail lasso of the subtree at `u`;
* otherwise (branching case), the query is the positional translation `trP m χ j` on the
  cyclic word with one letter for `ℓ` and one letter for every position of the subtree at `u`.

`QP_correct`: if the answers of the previous round are correct for the children of `u`, the
query belongs to `LTLPathChecking` iff `χ` holds on the path from `u` towards `ℓ`.
-/

@[expose] public section

namespace PathChecking

namespace ShallowP

open CTLP MCVPReduction

variable {ts : List Tok}

/-- The tail case: a leaf, or a node at depth `≥ d` (counting brackets from the root `r₀`). -/
def tailCond (ts : List Tok) (r₀ d u : ℕ) : Bool :=
  isLeaf ts u || decide (d + cnt ts 4 r₀ (u - r₀) ≤ cnt ts 3 r₀ (u - r₀))

/-- The letter for the path from `u` towards `ℓ'`. -/
def letterToks (ts : List Tok) (m N u : ℕ) (A : ℕ → ℕ → ℕ → Bool) (ℓ' : ℕ) : List Tok :=
  Tok.lpar :: (freshToks N (A (nxt ts ℓ' u) ℓ') ++ labG ts m u) ++ [Tok.rpar]

/-- **The query** for the triple `(u, ℓ, j)`, given the answers `A` of the previous round. -/
def QP (ts : List Tok) (r₀ d m N u ℓ j : ℕ) (A : ℕ → ℕ → ℕ → Bool) : List Tok :=
  if tailCond ts r₀ d u then
    Tok.lpar :: (eraseToks ts j ++ Tok.rpar ::
      (Tok.lpar :: (stemToks ts u ++ Tok.rpar :: Tok.lpar :: (leafToks ts u ++ [Tok.rpar]))))
  else
    Tok.lpar :: (trToks ts m j ++ Tok.rpar :: (Tok.lpar :: Tok.rpar :: Tok.lpar ::
      ((letterToks ts m N u A ℓ ++ rng u (tend ts u - u) (letterToks ts m N u A)) ++
        [Tok.rpar])))

lemma lt_length_of_drop {k : ℕ} {ψ : CTLStar} {R : List Tok} (h : ts.drop k = ψ.toks ++ R) :
    k < ts.length := by
  have := CTLStar.toks_length_pos ψ
  obtain ⟨t, l, e⟩ : ∃ t l, ψ.toks = t :: l := by
    cases e : ψ.toks with
    | nil => rw [e] at this; simp at this
    | cons t l => exact ⟨t, l, rfl⟩
  exact lt_of_drop (t := t) (rest := l ++ R) (by rw [h, e]; rfl)

/-- Correctness of the tail query. -/
theorem QP_tail {r₀ d m N u ℓ j : ℕ} (A : ℕ → ℕ → ℕ → Bool) {s : LTree} {R : List Tok}
    (hu : ts.drop u = s.toks ++ R) (hlin : Shallow.Linear s) (htail : tailCond ts r₀ d u = true)
    {χ : CTLStar} {Rj : List Tok} (hj : ts.drop j = χ.toks ++ Rj) :
    encodeToks (QP ts r₀ d m N u ℓ j A) ∈ LTLPathChecking ↔
      CTLStar.Holds χ (pathOf ts u ℓ) := by
  have e : QP ts r₀ d m N u ℓ j A =
      Tok.lpar :: ((Shallow.erase χ).toks ++ Tok.rpar :: (Shallow.tailLasso s).toks) := by
    rw [QP, if_pos htail, eraseToks_eq χ hj, ← tail_toks hlin hu]
  rw [e, ← Shallow.ltlQuery, Shallow.ltlQuery_mem_iff]
  have hπ := pathOf_isTreePath hu ℓ
  have h0 : pathOf ts u ℓ 0 = s := by rw [pathOf_zero, sub_eq hu]
  rw [Shallow.holds_iff_erase χ _ hπ (by rw [h0]; exact hlin)]
  have hmem : pathOf ts u ℓ ∈ Shallow.treePaths s := (Shallow.mem_treePaths s _).2 ⟨hπ, h0⟩
  have hl : (Shallow.tailLasso s).letter = fun i => (pathOf ts u ℓ i).label := by
    funext i; exact Shallow.tailLasso_letter s hlin _ hmem i
  rw [hl]

/-- Correctness of the branching query. -/
theorem QP_branch {r₀ d m N u ℓ j : ℕ} (A : ℕ → ℕ → ℕ → Bool) {l : Finset ℕ}
    {cs : List LTree} {R : List Tok} (hu : ts.drop u = (LTree.node l cs).toks ++ R)
    (htail : tailCond ts r₀ d u = false) (hN : N + 1 < 2 ^ m)
    (hNt : ts.length ≤ N)
    (hA : ∀ ℓ' k (ψ : CTLStar) Rk, (ℓ' = ℓ ∨ (u ≤ ℓ' ∧ ℓ' < u + (LTree.node l cs).toks.length)) →
      ts.drop k = ψ.toks ++ Rk →
      (A (nxt ts ℓ' u) ℓ' k = true ↔ CTLStar.Holds ψ (pathOf ts (nxt ts ℓ' u) ℓ')))
    {χ : CTLStar} {Rj : List Tok} (hj : ts.drop j = χ.toks ++ Rj) :
    encodeToks (QP ts r₀ d m N u ℓ j A) ∈ LTLPathChecking ↔
      CTLStar.Holds χ (pathOf ts u ℓ) := by
  set s := LTree.node l cs with hs
  set S := s.toks.length
  set Ps : List ℕ := ℓ :: (List.range S).map (u + ·) with hPs
  set F : ℕ → Finset ℕ := fun ℓ' => (letterList m N (A (nxt ts ℓ' u) ℓ') l).toFinset with hF
  set Ls := Ps.map F with hLs
  set ps := Ps.map (pathOf ts u) with hps
  have hPs_mem : ∀ ℓ' ∈ Ps, ℓ' = ℓ ∨ (u ≤ ℓ' ∧ ℓ' < u + S) := by
    intro ℓ' h
    simp only [hPs, List.mem_cons, List.mem_map, List.mem_range] at h
    rcases h with rfl | ⟨i, hi, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨by omega, by omega⟩
  have hletter : ∀ ℓ', letterToks ts m N u A ℓ' = finsetToks (F ℓ') := by
    intro ℓ'
    rw [letterToks, labG_eq m hu, hF, ← letter_toks m N hN]
  have hlasso : Tok.lpar :: Tok.rpar :: Tok.lpar ::
      ((letterToks ts m N u A ℓ ++ rng u (tend ts u - u) (letterToks ts m N u A)) ++
        [Tok.rpar]) = (cycLasso Ls).toks := by
    have hne : Ls ≠ [] := by simp [hLs, hPs]
    rw [tend_tree s hu, Nat.add_sub_cancel_left]
    have hfl : Ls.flatMap finsetToks =
        letterToks ts m N u A ℓ ++ rng u S (letterToks ts m N u A) := by
      simp only [hLs, hPs, List.map_cons, List.flatMap_cons, List.flatMap_map, rng, hletter]
    simp only [cycLasso, hne, if_false, LassoPath.toks, List.flatMap_nil, List.nil_append, hfl,
      List.append_assoc]
    rfl
  have e : QP ts r₀ d m N u ℓ j A =
      Tok.lpar :: ((trP m χ j).toks ++ Tok.rpar :: (cycLasso Ls).toks) := by
    rw [QP, if_neg (by simp [htail]), trToks_eq m χ hj, ← hlasso]
  rw [e, ← Shallow.ltlQuery, Shallow.ltlQuery_mem_iff]
  have hk : 0 < ps.length := by simp [hps, hPs]
  have hlen : Ls.length = ps.length := by simp [hLs, hps]
  have hps' : ∀ π, π ∈ ps ↔ IsTreePath π ∧ π 0 = s := by
    intro π
    constructor
    · intro h
      simp only [hps, List.mem_map] at h
      obtain ⟨ℓ', -, rfl⟩ := h
      exact ⟨pathOf_isTreePath hu ℓ', by rw [pathOf_zero, sub_eq hu]⟩
    · rintro ⟨hπ, h0⟩
      obtain ⟨ℓ', hl1, hl2, rfl⟩ := path_cover _ s le_rfl hu π hπ h0
      simp only [hps, hPs, List.map_cons, List.mem_cons, List.mem_map, List.mem_range]
      exact Or.inr ⟨u + (ℓ' - u), ⟨ℓ' - u, by omega, rfl⟩, by rw [Nat.add_sub_cancel' hl1]⟩
  have hg : ∀ i (h : i < Ls.length) a, gm m a ∈ Ls[i] ↔ a ∈ s.label := by
    intro i h a
    simp only [hLs, List.getElem_map, hF]
    rw [mem_letterList_gm m N hN]; rfl
  have hfr : ∀ i (h1 : i < Ls.length) (h2 : i < ps.length) k (ψ : CTLStar) Rk,
      ts.drop k = ψ.toks ++ Rk → (k + 1 ∈ Ls[i] ↔ CTLStar.Holds ψ (fun t => ps[i] (t + 1))) := by
    intro i h1 h2 k ψ Rk hk
    have hkN : k < N := lt_of_lt_of_le (lt_length_of_drop hk) hNt
    simp only [hLs, List.getElem_map, hF]
    rw [mem_letterList_fresh m N hN _ _ k hkN,
      hA _ k ψ Rk (hPs_mem _ (List.getElem_mem _)) hk]
    have hpi : ps[i] = pathOf ts u (Ps[i]'(by simpa [hps] using h2)) := by simp [hps]
    rw [hpi, pathOf_shift]
  have := roundP_correct ts m s ps Ls hlen hk hps' hg hfr χ j Rj hj
  rw [← this]
  simp [hps, hPs]

/-- **Correctness of a query.** -/
theorem QP_correct {r₀ d m N u ℓ j : ℕ} (A : ℕ → ℕ → ℕ → Bool) {s : LTree} {R : List Tok}
    (hu : ts.drop u = s.toks ++ R) (hN : N + 1 < 2 ^ m) (hNt : ts.length ≤ N)
    (htl : tailCond ts r₀ d u = true → Shallow.Linear s)
    (hA : tailCond ts r₀ d u = false → ∀ ℓ' k (ψ : CTLStar) Rk,
      (ℓ' = ℓ ∨ (u ≤ ℓ' ∧ ℓ' < u + s.toks.length)) → ts.drop k = ψ.toks ++ Rk →
      (A (nxt ts ℓ' u) ℓ' k = true ↔ CTLStar.Holds ψ (pathOf ts (nxt ts ℓ' u) ℓ')))
    {χ : CTLStar} {Rj : List Tok} (hj : ts.drop j = χ.toks ++ Rj) :
    encodeToks (QP ts r₀ d m N u ℓ j A) ∈ LTLPathChecking ↔
      CTLStar.Holds χ (pathOf ts u ℓ) := by
  cases htc : tailCond ts r₀ d u with
  | true => exact QP_tail A hu (htl htc) htc hj
  | false =>
    obtain ⟨l, cs⟩ := s
    exact QP_branch A hu htc hN hNt (hA htc) hj

end ShallowP

end PathChecking
