module

public import RequestProject.Shallow.QSpec

/-!
# Stabilisation of the rounds

All queries of all triples are asked in every round.  The answers for a node at depth `δ`
are correct from round `d + 1 - δ` on (and from round `1` on for leaves and nodes at depth
`≥ d`), provided that all branching nodes lie at depth `< d`.  In particular the answers for
the root are correct after `d + 1` rounds (`stab_root`).
-/

@[expose] public section

namespace PathChecking

namespace ShallowP

open CTLP MCVPReduction

variable {ts : List Tok}

lemma toks_lt_length {u : ℕ} {s : LTree} {R : List Tok} (h : ts.drop u = s.toks ++ R) :
    u < ts.length := by
  have := toks_le h; have := LTree.toks_length_pos s; omega

/-- **Stabilisation.** -/
theorem stab {r₀ d m M : ℕ} (T : ℕ → ℕ → ℕ → ℕ → Bool) (hN : M + 1 < 2 ^ m)
    (hM : ts.length ≤ M)
    (hT : ∀ r u ℓ j, u < M → ℓ < M → j < M →
      (T (r + 1) u ℓ j = true ↔ encodeToks (QP ts r₀ d m M u ℓ j (T r)) ∈ LTLPathChecking)) :
    ∀ r u (s : LTree) R δ, ts.drop u = s.toks ++ R → r₀ ≤ u →
      cnt ts 3 r₀ (u - r₀) = cnt ts 4 r₀ (u - r₀) + δ → δ ≤ d →
      Shallow.ShallowBranching (d - δ) s → d + 1 ≤ r + δ → 1 ≤ r →
      ∀ ℓ < M, ∀ j (χ : CTLStar) Rj, ts.drop j = χ.toks ++ Rj →
        (T r u ℓ j = true ↔ CTLStar.Holds χ (pathOf ts u ℓ)) := by
  intro r
  induction r with
  | zero => intro u s R δ _ _ _ _ _ _ h; omega
  | succ r ih =>
    intro u s R δ hu hr₀ hδ hδd hsb hr _ ℓ hℓ j χ Rj hj
    rw [hT r u ℓ j (by have := toks_lt_length hu; omega) hℓ
      (by have := lt_length_of_drop hj; omega)]
    apply QP_correct (T r) hu hN hM _ _ hj
    · intro htc
      simp only [tailCond, Bool.or_eq_true, decide_eq_true_eq] at htc
      rcases htc with hl | hd
      · obtain ⟨l, cs⟩ := s
        rw [(isLeaf_iff hu).1 hl]; exact Shallow.Linear.leaf l
      · rw [show d - δ = 0 by omega] at hsb
        cases hsb with
        | lin h => exact h
    · intro htc ℓ' k ψ Rk hℓ' hk
      simp only [tailCond, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_le] at htc
      obtain ⟨hnl, hdep⟩ := htc
      obtain ⟨l, cs⟩ := s
      have hcs : cs ≠ [] := by
        intro e; subst e; rw [(isLeaf_iff hu).2 rfl] at hnl; exact absurd hnl (by simp)
      obtain ⟨s', hs', r', hp, hup, -⟩ := nxt_node ℓ' hu hcs
      obtain ⟨-, hbal⟩ := nxt_bal hu hcs ℓ'
      have hδ' : cnt ts 3 r₀ (nxt ts ℓ' u - r₀) = cnt ts 4 r₀ (nxt ts ℓ' u - r₀) + (δ + 1) := by
        rw [show nxt ts ℓ' u - r₀ = (u - r₀) + (nxt ts ℓ' u - u) by omega, cnt_add, cnt_add,
          show r₀ + (u - r₀) = u by omega, hbal, hδ]
        omega
      have hsb' : Shallow.ShallowBranching (d - (δ + 1)) s' := by
        generalize hn : d - δ = n at hsb
        cases hsb with
        | lin h => exact .lin (Shallow.linear_child h hs')
        | step h =>
          rename_i n'
          rw [show d - (δ + 1) = n' by omega]
          exact h s' hs'
      have hℓM : ℓ' < M := by
        rcases hℓ' with rfl | ⟨-, h2⟩
        · exact hℓ
        · have := toks_le hu; omega
      exact ih _ s' r' (δ + 1) hp (by omega) hδ' (by omega) hsb' (by omega) (by omega) ℓ' hℓM k
        ψ Rk hk

/-- The answers for the root after `d + 1` rounds. -/
theorem stab_root {r₀ d m M : ℕ} (T : ℕ → ℕ → ℕ → ℕ → Bool) (hN : M + 1 < 2 ^ m)
    (hM : ts.length ≤ M)
    (hT : ∀ r u ℓ j, u < M → ℓ < M → j < M →
      (T (r + 1) u ℓ j = true ↔ encodeToks (QP ts r₀ d m M u ℓ j (T r)) ∈ LTLPathChecking))
    {t : LTree} {R : List Tok} (ht : ts.drop r₀ = t.toks ++ R)
    (hsb : Shallow.ShallowBranching d t) {r : ℕ} (hr : d + 1 ≤ r) :
    ∀ ℓ < M, ∀ j (χ : CTLStar) Rj, ts.drop j = χ.toks ++ Rj →
      (T r r₀ ℓ j = true ↔ CTLStar.Holds χ (pathOf ts r₀ ℓ)) :=
  stab T hN hM hT r r₀ t R 0 ht le_rfl (by simp [cnt]) (Nat.zero_le _) (by simpa using hsb)
    (by omega) (by omega)

end ShallowP

end PathChecking
