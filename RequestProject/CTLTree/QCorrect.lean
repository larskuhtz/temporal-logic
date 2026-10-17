module

public import RequestProject.CTLTree.Query

/-!
# Correctness of the query of a round

`CQ_correct`: if the answers `A` of the previous round are correct for all nodes of size
`< sz u / 2`, then the query `CQ ts m M u j A` belongs to `LTLPathChecking` iff the CTL formula at
position `j` holds at the node at position `u`.
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open CTLP MCVPReduction ShallowP LS

variable {ts : List Tok}

lemma kpos_lt_tend {p : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) {jj : ℕ} (hj : jj < cs.length) :
    p < kpos l cs p jj ∧ kpos l cs p jj < tend ts p := by
  have := (kidP_eq (ts := ts) p (kpos l cs p jj)).1 ((kidP_iff h _).2 ⟨jj, hj, rfl⟩)
  exact ⟨this.2.1, this.2.2.1⟩

lemma smallKid_iff {p Z c : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) :
    smallKid ts Z p c = true ↔ ∃ jj < cs.length, c = kpos l cs p jj ∧ 2 * sz ts c < Z := by
  simp only [smallKid, Bool.and_eq_true, decide_eq_true_eq, kidP_iff h]
  constructor
  · rintro ⟨⟨jj, hj, rfl⟩, h2⟩; exact ⟨jj, hj, rfl, h2⟩
  · rintro ⟨jj, hj, rfl, h2⟩; exact ⟨⟨jj, hj, rfl⟩, h2⟩

lemma anyKid_iff {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) (P : ℕ → Bool) :
    anyKid ts Z p P = true ↔ ∃ jj, ∃ _ : jj < cs.length, 2 * sz ts (kpos l cs p jj) < Z ∧
      P (kpos l cs p jj) = true := by
  simp only [anyKid, List.any_eq_true, List.mem_range, Bool.and_eq_true, smallKid_iff h]
  constructor
  · rintro ⟨i, -, ⟨jj, hj, he, hs⟩, hP⟩
    exact ⟨jj, hj, he ▸ hs, he ▸ hP⟩
  · rintro ⟨jj, hj, hs, hP⟩
    have := kpos_lt_tend h hj
    refine ⟨kpos l cs p jj - p, by unfold sz; omega, ⟨jj, hj, by omega, ?_⟩, ?_⟩
    · rw [show p + (kpos l cs p jj - p) = kpos l cs p jj by omega]; exact hs
    · rw [show p + (kpos l cs p jj - p) = kpos l cs p jj by omega]; exact hP

lemma allKid_iff {p Z : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop p = (LTree.node l cs).toks ++ R) (P : ℕ → Bool) :
    allKid ts Z p P = true ↔ ∀ jj (_ : jj < cs.length), 2 * sz ts (kpos l cs p jj) < Z →
      P (kpos l cs p jj) = true := by
  simp only [allKid, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro H jj hj hs
    have := kpos_lt_tend h hj
    rcases H (kpos l cs p jj - p) (by unfold sz; omega) with h1 | h1
    · rw [show p + (kpos l cs p jj - p) = kpos l cs p jj by omega] at h1
      have : smallKid ts Z p (kpos l cs p jj) = true := (smallKid_iff h).2 ⟨jj, hj, rfl, hs⟩
      rw [this] at h1; exact absurd h1 (by simp)
    · rwa [show p + (kpos l cs p jj - p) = kpos l cs p jj by omega] at h1
  · intro H i _
    by_cases hk : smallKid ts Z p (p + i) = true
    · obtain ⟨jj, hj, he, hs⟩ := (smallKid_iff h).1 hk
      right; rw [he]; exact H jj hj (he ▸ hs)
    · left; simpa using hk

/-- Nodes inside a node are not larger. -/
lemma sz_le_of_inside {u q : ℕ} {s : LTree} {R : List Tok} (h : ts.drop u = s.toks ++ R)
    (hq1 : u ≤ q) (hq2 : q < tend ts u) (hn : isNode ts q = true) : sz ts q ≤ sz ts u := by
  rcases Nat.eq_or_lt_of_le hq1 with rfl | hlt
  · exact le_rfl
  · obtain ⟨t, R', -, ht⟩ := tend_le_of_inside h hlt hq2 hn
    unfold sz; omega

/-- Kids of chain nodes are small or the next chain node. -/
lemma kid_dich {u : ℕ} {s : LTree} {R : List Tok} (hu : ts.drop u = s.toks ++ R) {L : List ℕ}
    (hL : chainF ts (sz ts u) u = L) {i : ℕ} (hi : i < L.length) {l : Finset ℕ}
    {cs : List LTree} {R' : List Tok} (hq : ts.drop L[i] = (LTree.node l cs).toks ++ R')
    {jj : ℕ} (hj : jj < cs.length) :
    2 * sz ts (kpos l cs L[i] jj) < sz ts u ∨ ∃ h : i + 1 < L.length, L[i + 1] = kpos l cs L[i] jj := by
  obtain ⟨-, -, hmem, hstep, hlast⟩ := chain_struct (sz ts u) s.toks.length u s R le_rfl hu
    (by omega) le_rfl L hL
  by_cases hs : 2 * sz ts (kpos l cs L[i] jj) < sz ts u
  · exact Or.inl hs
  right
  have hnb : noBig ts (sz ts u) L[i] = false := by
    by_contra hc
    have := (noBig_iff hq).1 (by simpa using hc) jj hj
    exact hs this
  have hi1 : i + 1 < L.length := by
    by_contra hc
    have := (hlast i hi).2 (by omega)
    rw [this] at hnb; exact absurd hnb (by simp)
  refine ⟨hi1, ?_⟩
  obtain ⟨l', cs', R'', j', hj', hq', he⟩ := hstep i hi1
  have e := tree_unique hq hq'
  simp only [LTree.node.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  have hmi := hmem L[i] (List.getElem_mem _)
  have hmi1 := hmem L[i + 1] (List.getElem_mem _)
  have hszi : sz ts L[i] ≤ sz ts u :=
    sz_le_of_inside hu hmi.2.2.1 hmi.2.2.2 (isNode_of_drop hq)
  have := big_kid_unique hq hszi hj' hj (he ▸ hmi1.2.1) (by omega)
  rw [he, this]

/-- **Correctness of the query.** -/
theorem CQ_correct {m M u j : ℕ} (A : ℕ → ℕ → Bool) {s : LTree} {R : List Tok}
    (hu : ts.drop u = s.toks ++ R) (hM : ts.length ≤ M) (hm : M + 2 < 2 ^ m)
    (hA : ∀ c k (s' : LTree) Rc (ψ : CTL) Rk, ts.drop c = s'.toks ++ Rc → 2 * sz ts c < sz ts u →
      ts.drop k = ψ.toks ++ Rk → (A c k = true ↔ CSat s' ψ))
    {χ : CTL} {Rj : List Tok} (hj : ts.drop j = χ.toks ++ Rj) :
    encodeToks (CQ ts m M u j A) ∈ LTLPathChecking ↔ CSat s χ := by
  set Z := sz ts u with hZ
  set L := chainF ts Z u with hL
  obtain ⟨hne, hhead, hmem, hstep, hlast⟩ := chain_struct Z s.toks.length u s R le_rfl hu
    (by omega) le_rfl L rfl
  have hm1 : 1 < 2 ^ m := by omega
  have hnode : ∀ q ∈ L, ∃ (s : LTree) (R : List Tok), ts.drop q = s.toks ++ R :=
    fun q hq => (hmem q hq).1
  obtain ⟨hst, hlp⟩ := stemC_eq (m := m) (M := M) A hm1 hL.symm hne hnode hlast
  set ql := L.getLast hne
  set p := lassoC ts m M A Z L ql with hp
  have hq : CQ ts m M u j A = Tok.lpar :: ((trC m χ j).toks ++ Tok.rpar :: p.toks) := by
    rw [CQ, trCToks_eq m χ hj, hst, hlp]; rfl
  rw [hq, ← Shallow.ltlQuery, Shallow.ltlQuery_mem_iff]
  have hL0 : 0 < L.length := List.length_pos_iff.2 hne
  have hL0u : L[0] = u := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hL0] at hhead
    simpa using hhead
  set vs := L.map (sub ts) with hvs
  -- the node structure at a chain index
  have hnd : ∀ i (h : i < L.length), ∃ (l : Finset ℕ) (cs : List LTree) (R' : List Tok),
      ts.drop L[i] = (LTree.node l cs).toks ++ R' := by
    intro i h
    obtain ⟨t', R', ht⟩ := hnode _ (List.getElem_mem h)
    obtain ⟨l, cs⟩ := t'
    exact ⟨l, cs, R', ht⟩
  have hvsi : ∀ i (h : i < vs.length), vs[i] = sub ts (L[i]'(by simpa [hvs] using h)) := by
    intro i h; simp [hvs]
  have hW : WordOK ts m vs p.letter := by
    refine ⟨by simpa [hvs] using hne, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i h
      have h' : i + 1 < L.length := by simpa [hvs] using h
      obtain ⟨l, cs, R', jj, hjj, hq', he⟩ := hstep i h'
      rw [hvsi, hvsi, sub_eq hq']
      simp only [he, sub_eq (kid_drop hq' hjj), LTree.children]
      exact List.getElem_mem _
    · intro i h a
      have h' : i < L.length := by simpa [hvs] using h
      rw [(lassoC_node A Z L hne i h').1, mem_ndS_gm m _ a hm1, hvsi]
    · intro i h
      exact (lassoC_node A Z L hne i (by simpa [hvs] using h)).1 ▸ not_mem_ndS m _ 0 hm1
    · intro i h
      rw [(lassoC_node A Z L hne i (by simpa [hvs] using h)).2]; exact mem_exS_zero _ _ _ _ _
    · intro i h
      have h' : i < L.length := by simpa [hvs] using h
      obtain ⟨l, cs, R', hq'⟩ := hnd i h'
      rw [(lassoC_node A Z L hne i h').2, mem_exS_one, hvsi, sub_eq hq']
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', LTree.children,
        hvs, List.length_map]
      rw [show isLeaf ts L[i] = false ↔ cs ≠ [] by
        rw [← Bool.not_eq_true, isLeaf_iff hq']]
    · intro i h hi hleaf n hn
      have h' : i < L.length := by simpa [hvs] using h
      have hiL : i + 1 = L.length := by simpa [hvs] using hi
      have hql : ql = L[i] := by
        simp only [ql, List.getLast_eq_getElem]; congr 1; omega
      obtain ⟨l, cs, R', hq'⟩ := hnd i h'
      rw [hvsi, sub_eq hq'] at hleaf
      have hlf : isLeaf ts ql = true := by rw [hql, isLeaf_iff hq']; exact hleaf
      exact lassoC_tail_leaf A Z L hne hlf n (by omega)
    · intro i h hi hleaf n hn
      have h' : i < L.length := by simpa [hvs] using h
      have hiL : i + 1 = L.length := by simpa [hvs] using hi
      have hql : ql = L[i] := by
        simp only [ql, List.getLast_eq_getElem]; congr 1; omega
      obtain ⟨l, cs, R', hq'⟩ := hnd i h'
      rw [hvsi, sub_eq hq'] at hleaf
      have hlf : isLeaf ts ql = false := by
        rw [hql]; by_contra hc; exact hleaf ((isLeaf_iff hq').1 (by simpa using hc))
      exact lassoC_tail_node A Z L hne hlf n (by omega)
    · intro i h k ψ Rk hk
      have h' : i < L.length := by simpa [hvs] using h
      obtain ⟨l, cs, R', hq'⟩ := hnd i h'
      have hkM : k < M := by have := lt_of_drop (t := Tok.tag 4) (rest := ψ.toks ++ Rk) hk; omega
      have htc : tc ts k = 9 := by rw [tc_of_drop (t := Tok.tag 4) (rest := ψ.toks ++ Rk) hk]; rfl
      have hk1 : ts.drop (k + 1) = ψ.toks ++ Rk := drop_toks_cons hk
      rw [(lassoC_node A Z L hne i h').2, mem_exS_fresh _ _ _ _ _ hkM, offv, if_pos htc,
        anyKid_iff hq', hvsi, sub_eq hq']
      constructor
      · rintro ⟨jj, hjj, hs, hA'⟩
        exact ⟨cs[jj], List.getElem_mem _, (hA _ _ _ _ _ _ (kid_drop hq' hjj) hs hk1).1 hA'⟩
      · rintro ⟨c, hc, hsat⟩
        obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem hc
        rcases kid_dich hu rfl h' hq' hjj with hs | ⟨h1, he⟩
        · exact Or.inl ⟨jj, hjj, hs, (hA _ _ _ _ _ _ (kid_drop hq' hjj) hs hk1).2 hsat⟩
        · refine Or.inr ⟨by simpa [hvs] using h1, ?_⟩
          rw [hvsi, show sub ts L[i + 1] = cs[jj] by rw [he]; exact sub_eq (kid_drop hq' hjj)]
          exact hsat
    · intro i h k ψ χ' Rk hk
      have h' : i < L.length := by simpa [hvs] using h
      obtain ⟨l, cs, R', hq'⟩ := hnd i h'
      have hkM : k < M := by
        have := lt_of_drop (t := Tok.tag 5) (rest := ψ.toks ++ χ'.toks ++ Rk) (by rw [hk]; simp [CTL.toks]); omega
      have htc : tc ts k = 10 := by
        rw [tc_of_drop (t := Tok.tag 5) (rest := ψ.toks ++ χ'.toks ++ Rk) (by rw [hk]; simp [CTL.toks])]; rfl
      rw [(lassoC_node A Z L hne i h').2, mem_exS_fresh _ _ _ _ _ hkM, offv, if_neg (by omega),
        if_pos htc, anyKid_iff hq', hvsi, sub_eq hq']
      simp only [LTree.children]
      constructor
      · rintro ⟨jj, hjj, hs, hA'⟩
        exact ⟨cs[jj], List.getElem_mem _, (hA _ _ _ _ _ _ (kid_drop hq' hjj) hs hk).1 hA'⟩
      · rintro ⟨c, hc, hsat⟩
        obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem hc
        rcases kid_dich hu rfl h' hq' hjj with hs | ⟨h1, he⟩
        · exact Or.inl ⟨jj, hjj, hs, (hA _ _ _ _ _ _ (kid_drop hq' hjj) hs hk).2 hsat⟩
        · refine Or.inr ⟨by simpa [hvs] using h1, ?_⟩
          rw [hvsi, show sub ts L[i + 1] = cs[jj] by rw [he]; exact sub_eq (kid_drop hq' hjj)]
          exact hsat
    · intro i h k ψ χ' Rk hk
      have h' : i < L.length := by simpa [hvs] using h
      obtain ⟨l, cs, R', hq'⟩ := hnd i h'
      have hkM : k < M := by
        have := lt_of_drop (t := Tok.tag 6) (rest := ψ.toks ++ χ'.toks ++ Rk) (by rw [hk]; simp [CTL.toks]); omega
      have htc : tc ts k = 11 := by
        rw [tc_of_drop (t := Tok.tag 6) (rest := ψ.toks ++ χ'.toks ++ Rk) (by rw [hk]; simp [CTL.toks])]; rfl
      rw [(lassoC_node A Z L hne i h').2, mem_exS_fresh _ _ _ _ _ hkM, offv, if_neg (by omega),
        if_neg (by omega), if_pos htc, allKid_iff hq', hvsi, sub_eq hq']
      constructor
      · intro H jj hjj hs
        exact (hA _ _ _ _ _ _ (kid_drop hq' hjj) hs hk).2 (H _ (List.getElem_mem _))
      · intro H Hn c hc
        obtain ⟨jj, hjj, rfl⟩ := List.getElem_of_mem hc
        rcases kid_dich hu rfl h' hq' hjj with hs | ⟨h1, he⟩
        · exact (hA _ _ _ _ _ _ (kid_drop hq' hjj) hs hk).1 (H jj hjj hs)
        · have := Hn (by simpa [hvs] using h1)
          rw [hvsi, show sub ts L[i + 1] = cs[jj] by rw [he]; exact sub_eq (kid_drop hq' hjj)]
            at this
          exact this
  have := trC_correct hW χ j Rj hj 0 (by simpa [hvs] using hL0)
  rw [show 2 * 0 = 0 by rfl] at this
  rw [this, hvsi]
  simp only [hL0u, sub_eq hu]

end CTLT

end PathChecking
