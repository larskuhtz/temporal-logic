module

public import RequestProject.CTLStarP.Eval

/-!
# Trees at positions of a token list

Unique parsing of trees, the subtree at a position (`sub`), and the navigation functions
`ctw`, `nxt` on encoded trees.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open LS MCVPReduction

variable {ts : List Tok}

/-! ## Unique parsing -/

lemma natToks_unique {p a b : ℕ} {r r' : List Tok} (h1 : ts.drop p = natToks a ++ r)
    (h2 : ts.drop p = natToks b ++ r') : a = b := by
  have e1 := numEq_natToks h1 h2
  have e2 := numEq_natToks h1 h1
  rw [e1] at e2; simpa using e2

lemma nums_unique (xs : List ℕ) : ∀ (ys : List ℕ) {p : ℕ} {r r' : List Tok},
    ts.drop p = xs.flatMap natToks ++ Tok.rpar :: r →
    ts.drop p = ys.flatMap natToks ++ Tok.rpar :: r' → xs = ys := by
  induction xs with
  | nil =>
    intro ys p r r' h1 h2
    cases ys with
    | nil => rfl
    | cons b ys =>
      obtain ⟨t, l, htl, htc⟩ := natToks_head_code b
      have h1' : ts.drop p = Tok.rpar :: r := by simpa using h1
      have h2' : ts.drop p = t :: (l ++ (ys.flatMap natToks ++ Tok.rpar :: r')) := by
        rw [h2, List.flatMap_cons, htl]; simp
      have := (tc_of_drop h1').symm.trans (tc_of_drop h2')
      rw [show Tok.rpar.code = 4 from rfl] at this; omega
  | cons a xs ih =>
    intro ys p r r' h1 h2
    cases ys with
    | nil =>
      obtain ⟨t, l, htl, htc⟩ := natToks_head_code a
      have h2' : ts.drop p = Tok.rpar :: r' := by simpa using h2
      have h1' : ts.drop p = t :: (l ++ (xs.flatMap natToks ++ Tok.rpar :: r)) := by
        rw [h1, List.flatMap_cons, htl]; simp
      have := (tc_of_drop h1').symm.trans (tc_of_drop h2')
      rw [show Tok.rpar.code = 4 from rfl] at this; omega
    | cons b ys =>
      have h1' : ts.drop p = natToks a ++ (xs.flatMap natToks ++ Tok.rpar :: r) := by simpa using h1
      have h2' : ts.drop p = natToks b ++ (ys.flatMap natToks ++ Tok.rpar :: r') := by simpa using h2
      obtain rfl := natToks_unique h1' h2'
      rw [ih ys (drop_append_of_drop h1') (drop_append_of_drop h2')]

lemma finset_unique {p : ℕ} {l l' : Finset ℕ} {r r' : List Tok}
    (h1 : ts.drop p = finsetToks l ++ r) (h2 : ts.drop p = finsetToks l' ++ r') : l = l' := by
  have h1' : ts.drop p = Tok.lpar :: ((l.sort (· ≤ ·)).flatMap natToks ++ Tok.rpar :: r) := by
    simpa [finsetToks] using h1
  have h2' : ts.drop p = Tok.lpar :: ((l'.sort (· ≤ ·)).flatMap natToks ++ Tok.rpar :: r') := by
    simpa [finsetToks] using h2
  have := nums_unique _ _ (drop_succ_of_drop h1') (drop_succ_of_drop h2')
  rw [← Finset.sort_toFinset l (· ≤ ·), ← Finset.sort_toFinset l' (· ≤ ·), this]

lemma tree_unique_aux (N : ℕ) :
    (∀ s : LTree, s.toks.length ≤ N → ∀ (s' : LTree) {p : ℕ} {r r' : List Tok},
      ts.drop p = s.toks ++ r → ts.drop p = s'.toks ++ r' → s = s') ∧
    (∀ cs : List LTree, (LTree.toksList cs).length < N → ∀ (cs' : List LTree) {p : ℕ}
      {r r' : List Tok}, ts.drop p = LTree.toksList cs ++ Tok.rpar :: r →
      ts.drop p = LTree.toksList cs' ++ Tok.rpar :: r' → cs = cs') := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hlist : ∀ cs : List LTree, (LTree.toksList cs).length < N → ∀ (cs' : List LTree)
        {p : ℕ} {r r' : List Tok}, ts.drop p = LTree.toksList cs ++ Tok.rpar :: r →
        ts.drop p = LTree.toksList cs' ++ Tok.rpar :: r' → cs = cs' := by
      intro cs
      induction cs with
      | nil =>
        intro _ cs' p r r' h1 h2
        cases cs' with
        | nil => rfl
        | cons t cs' =>
          obtain ⟨l, hl⟩ := LTree.toks_head t
          have h1' : ts.drop p = Tok.rpar :: r := by simpa [LTree.toksList] using h1
          have h2' : ts.drop p = Tok.lpar :: (l ++ (LTree.toksList cs' ++ Tok.rpar :: r')) := by
            rw [h2, LTree.toksList_cons, hl]; simp
          have := (tc_of_drop h1').symm.trans (tc_of_drop h2')
          simp [Tok.code] at this
      | cons t cs ihc =>
        intro hN cs' p r r' h1 h2
        rw [LTree.toksList_cons, List.length_append] at hN
        have htp := LTree.toks_length_pos t
        cases cs' with
        | nil =>
          obtain ⟨l, hl⟩ := LTree.toks_head t
          have h2' : ts.drop p = Tok.rpar :: r' := by simpa [LTree.toksList] using h2
          have h1' : ts.drop p = Tok.lpar :: (l ++ (LTree.toksList cs ++ Tok.rpar :: r)) := by
            rw [h1, LTree.toksList_cons, hl]; simp
          have := (tc_of_drop h1').symm.trans (tc_of_drop h2')
          simp [Tok.code] at this
        | cons t' cs' =>
          rw [LTree.toksList_cons, List.append_assoc] at h1 h2
          obtain rfl := (ih t.toks.length (by omega)).1 t le_rfl t' h1 h2
          rw [ihc (by omega) cs' (drop_append_of_drop h1) (drop_append_of_drop h2)]
    refine ⟨?_, hlist⟩
    intro s hs s' p r r' h1 h2
    obtain ⟨l, cs⟩ := s
    obtain ⟨l', cs'⟩ := s'
    have h1' := node_toks_drop h1
    have h2' := node_toks_drop h2
    have hlt := LTree.toks_length_lt l cs
    have g1 := drop_succ_of_drop h1'
    have g2 := drop_succ_of_drop h2'
    obtain rfl := finset_unique g1 g2
    rw [hlist cs (by omega) cs' (drop_append_of_drop g1) (drop_append_of_drop g2)]

lemma tree_unique {s s' : LTree} {p : ℕ} {r r' : List Tok} (h1 : ts.drop p = s.toks ++ r)
    (h2 : ts.drop p = s'.toks ++ r') : s = s' :=
  (tree_unique_aux s.toks.length).1 s le_rfl s' h1 h2

open Classical in
/-- The subtree encoded at position `p` (a default tree if there is none). -/
noncomputable def sub (ts : List Tok) (p : ℕ) : LTree :=
  if h : ∃ (s : LTree) (rest : List Tok), ts.drop p = s.toks ++ rest then h.choose
  else .node ∅ []

lemma sub_eq {p : ℕ} {s : LTree} {rest : List Tok} (h : ts.drop p = s.toks ++ rest) :
    sub ts p = s := by
  have hex : ∃ (s : LTree) (rest : List Tok), ts.drop p = s.toks ++ rest := ⟨s, rest, h⟩
  rw [sub, dif_pos hex]
  obtain ⟨r, hr⟩ := hex.choose_spec
  exact tree_unique hr h

/-! ## Children -/

lemma ctw_eq (c ℓ : ℕ) : ctw ts c ℓ =
    if ts.length ≤ c then c
    else if tend ts c ≤ ℓ ∧ tc ts (tend ts c) ≠ 4 then ctw ts (tend ts c) ℓ else c := by
  rw [ctw]

lemma ctw_mem (cs : List LTree) : ∀ {c : ℕ} {R : List Tok} (ℓ : ℕ), cs ≠ [] →
    ts.drop c = LTree.toksList cs ++ Tok.rpar :: R →
    ∃ s' ∈ cs, ∃ r', ts.drop (ctw ts c ℓ) = s'.toks ++ r' ∧ c ≤ ctw ts c ℓ ∧
      ctw ts c ℓ + s'.toks.length ≤ c + (LTree.toksList cs).length := by
  induction cs with
  | nil => intro c R ℓ h; exact absurd rfl h
  | cons t cs ih =>
    intro c R ℓ _ h
    rw [LTree.toksList_cons, List.append_assoc] at h
    have htp := LTree.toks_length_pos t
    obtain ⟨l0, hl0⟩ := LTree.toks_head t
    have hc : c < ts.length := lt_of_drop (t := Tok.lpar) (rest := l0 ++ _) (by rw [h, hl0]; rfl)
    have hte := tend_tree t h
    have hd := drop_append_of_drop h
    rw [← hte] at hd
    rw [LTree.toksList_cons, List.length_append]
    cases cs with
    | nil =>
      have hd' : ts.drop (tend ts c) = Tok.rpar :: R := by simpa [LTree.toksList] using hd
      rw [ctw_eq, if_neg (by omega), if_neg (by rw [tc_of_drop hd']; simp [Tok.code])]
      exact ⟨t, by simp, _, h, le_rfl, by omega⟩
    | cons t2 cs =>
      obtain ⟨l2, hl2⟩ := LTree.toks_head t2
      have hd' : ts.drop (tend ts c) = Tok.lpar :: (l2 ++ (LTree.toksList cs ++ Tok.rpar :: R)) := by
        rw [hd, LTree.toksList_cons, hl2]; simp
      have h4 : tc ts (tend ts c) ≠ 4 := by rw [tc_of_drop hd']; simp [Tok.code]
      rw [ctw_eq, if_neg (by omega)]
      by_cases hl : tend ts c ≤ ℓ
      · rw [if_pos ⟨hl, h4⟩]
        obtain ⟨s', hs', r', h1, h2, h3⟩ := ih ℓ (by simp) hd
        exact ⟨s', by simp [hs'], r', h1, by omega, by omega⟩
      · rw [if_neg (by tauto)]
        exact ⟨t, by simp, _, h, le_rfl, by omega⟩

lemma ctw_child (cs : List LTree) : ∀ {c : ℕ} {R : List Tok},
    ts.drop c = LTree.toksList cs ++ Tok.rpar :: R → ∀ s' ∈ cs, ∃ p r',
      ts.drop p = s'.toks ++ r' ∧ c ≤ p ∧ p + s'.toks.length ≤ c + (LTree.toksList cs).length ∧
      ∀ ℓ, p ≤ ℓ → ℓ < p + s'.toks.length → ctw ts c ℓ = p := by
  induction cs with
  | nil => intro c R _ s' hs; simp at hs
  | cons t cs ih =>
    intro c R h s' hs
    rw [LTree.toksList_cons, List.append_assoc] at h
    have htp := LTree.toks_length_pos t
    obtain ⟨l0, hl0⟩ := LTree.toks_head t
    have hc : c < ts.length := lt_of_drop (t := Tok.lpar) (rest := l0 ++ _) (by rw [h, hl0]; rfl)
    have hte := tend_tree t h
    have hd := drop_append_of_drop h
    rw [← hte] at hd
    rw [LTree.toksList_cons, List.length_append]
    rcases List.mem_cons.1 hs with rfl | hs
    · refine ⟨c, _, h, le_rfl, by omega, fun ℓ _ h2 => ?_⟩
      rw [ctw_eq, if_neg (by omega), if_neg (by omega)]
    · obtain ⟨p, r', h1, h2, h3, h4⟩ := ih hd s' hs
      refine ⟨p, r', h1, by omega, by omega, fun ℓ hl1 hl2 => ?_⟩
      cases cs with
      | nil => simp at hs
      | cons t2 cs =>
        obtain ⟨l2, hl2'⟩ := LTree.toks_head t2
        have hd' : ts.drop (tend ts c) =
            Tok.lpar :: (l2 ++ (LTree.toksList cs ++ Tok.rpar :: R)) := by
          rw [hd, LTree.toksList_cons, hl2']; simp
        have h5 : tc ts (tend ts c) ≠ 4 := by rw [tc_of_drop hd']; simp [Tok.code]
        rw [ctw_eq, if_neg (by omega), if_pos ⟨by omega, h5⟩, h4 ℓ hl1 hl2]

/-! ## Nodes -/

lemma kids_drop {u : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) :
    tend ts (u + 1) = u + 1 + (finsetToks l).length ∧
    ts.drop (u + 1 + (finsetToks l).length) = LTree.toksList cs ++ Tok.rpar :: R := by
  have hn := node_toks_drop h
  have hs := drop_succ_of_drop hn
  exact ⟨tend_finset l hs, drop_append_of_drop hs⟩

lemma isLeaf_iff {u : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) : isLeaf ts u = true ↔ cs = [] := by
  obtain ⟨e, hk⟩ := kids_drop h
  rw [isLeaf, e]
  cases cs with
  | nil =>
    have : ts.drop (u + 1 + (finsetToks l).length) = Tok.rpar :: R := by
      simpa [LTree.toksList] using hk
    simp [tc_of_drop this, Tok.code]
  | cons t cs =>
    obtain ⟨l2, hl2⟩ := LTree.toks_head t
    have : ts.drop (u + 1 + (finsetToks l).length) =
        Tok.lpar :: (l2 ++ (LTree.toksList cs ++ Tok.rpar :: R)) := by
      rw [hk, LTree.toksList_cons, hl2]; simp
    simp [tc_of_drop this, Tok.code]

lemma nxt_leaf {u ℓ : ℕ} {l : Finset ℕ} {R : List Tok}
    (h : ts.drop u = (LTree.node l []).toks ++ R) : nxt ts ℓ u = u := by
  rw [nxt, if_pos ((isLeaf_iff h).2 rfl)]

lemma toks_le {u : ℕ} {s : LTree} {R : List Tok} (h : ts.drop u = s.toks ++ R) :
    u + s.toks.length ≤ ts.length := by
  have h1 := congrArg List.length h
  have := LTree.toks_length_pos s
  simp only [List.length_drop, List.length_append] at h1; omega

lemma nxt_node {u : ℕ} (ℓ : ℕ) {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) (hcs : cs ≠ []) :
    ∃ s' ∈ cs, ∃ r', ts.drop (nxt ts ℓ u) = s'.toks ++ r' ∧ u < nxt ts ℓ u ∧
      nxt ts ℓ u + s'.toks.length < u + (LTree.node l cs).toks.length := by
  obtain ⟨e, hk⟩ := kids_drop h
  rw [nxt, if_neg (by rw [isLeaf_iff h]; exact hcs), e]
  obtain ⟨s', hs', r', h1, h2, h3⟩ := ctw_mem cs ℓ hcs hk
  refine ⟨s', hs', r', h1, by omega, ?_⟩
  simp [LTree.toks]; omega

lemma nxt_child {u : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) (s' : LTree) (hs' : s' ∈ cs) :
    ∃ p r', ts.drop p = s'.toks ++ r' ∧ u < p ∧
      p + s'.toks.length < u + (LTree.node l cs).toks.length ∧
      ∀ ℓ, p ≤ ℓ → ℓ < p + s'.toks.length → nxt ts ℓ u = p := by
  obtain ⟨e, hk⟩ := kids_drop h
  have hcs : cs ≠ [] := List.ne_nil_of_mem hs'
  obtain ⟨p, r', h1, h2, h3, h4⟩ := ctw_child cs hk s' hs'
  refine ⟨p, r', h1, by omega, by simp [LTree.toks]; omega, fun ℓ hl1 hl2 => ?_⟩
  rw [nxt, if_neg (by rw [isLeaf_iff h]; exact hcs), e, h4 ℓ hl1 hl2]

/-! ## Labels -/

lemma labHas_eq (p q : ℕ) : labHas ts p q =
    if ts.length ≤ p then false
    else if tc ts p = 4 then false
    else numEq ts p q || labHas ts (numEnd ts p) q := by
  rw [labHas]

lemma labHas_correct (xs : List ℕ) : ∀ {p : ℕ} {R : List Tok},
    ts.drop p = xs.flatMap natToks ++ Tok.rpar :: R → ∀ {q a : ℕ} {r : List Tok},
    ts.drop q = natToks a ++ r → labHas ts p q = decide (a ∈ xs) := by
  induction xs with
  | nil =>
    intro p R h q a r hq
    have h' : ts.drop p = Tok.rpar :: R := by simpa using h
    rw [labHas_eq, if_neg (by have := lt_of_drop h'; omega), if_pos (by rw [tc_of_drop h']; rfl)]
    simp
  | cons b xs ih =>
    intro p R h q a r hq
    have hb : ts.drop p = natToks b ++ (xs.flatMap natToks ++ Tok.rpar :: R) := by simpa using h
    obtain ⟨t, l, htl, htc⟩ := natToks_head_code b
    have hb' : ts.drop p = t :: (l ++ (xs.flatMap natToks ++ Tok.rpar :: R)) := by
      rw [hb, htl]; rfl
    rw [labHas_eq, if_neg (by have := lt_of_drop hb'; omega),
      if_neg (by rw [tc_of_drop hb']; omega), numEq_natToks hb hq, numEnd_natToks b hb,
      ih (drop_append_of_drop hb) hq]
    by_cases hab : b = a
    · subst hab; simp
    · simp [hab, eq_comm]

lemma labHas_node {u j : ℕ} {l : Finset ℕ} {cs : List LTree} {R : List Tok}
    (h : ts.drop u = (LTree.node l cs).toks ++ R) {a : ℕ} {r : List Tok}
    (hq : ts.drop j = natToks a ++ r) : labHas ts (u + 2) j = decide (a ∈ l) := by
  have hn := node_toks_drop h
  have hs := drop_succ_of_drop hn
  have hs' : ts.drop (u + 1) = Tok.lpar :: ((l.sort (· ≤ ·)).flatMap natToks ++
      Tok.rpar :: (LTree.toksList cs ++ Tok.rpar :: R)) := by
    rw [hs]; simp [finsetToks]
  rw [labHas_correct _ (drop_succ_of_drop hs') hq]
  simp

end CTLP

end PathChecking
