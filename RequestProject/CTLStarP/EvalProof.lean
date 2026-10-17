module

public import RequestProject.CTLStarP.TreePos

/-!
# Correctness of the evaluation of CTL* formulas on encoded trees

`decideCTL_iff`: the pure decision procedure `decideCTL` accepts a token list iff it encodes an
instance `( φ ) t` with `t ⊨ φ`.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open LS MCVPReduction

variable {ts : List Tok}

variable (ts) in
/-- The path from node `u` towards position `ℓ`, as a sequence of subtrees. -/
noncomputable def pathOf (u ℓ : ℕ) : ℕ → LTree := fun i => sub ts ((nxt ts ℓ)^[i] u)

lemma pathOf_zero (u ℓ : ℕ) : pathOf ts u ℓ 0 = sub ts u := rfl

lemma pathOf_shift (u ℓ : ℕ) : (fun i => pathOf ts u ℓ (i + 1)) = pathOf ts (nxt ts ℓ u) ℓ := by
  funext i; simp only [pathOf, Function.iterate_succ_apply]

lemma pathOf_leaf {u ℓ : ℕ} {l : Finset ℕ} {R : List Tok}
    (h : ts.drop u = (LTree.node l []).toks ++ R) :
    pathOf ts u ℓ = fun _ => LTree.node l [] := by
  funext i
  simp only [pathOf, Function.iterate_fixed (nxt_leaf h) i, sub_eq h]

lemma iter_node {u : ℕ} {s : LTree} {R : List Tok} (h : ts.drop u = s.toks ++ R) (ℓ : ℕ) :
    ∀ i, ∃ (s' : LTree) (r' : List Tok), ts.drop ((nxt ts ℓ)^[i] u) = s'.toks ++ r' := by
  intro i
  induction i with
  | zero => exact ⟨s, R, h⟩
  | succ i ih =>
    obtain ⟨⟨l, cs⟩, r', h'⟩ := ih
    rw [Function.iterate_succ_apply']
    cases cs with
    | nil => rw [nxt_leaf h']; exact ⟨_, _, h'⟩
    | cons c cs =>
      obtain ⟨s'', -, r'', h'', -⟩ := nxt_node ℓ h' (by simp)
      exact ⟨s'', r'', h''⟩

lemma pathOf_isTreePath {u : ℕ} {s : LTree} {R : List Tok} (h : ts.drop u = s.toks ++ R)
    (ℓ : ℕ) : IsTreePath (pathOf ts u ℓ) := by
  intro i
  obtain ⟨⟨l, cs⟩, r', h'⟩ := iter_node h ℓ i
  simp only [pathOf, Function.iterate_succ_apply', sub_eq h']
  cases cs with
  | nil => right; rw [nxt_leaf h', sub_eq h']; exact ⟨rfl, rfl⟩
  | cons c cs =>
    left
    obtain ⟨s'', hs'', r'', h'', -⟩ := nxt_node ℓ h' (by simp)
    rw [sub_eq h'']; exact hs''

/-- Every tree path from the node at `u` is the path towards some position inside the node. -/
lemma path_cover (N : ℕ) : ∀ s : LTree, s.toks.length ≤ N → ∀ {u : ℕ} {R : List Tok},
    ts.drop u = s.toks ++ R → ∀ π, IsTreePath π → π 0 = s →
      ∃ ℓ, u ≤ ℓ ∧ ℓ < u + s.toks.length ∧ π = pathOf ts u ℓ := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro s hs u R h π hπ h0
    obtain ⟨l, cs⟩ := s
    have hpos := LTree.toks_length_pos (LTree.node l cs)
    cases cs with
    | nil =>
      have hc : ∀ i, π i = LTree.node l [] := by
        intro i
        induction i with
        | zero => exact h0
        | succ i ih' =>
          rcases hπ i with h1 | ⟨-, h2⟩
          · rw [ih'] at h1; simp [LTree.children] at h1
          · rw [h2, ih']
      refine ⟨u, le_rfl, by omega, ?_⟩
      rw [pathOf_leaf h]; funext i; exact hc i
    | cons c cs =>
      have h1 : π 1 ∈ c :: cs := by
        rcases hπ 0 with h1 | ⟨h2, -⟩
        · rw [h0] at h1; exact h1
        · rw [h0] at h2; simp [LTree.children] at h2
      obtain ⟨p, r', hp, hup, hpe, hnx⟩ := nxt_child h (π 1) h1
      have hlt : (π 1).toks.length < N := by
        have := toks_le hp; omega
      obtain ⟨ℓ, hl1, hl2, hπ'⟩ := ih _ hlt (π 1) le_rfl hp (fun i => π (i + 1))
        (fun i => hπ (i + 1)) rfl
      refine ⟨ℓ, by omega, by omega, ?_⟩
      funext i
      cases i with
      | zero => rw [h0, pathOf_zero, sub_eq h]
      | succ i =>
        have := congrFun hπ' i
        simp only at this
        rw [this, ← hnx ℓ hl1 hl2]
        exact (congrFun (pathOf_shift u ℓ) i).symm

/-! ## CTL* semantics -/

lemma holds_U_iff (φ ψ : CTLStar) (π : ℕ → LTree) :
    CTLStar.Holds (.U φ ψ) π ↔ CTLStar.Holds ψ π ∨
      (CTLStar.Holds φ π ∧ CTLStar.Holds (.U φ ψ) (fun i => π (i + 1))) := by
  simp only [CTLStar.Holds]
  constructor
  · rintro ⟨k, hk, hj⟩
    cases k with
    | zero => left; simpa using hk
    | succ k =>
      right
      refine ⟨by simpa using hj 0 (by omega), k, ?_, fun j hj' => ?_⟩
      · convert hk using 2
      · convert hj (j + 1) (by omega) using 2
  · rintro (h | ⟨h1, k, hk, hj⟩)
    · exact ⟨0, by simpa using h, fun j hj => absurd hj (by omega)⟩
    · refine ⟨k + 1, ?_, fun j hj' => ?_⟩
      · convert hk using 2
      · cases j with
        | zero => simpa using h1
        | succ j => convert hj j (by omega) using 2

lemma holds_U_const (φ ψ : CTLStar) (x : LTree) :
    CTLStar.Holds (.U φ ψ) (fun _ => x) ↔ CTLStar.Holds ψ (fun _ => x) := by
  simp only [CTLStar.Holds]
  constructor
  · rintro ⟨k, hk, -⟩; exact hk
  · intro h; exact ⟨0, h, fun j hj => absurd hj (by omega)⟩

/-! ## Correctness of `val` -/

lemma val_eq (j u ℓ : ℕ) : val ts j u ℓ =
    if ts.length ≤ j then false
    else if tc ts j = 5 then labHas ts (u + 2) (j + 1)
    else if tc ts j = 6 then true
    else if tc ts j = 7 then !val ts (j + 1) u ℓ
    else if tc ts j = 8 then val ts (j + 1) u ℓ && val ts (fend ts (j + 1)) u ℓ
    else if tc ts j = 9 then
      (if nxt ts ℓ u < ts.length then val ts (j + 1) (nxt ts ℓ u) ℓ else false)
    else if tc ts j = 10 then
      val ts (fend ts (j + 1)) u ℓ ||
        (val ts (j + 1) u ℓ &&
          (if u < nxt ts ℓ u ∧ nxt ts ℓ u < ts.length then val ts j (nxt ts ℓ u) ℓ else false))
    else if tc ts j = 11 then (List.range ts.length).any (fun ℓ' => val ts (j + 1) u ℓ')
    else false := by
  rw [val]; simp only [dite_eq_ite]

/-- **Correctness of the evaluation.** -/
theorem val_correct (ψ : CTLStar) : ∀ {j : ℕ} {Rj : List Tok}, ts.drop j = ψ.toks ++ Rj →
    ∀ {u : ℕ} {s : LTree} {R : List Tok}, ts.drop u = s.toks ++ R → ∀ ℓ,
      (val ts j u ℓ = true ↔ CTLStar.Holds ψ (pathOf ts u ℓ)) := by
  induction ψ with
  | ap a =>
    intro j Rj hj u s R hu ℓ
    have h' : ts.drop j = Tok.tag 0 :: (natToks a ++ Rj) := by simpa [CTLStar.toks] using hj
    obtain ⟨l, cs⟩ := s
    rw [val_eq, if_neg (by have := lt_of_drop h'; omega), if_pos (by rw [tc_of_drop h']; rfl),
      labHas_node hu (drop_succ_of_drop h')]
    simp [CTLStar.Holds, pathOf_zero, sub_eq hu, LTree.label]
  | tt =>
    intro j Rj hj u s R hu ℓ
    have h' : ts.drop j = Tok.tag 1 :: Rj := by simpa [CTLStar.toks] using hj
    rw [val_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp [tc_of_drop h', Tok.code, CTLStar.Holds]
  | neg φ ih =>
    intro j Rj hj u s R hu ℓ
    have h' : ts.drop j = Tok.tag 2 :: (φ.toks ++ Rj) := by simpa [CTLStar.toks] using hj
    rw [val_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h', show (Tok.tag 2).code = 7 from rfl]
    simp [CTLStar.Holds, ← ih (drop_succ_of_drop h') hu ℓ]
  | and φ ψ ih1 ih2 =>
    intro j Rj hj u s R hu ℓ
    have h' : ts.drop j = Tok.tag 3 :: (φ.toks ++ (ψ.toks ++ Rj)) := by
      simpa [CTLStar.toks] using hj
    have h1 := drop_succ_of_drop h'
    rw [val_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h', show (Tok.tag 3).code = 8 from rfl, fend_formula φ h1]
    simp [CTLStar.Holds, ← ih1 h1 hu ℓ, ← ih2 (drop_append_of_drop h1) hu ℓ]
  | X φ ih =>
    intro j Rj hj u s R hu ℓ
    have h' : ts.drop j = Tok.tag 4 :: (φ.toks ++ Rj) := by simpa [CTLStar.toks] using hj
    rw [val_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h', show (Tok.tag 4).code = 9 from rfl]
    obtain ⟨s', r', h''⟩ := iter_node hu ℓ 1
    simp only [Function.iterate_one] at h''
    have hlt : nxt ts ℓ u < ts.length := by
      have := toks_le h''; have := LTree.toks_length_pos s'; omega
    simp only [CTLStar.Holds, pathOf_shift]
    simp [hlt, ih (drop_succ_of_drop h') h'' ℓ]
  | U φ ψ ih1 ih2 =>
    intro j Rj hj
    have h' : ts.drop j = Tok.tag 5 :: (φ.toks ++ (ψ.toks ++ Rj)) := by
      simpa [CTLStar.toks] using hj
    have h1 := drop_succ_of_drop h'
    have h2 := drop_append_of_drop h1
    have hj' : ¬ ts.length ≤ j := by have := lt_of_drop h'; omega
    suffices H : ∀ m u (s : LTree) (R : List Tok), ts.length - u = m →
        ts.drop u = s.toks ++ R → ∀ ℓ,
        (val ts j u ℓ = true ↔ CTLStar.Holds (.U φ ψ) (pathOf ts u ℓ)) by
      intro u s R hu ℓ; exact H _ u s R rfl hu ℓ
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ihm =>
      intro u s R hm hu ℓ
      rw [val_eq, if_neg hj']
      simp only [tc_of_drop h', show (Tok.tag 5).code = 10 from rfl, fend_formula φ h1]
      simp only [show ¬ (10 = 5) from by decide, show ¬ (10 = 6) from by decide,
        show ¬ (10 = 7) from by decide, show ¬ (10 = 8) from by decide,
        show ¬ (10 = 9) from by decide, if_false, if_true]
      obtain ⟨l, cs⟩ := s
      cases cs with
      | nil =>
        rw [nxt_leaf hu, if_neg (by omega)]
        have e2 := ih2 h2 hu ℓ
        rw [pathOf_leaf hu] at e2 ⊢
        rw [holds_U_const]
        simp [e2]
      | cons c cs =>
        obtain ⟨s', -, r', h'', hlt1, hlt2⟩ := nxt_node ℓ hu (by simp)
        have hle := toks_le hu
        have hpos := LTree.toks_length_pos s'
        rw [if_pos ⟨hlt1, by omega⟩, holds_U_iff, pathOf_shift,
          ← ihm _ (by omega) _ s' r' rfl h'' ℓ, ← ih1 h1 hu ℓ, ← ih2 h2 hu ℓ]
        simp
  | E φ ih =>
    intro j Rj hj u s R hu ℓ
    have h' : ts.drop j = Tok.tag 6 :: (φ.toks ++ Rj) := by simpa [CTLStar.toks] using hj
    rw [val_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h', show (Tok.tag 6).code = 11 from rfl]
    simp only [show ¬ (11 = 5) from by decide, show ¬ (11 = 6) from by decide,
      show ¬ (11 = 7) from by decide, show ¬ (11 = 8) from by decide,
      show ¬ (11 = 9) from by decide, show ¬ (11 = 10) from by decide, if_false, if_true,
      List.any_eq_true, List.mem_range, CTLStar.Holds, pathOf_zero, sub_eq hu]
    constructor
    · rintro ⟨ℓ', -, hv⟩
      exact ⟨pathOf ts u ℓ', pathOf_isTreePath hu ℓ', by rw [pathOf_zero, sub_eq hu],
        (ih (drop_succ_of_drop h') hu ℓ').1 hv⟩
    · rintro ⟨π, hπ, h0, hh⟩
      obtain ⟨ℓ', -, hl2, rfl⟩ := path_cover _ s le_rfl hu π hπ h0
      exact ⟨ℓ', by have := toks_le hu; omega, (ih (drop_succ_of_drop h') hu ℓ').2 hh⟩

/-- **Correctness of the decision procedure on instances.** -/
theorem decideCTL_instance (φ : CTLStar) (t : LTree) :
    decideCTL (Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks)) = true ↔ CTLStar.TreeSat t φ := by
  set ts := Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks)
  have hv : validTop ts = true := validTop_iff.2 ⟨φ, t, rfl⟩
  have h1 : ts.drop 1 = φ.toks ++ Tok.rpar :: t.toks := rfl
  have hfe := fend_formula φ h1
  have h2 := drop_append_of_drop h1
  rw [← hfe] at h2
  have h3 : ts.drop (root ts) = t.toks ++ [] := by
    simpa [root] using drop_succ_of_drop h2
  simp only [decideCTL, hv, Bool.true_and, List.all_eq_true, List.mem_range, CTLStar.TreeSat]
  constructor
  · intro h π hπ h0
    obtain ⟨ℓ, -, hl2, rfl⟩ := path_cover _ t le_rfl h3 π hπ h0
    exact (val_correct φ h1 h3 ℓ).1 (h ℓ (by have := toks_le h3; omega))
  · intro h ℓ _
    exact (val_correct φ h1 h3 ℓ).2 (h _ (pathOf_isTreePath h3 ℓ) (by rw [pathOf_zero, sub_eq h3]))

/-- **The pure decision procedure decides CTL* tree checking (on token lists).** -/
theorem decideCTL_iff (ts : List Tok) :
    decideCTL ts = true ↔ ∃ (φ : CTLStar) (t : LTree),
      ts = Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks) ∧ CTLStar.TreeSat t φ := by
  constructor
  · intro h
    have hv : validTop ts = true := by
      simp only [decideCTL, Bool.and_eq_true] at h; exact h.1
    obtain ⟨φ, t, rfl⟩ := validTop_iff.1 hv
    exact ⟨φ, t, rfl, (decideCTL_instance φ t).1 h⟩
  · rintro ⟨φ, t, rfl, h⟩
    exact (decideCTL_instance φ t).2 h

end CTLP

end PathChecking
