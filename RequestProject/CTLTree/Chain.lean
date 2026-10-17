module

public import RequestProject.CTLTree.Sem
public import RequestProject.Shallow.PosRound

/-!
# One query: CTL along a path of the tree as LTL path checking

Let `v₀, v₁, …, v_m` be a path of the tree (`v_{i+1}` a child of `v_i`).  The LTL query asked for
this path uses the word

  `N₀ X₀ N₁ X₁ ⋯ N_m X_m …`

with a *node letter* `N_i` (the label of `v_i`, renamed by `gm m`) and an *exit letter* `X_i`
for every node.  The exit letter contains the proposition `0` (it marks exit positions), the
proposition `1` if `v_m` is the last node and is not a leaf, and a fresh proposition `k + 2` for
every `EX`, `EU`, `AU` subformula at token position `k`, carrying the value of that subformula
"through the other children" of `v_i` (computed in the previous round).  After `X_m` the word is
periodic: `(N_m X_m)^ω` if `v_m` is a leaf, `X_m^ω` otherwise.

The translation `trC m χ j` of the CTL subformula `χ` at token position `j` is the identity on
Boolean structure and

* `EX ψ ↦ X (k + 2 ∨ X (¬0 ∧ ψ))`,
* `EU ψ χ ↦ (0 ∨ ψ) U (if 0 then k + 2 else χ)`,
* `AU ψ χ ↦ (if 0 then k + 2 else ψ) U (if 0 then (k + 2 ∧ 1) else χ)`.

Every subformula occurs exactly once in its translation.  `trC_correct`: at every node position
`2 i`, the translation holds iff the CTL subformula holds at `v_i`.
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open ShallowP

/-- LTL disjunction. -/
def lor (a b : LTL) : LTL := .neg (.and (.neg a) (.neg b))

/-- LTL if-then-else. -/
def lite (c a b : LTL) : LTL := lor (.and c a) (.and (.neg c) b)

lemma sat_lor (w : ℕ → Finset ℕ) (a b : LTL) (n : ℕ) :
    LTL.Sat w (lor a b) n ↔ LTL.Sat w a n ∨ LTL.Sat w b n := by
  simp only [lor, LTL.Sat]; tauto

lemma sat_lite (w : ℕ → Finset ℕ) (c a b : LTL) (n : ℕ) :
    LTL.Sat w (lite c a b) n ↔ (LTL.Sat w c n ∧ LTL.Sat w a n) ∨ (¬ LTL.Sat w c n ∧ LTL.Sat w b n) := by
  simp only [lite, sat_lor, LTL.Sat]

/-- The translation of the CTL subformula `χ` at token position `j`. -/
def trC (m : ℕ) : CTL → ℕ → LTL
  | .ap a, _ => .ap (gm m a)
  | .tt, _ => .tt
  | .neg ψ, j => .neg (trC m ψ (j + 1))
  | .and ψ χ, j => .and (trC m ψ (j + 1)) (trC m χ (j + 1 + ψ.toks.length))
  | .EX ψ, j => .X (lor (.ap (j + 2)) (.X (.and (.neg (.ap 0)) (trC m ψ (j + 1)))))
  | .EU ψ χ, j => .U (lor (.ap 0) (trC m ψ (j + 1)))
      (lite (.ap 0) (.ap (j + 2)) (trC m χ (j + 1 + ψ.toks.length)))
  | .AU ψ χ, j => .U (lite (.ap 0) (.ap (j + 2)) (trC m ψ (j + 1)))
      (lite (.ap 0) (.and (.ap (j + 2)) (.ap 1)) (trC m χ (j + 1 + ψ.toks.length)))

/-! ## Periodic words -/

lemma sat_periodic (w : ℕ → Finset ℕ) {n₀ p : ℕ} (hw : ∀ n, n₀ ≤ n → w (n + p) = w n) :
    ∀ (ψ : LTL) (n : ℕ), n₀ ≤ n → (LTL.Sat w ψ (n + p) ↔ LTL.Sat w ψ n) := by
  intro ψ
  induction ψ with
  | ap a => intro n hn; simp only [LTL.Sat, hw n hn]
  | tt => intro n hn; simp [LTL.Sat]
  | neg φ ih => intro n hn; simp only [LTL.Sat, ih n hn]
  | and φ ψ ih1 ih2 => intro n hn; simp only [LTL.Sat, ih1 n hn, ih2 n hn]
  | X φ ih =>
    intro n hn; simp only [LTL.Sat]
    rw [show n + p + 1 = (n + 1) + p by omega, ih (n + 1) (by omega)]
  | U φ ψ ih1 ih2 =>
    intro n hn; simp only [LTL.Sat]
    refine exists_congr fun k => and_congr ?_ (forall_congr' fun j => imp_congr_right fun _ => ?_)
    · rw [show n + p + k = (n + k) + p by omega, ih2 (n + k) (by omega)]
    · rw [show n + p + j = (n + j) + p by omega, ih1 (n + j) (by omega)]

/-- On a word periodic from `n₀`, an until at `n₀` is decided within one period. -/
lemma sat_U_periodic (w : ℕ → Finset ℕ) {n₀ p : ℕ} (hp : 0 < p)
    (hw : ∀ n, n₀ ≤ n → w (n + p) = w n) (a b : LTL) :
    LTL.Sat w (.U a b) n₀ ↔ ∃ k < p, LTL.Sat w b (n₀ + k) ∧ ∀ j < k, LTL.Sat w a (n₀ + j) := by
  simp only [LTL.Sat]
  constructor
  · intro h
    classical
    let k := Nat.find h
    have hk : LTL.Sat w b (n₀ + k) ∧ ∀ j < k, LTL.Sat w a (n₀ + j) := Nat.find_spec h
    by_cases hkp : k < p
    · exact ⟨k, hkp, hk⟩
    · exfalso
      have hmin := Nat.find_min h (show k - p < k by omega)
      apply hmin
      refine ⟨?_, fun j hj => hk.2 j (by omega)⟩
      have := (sat_periodic w hw b (n₀ + (k - p)) (by omega)).1
      rw [show n₀ + (k - p) + p = n₀ + k by omega] at this
      exact this hk.1
  · rintro ⟨k, -, hk⟩; exact ⟨k, hk⟩

lemma sat_U_iff (w : ℕ → Finset ℕ) (a b : LTL) (n : ℕ) :
    LTL.Sat w (.U a b) n ↔ LTL.Sat w b n ∨ (LTL.Sat w a n ∧ LTL.Sat w (.U a b) (n + 1)) := by
  simp only [LTL.Sat]
  constructor
  · rintro ⟨k, hk, hj⟩
    cases k with
    | zero => left; simpa using hk
    | succ k =>
      right
      refine ⟨by simpa using hj 0 (by omega), k, by rw [show n + 1 + k = n + (k + 1) by omega]; exact hk,
        fun j hj' => ?_⟩
      rw [show n + 1 + j = n + (j + 1) by omega]; exact hj _ (by omega)
  · rintro (h | ⟨h1, k, hk, hj⟩)
    · exact ⟨0, by simpa using h, fun j hj => absurd hj (by omega)⟩
    · refine ⟨k + 1, by rw [show n + (k + 1) = n + 1 + k by omega]; exact hk, fun j hj' => ?_⟩
      cases j with
      | zero => simpa using h1
      | succ j => rw [show n + (j + 1) = n + 1 + j by omega]; exact hj j (by omega)

/-! ## The word of a query -/

/-- The conditions on the word `W` of the query for the path `vs`. -/
structure WordOK (ts : List Tok) (m : ℕ) (vs : List LTree) (W : ℕ → Finset ℕ) : Prop where
  ne : vs ≠ []
  path : ∀ i (h : i + 1 < vs.length), vs[i + 1] ∈ vs[i].children
  nd_gm : ∀ i (h : i < vs.length) a, gm m a ∈ W (2 * i) ↔ a ∈ vs[i].label
  nd_e : ∀ i < vs.length, 0 ∉ W (2 * i)
  ex_e : ∀ i < vs.length, 0 ∈ W (2 * i + 1)
  ex_en : ∀ i (h : i < vs.length), 1 ∈ W (2 * i + 1) ↔ (i + 1 = vs.length ∧ vs[i].children ≠ [])
  tail_leaf : ∀ i (h : i < vs.length), i + 1 = vs.length → vs[i].children = [] →
    ∀ n, 2 * i ≤ n → W (n + 2) = W n
  tail_node : ∀ i (h : i < vs.length), i + 1 = vs.length → vs[i].children ≠ [] →
    ∀ n, 2 * i + 1 ≤ n → W (n + 1) = W n
  hEX : ∀ i (h : i < vs.length) k (ψ : CTL) R, ts.drop k = (CTL.EX ψ).toks ++ R →
    (k + 2 ∈ W (2 * i + 1) → ∃ c ∈ vs[i].children, CSat c ψ) ∧
    ((∃ c ∈ vs[i].children, CSat c ψ) →
      k + 2 ∈ W (2 * i + 1) ∨ ∃ h' : i + 1 < vs.length, CSat vs[i + 1] ψ)
  hEU : ∀ i (h : i < vs.length) k (ψ χ : CTL) R, ts.drop k = (CTL.EU ψ χ).toks ++ R →
    (k + 2 ∈ W (2 * i + 1) → ∃ c ∈ vs[i].children, CSat c (.EU ψ χ)) ∧
    ((∃ c ∈ vs[i].children, CSat c (.EU ψ χ)) →
      k + 2 ∈ W (2 * i + 1) ∨ ∃ h' : i + 1 < vs.length, CSat vs[i + 1] (.EU ψ χ))
  hAU : ∀ i (h : i < vs.length) k (ψ χ : CTL) R, ts.drop k = (CTL.AU ψ χ).toks ++ R →
    ((∀ c ∈ vs[i].children, CSat c (.AU ψ χ)) → k + 2 ∈ W (2 * i + 1)) ∧
    (k + 2 ∈ W (2 * i + 1) → (∀ h' : i + 1 < vs.length, CSat vs[i + 1] (.AU ψ χ)) →
      ∀ c ∈ vs[i].children, CSat c (.AU ψ χ))

lemma drop_tag {ts : List Tok} {j : ℕ} {t : Tok} {l R : List Tok}
    (h : ts.drop j = (t :: l) ++ R) : ts.drop (j + 1) = l ++ R := drop_toks_cons h

/-- Backward induction along the path. -/
lemma back_ind {L : ℕ} {P : ℕ → Prop} (hlast : ∀ i, i + 1 = L → P i)
    (hstep : ∀ i, i + 1 < L → P (i + 1) → P i) : ∀ i, i < L → P i := by
  have : ∀ d i, i + d + 1 = L → P i := by
    intro d
    induction d with
    | zero => intro i hi; exact hlast i (by omega)
    | succ d ih => intro i hi; exact hstep i (by omega) (ih (i + 1) (by omega))
  intro i hi
  exact this (L - 1 - i) i (by omega)

/-- **Correctness of the translation on the word of a query.** -/
theorem trC_correct {ts : List Tok} {m : ℕ} {vs : List LTree} {W : ℕ → Finset ℕ}
    (hW : WordOK ts m vs W) (χ : CTL) :
    ∀ j R, ts.drop j = χ.toks ++ R → ∀ i (h : i < vs.length),
      (LTL.Sat W (trC m χ j) (2 * i) ↔ CSat vs[i] χ) := by
  set L := vs.length with hL
  have hL0 : 0 < L := List.length_pos_iff.2 hW.ne
  induction χ with
  | ap a =>
    intro j R hj i h
    simp only [trC, LTL.Sat, csat_ap]
    exact hW.nd_gm i h a
  | tt => intro j R hj i h; simp [trC, LTL.Sat, csat_tt]
  | neg ψ ih =>
    intro j R hj i h
    simp only [trC, LTL.Sat, csat_neg, ih (j + 1) R (drop_tag hj) i h]
  | and ψ χ ih1 ih2 =>
    intro j R hj i h
    have h1 : ts.drop (j + 1) = ψ.toks ++ (χ.toks ++ R) := by
      have := drop_tag (l := ψ.toks ++ χ.toks) hj; simpa using this
    have h2 := CTLP.drop_append_of_drop h1
    simp only [trC, LTL.Sat, csat_and, ih1 _ _ h1 i h, ih2 _ _ h2 i h]
  | EX ψ ih =>
    intro j R hj i h
    have h1 : ts.drop (j + 1) = ψ.toks ++ R := drop_tag hj
    simp only [trC, LTL.Sat, sat_lor]
    rw [csat_EX]
    obtain ⟨hE1, hE2⟩ := hW.hEX i h j ψ R hj
    by_cases hi : i + 1 < L
    · have e : 2 * i + 1 + 1 = 2 * (i + 1) := by ring
      rw [e, ih _ _ h1 (i + 1) hi]
      have hc := hW.path i hi
      have hne : vs[i].children ≠ [] := by intro e'; rw [e'] at hc; simp at hc
      have h0 := hW.nd_e (i + 1) hi
      constructor
      · rintro (h' | ⟨-, h'⟩)
        · exact Or.inr (hE1 h')
        · exact Or.inr ⟨_, hc, h'⟩
      · rintro (⟨h', -⟩ | h')
        · exact absurd h' hne
        · rcases hE2 h' with h'' | ⟨_, h''⟩
          · exact Or.inl h''
          · exact Or.inr ⟨h0, h''⟩
    · have hi' : i = L - 1 := by omega
      by_cases hl : vs[i].children = []
      · have hp := hW.tail_leaf i h (by omega) hl
        have e : 2 * i + 1 + 1 = 2 * i + 2 := by ring
        rw [e, sat_periodic W hp _ (2 * i) (by omega), ih _ _ h1 i h, hp (2 * i) (by omega)]
        constructor
        · rintro (h' | ⟨-, h'⟩)
          · obtain ⟨c, hc, -⟩ := hE1 h'; rw [hl] at hc; simp at hc
          · exact Or.inl ⟨hl, h'⟩
        · rintro (⟨-, h'⟩ | ⟨c, hc, -⟩)
          · exact Or.inr ⟨hW.nd_e i h, h'⟩
          · rw [hl] at hc; simp at hc
      · have hp := hW.tail_node i h (by omega) hl
        rw [hp (2 * i + 1) (by omega)]
        constructor
        · rintro (h' | ⟨h', -⟩)
          · exact Or.inr (hE1 h')
          · exact absurd (hW.ex_e i h) h'
        · rintro (⟨h', -⟩ | h')
          · exact absurd h' hl
          · rcases hE2 h' with h'' | ⟨h3, -⟩
            · exact Or.inl h''
            · exact absurd h3 hi
  | EU ψ χ ih1 ih2 =>
    intro j R hj
    have h1 : ts.drop (j + 1) = ψ.toks ++ (χ.toks ++ R) := by
      have := drop_tag (l := ψ.toks ++ χ.toks) hj; simpa using this
    have h2 := CTLP.drop_append_of_drop h1
    -- the values at node and exit positions
    have hb0 : ∀ i (h : i < L), LTL.Sat W (lite (.ap 0) (.ap (j + 2))
        (trC m χ (j + 1 + ψ.toks.length))) (2 * i) ↔ CSat vs[i] χ := by
      intro i h
      rw [sat_lite]; simp only [LTL.Sat, hW.nd_e i h, false_and, not_false_eq_true, true_and,
        false_or]
      exact ih2 _ _ h2 i h
    have ha0 : ∀ i (h : i < L), LTL.Sat W (lor (.ap 0) (trC m ψ (j + 1))) (2 * i) ↔
        CSat vs[i] ψ := by
      intro i h
      rw [sat_lor]; simp only [LTL.Sat, hW.nd_e i h, false_or]
      exact ih1 _ _ h1 i h
    have hb1 : ∀ i (h : i < L), LTL.Sat W (lite (.ap 0) (.ap (j + 2))
        (trC m χ (j + 1 + ψ.toks.length))) (2 * i + 1) ↔ j + 2 ∈ W (2 * i + 1) := by
      intro i h
      rw [sat_lite]; simp only [LTL.Sat, hW.ex_e i h, true_and, not_true_eq_false, false_and,
        or_false]
    have ha1 : ∀ i (h : i < L), LTL.Sat W (lor (.ap 0) (trC m ψ (j + 1))) (2 * i + 1) := by
      intro i h
      rw [sat_lor]; exact Or.inl (hW.ex_e i h)
    set T := LTL.U (lor (.ap 0) (trC m ψ (j + 1)))
      (lite (.ap 0) (.ap (j + 2)) (trC m χ (j + 1 + ψ.toks.length))) with hT
    have hexp : ∀ i (h : i < L), LTL.Sat W T (2 * i) ↔ CSat vs[i] χ ∨ (CSat vs[i] ψ ∧
        (j + 2 ∈ W (2 * i + 1) ∨ LTL.Sat W T (2 * i + 2))) := by
      intro i h
      rw [hT, sat_U_iff, ← hT, hb0 i h, ha0 i h, sat_U_iff, ← hT, hb1 i h]
      simp only [ha1 i h, true_and]
    show ∀ i (h : i < L), LTL.Sat W T (2 * i) ↔ CSat vs[i] (.EU ψ χ)
    refine fun i h => back_ind (L := L)
      (P := fun i => ∀ h : i < L, LTL.Sat W T (2 * i) ↔ CSat vs[i] (.EU ψ χ)) ?_ ?_ i h h
    · intro i hi h
      obtain ⟨hE1, hE2⟩ := hW.hEU i h j ψ χ R hj
      rw [csat_EU]
      by_cases hl : vs[i].children = []
      · have hp := hW.tail_leaf i h hi hl
        rw [sat_U_periodic W (by omega) hp]
        simp only [hl, ne_eq, not_true_eq_false, false_and, and_false, or_false]
        constructor
        · rintro ⟨k, hk, hk1, hk2⟩
          rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
          · exact (hb0 i h).1 hk1
          · obtain ⟨c, hc, -⟩ := hE1 ((hb1 i h).1 hk1); simp [hl] at hc
        · intro h'; exact ⟨0, by omega, (hb0 i h).2 h', fun _ hj => absurd hj (by omega)⟩
      · have hp := hW.tail_node i h hi hl
        rw [hexp i h]
        have e : 2 * i + 2 = (2 * i + 1) + 1 := rfl
        rw [e, sat_periodic W hp _ _ le_rfl, sat_U_periodic W (by omega) hp]
        simp only [Nat.lt_one_iff, exists_eq_left, add_zero, not_lt_zero', IsEmpty.forall_iff,
          implies_true, and_true]
        rw [hb1 i h]
        simp only [or_self]
        constructor
        · rintro (h' | ⟨h3, h4⟩)
          · exact Or.inl h'
          · exact Or.inr ⟨h3, hl, hE1 h4⟩
        · rintro (h' | ⟨h3, -, h4⟩)
          · exact Or.inl h'
          · rcases hE2 h4 with h5 | ⟨h5, -⟩
            · exact Or.inr ⟨h3, h5⟩
            · omega
    · intro i hi ih h
      obtain ⟨hE1, hE2⟩ := hW.hEU i h j ψ χ R hj
      rw [hexp i h, show 2 * i + 2 = 2 * (i + 1) by ring, ih hi, csat_EU ψ χ vs[i]]
      have hc := hW.path i hi
      have hne : vs[i].children ≠ [] := by intro e'; rw [e'] at hc; simp at hc
      constructor
      · rintro (h' | ⟨h3, h4 | h4⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨h3, hne, hE1 h4⟩
        · exact Or.inr ⟨h3, hne, _, hc, h4⟩
      · rintro (h' | ⟨h3, -, h4⟩)
        · exact Or.inl h'
        · rcases hE2 h4 with h5 | ⟨_, h5⟩
          · exact Or.inr ⟨h3, Or.inl h5⟩
          · exact Or.inr ⟨h3, Or.inr h5⟩
  | AU ψ χ ih1 ih2 =>
    intro j R hj
    have h1 : ts.drop (j + 1) = ψ.toks ++ (χ.toks ++ R) := by
      have := drop_tag (l := ψ.toks ++ χ.toks) hj; simpa using this
    have h2 := CTLP.drop_append_of_drop h1
    have hb0 : ∀ i (h : i < L), LTL.Sat W (lite (.ap 0) (.and (.ap (j + 2)) (.ap 1))
        (trC m χ (j + 1 + ψ.toks.length))) (2 * i) ↔ CSat vs[i] χ := by
      intro i h
      rw [sat_lite]; simp only [LTL.Sat, hW.nd_e i h, false_and, not_false_eq_true, true_and,
        false_or]
      exact ih2 _ _ h2 i h
    have ha0 : ∀ i (h : i < L), LTL.Sat W (lite (.ap 0) (.ap (j + 2)) (trC m ψ (j + 1))) (2 * i) ↔
        CSat vs[i] ψ := by
      intro i h
      rw [sat_lite]; simp only [LTL.Sat, hW.nd_e i h, false_and, not_false_eq_true, true_and,
        false_or]
      exact ih1 _ _ h1 i h
    have hb1 : ∀ i (h : i < L), LTL.Sat W (lite (.ap 0) (.and (.ap (j + 2)) (.ap 1))
        (trC m χ (j + 1 + ψ.toks.length))) (2 * i + 1) ↔
          (j + 2 ∈ W (2 * i + 1) ∧ 1 ∈ W (2 * i + 1)) := by
      intro i h
      rw [sat_lite]; simp only [LTL.Sat, hW.ex_e i h, true_and, not_true_eq_false, false_and,
        or_false]
    have ha1 : ∀ i (h : i < L), LTL.Sat W (lite (.ap 0) (.ap (j + 2)) (trC m ψ (j + 1)))
        (2 * i + 1) ↔ j + 2 ∈ W (2 * i + 1) := by
      intro i h
      rw [sat_lite]; simp only [LTL.Sat, hW.ex_e i h, true_and, not_true_eq_false, false_and,
        or_false]
    set T := LTL.U (lite (.ap 0) (.ap (j + 2)) (trC m ψ (j + 1)))
      (lite (.ap 0) (.and (.ap (j + 2)) (.ap 1)) (trC m χ (j + 1 + ψ.toks.length))) with hT
    have hexp : ∀ i (h : i < L), LTL.Sat W T (2 * i) ↔ CSat vs[i] χ ∨ (CSat vs[i] ψ ∧
        ((j + 2 ∈ W (2 * i + 1) ∧ 1 ∈ W (2 * i + 1)) ∨
          (j + 2 ∈ W (2 * i + 1) ∧ LTL.Sat W T (2 * i + 2)))) := by
      intro i h
      rw [hT, sat_U_iff, ← hT, hb0 i h, ha0 i h, sat_U_iff, ← hT, hb1 i h, ha1 i h]
    show ∀ i (h : i < L), LTL.Sat W T (2 * i) ↔ CSat vs[i] (.AU ψ χ)
    refine fun i h => back_ind (L := L)
      (P := fun i => ∀ h : i < L, LTL.Sat W T (2 * i) ↔ CSat vs[i] (.AU ψ χ)) ?_ ?_ i h h
    · intro i hi h
      obtain ⟨hE1, hE2⟩ := hW.hAU i h j ψ χ R hj
      have hen := hW.ex_en i h
      rw [csat_AU]
      by_cases hl : vs[i].children = []
      · have hp := hW.tail_leaf i h hi hl
        rw [sat_U_periodic W (by omega) hp]
        simp only [hl, ne_eq, not_true_eq_false, false_and, and_false, or_false]
        constructor
        · rintro ⟨k, hk, hk1, hk2⟩
          rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
          · exact (hb0 i h).1 hk1
          · have := ((hb1 i h).1 hk1).2; rw [hen] at this; exact absurd hl this.2
        · intro h'; exact ⟨0, by omega, (hb0 i h).2 h', fun _ hj => absurd hj (by omega)⟩
      · have hp := hW.tail_node i h hi hl
        have h1m : 1 ∈ W (2 * i + 1) := hen.2 ⟨by omega, hl⟩
        rw [hexp i h]
        simp only [h1m, and_true]
        constructor
        · rintro (h' | ⟨h3, h4 | ⟨h4, -⟩⟩)
          · exact Or.inl h'
          · exact Or.inr ⟨h3, hl, hE2 h4 (fun h5 => absurd h5 (by omega))⟩
          · exact Or.inr ⟨h3, hl, hE2 h4 (fun h5 => absurd h5 (by omega))⟩
        · rintro (h' | ⟨h3, -, h4⟩)
          · exact Or.inl h'
          · exact Or.inr ⟨h3, Or.inl (hE1 h4)⟩
    · intro i hi ih h
      obtain ⟨hE1, hE2⟩ := hW.hAU i h j ψ χ R hj
      have h1n : 1 ∉ W (2 * i + 1) := by rw [hW.ex_en i h]; omega
      rw [hexp i h, show 2 * i + 2 = 2 * (i + 1) by ring, ih hi, csat_AU ψ χ vs[i]]
      simp only [h1n, and_false, false_or]
      have hc := hW.path i hi
      have hne : vs[i].children ≠ [] := by intro e'; rw [e'] at hc; simp at hc
      constructor
      · rintro (h' | ⟨h3, h4, h5⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨h3, hne, hE2 h4 (fun _ => h5)⟩
      · rintro (h' | ⟨h3, -, h4⟩)
        · exact Or.inl h'
        · exact Or.inr ⟨h3, hE1 h4, h4 _ hc⟩

end CTLT

end PathChecking
