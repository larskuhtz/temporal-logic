module

public import RequestProject.Shallow.Valid
public import RequestProject.Shallow.Reduction

/-!
# Recognition of trees with shallow branching

Soundness and completeness of the counter-based tree recognizer `polT` (with the check of the
branching depth), and the recognizer `recog` of instances `( φ ) t` whose tree has branching
depth `< b` (`recog_iff`).
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open Shallow

/-! ## Shallow branching, locally -/

lemma SB_zero_linear {t : LTree} (h : ShallowBranching 0 t) : Linear t := by
  cases h with
  | lin h => exact h

lemma linear_children {l : Finset ℕ} {cs : List LTree} (h : Linear (.node l cs)) :
    cs.length ≤ 1 ∧ ∀ c ∈ cs, Linear c := by
  cases h with
  | leaf => simp
  | cons _ c hc => simp [hc]

lemma SB_child {n : ℕ} {l : Finset ℕ} {cs : List LTree} (h : ShallowBranching n (.node l cs))
    {c : LTree} (hc : c ∈ cs) : ShallowBranching (n - 1) c := by
  cases h with
  | lin h => exact .lin ((linear_children h).2 c hc)
  | step h => simpa using h c hc

lemma SB_two {n : ℕ} {l : Finset ℕ} {cs : List LTree} (h : ShallowBranching n (.node l cs))
    (h2 : 2 ≤ cs.length) : 0 < n := by
  cases h with
  | lin h => have := (linear_children h).1; omega
  | step _ => omega

lemma SB_node {n : ℕ} {l : Finset ℕ} {cs : List LTree}
    (hc : ∀ c ∈ cs, ShallowBranching (n - 1) c) (h2 : 2 ≤ cs.length → 0 < n) :
    ShallowBranching n (.node l cs) := by
  rcases n with _ | n
  · refine .lin ?_
    rcases cs with _ | ⟨c, _ | ⟨c', cs⟩⟩
    · exact .leaf l
    · exact .cons l c (SB_zero_linear (hc c (by simp)))
    · simp at h2
  · exact .step (fun c h => by simpa using hc c h)

/-- The invariant of the tree recognizer on the stack of lists of trees still to be read: the
head list consists of nodes at depth `d`; `f` records whether the head list is the first
part of its parent's children seen so far. -/
def sbI (b : ℕ) : ℕ → Bool → List (List LTree) → Prop
  | _, _, [] => True
  | d, f, cs :: css => (∀ t ∈ cs, ShallowBranching (b - d) t) ∧
      ((if f then 2 else 1) ≤ cs.length → d - 1 < b) ∧ sbI b (d - 1) false css

lemma sbI_true_of_false {b d : ℕ} {css : List (List LTree)} (h : sbI b d false css) :
    sbI b d true css := by
  cases css with
  | nil => trivial
  | cons cs css =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨h1, fun h => h2 (by simp at h ⊢; omega), h3⟩

lemma toksList_cons_drop {p : ℕ} {ts : List Tok} {t : LTree} {cs : List LTree}
    {rest : List Tok} (h : ts.drop p = LTree.toksList (t :: cs) ++ rest) : tc ts p = 3 := by
  obtain ⟨l, ds⟩ := t
  have h' : ts.drop p = Tok.lpar :: (finsetToks l ++ LTree.toksList ds ++ [Tok.rpar] ++
      LTree.toksList cs ++ rest) := by
    rw [h]; simp [LTree.toksList, LTree.toks]
  rw [tc_of_drop h']; rfl

variable {ts : List Tok} {b : ℕ}

lemma polT_sound : ∀ m p c, ts.length - p = m → 1 ≤ c → polT ts b p c = true →
    ∃ css : List (List LTree), css.length = c ∧ sbI b c true css ∧
      ∃ rest, ts.drop p = kToks css ++ rest := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p c hm hc h
    rw [polT_eq] at h
    split_ifs at h with h1 h2 h3
    · have hd := drop_of_tc (t := Tok.rpar) h2
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true',
        ] at h
      by_cases hc1 : c = 1
      · subst hc1
        exact ⟨[[]], rfl, ⟨by simp, by simp, trivial⟩, ts.drop (p + 1), by
          rw [hd]; simp [LTree.toksList]⟩
      · have ⟨hchk, hr⟩ : (tc ts (p + 1) == 3 && decide (b + 2 ≤ c)) = false ∧
            polT ts b (p + 1) (c - 1) = true := by
          rcases h with h | h
          · exact absurd h hc1
          · exact h
        obtain ⟨css, hl, hI, r, hcss⟩ := ih _ (by omega) _ (c - 1) rfl (by omega) hr
        refine ⟨[] :: css, by simp; omega, ⟨by simp, by simp, ?_⟩, r, ?_⟩
        · cases css with
          | nil => trivial
          | cons cs css =>
            obtain ⟨i1, i2, i3⟩ := hI
            refine ⟨by simpa using i1, fun hlen => ?_, by simpa using i3⟩
            obtain ⟨t, cs', rfl⟩ : ∃ t cs', cs = t :: cs' := by
              cases cs with
              | nil => simp at hlen
              | cons t cs' => exact ⟨t, cs', rfl⟩
            have h3 : tc ts (p + 1) = 3 := toksList_cons_drop (t := t) (cs := cs')
              (rest := [Tok.rpar] ++ kToks css ++ r) (by rw [hcss]; simp)
            simp [h3] at hchk
            omega
        · rw [hd, hcss]; simp [LTree.toksList]
    · simp only [Bool.and_eq_true] at h
      obtain ⟨hv, hr⟩ := h
      obtain ⟨s, r1, hs⟩ := (validLab_iff _).1 hv
      have hte := tend_finset s hs
      have hlen := congrArg List.length hs
      simp only [List.length_drop, List.length_append] at hlen
      have hfl : 0 < (finsetToks s).length := by simp [finsetToks]
      obtain ⟨css, hl, hI, r, hcss⟩ := ih _ (by omega) _ (c + 1) rfl (by omega) hr
      obtain ⟨cs1, cs2, css', rfl⟩ : ∃ cs1 cs2 css', css = cs1 :: cs2 :: css' := by
        rcases css with _ | ⟨cs1, _ | ⟨cs2, css'⟩⟩
        · simp at hl
        · simp at hl; omega
        · exact ⟨cs1, cs2, css', rfl⟩
      obtain ⟨i1, i2, i3, i4, i5⟩ : (∀ t ∈ cs1, ShallowBranching (b - (c + 1)) t) ∧
          (2 ≤ cs1.length → c < b) ∧ (∀ t ∈ cs2, ShallowBranching (b - c) t) ∧
          (1 ≤ cs2.length → c - 1 < b) ∧ sbI b (c - 1) false css' := by
        obtain ⟨a1, a2, a3, a4, a5⟩ := hI
        exact ⟨a1, fun h => by simpa using a2 h, by simpa using a3, by simpa using a4,
          by simpa using a5⟩
      refine ⟨(LTree.node s cs1 :: cs2) :: css', by simp at hl ⊢; omega, ⟨?_, ?_, i5⟩, r, ?_⟩
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact SB_node (fun t ht => by rw [show b - c - 1 = b - (c + 1) by omega]; exact i1 t ht)
            (fun h => by have := i2 h; omega)
        · exact i3 t ht
      · intro h; simp at h; exact i4 (by omega)
      · rw [hte] at hcss; rw [drop_of_tc (t := Tok.lpar) h3, drop_split hs, hcss]
        simp [LTree.toksList, LTree.toks]

lemma polT_complete (N : ℕ) : ∀ css : List (List LTree), (kToks css).length ≤ N → css ≠ [] →
    sbI b css.length true css → ∀ p rest, ts.drop p = kToks css ++ rest →
      polT ts b p css.length = true := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro css hN hne hI p rest h
    obtain ⟨cs, css', rfl⟩ : ∃ cs css', css = cs :: css' := by
      cases css with
      | nil => exact absurd rfl hne
      | cons cs css' => exact ⟨cs, css', rfl⟩
    rw [polT_eq]
    cases cs with
    | nil =>
      have h' : ts.drop p = Tok.rpar :: (kToks css' ++ rest) := by
        rw [h]; simp [LTree.toksList]
      have hlt := lt_of_drop h'
      rw [if_neg (by omega), if_pos (by rw [tc_of_drop h']; rfl)]
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true']
      rcases eq_or_ne css' [] with rfl | hne'
      · left; rfl
      · right
        obtain ⟨-, -, hI'⟩ := hI
        refine ⟨?_, ?_⟩
        · obtain ⟨cs', css'', rfl⟩ : ∃ cs' css'', css' = cs' :: css'' := by
            cases css' with
            | nil => exact absurd rfl hne'
            | cons cs' css'' => exact ⟨cs', css'', rfl⟩
          obtain ⟨-, j2, -⟩ := hI'
          cases cs' with
          | nil =>
            have h2 : ts.drop (p + 1) = Tok.rpar :: (kToks css'' ++ rest) := by
              rw [drop_succ_of_drop h']; simp [LTree.toksList]
            simp [tc_of_drop h2, Tok.code]
          | cons t cs'' =>
            have := j2 (by simp)
            simp only [List.length_cons] at this ⊢
            simp; omega
        · have := ih _ (by
            have : (kToks ([] :: css')).length = (kToks css').length + 1 := by
              simp [LTree.toksList]
            omega) css' le_rfl hne' (sbI_true_of_false (by simpa using hI')) (p + 1) rest
            (drop_succ_of_drop h')
          simpa using this
    | cons t cs2 =>
      obtain ⟨s, cs1⟩ := t
      have h' : ts.drop p = Tok.lpar :: (finsetToks s ++ (kToks (cs1 :: cs2 :: css') ++ rest)) := by
        rw [h]; simp [LTree.toksList, LTree.toks]
      have hlt := lt_of_drop h'
      rw [if_neg (by omega), if_neg (by rw [tc_of_drop h']; decide),
        if_pos (by rw [tc_of_drop h']; rfl)]
      have hs := drop_succ_of_drop h'
      have hte := tend_finset s hs
      simp only [Bool.and_eq_true]
      refine ⟨(validLab_iff _).2 ⟨s, _, hs⟩, ?_⟩
      obtain ⟨i1, i2, i3⟩ := hI
      have hnode := i1 (LTree.node s cs1) (by simp)
      have := ih _ (by
          have : (kToks ((LTree.node s cs1 :: cs2) :: css')).length =
              1 + (finsetToks s).length + (kToks (cs1 :: cs2 :: css')).length := by
            simp [LTree.toksList, LTree.toks]; omega
          have : 0 < (finsetToks s).length := by simp [finsetToks]
          omega) (cs1 :: cs2 :: css') le_rfl (by simp) ?_ (tend ts (p + 1)) rest
        (by rw [hte]; exact drop_append_of_drop hs)
      · simpa using this
      · refine ⟨fun t ht => ?_, fun h2 => ?_, fun t ht => ?_, fun h1 => ?_, ?_⟩
        · have := SB_child hnode ht
          simp only [List.length_cons] at this ⊢
          rwa [show b - (css'.length + 1) - 1 = b - (css'.length + 1 + 1) by omega] at this
        · have := SB_two hnode h2
          simp only [List.length_cons] at this ⊢
          simp; omega
        · simpa using i1 t (by simp [ht])
        · have := i2 (by simp at h1 ⊢; omega)
          simpa using this
        · simpa using i3

/-! ## Trees and instances -/

lemma validT'_iff (u : ℕ) : validT' ts b u = true ↔
    ∃ (t : LTree) (rest : List Tok), ts.drop u = t.toks ++ rest ∧ ShallowBranching b t := by
  constructor
  · intro h
    simp only [validT', Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨s, r1, hs⟩ := (validLab_iff _).1 h2
    obtain ⟨css, hl, hI, r, hcss⟩ := polT_sound _ _ 1 rfl le_rfl h3
    obtain ⟨cs, rfl⟩ := List.length_eq_one_iff.1 hl
    obtain ⟨i1, i2, -⟩ := hI
    refine ⟨.node s cs, r, ?_, SB_node (fun t ht => i1 t ht) (fun h => by simpa using i2 h)⟩
    rw [tend_finset s hs] at hcss; rw [drop_of_tc (t := Tok.lpar) h1, drop_split hs, hcss]
    simp [LTree.toks]
  · rintro ⟨⟨s, cs⟩, rest, h, hsb⟩
    have h' : ts.drop u = Tok.lpar :: (finsetToks s ++ (kToks [cs] ++ rest)) := by
      rw [h]; simp [LTree.toks]
    have hs := drop_succ_of_drop h'
    simp only [validT', Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨by rw [tc_of_drop h']; rfl, (validLab_iff _).2 ⟨s, _, hs⟩⟩, ?_⟩
    rw [tend_finset s hs]
    have := polT_complete (ts := ts) (b := b) _ [cs] le_rfl (by simp)
      ⟨fun t ht => SB_child hsb ht, fun h2 => by simpa using SB_two hsb h2, trivial⟩ _ rest
      (drop_append_of_drop hs)
    simpa using this

/-- **Recognition of instances with shallow branching.** -/
theorem recog_iff : recog ts b = true ↔ ∃ (φ : CTLStar) (t : LTree),
    ts = Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks) ∧ ShallowBranching b t := by
  constructor
  · intro h
    simp only [recog, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨φ, r1, hφ⟩ := (polF_one_iff _).1 h2
    have hfe := fend_formula φ hφ
    obtain ⟨t, r2, ht, hsb⟩ := (validT'_iff _).1 h4
    have hte := tend_tree t ht
    have hr := drop_of_tc (t := Tok.rpar) h3
    have hl := congrArg List.length ht
    rw [List.length_drop, List.length_append] at hl
    have hr2 : r2 = [] := by
      rw [← List.length_eq_zero_iff]; omega
    subst hr2
    refine ⟨φ, t, ?_, hsb⟩
    have e0 := drop_of_tc (t := Tok.lpar) h1
    simp only [List.drop_zero] at e0
    rw [e0, drop_split hφ, ← hfe, hr, ht]
    simp
  · rintro ⟨φ, t, rfl, hsb⟩
    set ts := Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks)
    have h1 : ts.drop 1 = φ.toks ++ Tok.rpar :: t.toks := rfl
    have hfe := fend_formula φ h1
    have h2 := drop_append_of_drop h1
    rw [← hfe] at h2
    have h3 := drop_succ_of_drop h2
    have h3' : ts.drop (fend ts 1 + 1) = t.toks ++ [] := by simpa using h3
    simp only [recog, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨rfl, (polF_one_iff _).2 ⟨φ, _, h1⟩⟩, by rw [tc_of_drop h2]; rfl⟩,
      (validT'_iff _).2 ⟨t, _, h3', hsb⟩⟩, ?_⟩
    rw [tend_tree t h3', hfe]
    simp [ts]; omega

end CTLP

end PathChecking
