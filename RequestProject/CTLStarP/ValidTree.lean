module

public import RequestProject.CTLStarP.ValidProof

/-!
# Correctness of the recognition of labels, trees, formulas and instances
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open LS MCVPReduction

variable {ts : List Tok}

lemma drop_split {p : ℕ} {l r : List Tok} (h : ts.drop p = l ++ r) :
    ts.drop p = l ++ ts.drop (p + l.length) := by
  rw [drop_append_of_drop h]; exact h

lemma labSuf_complete (xs : List ℕ) : ∀ {q : ℕ} {rest : List Tok}, xs.Pairwise (· < ·) →
    ts.drop q = xs.flatMap natToks ++ Tok.rpar :: rest → labSuf ts q = true := by
  induction xs with
  | nil =>
    intro q rest _ h
    have h' : ts.drop q = Tok.rpar :: rest := by simpa using h
    rw [labSuf_eq, if_neg (by have := lt_of_drop h'; omega), if_pos (by rw [tc_of_drop h']; rfl)]
  | cons a xs ih =>
    intro q rest hp h
    have ha : ts.drop q = natToks a ++ (xs.flatMap natToks ++ Tok.rpar :: rest) := by
      simpa using h
    obtain ⟨t, l, htl, htc⟩ := natToks_head_code a
    have ha' : ts.drop q = t :: (l ++ (xs.flatMap natToks ++ Tok.rpar :: rest)) := by
      rw [ha, htl]; rfl
    have hq := lt_of_drop ha'
    have hne : tc ts q ≠ 4 := by rw [tc_of_drop ha']; omega
    have he := numEnd_natToks a ha
    have hd := drop_append_of_drop ha
    rw [labSuf_eq, if_neg (by omega), if_neg hne]
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    refine ⟨⟨numOK_natToks a ha, ?_⟩, ?_⟩
    · cases xs with
      | nil => left; rw [he]; simp at hd; rw [tc_of_drop hd]; rfl
      | cons x xs =>
        right
        rw [he, numLt_natToks ha (r2 := xs.flatMap natToks ++ Tok.rpar :: rest) (by simpa using hd)]
        simpa using (List.pairwise_cons.1 hp).1 x (by simp)
    · rw [he]; exact ih (List.pairwise_cons.1 hp).2 hd

lemma validLab_iff (p : ℕ) :
    validLab ts p = true ↔ ∃ s rest, ts.drop p = finsetToks s ++ rest := by
  constructor
  · intro h
    simp only [validLab, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨xs, rest, hxs, hd⟩ := labSuf_sound _ _ rfl h2
    have hnd : xs.Nodup := hxs.imp (fun h => ne_of_lt h)
    refine ⟨xs.toFinset, rest, ?_⟩
    rw [drop_of_tc (t := Tok.lpar) h1, hd, finsetToks,
      (List.toFinset_sort (· ≤ ·) hnd).2 (hxs.imp le_of_lt)]
    simp
  · rintro ⟨s, rest, h⟩
    have h' : ts.drop p = Tok.lpar :: ((s.sort (· ≤ ·)).flatMap natToks ++ Tok.rpar :: rest) := by
      simpa [finsetToks] using h
    simp only [validLab, Bool.and_eq_true, beq_iff_eq]
    refine ⟨by rw [tc_of_drop h']; rfl, ?_⟩
    have hs : (s.sort (· ≤ ·)).Pairwise (· < ·) :=
      (Finset.pairwise_sort s (· ≤ ·)).imp₂ (fun a b hab hne => lt_of_le_of_ne hab hne)
        (Finset.sort_nodup s (· ≤ ·))
    exact labSuf_complete _ hs (drop_succ_of_drop h')

/-! ## Trees -/

lemma kidsOK_eq (c : ℕ) : kidsOK ts c =
    if ts.length ≤ c then false
    else if tc ts c = 4 then true
    else tc ts c == 3 && validLab ts (c + 1) && kidsOK ts (tend ts (c + 1)) &&
      kidsOK ts (tend ts c) := by
  rw [kidsOK]; simp only [dite_eq_ite]

lemma node_toks_drop {p : ℕ} {s : Finset ℕ} {cs : List LTree} {rest : List Tok}
    (h : ts.drop p = (LTree.node s cs).toks ++ rest) :
    ts.drop p = Tok.lpar :: (finsetToks s ++ (LTree.toksList cs ++ Tok.rpar :: rest)) := by
  rw [h]; simp [LTree.toks]

lemma kidsOK_sound : ∀ m c, ts.length - c = m → kidsOK ts c = true →
    ∃ (cs : List LTree) (rest : List Tok), ts.drop c = LTree.toksList cs ++ Tok.rpar :: rest := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hm h
    rw [kidsOK_eq] at h
    split_ifs at h with h1 h2
    · exact ⟨[], ts.drop (c + 1), by simpa [LTree.toksList] using drop_of_tc (t := Tok.rpar) h2⟩
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h
      obtain ⟨s, r1, hs⟩ := (validLab_iff _).1 h4
      have hd1 := drop_of_tc (t := Tok.lpar) h3
      have hte := tend_finset s hs
      obtain ⟨cs1, r2, hcs1⟩ := ih _ (by have := (finsetToks s).length; omega) _ rfl h5
      have hcs1' : ts.drop (c + 1 + (finsetToks s).length) =
          LTree.toksList cs1 ++ Tok.rpar :: r2 := by rw [← hte]; exact hcs1
      have ht : ts.drop c = (LTree.node s cs1).toks ++ r2 := by
        rw [hd1, drop_split hs, hcs1']
        simp [LTree.toks]
      have htc := tend_tree _ ht
      have hd2 := drop_append_of_drop ht
      rw [← htc] at hd2
      obtain ⟨cs2, r3, hcs2⟩ := ih _ (by have := LTree.toks_length_pos (LTree.node s cs1); omega)
        _ rfl h6
      refine ⟨LTree.node s cs1 :: cs2, r3, ?_⟩
      rw [ht, LTree.toksList_cons, List.append_assoc, ← hcs2, hd2]

lemma kidsOK_complete (N : ℕ) : ∀ cs : List LTree, (LTree.toksList cs).length ≤ N →
    ∀ {c : ℕ} {rest : List Tok}, ts.drop c = LTree.toksList cs ++ Tok.rpar :: rest →
      kidsOK ts c = true := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro cs hN c rest h
    cases cs with
    | nil =>
      have h' : ts.drop c = Tok.rpar :: rest := by simpa [LTree.toksList] using h
      rw [kidsOK_eq, if_neg (by have := lt_of_drop h'; omega), if_pos (by rw [tc_of_drop h']; rfl)]
    | cons t cs =>
      obtain ⟨s, cs1⟩ := t
      rw [LTree.toksList_cons, List.append_assoc] at h
      have hn := node_toks_drop h
      have hc := lt_of_drop hn
      rw [LTree.toksList_cons, List.length_append] at hN
      have hlt := LTree.toks_length_lt s cs1
      have hpos := LTree.toks_length_pos (LTree.node s cs1)
      rw [kidsOK_eq, if_neg (by omega), if_neg (by rw [tc_of_drop hn]; decide)]
      simp only [Bool.and_eq_true, beq_iff_eq]
      have hs := drop_succ_of_drop hn
      refine ⟨⟨⟨by rw [tc_of_drop hn]; rfl, (validLab_iff _).2 ⟨s, _, hs⟩⟩, ?_⟩, ?_⟩
      · rw [tend_finset s hs]
        exact ih _ (by omega) cs1 le_rfl (drop_append_of_drop hs)
      · rw [tend_tree _ h]
        exact ih _ (by omega) cs le_rfl (drop_append_of_drop h)

lemma validT_iff (u : ℕ) :
    validT ts u = true ↔ ∃ t rest, ts.drop u = LTree.toks t ++ rest := by
  constructor
  · intro h
    simp only [validT, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨s, r1, hs⟩ := (validLab_iff _).1 h2
    obtain ⟨cs, r2, hcs⟩ := kidsOK_sound _ _ rfl h3
    rw [tend_finset s hs] at hcs
    refine ⟨LTree.node s cs, r2, ?_⟩
    rw [drop_of_tc (t := Tok.lpar) h1, drop_split hs, hcs]
    simp [LTree.toks]
  · rintro ⟨⟨s, cs⟩, rest, h⟩
    have hn := node_toks_drop h
    have hs := drop_succ_of_drop hn
    simp only [validT, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨by rw [tc_of_drop hn]; rfl, (validLab_iff _).2 ⟨s, _, hs⟩⟩, ?_⟩
    rw [tend_finset s hs]
    exact kidsOK_complete _ cs le_rfl (drop_append_of_drop hs)

/-! ## Formulas -/

lemma validF_eq (j : ℕ) : validF ts j =
    if ts.length ≤ j then false
    else if tc ts j = 5 then numOK ts (j + 1)
    else if tc ts j = 6 then true
    else if tc ts j = 7 ∨ tc ts j = 9 ∨ tc ts j = 11 then validF ts (j + 1)
    else if tc ts j = 8 ∨ tc ts j = 10 then validF ts (j + 1) && validF ts (fend ts (j + 1))
    else false := by
  rw [validF]; simp only [dite_eq_ite]

lemma validF_sound : ∀ m j, ts.length - j = m → validF ts j = true →
    ∃ (φ : CTLStar) (rest : List Tok), ts.drop j = φ.toks ++ rest := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro j hm h
    rw [validF_eq] at h
    split_ifs at h with h1 h2 h3 h4 h5
    · obtain ⟨a, rest, ha⟩ := numOK_sound h
      exact ⟨.ap a, rest, by rw [drop_of_tc (t := Tok.tag 0) h2, ha]; rfl⟩
    · exact ⟨.tt, ts.drop (j + 1), by rw [drop_of_tc (t := Tok.tag 1) h3]; rfl⟩
    · obtain ⟨φ, rest, hφ⟩ := ih _ (by omega) _ rfl h
      rcases h4 with h4 | h4 | h4
      · exact ⟨.neg φ, rest, by rw [drop_of_tc (t := Tok.tag 2) h4, hφ]; rfl⟩
      · exact ⟨.X φ, rest, by rw [drop_of_tc (t := Tok.tag 4) h4, hφ]; rfl⟩
      · exact ⟨.E φ, rest, by rw [drop_of_tc (t := Tok.tag 6) h4, hφ]; rfl⟩
    · simp only [Bool.and_eq_true] at h
      obtain ⟨ha, hb⟩ := h
      obtain ⟨φ, r1, hφ⟩ := ih _ (by omega) _ rfl ha
      have hfe := fend_formula φ hφ
      obtain ⟨ψ, r2, hψ⟩ := ih _ (by omega) _ rfl hb
      rw [hfe] at hψ
      have e : ts.drop (j + 1) = φ.toks ++ (ψ.toks ++ r2) := by
        rw [← hψ, ← drop_split hφ, hφ]
      rcases h5 with h5 | h5
      · exact ⟨.and φ ψ, r2, by rw [drop_of_tc (t := Tok.tag 3) h5, e]; simp [CTLStar.toks]⟩
      · exact ⟨.U φ ψ, r2, by rw [drop_of_tc (t := Tok.tag 5) h5, e]; simp [CTLStar.toks]⟩

lemma validF_complete (φ : CTLStar) : ∀ {j : ℕ} {rest : List Tok},
    ts.drop j = φ.toks ++ rest → validF ts j = true := by
  induction φ with
  | ap a =>
    intro j rest h
    have h' : ts.drop j = Tok.tag 0 :: (natToks a ++ rest) := by simpa [CTLStar.toks] using h
    rw [validF_eq, if_neg (by have := lt_of_drop h'; omega), if_pos (by rw [tc_of_drop h']; rfl)]
    exact numOK_natToks a (drop_succ_of_drop h')
  | tt =>
    intro j rest h
    have h' : ts.drop j = Tok.tag 1 :: rest := by simpa [CTLStar.toks] using h
    rw [validF_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp [tc_of_drop h', Tok.code]
  | neg φ ih =>
    intro j rest h
    have h' : ts.drop j = Tok.tag 2 :: (φ.toks ++ rest) := by simpa [CTLStar.toks] using h
    rw [validF_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h']
    simpa [Tok.code] using ih (drop_succ_of_drop h')
  | X φ ih =>
    intro j rest h
    have h' : ts.drop j = Tok.tag 4 :: (φ.toks ++ rest) := by simpa [CTLStar.toks] using h
    rw [validF_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h']
    simpa [Tok.code] using ih (drop_succ_of_drop h')
  | E φ ih =>
    intro j rest h
    have h' : ts.drop j = Tok.tag 6 :: (φ.toks ++ rest) := by simpa [CTLStar.toks] using h
    rw [validF_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h']
    simpa [Tok.code] using ih (drop_succ_of_drop h')
  | and φ ψ ih1 ih2 =>
    intro j rest h
    have h' : ts.drop j = Tok.tag 3 :: (φ.toks ++ (ψ.toks ++ rest)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    rw [validF_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h', fend_formula φ h1]
    simpa [Tok.code] using ⟨ih1 h1, ih2 (drop_append_of_drop h1)⟩
  | U φ ψ ih1 ih2 =>
    intro j rest h
    have h' : ts.drop j = Tok.tag 5 :: (φ.toks ++ (ψ.toks ++ rest)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    rw [validF_eq, if_neg (by have := lt_of_drop h'; omega)]
    simp only [tc_of_drop h', fend_formula φ h1]
    simpa [Tok.code] using ⟨ih1 h1, ih2 (drop_append_of_drop h1)⟩

lemma validF_iff (j : ℕ) :
    validF ts j = true ↔ ∃ (φ : CTLStar) (rest : List Tok), ts.drop j = φ.toks ++ rest :=
  ⟨validF_sound _ _ rfl, fun ⟨φ, _, h⟩ => validF_complete φ h⟩

/-! ## Instances -/

/-- **Recognition of instances.** -/
theorem validTop_iff :
    validTop ts = true ↔ ∃ (φ : CTLStar) (t : LTree), ts = Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks) := by
  constructor
  · intro h
    simp only [validTop, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    obtain ⟨φ, r1, hφ⟩ := (validF_iff _).1 h2
    have hfe := fend_formula φ hφ
    obtain ⟨t, r2, ht⟩ := (validT_iff _).1 h4
    have hte := tend_tree t ht
    have hr := drop_of_tc (t := Tok.rpar) h3
    have hl := congrArg List.length ht
    rw [List.length_drop, List.length_append] at hl
    have hr2 : r2 = [] := by
      rw [← List.length_eq_zero_iff]; omega
    subst hr2
    refine ⟨φ, t, ?_⟩
    have e0 := drop_of_tc (t := Tok.lpar) h1
    simp only [List.drop_zero] at e0
    rw [e0, drop_split hφ, ← hfe, hr, ht]
    simp
  · rintro ⟨φ, t, rfl⟩
    set ts := Tok.lpar :: (φ.toks ++ Tok.rpar :: t.toks)
    have h1 : ts.drop 1 = φ.toks ++ Tok.rpar :: t.toks := rfl
    have hfe := fend_formula φ h1
    have h2 := drop_append_of_drop h1
    rw [← hfe] at h2
    have h3 := drop_succ_of_drop h2
    have h3' : ts.drop (fend ts 1 + 1) = t.toks ++ [] := by simpa using h3
    simp only [validTop, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨⟨⟨rfl, (validF_iff _).2 ⟨φ, _, h1⟩⟩, by rw [tc_of_drop h2]; rfl⟩,
      (validT_iff _).2 ⟨t, _, h3'⟩⟩, ?_⟩
    rw [tend_tree t h3', hfe]
    simp [ts]; omega

end CTLP

end PathChecking
