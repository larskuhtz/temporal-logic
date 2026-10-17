module

public import RequestProject.CTLStarP.ValidTree

/-!
# Counter-based recognition of instances

`polF ts p c` checks (left to right, with a counter `c` of formulas still to be read) that the
tokens from position `p` on start with `c` formulas; `polT ts p c` checks that they start with
`c` lists of trees, each closed by `)`.  Both functions are tail recursive with strictly
increasing positions, so that they can be evaluated by a single left-to-right loop.
`recog ts` combines them into a recognizer of instances `( φ ) t` (`recog_iff`).
-/

@[expose] public section

namespace PathChecking

namespace CTLP

variable (ts : List Tok)

/-- `c ≥ 1` formulas start at position `p`. -/
def polF (p c : ℕ) : Bool :=
  if h : ts.length ≤ p then false
  else if tc ts p = 5 then numOK ts (p + 1) && (c == 1 || polF (numEnd ts (p + 1)) (c - 1))
  else if tc ts p = 6 then (c == 1 || polF (p + 1) (c - 1))
  else if tc ts p = 7 ∨ tc ts p = 9 ∨ tc ts p = 11 then polF (p + 1) c
  else if tc ts p = 8 ∨ tc ts p = 10 then polF (p + 1) (c + 1)
  else false
termination_by ts.length - p
decreasing_by
  all_goals first
    | omega
    | (have := le_scan (ts := ts) upN downN (p + 1) 1; simp only [numEnd]; omega)

/-- `c ≥ 1` lists of trees, each followed by `)`, start at position `p`; the innermost list
consists of nodes at depth `c`, and every node with two or more children has depth `< b`
(checked at the closing bracket of a node followed by a sibling). -/
def polT (b p c : ℕ) : Bool :=
  if h : ts.length ≤ p then false
  else if tc ts p = 4 then
    (c == 1 || (!(tc ts (p + 1) == 3 && b + 2 ≤ c) && polT b (p + 1) (c - 1)))
  else if tc ts p = 3 then validLab ts (p + 1) && polT b (tend ts (p + 1)) (c + 1)
  else false
termination_by ts.length - p
decreasing_by
  all_goals first
    | omega
    | (have := le_scan (ts := ts) upT downT (p + 1) 0; simp only [tend]; omega)

/-- A tree with branching depth `< b` starts at position `u`. -/
def validT' (b u : ℕ) : Bool :=
  tc ts u == 3 && validLab ts (u + 1) && polT ts b (tend ts (u + 1)) 1

/-- The recognizer of instances `( φ ) t` with branching depth `< b`. -/
def recog (b : ℕ) : Bool :=
  tc ts 0 == 3 && polF ts 1 1 && tc ts (fend ts 1) == 4 && validT' ts b (fend ts 1 + 1) &&
    tend ts (fend ts 1 + 1) == ts.length

variable {ts}

lemma polF_eq (p c : ℕ) : polF ts p c =
    if ts.length ≤ p then false
    else if tc ts p = 5 then numOK ts (p + 1) && (c == 1 || polF ts (numEnd ts (p + 1)) (c - 1))
    else if tc ts p = 6 then (c == 1 || polF ts (p + 1) (c - 1))
    else if tc ts p = 7 ∨ tc ts p = 9 ∨ tc ts p = 11 then polF ts (p + 1) c
    else if tc ts p = 8 ∨ tc ts p = 10 then polF ts (p + 1) (c + 1)
    else false := by
  rw [polF]; simp only [dite_eq_ite]

lemma polT_eq (b p c : ℕ) : polT ts b p c =
    if ts.length ≤ p then false
    else if tc ts p = 4 then
      (c == 1 || (!(tc ts (p + 1) == 3 && b + 2 ≤ c) && polT ts b (p + 1) (c - 1)))
    else if tc ts p = 3 then validLab ts (p + 1) && polT ts b (tend ts (p + 1)) (c + 1)
    else false := by
  rw [polT]; simp only [dite_eq_ite]

/-- Concatenated encodings of a list of formulas. -/
def fToks (φs : List CTLStar) : List Tok := φs.flatMap CTLStar.toks

/-- Concatenated encodings of lists of trees, each followed by `)`. -/
def kToks (css : List (List LTree)) : List Tok :=
  css.flatMap (fun cs => LTree.toksList cs ++ [Tok.rpar])

@[simp] lemma fToks_nil : fToks [] = [] := rfl
@[simp] lemma fToks_cons (φ : CTLStar) (φs : List CTLStar) :
    fToks (φ :: φs) = φ.toks ++ fToks φs := rfl
@[simp] lemma kToks_nil : kToks [] = [] := rfl
@[simp] lemma kToks_cons (cs : List LTree) (css : List (List LTree)) :
    kToks (cs :: css) = LTree.toksList cs ++ [Tok.rpar] ++ kToks css := rfl

lemma polF_sound : ∀ m p c, ts.length - p = m → 1 ≤ c → polF ts p c = true →
    ∃ φs : List CTLStar, φs.length = c ∧ ∃ rest, ts.drop p = fToks φs ++ rest := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p c hm hc h
    rw [polF_eq] at h
    split_ifs at h with h1 h2 h3 h4 h5
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨hn, hr⟩ := h
      obtain ⟨a, rest, ha⟩ := numOK_sound hn
      have hd : ts.drop p = (CTLStar.ap a).toks ++ rest := by
        rw [drop_of_tc (t := Tok.tag 0) h2, ha]; rfl
      by_cases hc1 : c = 1
      · subst hc1; exact ⟨[.ap a], rfl, rest, by simp [hd]⟩
      · have hr' : polF ts (numEnd ts (p + 1)) (c - 1) = true := by
          rcases hr with h | h
          · exact absurd h hc1
          · exact h
        have hne := numEnd_natToks a ha
        have hlen : (CTLStar.ap a).toks.length = 1 + (natToks a).length := by
          simp [CTLStar.toks]; omega
        obtain ⟨φs, hl, r, hφ⟩ := ih _ (by
          have := lt_of_drop (t := Tok.tag 0) (rest := natToks a ++ rest)
            (by rw [hd]; rfl)
          have : 0 < (natToks a).length := by simp [natToks]
          omega) _ (c - 1) rfl (by omega) hr'
        refine ⟨.ap a :: φs, by simp; omega, r, ?_⟩
        rw [drop_split hd, hlen, show p + (1 + (natToks a).length) = numEnd ts (p + 1) by omega,
          hφ]
        simp
    · simp only [Bool.or_eq_true, beq_iff_eq] at h
      have hd : ts.drop p = CTLStar.tt.toks ++ ts.drop (p + 1) := by
        rw [drop_of_tc (t := Tok.tag 1) h3]; rfl
      by_cases hc1 : c = 1
      · subst hc1; exact ⟨[.tt], rfl, ts.drop (p + 1), by simp [hd]⟩
      · have hr' : polF ts (p + 1) (c - 1) = true := by
          rcases h with h | h
          · exact absurd h hc1
          · exact h
        obtain ⟨φs, hl, r, hφ⟩ := ih _ (by omega) _ (c - 1) rfl (by omega) hr'
        exact ⟨.tt :: φs, by simp; omega, r, by rw [hd, hφ]; simp⟩
    · obtain ⟨φs, hl, r, hφ⟩ := ih _ (by omega) _ c rfl hc h
      obtain ⟨ψ, φs', rfl⟩ : ∃ ψ φs', φs = ψ :: φs' := by
        cases φs with
        | nil => simp at hl; omega
        | cons ψ φs' => exact ⟨ψ, φs', rfl⟩
      simp only [fToks_cons, List.append_assoc] at hφ
      rcases h4 with h4 | h4 | h4
      · exact ⟨.neg ψ :: φs', hl, r, by rw [drop_of_tc (t := Tok.tag 2) h4, hφ]; simp [CTLStar.toks]⟩
      · exact ⟨.X ψ :: φs', hl, r, by rw [drop_of_tc (t := Tok.tag 4) h4, hφ]; simp [CTLStar.toks]⟩
      · exact ⟨.E ψ :: φs', hl, r, by rw [drop_of_tc (t := Tok.tag 6) h4, hφ]; simp [CTLStar.toks]⟩
    · obtain ⟨φs, hl, r, hφ⟩ := ih _ (by omega) _ (c + 1) rfl (by omega) h
      obtain ⟨ψ1, ψ2, φs', rfl⟩ : ∃ ψ1 ψ2 φs', φs = ψ1 :: ψ2 :: φs' := by
        rcases φs with _ | ⟨ψ1, _ | ⟨ψ2, φs'⟩⟩
        · simp at hl
        · simp at hl; omega
        · exact ⟨ψ1, ψ2, φs', rfl⟩
      simp only [fToks_cons, List.append_assoc] at hφ
      simp only [List.length_cons] at hl
      rcases h5 with h5 | h5
      · exact ⟨.and ψ1 ψ2 :: φs', by simp; omega, r, by
          rw [drop_of_tc (t := Tok.tag 3) h5, hφ]; simp [CTLStar.toks]⟩
      · exact ⟨.U ψ1 ψ2 :: φs', by simp; omega, r, by
          rw [drop_of_tc (t := Tok.tag 5) h5, hφ]; simp [CTLStar.toks]⟩

lemma polF_complete : ∀ m p, ts.length - p = m → ∀ φs : List CTLStar, φs ≠ [] → ∀ rest,
    ts.drop p = fToks φs ++ rest → polF ts p φs.length = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p hm φs hne rest h
    obtain ⟨φ, φs', rfl⟩ : ∃ φ φs', φs = φ :: φs' := by
      cases φs with
      | nil => exact absurd rfl hne
      | cons φ φs' => exact ⟨φ, φs', rfl⟩
    simp only [fToks_cons, List.append_assoc] at h
    rw [polF_eq]
    cases φ with
    | ap a =>
      have h' : ts.drop p = Tok.tag 0 :: (natToks a ++ (fToks φs' ++ rest)) := by
        simpa [CTLStar.toks] using h
      have hlt := lt_of_drop h'
      rw [if_neg (by omega), if_pos (by rw [tc_of_drop h']; rfl)]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      refine ⟨numOK_natToks a (drop_succ_of_drop h'), ?_⟩
      rcases eq_or_ne φs' [] with rfl | hne'
      · left; rfl
      · right
        have hne := numEnd_natToks a (drop_succ_of_drop h')
        have hl2 := congrArg List.length h'
        simp only [List.length_drop, List.length_cons, List.length_append] at hl2
        have := ih (ts.length - numEnd ts (p + 1)) (by
                         have : 0 < (natToks a).length := by simp [natToks]
                         omega) _ rfl φs' hne' rest
          (by rw [hne]; exact drop_append_of_drop (drop_succ_of_drop h'))
        simpa using this
    | tt =>
      have h' : ts.drop p = Tok.tag 1 :: (fToks φs' ++ rest) := by simpa [CTLStar.toks] using h
      have hlt := lt_of_drop h'
      rw [if_neg (by omega), if_neg (by rw [tc_of_drop h']; decide),
        if_pos (by rw [tc_of_drop h']; rfl)]
      simp only [Bool.or_eq_true, beq_iff_eq]
      rcases eq_or_ne φs' [] with rfl | hne'
      · left; rfl
      · right
        simpa using ih _ (by omega) _ rfl φs' hne' rest (drop_succ_of_drop h')
    | neg ψ =>
      have h' : ts.drop p = Tok.tag 2 :: (fToks (ψ :: φs') ++ rest) := by
        simpa [CTLStar.toks] using h
      have hlt := lt_of_drop h'
      rw [if_neg (by omega)]
      simp only [tc_of_drop h']
      have := ih _ (by omega) _ rfl (ψ :: φs') (by simp) rest (drop_succ_of_drop h')
      simpa [Tok.code] using this
    | X ψ =>
      have h' : ts.drop p = Tok.tag 4 :: (fToks (ψ :: φs') ++ rest) := by
        simpa [CTLStar.toks] using h
      have hlt := lt_of_drop h'
      rw [if_neg (by omega)]
      simp only [tc_of_drop h']
      have := ih _ (by omega) _ rfl (ψ :: φs') (by simp) rest (drop_succ_of_drop h')
      simpa [Tok.code] using this
    | E ψ =>
      have h' : ts.drop p = Tok.tag 6 :: (fToks (ψ :: φs') ++ rest) := by
        simpa [CTLStar.toks] using h
      have hlt := lt_of_drop h'
      rw [if_neg (by omega)]
      simp only [tc_of_drop h']
      have := ih _ (by omega) _ rfl (ψ :: φs') (by simp) rest (drop_succ_of_drop h')
      simpa [Tok.code] using this
    | and ψ1 ψ2 =>
      have h' : ts.drop p = Tok.tag 3 :: (fToks (ψ1 :: ψ2 :: φs') ++ rest) := by
        simpa [CTLStar.toks] using h
      have hlt := lt_of_drop h'
      rw [if_neg (by omega)]
      simp only [tc_of_drop h']
      have := ih _ (by omega) _ rfl (ψ1 :: ψ2 :: φs') (by simp) rest (drop_succ_of_drop h')
      simpa [Tok.code] using this
    | U ψ1 ψ2 =>
      have h' : ts.drop p = Tok.tag 5 :: (fToks (ψ1 :: ψ2 :: φs') ++ rest) := by
        simpa [CTLStar.toks] using h
      have hlt := lt_of_drop h'
      rw [if_neg (by omega)]
      simp only [tc_of_drop h']
      have := ih _ (by omega) _ rfl (ψ1 :: ψ2 :: φs') (by simp) rest (drop_succ_of_drop h')
      simpa [Tok.code] using this

lemma polF_one_iff (p : ℕ) :
    polF ts p 1 = true ↔ ∃ (φ : CTLStar) (rest : List Tok), ts.drop p = φ.toks ++ rest := by
  constructor
  · intro h
    obtain ⟨φs, hl, rest, hd⟩ := polF_sound _ p 1 rfl le_rfl h
    obtain ⟨φ, rfl⟩ := List.length_eq_one_iff.1 hl
    exact ⟨φ, rest, by simpa using hd⟩
  · rintro ⟨φ, rest, h⟩
    simpa using polF_complete _ p rfl [φ] (by simp) rest (by simpa using h)

end CTLP

end PathChecking
