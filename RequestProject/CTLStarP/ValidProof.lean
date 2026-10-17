module

public import RequestProject.CTLStarP.Valid

/-!
# Correctness of the recognition of instances

`validTop_iff`: `validTop ts = true` iff `ts` is the token encoding `( φ ) t` of a pair of a
CTL* formula and a tree.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open LS MCVPReduction

variable {ts : List Tok}

lemma Tok.code_inj {t u : Tok} (h : t.code = u.code) : t = u := by
  cases t <;> cases u <;> simp_all [Tok.code] <;> omega

lemma drop_of_tc {p : ℕ} {t : Tok} (h : tc ts p = t.code) : ts.drop p = t :: ts.drop (p + 1) := by
  have hp : p < ts.length := lt_of_tc_ne (by rw [h]; have := Tok.code_lt t; omega)
  have h' : ts[p].code = t.code := by simpa [tc, List.getElem?_eq_getElem hp] using h
  rw [List.drop_eq_getElem_cons hp, Tok.code_inj h']

lemma tc_eq_of_drop {p : ℕ} {t : Tok} {l : List Tok} (h : ts.drop p = t :: l) : tc ts p = t.code :=
  tc_of_drop h

/-! ## Numbers -/

lemma digitsOK_eq (p : ℕ) (ok : Bool) : digitsOK ts p ok =
    if ts.length ≤ p then false
    else if tc ts p = 2 then ok
    else if tc ts p = 0 then digitsOK ts (p + 1) false
    else if tc ts p = 1 then digitsOK ts (p + 1) true
    else false := by
  rw [digitsOK]

lemma digitTok_code (b : Bool) : (digitTok b).code = if b then 1 else 0 := by
  cases b <;> rfl

lemma digitsOK_digits (bs : List Bool) :
    ∀ {p : ℕ} {ok : Bool} {rest : List Tok}, ts.drop p = bs.map digitTok ++ Tok.sep :: rest →
      digitsOK ts p ok = bs.getLast?.getD ok := by
  induction bs with
  | nil =>
    intro p ok rest h
    have h' : ts.drop p = Tok.sep :: rest := by simpa using h
    rw [digitsOK_eq, if_neg (by have := lt_of_drop h'; omega), if_pos (by rw [tc_of_drop h']; rfl)]
    rfl
  | cons b bs ih =>
    intro p ok rest h
    have h' : ts.drop p = digitTok b :: (bs.map digitTok ++ Tok.sep :: rest) := by simpa using h
    rw [digitsOK_eq, if_neg (by have := lt_of_drop h'; omega), tc_of_drop h', digitTok_code]
    rw [List.getLast?_cons]
    cases b <;> simp [ih (drop_succ_of_drop h')]

lemma numOK_natToks (a : ℕ) {p : ℕ} {rest : List Tok} (h : ts.drop p = natToks a ++ rest) :
    numOK ts p = true := by
  rw [natToks_eq] at h
  simp only [List.append_assoc, List.singleton_append] at h
  rw [numOK, digitsOK_digits _ h]
  rcases canon_bits a with h0 | h0
  · simp [h0]
  · simp [h0]

lemma digitsOK_sound : ∀ m p ok, ts.length - p = m → digitsOK ts p ok = true →
    ∃ (bs : List Bool) (rest : List Tok), ts.drop p = bs.map digitTok ++ Tok.sep :: rest ∧
      bs.getLast?.getD ok = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p ok hm h
    rw [digitsOK_eq] at h
    split_ifs at h with h1 h2 h3 h4
    · exact ⟨[], ts.drop (p + 1), by simpa using drop_of_tc (t := Tok.sep) h2, by simpa using h⟩
    · obtain ⟨bs, rest, e, e'⟩ := ih _ (by omega) (p + 1) false rfl h
      refine ⟨false :: bs, rest, ?_, ?_⟩
      · rw [drop_of_tc (t := Tok.zero) h3, e]; rfl
      · rw [List.getLast?_cons]; simpa using e'
    · obtain ⟨bs, rest, e, e'⟩ := ih _ (by omega) (p + 1) true rfl h
      refine ⟨true :: bs, rest, ?_, ?_⟩
      · rw [drop_of_tc (t := Tok.one) h4, e]; rfl
      · rw [List.getLast?_cons]; simpa using e'

lemma numOK_sound {p : ℕ} (h : numOK ts p = true) : ∃ a rest, ts.drop p = natToks a ++ rest := by
  obtain ⟨bs, rest, e, e'⟩ := digitsOK_sound _ p true rfl h
  have hc : Canon bs := by
    cases hb : bs.getLast? with
    | none => left; simpa using hb
    | some x => right; rw [hb] at e'; simp at e'; rw [hb, e']
  refine ⟨ofBits bs, rest, ?_⟩
  rw [natToks_eq, bits_ofBits hc, e]; simp

/-! ## Comparing numbers -/

lemma dig_of_drop_digit {p : ℕ} {b : Bool} {l : List Tok} (h : ts.drop p = digitTok b :: l) :
    dig ts p = some b := by
  cases b <;> simp [dig, tc_of_drop h, digitTok, Tok.code]

lemma dig_of_drop_sep {p : ℕ} {l : List Tok} (h : ts.drop p = Tok.sep :: l) : dig ts p = none := by
  simp [dig, tc_of_drop h, Tok.code]

lemma cmpScan_nn {p q : ℕ} {acc : Bool} (h1 : dig ts p = none) (h2 : dig ts q = none) :
    cmpScan ts p q acc = acc := by
  rw [cmpScan]; split <;> simp_all

lemma cmpScan_sn {p q : ℕ} {acc x : Bool} (h1 : dig ts p = some x) (h2 : dig ts q = none) :
    cmpScan ts p q acc = cmpScan ts (p + 1) q (if x then false else acc) := by
  rw [cmpScan]; split <;> simp_all

lemma cmpScan_ns {p q : ℕ} {acc y : Bool} (h1 : dig ts p = none) (h2 : dig ts q = some y) :
    cmpScan ts p q acc = cmpScan ts p (q + 1) (if y then true else acc) := by
  rw [cmpScan]; split <;> simp_all

lemma cmpScan_ss {p q : ℕ} {acc x y : Bool} (h1 : dig ts p = some x) (h2 : dig ts q = some y) :
    cmpScan ts p q acc = cmpScan ts (p + 1) (q + 1) (if x = y then acc else y) := by
  rw [cmpScan]; split <;> simp_all

lemma ofBits_cons (b : Bool) (bs : List Bool) : ofBits (b :: bs) = b.toNat + 2 * ofBits bs := rfl

/-- **Comparison of binary numbers.** -/
lemma cmpScan_correct (bs : List Bool) :
    ∀ (cs : List Bool) {p q : ℕ} {acc : Bool} {r1 r2 : List Tok},
      ts.drop p = bs.map digitTok ++ Tok.sep :: r1 → ts.drop q = cs.map digitTok ++ Tok.sep :: r2 →
      cmpScan ts p q acc =
        (decide (ofBits bs < ofBits cs) || (decide (ofBits bs = ofBits cs) && acc)) := by
  induction bs with
  | nil =>
    intro cs
    induction cs with
    | nil =>
      intro p q acc r1 r2 h1 h2
      rw [cmpScan_nn (dig_of_drop_sep (by simpa using h1)) (dig_of_drop_sep (by simpa using h2))]
      simp [ofBits]
    | cons c cs ih =>
      intro p q acc r1 r2 h1 h2
      have h2' : ts.drop q = digitTok c :: (cs.map digitTok ++ Tok.sep :: r2) := by simpa using h2
      rw [cmpScan_ns (dig_of_drop_sep (by simpa using h1)) (dig_of_drop_digit h2'),
        ih h1 (drop_succ_of_drop h2')]
      simp only [ofBits]
      rcases Nat.eq_zero_or_pos (ofBits cs) with h0 | h0 <;> cases c <;> simp [h0]
  | cons b bs ih =>
    intro cs
    induction cs with
    | nil =>
      intro p q acc r1 r2 h1 h2
      have h1' : ts.drop p = digitTok b :: (bs.map digitTok ++ Tok.sep :: r1) := by simpa using h1
      rw [cmpScan_sn (dig_of_drop_digit h1') (dig_of_drop_sep (by simpa using h2)),
        ih [] (drop_succ_of_drop h1') h2]
      simp only [ofBits]
      rcases Nat.eq_zero_or_pos (ofBits bs) with h0 | h0 <;> cases b <;> simp [h0]
    | cons c cs _ =>
      intro p q acc r1 r2 h1 h2
      have h1' : ts.drop p = digitTok b :: (bs.map digitTok ++ Tok.sep :: r1) := by simpa using h1
      have h2' : ts.drop q = digitTok c :: (cs.map digitTok ++ Tok.sep :: r2) := by simpa using h2
      rw [cmpScan_ss (dig_of_drop_digit h1') (dig_of_drop_digit h2'),
        ih cs (drop_succ_of_drop h1') (drop_succ_of_drop h2')]
      simp only [ofBits_cons]
      rcases lt_trichotomy (ofBits bs) (ofBits cs) with hlt | heq | hgt
      · have : b.toNat + 2 * ofBits bs < c.toNat + 2 * ofBits cs := by
          cases b <;> cases c <;> simp <;> omega
        simp [hlt, this]
      · cases b <;> cases c <;> simp [heq]
      · have h1 : ¬ ofBits bs < ofBits cs := by omega
        have h2 : ¬ b.toNat + 2 * ofBits bs < c.toNat + 2 * ofBits cs := by
          cases b <;> cases c <;> simp <;> omega
        have h3 : ofBits bs ≠ ofBits cs := by omega
        have h4 : b.toNat + 2 * ofBits bs ≠ c.toNat + 2 * ofBits cs := by
          cases b <;> cases c <;> simp <;> omega
        simp [h1, h2, h3, h4]

lemma natToks_drop {a p : ℕ} {rest : List Tok} (h : ts.drop p = natToks a ++ rest) :
    ts.drop p = (Nat.bits a).map digitTok ++ Tok.sep :: rest := by
  rw [h, natToks_eq]; simp

lemma numLt_natToks {a b p q : ℕ} {r1 r2 : List Tok} (h1 : ts.drop p = natToks a ++ r1)
    (h2 : ts.drop q = natToks b ++ r2) : numLt ts p q = decide (a < b) := by
  rw [numLt, cmpScan_correct _ _ (natToks_drop h1) (natToks_drop h2), ofBits_bits, ofBits_bits]
  simp

lemma numEq_natToks {a b p q : ℕ} {r1 r2 : List Tok} (h1 : ts.drop p = natToks a ++ r1)
    (h2 : ts.drop q = natToks b ++ r2) : numEq ts p q = decide (a = b) := by
  rw [numEq, numLe, numLe, cmpScan_correct _ _ (natToks_drop h1) (natToks_drop h2),
    cmpScan_correct _ _ (natToks_drop h2) (natToks_drop h1), ofBits_bits, ofBits_bits]
  by_cases h : a = b
  · simp [h]
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · simp [h, h', show ¬ b < a by omega, Ne.symm h]
    · simp [h, h', show ¬ a < b by omega]

/-! ## Labels -/

lemma labSuf_eq (q : ℕ) : labSuf ts q =
    if ts.length ≤ q then false
    else if tc ts q = 4 then true
    else numOK ts q && (tc ts (numEnd ts q) == 4 || numLt ts q (numEnd ts q)) &&
      labSuf ts (numEnd ts q) := by
  rw [labSuf]

lemma natToks_head_code (a : ℕ) : ∃ t l, natToks a = t :: l ∧ t.code ≤ 2 := by
  obtain ⟨l, hl | hl | hl⟩ := natToks_head a
  · exact ⟨_, _, hl, by simp [Tok.code]⟩
  · exact ⟨_, _, hl, by simp [Tok.code]⟩
  · exact ⟨_, _, hl, by simp [Tok.code]⟩

lemma labSuf_sound : ∀ m q, ts.length - q = m → labSuf ts q = true →
    ∃ (xs : List ℕ) (rest : List Tok), xs.Pairwise (· < ·) ∧
      ts.drop q = xs.flatMap natToks ++ Tok.rpar :: rest := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro q hm h
    rw [labSuf_eq] at h
    split_ifs at h with h1 h2
    · exact ⟨[], ts.drop (q + 1), by simp, by simpa using drop_of_tc (t := Tok.rpar) h2⟩
    · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hnum, hcmp⟩, hrec⟩ := h
      obtain ⟨a, rest₀, ha⟩ := numOK_sound hnum
      have he := numEnd_natToks a ha
      have hgt : q < numEnd ts q := by rw [he]; simp [natToks]
      obtain ⟨xs, rest, hxs, hd⟩ := ih _ (by omega) _ rfl hrec
      refine ⟨a :: xs, rest, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, hxs⟩
        cases xs with
        | nil => simp
        | cons x xs =>
          have hx : ts.drop (numEnd ts q) = natToks x ++ (xs.flatMap natToks ++ Tok.rpar :: rest) := by
            simpa using hd
          have hax : a < x := by
            rcases hcmp with hc | hc
            · obtain ⟨t, l, htl, htc⟩ := natToks_head_code x
              rw [htl] at hx
              have := tc_of_drop (by simpa using hx)
              omega
            · rw [numLt_natToks ha hx] at hc; simpa using hc
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact hax
          · exact lt_trans hax (List.rel_of_pairwise_cons hxs hy)
      · rw [List.flatMap_cons, List.append_assoc, ← hd, he, drop_append_of_drop ha]
        exact ha

end CTLP

end PathChecking
