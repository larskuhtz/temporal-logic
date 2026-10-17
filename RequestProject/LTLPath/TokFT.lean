module

public import RequestProject.LTLPath.Path
public import RequestProject.LTLPath.Sem

/-!
# The formula tree with path data of an encoded instance

For a token list `ts = ( φ ) p` (an LTL formula `φ` and a lasso path `p`) we define, by
token-level functions only (bracket scans, counting and bounded search):

* the positions of the path, the stem length `sLen` and the loop length `lLen`;
* the start `lpos i` of the `i`-th letter of the path, and membership of the number at position
  `v` in the letter starting at position `j` (`memAt`);
* the truth value `lvTok q i` of the leaf at position `q` at path position `i` and the polarity
  `polTok q` (the parity of the number of negations above `q`).

`tokFT` is the resulting formula tree, and `tokFT_sem` shows that the semantics of the
subformulas is a semantics of it (`FT.Sem`), with root value the truth value of `φ` on `p`.
-/

@[expose] public section

namespace PathChecking

open CTLP

namespace LTok

variable (ts : List Tok)

/-! ## Token-level definitions -/

/-- Position of the opening bracket of the path. -/
def tP : ℕ := tF ts + 1

/-- End of the bracketed group opened at position `j` (the scan starts after the bracket). -/
def tend1 (j : ℕ) : ℕ := scan ts upT downT (j + 1) 1

/-- Position of the closing bracket of the stem. -/
def sE : ℕ := tend1 ts (tP ts) - 1

/-- Number of letters of the stem. -/
def sLen : ℕ := cnt ts 3 (tP ts + 1) (sE ts)

/-- Position of the first letter of the loop. -/
def lB : ℕ := sE ts + 2

/-- Number of letters of the loop. -/
def lLen : ℕ := cnt ts 3 (lB ts) (ts.length - 1)

/-- Position of the `m`-th opening bracket in `[b, e)`, counted from `b`. -/
def setAt (b e m : ℕ) : ℕ := ffind (fun j => tc ts j == 3 && cnt ts 3 b j == m) b e

/-- Start of the `i`-th letter of the path. -/
def lpos (i : ℕ) : ℕ :=
  if i < sLen ts then setAt ts (tP ts + 1) (sE ts) i
  else setAt ts (lB ts) (ts.length - 1) ((i - sLen ts) % lLen ts)

/-- Length of the number starting at `v` (including the terminating `sep`). -/
def numLen (v : ℕ) : ℕ := numEnd ts v - v

/-- The number at `u` has the same tokens as the number at `v`. -/
def numEqAt (u v : ℕ) : Bool := decide (∀ m < numLen ts v, tc ts (u + m) = tc ts (v + m))

/-- The letter starting at `j` contains the number starting at `v`. -/
def memAt (j v : ℕ) : Bool :=
  decide (∃ u < tend1 ts j, j < u ∧ u + 1 < tend1 ts j ∧ (tc ts (u - 1) = 3 ∨ tc ts (u - 1) = 2) ∧
    numEqAt ts u v = true)

/-- Truth value of the leaf at position `q` at path position `i`. -/
def lvTok (q i : ℕ) : Bool := if tkd ts q = 1 then true else memAt ts (lpos ts i) (q + 1)

/-- Number of negations strictly above position `q`. -/
def negAbove (q : ℕ) : ℕ :=
  ((List.range q).filter fun r => tnd ts r && tkd ts r == 2 && decide (q < fend ts r)).length

/-- Polarity of position `q`. -/
def polTok (q : ℕ) : Bool := negAbove ts q % 2 == 1

/-! ## Instances -/

/-- `ts` encodes the instance `(φ, p)`. -/
def Enc (ts : List Tok) (φ : LTL) (p : LassoPath) : Prop :=
  ts = Tok.lpar :: (φ.toks ++ (Tok.rpar :: p.toks))

variable {ts} {φ : LTL} {p : LassoPath}

lemma enc_at (h : Enc ts φ p) : At ts 1 φ := ⟨Tok.rpar :: p.toks, by rw [h]; simp⟩

lemma enc_tF (h : Enc ts φ p) : tF ts = 1 + φ.toks.length := tF_eq (enc_at h)

lemma enc_drop_tP (h : Enc ts φ p) : ts.drop (tP ts) = p.toks := by
  rw [tP, enc_tF h, h]
  simp [show 1 + φ.toks.length + 1 = (φ.toks.length + 1) + 1 by omega]

lemma enc_tc_tF (h : Enc ts φ p) : tc ts (tF ts) = 4 := by
  have : ts.drop (tF ts) = Tok.rpar :: p.toks := by
    rw [enc_tF h, h]; simp [show 1 + φ.toks.length = φ.toks.length + 1 by omega, List.drop_append]
  rw [tc_of_drop this]; rfl

/-- Tokens of a list of letters. -/
def lettersToks (l : List (Finset ℕ)) : List Tok := l.flatMap finsetToks

lemma lassoPath_toks (p : LassoPath) : p.toks = Tok.lpar :: (lettersToks p.stem ++
    (Tok.rpar :: Tok.lpar :: (lettersToks p.loop ++ [Tok.rpar]))) := rfl

lemma lettersToks_cons (S : Finset ℕ) (l : List (Finset ℕ)) :
    lettersToks (S :: l) = finsetToks S ++ lettersToks l := rfl

lemma scan_letters (l : List (Finset ℕ)) : ∀ {q k : ℕ} {rest : List Tok}, k ≠ 0 →
    ts.drop q = lettersToks l ++ rest →
    scan ts upT downT q k = scan ts upT downT (q + (lettersToks l).length) k := by
  induction l with
  | nil => intros; simp [lettersToks]
  | cons S l ih =>
    intro q k rest hk h
    rw [lettersToks_cons, List.append_assoc] at h
    rw [scan_finset S h, if_neg hk, ih hk (drop_append_of_drop h), lettersToks_cons,
      List.length_append, Nat.add_assoc]

lemma enc_drop_tP' (h : Enc ts φ p) : ts.drop (tP ts) = Tok.lpar :: (lettersToks p.stem ++
    (Tok.rpar :: Tok.lpar :: (lettersToks p.loop ++ [Tok.rpar]))) := by
  rw [enc_drop_tP h]; rfl

lemma enc_drop_stem (h : Enc ts φ p) :
    ts.drop (tP ts + 1) = lettersToks p.stem ++
      (Tok.rpar :: Tok.lpar :: (lettersToks p.loop ++ [Tok.rpar])) :=
  drop_succ_of_drop (enc_drop_tP' h)

lemma enc_sE (h : Enc ts φ p) : sE ts = tP ts + 1 + (lettersToks p.stem).length := by
  have h1 := enc_drop_tP' h
  have h2 := enc_drop_stem h
  have h3 := drop_append_of_drop h2
  unfold sE tend1
  have h4 := scan_down (ts := ts) (up := upT) (down := downT) (k := 0) (lt_of_drop h3)
    (by rw [tc_of_drop h3]; rfl) (by rw [tc_of_drop h3]; rfl)
  simp only [zero_add, if_pos] at h4
  rw [scan_letters p.stem one_ne_zero h2, h4]
  omega

lemma enc_drop_loop (h : Enc ts φ p) :
    ts.drop (lB ts) = lettersToks p.loop ++ [Tok.rpar] := by
  have h3 := drop_append_of_drop (enc_drop_stem h)
  rw [lB, enc_sE h, show tP ts + 1 + (lettersToks p.stem).length + 2 =
    tP ts + 1 + (lettersToks p.stem).length + 1 + 1 by omega]
  exact drop_succ_of_drop (drop_succ_of_drop h3)

lemma enc_length (h : Enc ts φ p) : ts.length = lB ts + (lettersToks p.loop).length + 1 := by
  have h1 := enc_drop_loop h
  have := congrArg List.length h1
  simp only [List.length_drop, List.length_append, List.length_singleton] at this
  have hlt : lB ts < ts.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at h1
    simp at h1
  omega

lemma letters_count3 (l : List (Finset ℕ)) :
    (lettersToks l).countP (fun t => t.code = 3) = l.length := by
  induction l with
  | nil => rfl
  | cons S l ih =>
    rw [lettersToks_cons, List.countP_append, ih, finsetToks_eq]
    have hn := nums_code (S.sort (· ≤ ·))
    have c3 : (((S.sort (· ≤ ·)).flatMap natToks).countP (fun t => t.code = 3)) = 0 :=
      List.countP_eq_zero.2 fun t ht => by have := hn t ht; simp; omega
    rw [List.countP_cons, List.countP_append, c3]
    simp [Tok.code]; omega

lemma enc_sLen (h : Enc ts φ p) : sLen ts = p.stem.length := by
  unfold sLen
  rw [enc_sE h, cnt_seg (enc_drop_stem h) 3 (by simp), List.take_length, letters_count3]

lemma enc_lLen (h : Enc ts φ p) : lLen ts = p.loop.length := by
  unfold lLen
  rw [enc_length h, show lB ts + (lettersToks p.loop).length + 1 - 1 =
    lB ts + (lettersToks p.loop).length by omega, cnt_seg (enc_drop_loop h) 3 (by simp),
    List.take_length, letters_count3]

lemma lettersToks_take_succ (l : List (Finset ℕ)) {m : ℕ} (hm : m < l.length) :
    lettersToks (l.take (m + 1)) = lettersToks (l.take m) ++ finsetToks l[m] := by
  unfold lettersToks
  rw [List.take_add_one, List.getElem?_eq_getElem hm, Option.toList_some, List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

lemma lettersToks_split (l : List (Finset ℕ)) {m : ℕ} (hm : m < l.length) :
    lettersToks l = lettersToks (l.take m) ++ (finsetToks l[m] ++ lettersToks (l.drop (m + 1))) := by
  rw [← List.append_assoc, ← lettersToks_take_succ l hm]
  unfold lettersToks
  rw [← List.flatMap_append, List.take_append_drop]

/-- The `m`-th letter of a list of letters. -/
lemma setAt_eq (l : List (Finset ℕ)) {b e m : ℕ} {rest : List Tok}
    (hb : ts.drop b = lettersToks l ++ rest) (hm : m < l.length)
    (he : b + (lettersToks l).length ≤ e) :
    setAt ts b e m = b + (lettersToks (l.take m)).length ∧
      ts.drop (b + (lettersToks (l.take m)).length) =
        finsetToks l[m] ++ (lettersToks (l.drop (m + 1)) ++ rest) := by
  have hsplit := lettersToks_split l hm
  rw [hsplit] at hb
  simp only [List.append_assoc] at hb
  have hx := drop_append_of_drop hb
  refine ⟨?_, by simpa using hx⟩
  set x := b + (lettersToks (l.take m)).length
  have hlenx : x < e := by
    have := congrArg List.length hsplit
    simp only [List.length_append] at this
    have := finsetToks_len l[m]
    omega
  have htx : tc ts x = 3 := by
    rw [finsetToks_eq] at hx
    rw [tc_of_drop (by simpa using hx)]; rfl
  have hcx : cnt ts 3 b x = m := by
    rw [cnt_seg hb 3 (by simp), List.take_length, letters_count3, List.length_take,
      min_eq_left hm.le]
  unfold setAt
  refine ffind_eq (by omega) hlenx (by simp [htx, hcx]) (fun j hj1 hj2 => ?_)
  simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  by_cases htj : tc ts j = 3
  · right
    have h1 := cnt_add (ts := ts) 3 hj1 hj2.le
    have h2 := cnt_add (ts := ts) 3 (show j ≤ j + 1 by omega) hj2
    have h3 : cnt ts 3 j (j + 1) = 1 := by rw [cnt_succ 3 le_rfl, cnt_self, if_pos htj]
    omega
  · left; exact htj

lemma letter_eq (p : LassoPath) (i : ℕ) : p.letter i =
    if i < p.stem.length then p.stem.getD i ∅
    else p.loop.getD ((i - p.stem.length) % p.loop.length) ∅ := rfl

lemma enc_lpos (h : Enc ts φ p) (i : ℕ) :
    ∃ r, ts.drop (lpos ts i) = finsetToks (p.letter i) ++ r := by
  unfold lpos
  rw [enc_sLen h, letter_eq]
  by_cases hi : i < p.stem.length
  · rw [if_pos hi, if_pos hi]
    obtain ⟨e1, e2⟩ := setAt_eq p.stem (enc_drop_stem h) hi (le_of_eq (enc_sE h).symm)
    rw [e1, e2, List.getD_eq_getElem _ _ hi]
    exact ⟨_, rfl⟩
  · rw [if_neg hi, if_neg hi, enc_lLen h]
    have hl : 0 < p.loop.length := List.length_pos_iff.2 p.loop_ne
    have hm := Nat.mod_lt (i - p.stem.length) hl
    obtain ⟨e1, e2⟩ := setAt_eq (e := ts.length - 1) p.loop (enc_drop_loop h) hm
      (by rw [enc_length h]; omega)
    rw [e1, e2, List.getD_eq_getElem _ _ hm]
    exact ⟨_, rfl⟩

lemma natToks_digit' (x i : ℕ) (hi : i + 1 < (natToks x).length) : ((natToks x)[i]).code ≤ 1 := by
  simp only [natToks, List.length_append, List.length_map, List.length_singleton] at hi
  simp only [natToks]
  rw [List.getElem_append_left (by simpa using hi)]
  simp only [List.getElem_map]
  split <;> simp [Tok.code]

lemma natToks_last (x : ℕ) : ((natToks x)[(natToks x).length - 1]'(by simp [natToks])).code = 2 := by
  simp [natToks, Tok.code]

lemma drop_of_codes : ∀ (l : List Tok) {u : ℕ}, (∀ m (hm : m < l.length), tc ts (u + m) = (l[m]).code) →
    ∃ R, ts.drop u = l ++ R := by
  intro l
  induction l with
  | nil => intro u _; exact ⟨ts.drop u, rfl⟩
  | cons t l ih =>
    intro u h
    have h0 := h 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at h0
    obtain ⟨R, hR⟩ := ih (u := u + 1) (fun m hm => by
      have := h (m + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 m] using this)
    exact ⟨R, by rw [drop_of_tc h0, hR]; rfl⟩

lemma numEqAt_iff {u v a b : ℕ} {r r' : List Tok} (hu : ts.drop u = natToks b ++ r)
    (hv : ts.drop v = natToks a ++ r') : numEqAt ts u v = true ↔ b = a := by
  have hlen : numLen ts v = (natToks a).length := by
    unfold numLen; rw [numEnd_natToks a hv]; omega
  unfold numEqAt
  rw [hlen, decide_eq_true_iff]
  constructor
  · intro hm
    obtain ⟨R, hR⟩ := drop_of_codes (ts := ts) (natToks a) (u := u) (fun m hm' => by
      rw [hm m hm', tc_seg hv hm'])
    exact natToks_unique hu hR
  · rintro rfl m hm
    rw [tc_seg hu hm, tc_seg hv hm]

/-- Membership in a list of numbers. -/
lemma nums_mem {v a : ℕ} {r' : List Tok} (hv : ts.drop v = natToks a ++ r') :
    ∀ (xs : List ℕ) {u0 : ℕ} {R : List Tok}, ts.drop u0 = xs.flatMap natToks ++ R →
    ((∃ u, u0 ≤ u ∧ u < u0 + (xs.flatMap natToks).length ∧ (u = u0 ∨ tc ts (u - 1) = 2) ∧
      numEqAt ts u v = true) ↔ a ∈ xs) := by
  intro xs
  induction xs with
  | nil => intro u0 R _; simp; intro x h1 h2; omega
  | cons x xs ih =>
    intro u0 R h
    rw [List.flatMap_cons, List.append_assoc] at h
    have hl := natToks_length_pos x
    set u1 := u0 + (natToks x).length
    have h1 : ts.drop u1 = xs.flatMap natToks ++ R := drop_append_of_drop h
    rw [List.mem_cons, ← ih h1, List.flatMap_cons, List.length_append]
    constructor
    · rintro ⟨u, hu1, hu2, hu3, hu4⟩
      by_cases hux : u = u0
      · subst hux; left; exact ((numEqAt_iff h hv).1 hu4).symm
      · right
        have hu3' : tc ts (u - 1) = 2 := hu3.resolve_left hux
        refine ⟨u, ?_, by omega, ?_, hu4⟩
        · by_contra hlt
          have hm : u - 1 - u0 + 1 < (natToks x).length := by omega
          have := natToks_digit' x _ hm
          rw [← tc_seg h (show u - 1 - u0 < (natToks x).length by omega),
            show u0 + (u - 1 - u0) = u - 1 by omega, hu3'] at this
          omega
        · by_cases hu1' : u = u1
          · left; exact hu1'
          · right; exact hu3'
    · rintro (rfl | ⟨u, hu1, hu2, hu3, hu4⟩)
      · exact ⟨u0, le_rfl, by omega, Or.inl rfl, (numEqAt_iff h hv).2 rfl⟩
      · refine ⟨u, by omega, by omega, Or.inr ?_, hu4⟩
        rcases hu3 with rfl | hu3
        · rw [show u0 + (natToks x).length - 1 = u0 + ((natToks x).length - 1) by omega,
            tc_seg h (by omega), natToks_last]
        · exact hu3
where natToks_length_pos (x : ℕ) : 0 < (natToks x).length := by simp [natToks]

lemma memAt_iff {j v a : ℕ} {S : Finset ℕ} {r r' : List Tok}
    (hj : ts.drop j = finsetToks S ++ r) (hv : ts.drop v = natToks a ++ r') :
    memAt ts j v = true ↔ a ∈ S := by
  have hj' : ts.drop j = Tok.lpar :: ((S.sort (· ≤ ·)).flatMap natToks ++ (Tok.rpar :: r)) := by
    rw [hj, finsetToks_eq]; simp
  have hte : tend1 ts j = j + (finsetToks S).length := by
    rw [← tend_finset S hj, tend1, tend, scan_up (lt_of_drop hj') (by rw [tc_of_drop hj']; rfl)]
  have hu0 := drop_succ_of_drop hj'
  have key := nums_mem hv (S.sort (· ≤ ·)) hu0
  rw [Finset.mem_sort] at key
  rw [← key, memAt, decide_eq_true_iff, hte]
  have hlenS : (finsetToks S).length = ((S.sort (· ≤ ·)).flatMap natToks).length + 2 := by
    simp [finsetToks_eq]
  have htj : tc ts j = 3 := by rw [tc_of_drop hj']; rfl
  have hnum : ∀ u, j + 1 < u → u < j + 1 + ((S.sort (· ≤ ·)).flatMap natToks).length + 1 →
      tc ts (u - 1) ≤ 2 := by
    intro u h1 h2
    have := tc_seg hu0 (show u - 1 - (j + 1) < ((S.sort (· ≤ ·)).flatMap natToks).length by omega)
    rw [show j + 1 + (u - 1 - (j + 1)) = u - 1 by omega] at this
    rw [this]
    exact nums_code _ _ (List.getElem_mem _)
  constructor
  · rintro ⟨u, -, hu1, hu2, hu3, hu4⟩
    refine ⟨u, by omega, by rw [hlenS] at hu2; omega, ?_, hu4⟩
    rcases hu3 with hu3 | hu3
    · left
      by_contra hne
      have := hnum u (by omega) (by rw [hlenS] at hu2; omega)
      omega
    · right; exact hu3
  · rintro ⟨u, hu1, hu2, hu3, hu4⟩
    refine ⟨u, by rw [hlenS]; omega, by omega, by rw [hlenS]; omega, ?_, hu4⟩
    rcases hu3 with rfl | hu3
    · left; simpa using htj
    · right; exact hu3

lemma enc_lvTok (h : Enc ts φ p) {q : ℕ} {ψ : LTL} (hq : At ts q ψ) (hk : ψ.tag ≤ 1) (i : ℕ) :
    lvTok ts q i = true ↔ LTL.Sat p.letter ψ i := by
  have hkd := tkd_at hq
  cases ψ with
  | tt => simp [lvTok, hkd, LTL.tag, LTL.Sat]
  | ap a =>
    obtain ⟨r, hr⟩ := hq
    have hv : ts.drop (q + 1) = natToks a ++ r := by
      have := drop_succ_of_drop (show ts.drop q = Tok.tag 0 :: (natToks a ++ r) by
        rw [hr]; simp [LTL.toks])
      exact this
    obtain ⟨r', hr'⟩ := enc_lpos h i
    simp only [lvTok, hkd, LTL.tag, LTL.Sat]
    simp only [zero_ne_one, if_false]
    exact memAt_iff hr' hv
  | _ => simp [LTL.tag] at hk

end LTok

end PathChecking
