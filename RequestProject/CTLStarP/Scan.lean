module

public import RequestProject.MCVP.Defs

/-!
# Scanning token lists

Pure functions on a token list `ts`, indexed by positions, that the polynomial-time
decision procedure for CTL* tree checking computes:

* `tc ts p`: the numeric code of the token at position `p` (`29` past the end);
* `scan up down p c`: a bracket-counting scan, starting at position `p` with counter `c`;
  it returns the position just after the token that brings the counter to `0`
  (`fend`: end of a formula in prefix notation, `tend`: end of a bracketed group,
  `numEnd`: end of a binary number).

We show that on encodings the scans find exactly the ends of the encoded objects.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open LS MCVPReduction

variable (ts : List Tok)

/-- Code of the token at position `p`, or `29` past the end. -/
def tc (p : ℕ) : ℕ := match ts[p]? with
  | some t => t.code
  | none => 29

lemma Tok.code_lt (t : Tok) : t.code < 29 := by
  cases t with
  | tag k => simp [Tok.code]; omega
  | _ => simp [Tok.code]

variable {ts}

lemma tc_of_drop {p : ℕ} {t : Tok} {rest : List Tok} (h : ts.drop p = t :: rest) :
    tc ts p = t.code := by
  have : ts[p]? = some t := by rw [← List.head?_drop, h]; rfl
  simp [tc, this]

lemma lt_of_drop {p : ℕ} {t : Tok} {rest : List Tok} (h : ts.drop p = t :: rest) :
    p < ts.length := by
  by_contra hc
  rw [List.drop_eq_nil_of_le (by omega)] at h
  simp at h

lemma drop_succ_of_drop {p : ℕ} {t : Tok} {rest : List Tok} (h : ts.drop p = t :: rest) :
    ts.drop (p + 1) = rest := by
  rw [← List.drop_drop, h]; rfl

lemma drop_append_of_drop {p : ℕ} {l rest : List Tok} (h : ts.drop p = l ++ rest) :
    ts.drop (p + l.length) = rest := by
  rw [← List.drop_drop, h]; simp

lemma lt_of_tc_ne {p : ℕ} (h : tc ts p ≠ 29) : p < ts.length := by
  by_contra hc
  simp [tc, List.getElem?_eq_none (show ts.length ≤ p by omega)] at h

lemma tc_lt_29 {p : ℕ} (h : p < ts.length) : tc ts p < 29 := by
  simp [tc, List.getElem?_eq_getElem h, Tok.code_lt]

variable (ts)

/-- One counting step. -/
def cstep (up down : ℕ → Bool) (k c : ℕ) : ℕ :=
  if up k then c + 1 else if down k then c - 1 else c

/-- Bracket-counting scan. -/
def scan (up down : ℕ → Bool) (p c : ℕ) : ℕ :=
  if ts.length ≤ p then p else
    if cstep up down (tc ts p) c = 0 then p + 1
    else scan up down (p + 1) (cstep up down (tc ts p) c)
termination_by ts.length - p

/-- Counting predicates for formulas: binary operators open, atoms close. -/
def upF (k : ℕ) : Bool := k == 8 || k == 10
def downF (k : ℕ) : Bool := k == 2 || k == 6
/-- Counting predicates for brackets. -/
def upT (k : ℕ) : Bool := k == 3
def downT (k : ℕ) : Bool := k == 4
/-- Counting predicates for numbers. -/
def upN (_ : ℕ) : Bool := false
def downN (k : ℕ) : Bool := k == 2

/-- End of the formula starting at `p`. -/
def fend (p : ℕ) : ℕ := scan ts upF downF p 1
/-- End of the bracketed group starting at `p`. -/
def tend (p : ℕ) : ℕ := scan ts upT downT p 0
/-- End of the binary number starting at `p`. -/
def numEnd (p : ℕ) : ℕ := scan ts upN downN p 1

variable {ts}

lemma scan_eq (up down : ℕ → Bool) (p c : ℕ) : scan ts up down p c =
    if ts.length ≤ p then p else
      if cstep up down (tc ts p) c = 0 then p + 1
      else scan ts up down (p + 1) (cstep up down (tc ts p) c) := by
  rw [scan]

lemma scan_bounds (up down : ℕ → Bool) : ∀ m p c, ts.length - p = m →
    p ≤ scan ts up down p c ∧ scan ts up down p c ≤ max p ts.length := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p c hm
    rw [scan_eq]
    split_ifs with h1 h2
    · omega
    · omega
    · have := ih (ts.length - (p + 1)) (by omega) (p + 1) (cstep up down (tc ts p) c) rfl
      omega

lemma le_scan (up down : ℕ → Bool) (p c : ℕ) : p ≤ scan ts up down p c :=
  (scan_bounds up down _ p c rfl).1

lemma scan_le (up down : ℕ → Bool) (p c : ℕ) : scan ts up down p c ≤ max p ts.length :=
  (scan_bounds up down _ p c rfl).2

lemma lt_scan (up down : ℕ → Bool) {p : ℕ} (c : ℕ) (hp : p < ts.length) :
    p < scan ts up down p c := by
  rw [scan_eq, if_neg (by omega)]
  split_ifs
  · omega
  · have := le_scan (ts := ts) up down (p + 1) (cstep up down (tc ts p) c)
    omega

/-- A neutral token. -/
lemma scan_neutral {up down : ℕ → Bool} {p c : ℕ} (hc : c ≠ 0) (hp : p < ts.length)
    (hu : up (tc ts p) = false) (hd : down (tc ts p) = false) :
    scan ts up down p c = scan ts up down (p + 1) c := by
  rw [scan_eq, if_neg (by omega)]; simp [cstep, hu, hd, hc]

/-- An opening token. -/
lemma scan_up {up down : ℕ → Bool} {p c : ℕ} (hp : p < ts.length) (hu : up (tc ts p) = true) :
    scan ts up down p c = scan ts up down (p + 1) (c + 1) := by
  rw [scan_eq, if_neg (by omega)]; simp [cstep, hu]

/-- A closing token. -/
lemma scan_down {up down : ℕ → Bool} {p k : ℕ} (hp : p < ts.length)
    (hu : up (tc ts p) = false) (hd : down (tc ts p) = true) :
    scan ts up down p (k + 1) = if k = 0 then p + 1 else scan ts up down (p + 1) k := by
  rw [scan_eq, if_neg (by omega)]; simp [cstep, hu, hd]

/-- A run of neutral tokens. -/
lemma scan_neutrals {up down : ℕ → Bool} (l : List Tok)
    (hl : ∀ t ∈ l, up t.code = false ∧ down t.code = false) :
    ∀ {p c : ℕ} {rest : List Tok}, c ≠ 0 → ts.drop p = l ++ rest →
      scan ts up down p c = scan ts up down (p + l.length) c := by
  induction l with
  | nil => intros; simp
  | cons t l ih =>
    intro p c rest hc h
    have h' : ts.drop p = t :: (l ++ rest) := by simpa using h
    have ht := tc_of_drop h'
    rw [scan_neutral hc (lt_of_drop h') (by rw [ht]; exact (hl t (by simp)).1)
      (by rw [ht]; exact (hl t (by simp)).2),
      ih (fun t ht => hl t (by simp [ht])) hc (drop_succ_of_drop h')]
    simp only [List.length_cons]; ring_nf

lemma digits_neutral_F (bs : List Bool) :
    ∀ t ∈ bs.map digitTok, upF t.code = false ∧ downF t.code = false := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨b, -, rfl⟩ := ht
  cases b <;> simp [digitTok, Tok.code, upF, downF]

lemma digits_neutral_T (bs : List Bool) :
    ∀ t ∈ bs.map digitTok, upT t.code = false ∧ downT t.code = false := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨b, -, rfl⟩ := ht
  cases b <;> simp [digitTok, Tok.code, upT, downT]

lemma digits_neutral_N (bs : List Bool) :
    ∀ t ∈ bs.map digitTok, upN t.code = false ∧ downN t.code = false := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨b, -, rfl⟩ := ht
  cases b <;> simp [digitTok, Tok.code, upN, downN]

/-- The scan for numbers. -/
lemma scan_natToks {up down : ℕ → Bool} (a : ℕ)
    (hd : ∀ t ∈ (Nat.bits a).map digitTok, up t.code = false ∧ down t.code = false)
    (hu : up 2 = false) (hs : down 2 = true) {p k : ℕ} {rest : List Tok}
    (h : ts.drop p = natToks a ++ rest) :
    scan ts up down p (k + 1) =
      if k = 0 then p + (natToks a).length else scan ts up down (p + (natToks a).length) k := by
  rw [natToks_eq] at h ⊢
  simp only [List.append_assoc] at h
  rw [scan_neutrals _ hd (by omega) h]
  have h2 := drop_append_of_drop h
  have hs' : ts.drop (p + ((Nat.bits a).map digitTok).length) = Tok.sep :: rest := by
    simpa using h2
  rw [scan_down (lt_of_drop hs') (by rw [tc_of_drop hs']; exact hu)
    (by rw [tc_of_drop hs']; exact hs)]
  simp [add_assoc]

lemma numEnd_natToks (a : ℕ) {p : ℕ} {rest : List Tok} (h : ts.drop p = natToks a ++ rest) :
    numEnd ts p = p + (natToks a).length := by
  have := scan_natToks (up := upN) (down := downN) (k := 0) a (digits_neutral_N _) rfl rfl h
  simpa [numEnd] using this

/-- **The formula scan finds the end of a formula.** -/
lemma scan_formula (φ : CTLStar) :
    ∀ {p k : ℕ} {rest : List Tok}, ts.drop p = φ.toks ++ rest →
      scan ts upF downF p (k + 1) =
        if k = 0 then p + φ.toks.length else scan ts upF downF (p + φ.toks.length) k := by
  induction φ with
  | ap a =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 0 :: (natToks a ++ rest) := by simpa [CTLStar.toks] using h
    rw [scan_neutral (by omega) (lt_of_drop h') (by rw [tc_of_drop h']; rfl)
      (by rw [tc_of_drop h']; rfl),
      scan_natToks a (digits_neutral_F _) rfl rfl (drop_succ_of_drop h')]
    simp only [CTLStar.toks, List.length_cons]; ring_nf
  | tt =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 1 :: rest := by simpa [CTLStar.toks] using h
    rw [scan_down (lt_of_drop h') (by rw [tc_of_drop h']; rfl) (by rw [tc_of_drop h']; rfl)]
    simp [CTLStar.toks]
  | neg φ ih =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 2 :: (φ.toks ++ rest) := by simpa [CTLStar.toks] using h
    rw [scan_neutral (by omega) (lt_of_drop h') (by rw [tc_of_drop h']; rfl)
      (by rw [tc_of_drop h']; rfl), ih (drop_succ_of_drop h')]
    simp only [CTLStar.toks, List.length_cons]; ring_nf
  | X φ ih =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 4 :: (φ.toks ++ rest) := by simpa [CTLStar.toks] using h
    rw [scan_neutral (by omega) (lt_of_drop h') (by rw [tc_of_drop h']; rfl)
      (by rw [tc_of_drop h']; rfl), ih (drop_succ_of_drop h')]
    simp only [CTLStar.toks, List.length_cons]; ring_nf
  | E φ ih =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 6 :: (φ.toks ++ rest) := by simpa [CTLStar.toks] using h
    rw [scan_neutral (by omega) (lt_of_drop h') (by rw [tc_of_drop h']; rfl)
      (by rw [tc_of_drop h']; rfl), ih (drop_succ_of_drop h')]
    simp only [CTLStar.toks, List.length_cons]; ring_nf
  | and φ ψ ih1 ih2 =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 3 :: (φ.toks ++ (ψ.toks ++ rest)) := by
      simpa [CTLStar.toks] using h
    have h2 := drop_append_of_drop (drop_succ_of_drop h')
    rw [scan_up (lt_of_drop h') (by rw [tc_of_drop h']; rfl), ih1 (drop_succ_of_drop h'),
      if_neg (by omega), ih2 h2]
    simp only [CTLStar.toks, List.length_cons, List.length_append]; ring_nf
  | U φ ψ ih1 ih2 =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 5 :: (φ.toks ++ (ψ.toks ++ rest)) := by
      simpa [CTLStar.toks] using h
    have h2 := drop_append_of_drop (drop_succ_of_drop h')
    rw [scan_up (lt_of_drop h') (by rw [tc_of_drop h']; rfl), ih1 (drop_succ_of_drop h'),
      if_neg (by omega), ih2 h2]
    simp only [CTLStar.toks, List.length_cons, List.length_append]; ring_nf

lemma fend_formula (φ : CTLStar) {p : ℕ} {rest : List Tok} (h : ts.drop p = φ.toks ++ rest) :
    fend ts p = p + φ.toks.length := by
  have := scan_formula (k := 0) φ h
  simpa [fend] using this

/-- The bracket scan over a label. -/
lemma scan_finset (s : Finset ℕ) {p k : ℕ} {rest : List Tok}
    (h : ts.drop p = finsetToks s ++ rest) :
    scan ts upT downT p k =
      if k = 0 then p + (finsetToks s).length
      else scan ts upT downT (p + (finsetToks s).length) k := by
  have h' : ts.drop p = Tok.lpar :: ((s.sort (· ≤ ·)).flatMap natToks ++ (Tok.rpar :: rest)) := by
    simpa [finsetToks] using h
  rw [scan_up (lt_of_drop h') (by rw [tc_of_drop h']; rfl)]
  have hn : ∀ t ∈ (s.sort (· ≤ ·)).flatMap natToks, upT t.code = false ∧ downT t.code = false := by
    intro t ht
    simp only [List.mem_flatMap] at ht
    obtain ⟨a, -, ha⟩ := ht
    rw [natToks_eq, List.mem_append] at ha
    rcases ha with ha | ha
    · exact digits_neutral_T _ t ha
    · simp at ha; subst ha; simp [Tok.code, upT, downT]
  rw [scan_neutrals _ hn (by omega) (drop_succ_of_drop h')]
  have h3 := drop_append_of_drop (drop_succ_of_drop h')
  rw [scan_down (lt_of_drop h3) (by rw [tc_of_drop h3]; rfl) (by rw [tc_of_drop h3]; rfl)]
  simp only [finsetToks, List.length_cons, List.length_append, List.length_nil]; ring_nf

/-- **The bracket scan finds the end of a tree.** -/
lemma scan_tree_aux (N : ℕ) :
    (∀ t : LTree, t.toks.length ≤ N → ∀ {p k : ℕ} {rest : List Tok}, ts.drop p = t.toks ++ rest →
      scan ts upT downT p k =
        if k = 0 then p + t.toks.length else scan ts upT downT (p + t.toks.length) k) ∧
    (∀ cs : List LTree, (LTree.toksList cs).length < N → ∀ {p k : ℕ} {rest : List Tok},
      k ≠ 0 → ts.drop p = LTree.toksList cs ++ rest →
      scan ts upT downT p k = scan ts upT downT (p + (LTree.toksList cs).length) k) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    have hlist : ∀ cs : List LTree, (LTree.toksList cs).length < N →
        ∀ {p k : ℕ} {rest : List Tok}, k ≠ 0 → ts.drop p = LTree.toksList cs ++ rest →
        scan ts upT downT p k = scan ts upT downT (p + (LTree.toksList cs).length) k := by
      intro cs
      induction cs with
      | nil => intros; simp [LTree.toksList]
      | cons c cs ihc =>
        intro hl p k rest hk h
        rw [LTree.toksList_cons] at hl h ⊢
        rw [List.length_append] at hl
        have hc := LTree.toks_length_pos c
        simp only [List.append_assoc] at h
        rw [(ih _ (show c.toks.length < N by omega)).1 c le_rfl h, if_neg hk,
          ihc (by omega) hk (drop_append_of_drop h)]
        simp only [List.length_append]; ring_nf
    refine ⟨?_, hlist⟩
    intro t ht p k rest h
    obtain ⟨l, cs⟩ := t
    have hlt := LTree.toks_length_lt l cs
    have h' : ts.drop p = Tok.lpar :: (finsetToks l ++ (LTree.toksList cs ++
        (Tok.rpar :: rest))) := by simpa [LTree.toks] using h
    rw [scan_up (lt_of_drop h') (by rw [tc_of_drop h']; rfl),
      scan_finset l (drop_succ_of_drop h'), if_neg (by omega),
      hlist cs (by omega) (by omega) (drop_append_of_drop (drop_succ_of_drop h'))]
    have h4 := drop_append_of_drop (drop_append_of_drop (drop_succ_of_drop h'))
    rw [scan_down (lt_of_drop h4) (by rw [tc_of_drop h4]; rfl) (by rw [tc_of_drop h4]; rfl)]
    simp only [LTree.toks, List.length_cons, List.length_append, List.length_nil]; ring_nf

lemma tend_tree (t : LTree) {p : ℕ} {rest : List Tok} (h : ts.drop p = t.toks ++ rest) :
    tend ts p = p + t.toks.length := by
  have := (scan_tree_aux t.toks.length).1 t le_rfl (k := 0) h
  simpa [tend] using this

lemma tend_finset (s : Finset ℕ) {p : ℕ} {rest : List Tok} (h : ts.drop p = finsetToks s ++ rest) :
    tend ts p = p + (finsetToks s).length := by
  have := scan_finset (k := 0) s h
  simpa [tend] using this

end CTLP

end PathChecking
