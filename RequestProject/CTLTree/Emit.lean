module

public import RequestProject.CTLTree.Pos

/-!
# Token-by-token production of the translated CTL formulas

`fendC` finds the end of a CTL formula (the binary operators `∧`, `EU`, `AU` open, atoms close).
The translation `trC m χ j` is produced by scanning the tokens of `χ`: every position `x`
emits `trBodyC` (depending only on the token at `x` and on `x`), preceded by `secC` if `x` starts
the second argument of an `EU` or `AU` at position `k` (that prefix depends on `k`).
`trCToks_eq`: the scan produces exactly the tokens of `trC m χ j`.
-/

@[expose] public section

namespace PathChecking

namespace CTLT

open CTLP MCVPReduction ShallowP LS

variable {ts : List Tok}

/-- Counting predicate for CTL formulas: binary operators open. -/
def upC (k : ℕ) : Bool := k == 8 || k == 10 || k == 11

/-- End of the CTL formula starting at `p`. -/
def fendC (ts : List Tok) (p : ℕ) : ℕ := scan ts upC downF p 1

lemma digits_neutral_C (bs : List Bool) :
    ∀ t ∈ bs.map digitTok, upC t.code = false ∧ downF t.code = false := by
  intro t ht
  simp only [List.mem_map] at ht
  obtain ⟨b, -, rfl⟩ := ht
  cases b <;> simp [digitTok, Tok.code, upC, downF]

/-- **The CTL formula scan finds the end of a formula.** -/
lemma scanC_formula (φ : CTL) :
    ∀ {p k : ℕ} {rest : List Tok}, ts.drop p = φ.toks ++ rest →
      scan ts upC downF p (k + 1) =
        if k = 0 then p + φ.toks.length else scan ts upC downF (p + φ.toks.length) k := by
  induction φ with
  | ap a =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 0 :: (natToks a ++ rest) := by simpa [CTL.toks] using h
    rw [scan_neutral (by omega) (lt_of_drop h') (by rw [tc_of_drop h']; rfl)
      (by rw [tc_of_drop h']; rfl),
      scan_natToks a (digits_neutral_C _) rfl rfl (drop_succ_of_drop h')]
    simp only [CTL.toks, List.length_cons]; ring_nf
  | tt =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 1 :: rest := by simpa [CTL.toks] using h
    rw [scan_down (lt_of_drop h') (by rw [tc_of_drop h']; rfl) (by rw [tc_of_drop h']; rfl)]
    simp [CTL.toks]
  | neg φ ih =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 2 :: (φ.toks ++ rest) := by simpa [CTL.toks] using h
    rw [scan_neutral (by omega) (lt_of_drop h') (by rw [tc_of_drop h']; rfl)
      (by rw [tc_of_drop h']; rfl), ih (drop_succ_of_drop h')]
    simp only [CTL.toks, List.length_cons]; ring_nf
  | EX φ ih =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 4 :: (φ.toks ++ rest) := by simpa [CTL.toks] using h
    rw [scan_neutral (by omega) (lt_of_drop h') (by rw [tc_of_drop h']; rfl)
      (by rw [tc_of_drop h']; rfl), ih (drop_succ_of_drop h')]
    simp only [CTL.toks, List.length_cons]; ring_nf
  | and φ ψ ih1 ih2 =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 3 :: (φ.toks ++ (ψ.toks ++ rest)) := by
      simpa [CTL.toks] using h
    have h2 := drop_append_of_drop (drop_succ_of_drop h')
    rw [scan_up (lt_of_drop h') (by rw [tc_of_drop h']; rfl), ih1 (drop_succ_of_drop h'),
      if_neg (by omega), ih2 h2]
    simp only [CTL.toks, List.length_cons, List.length_append]; ring_nf
  | EU φ ψ ih1 ih2 =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 5 :: (φ.toks ++ (ψ.toks ++ rest)) := by
      simpa [CTL.toks] using h
    have h2 := drop_append_of_drop (drop_succ_of_drop h')
    rw [scan_up (lt_of_drop h') (by rw [tc_of_drop h']; rfl), ih1 (drop_succ_of_drop h'),
      if_neg (by omega), ih2 h2]
    simp only [CTL.toks, List.length_cons, List.length_append]; ring_nf
  | AU φ ψ ih1 ih2 =>
    intro p k rest h
    have h' : ts.drop p = Tok.tag 6 :: (φ.toks ++ (ψ.toks ++ rest)) := by
      simpa [CTL.toks] using h
    have h2 := drop_append_of_drop (drop_succ_of_drop h')
    rw [scan_up (lt_of_drop h') (by rw [tc_of_drop h']; rfl), ih1 (drop_succ_of_drop h'),
      if_neg (by omega), ih2 h2]
    simp only [CTL.toks, List.length_cons, List.length_append]; ring_nf

lemma fendC_formula (φ : CTL) {p : ℕ} {rest : List Tok} (h : ts.drop p = φ.toks ++ rest) :
    fendC ts p = p + φ.toks.length := by
  have := scanC_formula (k := 0) φ h
  simpa [fendC] using this

lemma CTL.toks_length_pos (χ : CTL) : 0 < χ.toks.length := by
  cases χ <;> simp [CTL.toks]

/-! ## Emission -/

/-- Tokens of the LTL atom `n`. -/
def apT (n : ℕ) : List Tok := Tok.tag 0 :: natToks n

lemma apT_eq (n : ℕ) : (LTL.ap n).toks = apT n := rfl

/-- Prefix emitted at an `EX` at position `x`. -/
def preEX (x : ℕ) : List Tok :=
  [Tok.tag 4, Tok.tag 2, Tok.tag 3, Tok.tag 2] ++ apT (x + 2) ++
    [Tok.tag 2, Tok.tag 4, Tok.tag 3, Tok.tag 2] ++ apT 0

/-- Prefix of the second argument of an `EU` at position `k`. -/
def secEU (k : ℕ) : List Tok :=
  [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3] ++ apT 0 ++ apT (k + 2) ++
    [Tok.tag 2, Tok.tag 3, Tok.tag 2] ++ apT 0

/-- Prefix of the second argument of an `AU` at position `k`. -/
def secAU (k : ℕ) : List Tok :=
  [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3] ++ apT 0 ++ (Tok.tag 3 :: (apT (k + 2) ++ apT 1)) ++
    [Tok.tag 2, Tok.tag 3, Tok.tag 2] ++ apT 0

/-- Prefix emitted at an `EU` at position `x`. -/
def preEU : List Tok := [Tok.tag 5, Tok.tag 2, Tok.tag 3, Tok.tag 2] ++ apT 0 ++ [Tok.tag 2]

/-- Prefix emitted at an `AU` at position `x`. -/
def preAU (x : ℕ) : List Tok := Tok.tag 5 :: secEU x

/-- Emission at position `x`, without the prefix of a second argument. -/
def trBodyC (ts : List Tok) (m x : ℕ) : List Tok :=
  if tc ts x = 5 then Tok.tag 0 :: List.replicate m Tok.one
  else if tc ts x = 6 then [Tok.tag 1]
  else if tc ts x = 7 then [Tok.tag 2]
  else if tc ts x = 8 then [Tok.tag 3]
  else if tc ts x = 9 then preEX x
  else if tc ts x = 10 then preEU
  else if tc ts x = 11 then preAU x
  else cp ts x

/-- Contribution of position `k` to the prefix of position `x`. -/
def secAt (ts : List Tok) (x k : ℕ) : List Tok :=
  if tc ts k = 10 ∧ fendC ts (k + 1) = x then secEU k
  else if tc ts k = 11 ∧ fendC ts (k + 1) = x then secAU k else []

/-- The prefix of position `x` (second arguments of `EU` and `AU` at positions in `[j₀, x)`). -/
def secC (ts : List Tok) (j₀ x : ℕ) : List Tok := rngL j₀ (x - j₀) (secAt ts x)

/-- Emission for the translation of the formula at `j₀`, at position `x`. -/
def trAtC (ts : List Tok) (m j₀ x : ℕ) : List Tok := secC ts j₀ x ++ trBodyC ts m x

lemma secC_nil {j₀ x : ℕ}
    (h : ∀ k, j₀ ≤ k → k < x → (tc ts k = 10 ∨ tc ts k = 11) → fendC ts (k + 1) ≠ x) :
    secC ts j₀ x = [] := by
  refine rngL_nil _ _ _ fun i hi => ?_
  simp only [secAt]
  by_cases h10 : tc ts (j₀ + i) = 10
  · rw [if_neg (fun hh => h _ (by omega) (by omega) (Or.inl h10) hh.2), if_neg (by omega)]
  · by_cases h11 : tc ts (j₀ + i) = 11
    · rw [if_neg (by tauto), if_neg (fun hh => h _ (by omega) (by omega) (Or.inr h11) hh.2)]
    · rw [if_neg (by tauto), if_neg (by tauto)]

lemma secC_at {j₀ x k : ℕ} (hk1 : j₀ ≤ k) (hk2 : k < x) (hfe : fendC ts (k + 1) = x)
    (h : ∀ k', j₀ ≤ k' → k' < x → k' ≠ k → (tc ts k' = 10 ∨ tc ts k' = 11) →
      fendC ts (k' + 1) ≠ x) :
    secC ts j₀ x = secAt ts x k := by
  unfold secC rngL
  rw [show secAt ts x k = (fun i => secAt ts x (j₀ + i)) (k - j₀) by
    simp only; rw [Nat.add_sub_cancel' hk1]]
  refine flatMap_range_single _ _ _ (by omega) fun i hi hik => ?_
  simp only [secAt]
  have hne : j₀ + i ≠ k := by omega
  by_cases h10 : tc ts (j₀ + i) = 10
  · rw [if_neg (fun hh => h _ (by omega) (by omega) hne (Or.inl h10) hh.2), if_neg (by omega)]
  · by_cases h11 : tc ts (j₀ + i) = 11
    · rw [if_neg (by tauto), if_neg (fun hh => h _ (by omega) (by omega) hne (Or.inr h11) hh.2)]
    · rw [if_neg (by tauto), if_neg (by tauto)]

/-- Internal binary temporal operators end their first argument inside the formula. -/
lemma bin_inside (χ : CTL) : ∀ a R, ts.drop a = χ.toks ++ R → ∀ k, a ≤ k →
    k < a + χ.toks.length → (tc ts k = 10 ∨ tc ts k = 11) →
    fendC ts (k + 1) < a + χ.toks.length := by
  induction χ with
  | ap b =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 0 :: (natToks b ++ R) := by simpa [CTL.toks] using h
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · have := tc_natToks_le (i := k - (a + 1)) (drop_succ_of_drop h')
        (by simp [CTL.toks] at hk2; omega)
      rw [show a + 1 + (k - (a + 1)) = k by omega] at this; omega
  | tt =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 1 :: R := by simpa [CTL.toks] using h
    simp [CTL.toks] at hk2
    rw [show k = a by omega, tc_of_drop h'] at h10; simp [Tok.code] at h10
  | neg ψ ih =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 2 :: (ψ.toks ++ R) := by simpa [CTL.toks] using h
    simp only [CTL.toks, List.length_cons] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · have := ih _ _ (drop_succ_of_drop h') k (by omega) (by omega) h10; omega
  | EX ψ ih =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 4 :: (ψ.toks ++ R) := by simpa [CTL.toks] using h
    simp only [CTL.toks, List.length_cons] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · have := ih _ _ (drop_succ_of_drop h') k (by omega) (by omega) h10; omega
  | and ψ₁ ψ₂ ih1 ih2 =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 3 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTL.toks] using h
    have h1 := drop_succ_of_drop h'
    simp only [CTL.toks, List.length_cons, List.length_append] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · by_cases hk : k < a + 1 + ψ₁.toks.length
      · have := ih1 _ _ h1 k (by omega) hk h10; omega
      · have := ih2 _ _ (drop_append_of_drop h1) k (by omega) (by omega) h10; omega
  | EU ψ₁ ψ₂ ih1 ih2 =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 5 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTL.toks] using h
    have h1 := drop_succ_of_drop h'
    have hp2 := CTL.toks_length_pos ψ₂
    simp only [CTL.toks, List.length_cons, List.length_append] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [fendC_formula ψ₁ h1]; omega
    · by_cases hk : k < a + 1 + ψ₁.toks.length
      · have := ih1 _ _ h1 k (by omega) hk h10; omega
      · have := ih2 _ _ (drop_append_of_drop h1) k (by omega) (by omega) h10; omega
  | AU ψ₁ ψ₂ ih1 ih2 =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 6 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTL.toks] using h
    have h1 := drop_succ_of_drop h'
    have hp2 := CTL.toks_length_pos ψ₂
    simp only [CTL.toks, List.length_cons, List.length_append] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [fendC_formula ψ₁ h1]; omega
    · by_cases hk : k < a + 1 + ψ₁.toks.length
      · have := ih1 _ _ h1 k (by omega) hk h10; omega
      · have := ih2 _ _ (drop_append_of_drop h1) k (by omega) (by omega) h10; omega

/-- The hypothesis of the emission lemma: no binary temporal operator before position `a`
(from `j₀` on) has the start of its second argument strictly inside the span `(a, a + n)`. -/
def NoSecC (ts : List Tok) (j₀ a n : ℕ) : Prop :=
  ∀ k, j₀ ≤ k → k < a → (tc ts k = 10 ∨ tc ts k = 11) →
    ¬ (a < fendC ts (k + 1) ∧ fendC ts (k + 1) < a + n)

lemma secC_child {j₀ a n : ℕ} (H : NoSecC ts j₀ a n) (hn : 1 < n)
    (h10 : ¬ (tc ts a = 10 ∨ tc ts a = 11)) : secC ts j₀ (a + 1) = [] := by
  apply secC_nil
  intro k hk1 hk2 hk3
  rcases Nat.lt_or_ge k a with hk | hk
  · intro he; exact H k hk1 hk hk3 ⟨by omega, by omega⟩
  · rw [show k = a by omega] at hk3; exact absurd hk3 h10

lemma NoSecC_child {j₀ a n : ℕ} (H : NoSecC ts j₀ a n) (h10 : ¬ (tc ts a = 10 ∨ tc ts a = 11)) :
    NoSecC ts j₀ (a + 1) (n - 1) := by
  intro k hk1 hk2 hk3 ⟨h1, h2⟩
  rcases Nat.lt_or_ge k a with hk | hk
  · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
  · rw [show k = a by omega] at hk3; exact h10 hk3

lemma trBodyC_digit {x : ℕ} (h : tc ts x ≤ 2) (m : ℕ) : trBodyC ts m x = cp ts x := by
  simp only [trBodyC]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

lemma lor_toks (a b : LTL) : (lor a b).toks =
    [Tok.tag 2, Tok.tag 3, Tok.tag 2] ++ a.toks ++ (Tok.tag 2 :: b.toks) := by
  simp [lor, LTL.toks]

lemma lite_toks (c a b : LTL) : (lite c a b).toks =
    [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3] ++ c.toks ++ a.toks ++
      [Tok.tag 2, Tok.tag 3, Tok.tag 2] ++ c.toks ++ b.toks := by
  simp [lite, lor, LTL.toks]

/-- Two-argument helper: the prefix of position `a + 1 + |ψ₁|` and the inner hypotheses. -/
lemma second_arg_hyps {j₀ a n : ℕ} {ψ₁ : CTL} {R : List Tok} (hj : j₀ ≤ a)
    (h1 : ts.drop (a + 1) = ψ₁.toks ++ R) (H : NoSecC ts j₀ a n)
    (hn : a + 1 + ψ₁.toks.length < a + n) :
    ∀ k', j₀ ≤ k' → k' < a + 1 + ψ₁.toks.length → k' ≠ a → (tc ts k' = 10 ∨ tc ts k' = 11) →
      fendC ts (k' + 1) ≠ a + 1 + ψ₁.toks.length := by
  intro k hk1 hk2 hka hk3 he
  rcases Nat.lt_or_ge k a with hk | hk
  · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
  · have := bin_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega

/-- **Emission lemma for the translation.** -/
lemma trC_emit (m : ℕ) (χ : CTL) : ∀ j₀ a R, ts.drop a = χ.toks ++ R → j₀ ≤ a →
    NoSecC ts j₀ a χ.toks.length →
    rng a χ.toks.length (trAtC ts m j₀) = secC ts j₀ a ++ (trC m χ a).toks := by
  induction χ with
  | ap b =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 0 :: (natToks b ++ R) := by simpa [CTL.toks] using h
    have h1 := drop_succ_of_drop h'
    simp only [CTL.toks, List.length_cons]
    rw [rng_succ']
    have hd : rng (a + 1) (natToks b).length (trAtC ts m j₀) = natToks b := by
      refine (rng_congr _ _ _ _ fun i hi => ?_).trans (rng_cp h1)
      have hle := tc_natToks_le h1 hi
      have hs : secC ts j₀ (a + 1 + i) = [] := by
        apply secC_nil
        intro k hk1 hk2 hk3
        rcases Nat.lt_or_ge k a with hk | hk
        · intro he
          exact H k hk1 hk hk3 ⟨by omega, by simp [CTL.toks]; omega⟩
        · rcases Nat.eq_or_lt_of_le hk with rfl | hk
          · rw [tc_of_drop h'] at hk3; simp [Tok.code] at hk3
          · have := tc_natToks_le (i := k - (a + 1)) h1 (by omega)
            rw [show a + 1 + (k - (a + 1)) = k by omega] at this; omega
      simp only [trAtC, hs, List.nil_append, trBodyC_digit hle]
    rw [hd]
    simp [trAtC, trBodyC, tc_of_drop h', Tok.code, trC, LTL.toks, natToks_gm]
  | tt =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 1 :: R := by simpa [CTL.toks] using h
    simp [CTL.toks, rng, trAtC, trBodyC, tc_of_drop h', Tok.code, trC, LTL.toks]
  | neg ψ ih =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 2 :: (ψ.toks ++ R) := by simpa [CTL.toks] using h
    have h10 : ¬ (tc ts a = 10 ∨ tc ts a = 11) := by rw [tc_of_drop h']; simp [Tok.code]
    have hl := CTL.toks_length_pos ψ
    simp only [CTL.toks, List.length_cons] at H ⊢
    rw [rng_succ', ih j₀ _ _ (drop_succ_of_drop h') (by omega) (by simpa using NoSecC_child H h10),
      secC_child H (by omega) h10]
    simp [trAtC, trBodyC, tc_of_drop h', Tok.code, trC, LTL.toks]
  | EX ψ ih =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 4 :: (ψ.toks ++ R) := by simpa [CTL.toks] using h
    have h10 : ¬ (tc ts a = 10 ∨ tc ts a = 11) := by rw [tc_of_drop h']; simp [Tok.code]
    have hl := CTL.toks_length_pos ψ
    simp only [CTL.toks, List.length_cons] at H ⊢
    rw [rng_succ', ih j₀ _ _ (drop_succ_of_drop h') (by omega) (by simpa using NoSecC_child H h10),
      secC_child H (by omega) h10]
    simp [trAtC, trBodyC, tc_of_drop h', Tok.code, trC, LTL.toks, lor_toks, preEX, apT]
  | and ψ₁ ψ₂ ih1 ih2 =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 3 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTL.toks] using h
    have h1 := drop_succ_of_drop h'
    have h2 := drop_append_of_drop h1
    have h10 : ¬ (tc ts a = 10 ∨ tc ts a = 11) := by rw [tc_of_drop h']; simp [Tok.code]
    have hl1 := CTL.toks_length_pos ψ₁
    have hl2 := CTL.toks_length_pos ψ₂
    simp only [CTL.toks, List.length_cons, List.length_append] at H ⊢
    have H1 : NoSecC ts j₀ (a + 1) ψ₁.toks.length := by
      intro k hk1 hk2 hk3 hh
      exact NoSecC_child H h10 k hk1 hk2 hk3 ⟨hh.1, by omega⟩
    have H2 : NoSecC ts j₀ (a + 1 + ψ₁.toks.length) ψ₂.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · exact h10 hk3
        · have := bin_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega
    have hs2 : secC ts j₀ (a + 1 + ψ₁.toks.length) = [] := by
      apply secC_nil
      intro k hk1 hk2 hk3 he
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · exact h10 hk3
        · have := bin_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega
    rw [rng_succ', rng_add, ih1 j₀ _ _ h1 (by omega) H1, ih2 j₀ _ _ h2 (by omega) H2, hs2,
      secC_child H (by omega) h10]
    simp [trAtC, trBodyC, tc_of_drop h', Tok.code, trC, LTL.toks]
  | EU ψ₁ ψ₂ ih1 ih2 =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 5 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTL.toks] using h
    have h1 := drop_succ_of_drop h'
    have h2 := drop_append_of_drop h1
    have h10 : tc ts a = 10 := by rw [tc_of_drop h']; simp [Tok.code]
    have hfe := fendC_formula ψ₁ h1
    have hl1 := CTL.toks_length_pos ψ₁
    have hl2 := CTL.toks_length_pos ψ₂
    simp only [CTL.toks, List.length_cons, List.length_append] at H ⊢
    have H1 : NoSecC ts j₀ (a + 1) ψ₁.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · obtain rfl : k = a := by omega
        rw [hfe] at hh2; omega
    have H2 : NoSecC ts j₀ (a + 1 + ψ₁.toks.length) ψ₂.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · rw [hfe] at hh1; omega
        · have := bin_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega
    have hs1 : secC ts j₀ (a + 1) = [] := by
      apply secC_nil
      intro k hk1 hk2 hk3 he
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rw [show k = a by omega, hfe] at he; omega
    have hs2 : secC ts j₀ (a + 1 + ψ₁.toks.length) = secEU a := by
      rw [secC_at hj (by omega) hfe (second_arg_hyps hj h1 H (by omega))]
      simp [secAt, h10, hfe]
    rw [rng_succ', rng_add, ih1 j₀ _ _ h1 (by omega) H1, ih2 j₀ _ _ h2 (by omega) H2, hs1, hs2]
    simp [trAtC, trBodyC, h10, trC, LTL.toks, lor_toks, lite_toks, preEU, secEU, apT]
  | AU ψ₁ ψ₂ ih1 ih2 =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 6 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTL.toks] using h
    have h1 := drop_succ_of_drop h'
    have h2 := drop_append_of_drop h1
    have h11 : tc ts a = 11 := by rw [tc_of_drop h']; simp [Tok.code]
    have hfe := fendC_formula ψ₁ h1
    have hl1 := CTL.toks_length_pos ψ₁
    have hl2 := CTL.toks_length_pos ψ₂
    simp only [CTL.toks, List.length_cons, List.length_append] at H ⊢
    have H1 : NoSecC ts j₀ (a + 1) ψ₁.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · obtain rfl : k = a := by omega
        rw [hfe] at hh2; omega
    have H2 : NoSecC ts j₀ (a + 1 + ψ₁.toks.length) ψ₂.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · rw [hfe] at hh1; omega
        · have := bin_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega
    have hs1 : secC ts j₀ (a + 1) = [] := by
      apply secC_nil
      intro k hk1 hk2 hk3 he
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rw [show k = a by omega, hfe] at he; omega
    have hs2 : secC ts j₀ (a + 1 + ψ₁.toks.length) = secAU a := by
      rw [secC_at hj (by omega) hfe (second_arg_hyps hj h1 H (by omega))]
      simp [secAt, h11, hfe]
    rw [rng_succ', rng_add, ih1 j₀ _ _ h1 (by omega) H1, ih2 j₀ _ _ h2 (by omega) H2, hs1, hs2]
    simp [trAtC, trBodyC, h11, trC, LTL.toks, lor_toks, lite_toks, preAU, secAU, secEU, apT]

/-- Tokens of the translation of the formula at position `j`. -/
def trCToks (ts : List Tok) (m j : ℕ) : List Tok := rng j (fendC ts j - j) (trAtC ts m j)

theorem trCToks_eq (m : ℕ) (χ : CTL) {j : ℕ} {R : List Tok} (h : ts.drop j = χ.toks ++ R) :
    trCToks ts m j = (trC m χ j).toks := by
  rw [trCToks, fendC_formula χ h, Nat.add_sub_cancel_left,
    trC_emit m χ j j R h le_rfl (fun k hk1 hk2 => absurd hk2 (by omega))]
  rw [secC_nil (fun k hk1 hk2 => absurd hk2 (by omega))]
  simp

end CTLT

end PathChecking
