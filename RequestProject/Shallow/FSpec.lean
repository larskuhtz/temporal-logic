module

public import RequestProject.Shallow.PosRound

/-!
# Token-by-token production of the translated formulas

The LTL formulas of the queries are produced by scanning the tokens of the input formula
from left to right and emitting, for every token, a short list of tokens that depends only on
the token, its position and (for the translation of `U`) on whether the position starts the
second argument of a `U`.  This file defines these emission functions on token lists and
proves that they produce `erase χ` and `trP m χ j`.
-/

@[expose] public section

namespace PathChecking

namespace ShallowP

open CTLP

/-- `f a ++ f (a + 1) ++ ⋯ ++ f (a + n - 1)`. -/
def rng (a n : ℕ) (f : ℕ → List Tok) : List Tok := (List.range n).flatMap fun i => f (a + i)

lemma rng_zero (a : ℕ) (f : ℕ → List Tok) : rng a 0 f = [] := rfl

lemma rng_add (a n k : ℕ) (f : ℕ → List Tok) : rng a (n + k) f = rng a n f ++ rng (a + n) k f := by
  simp [rng, List.range_add, List.flatMap_append, List.flatMap_map, Nat.add_assoc]

lemma rng_succ (a n : ℕ) (f : ℕ → List Tok) : rng a (n + 1) f = rng a n f ++ f (a + n) := by
  rw [rng_add]; simp [rng]

lemma rng_succ' (a n : ℕ) (f : ℕ → List Tok) : rng a (n + 1) f = f a ++ rng (a + 1) n f := by
  rw [Nat.add_comm, rng_add]; simp [rng]

lemma rng_congr (a n : ℕ) (f g : ℕ → List Tok) (h : ∀ i < n, f (a + i) = g (a + i)) :
    rng a n f = rng a n g := by
  unfold rng
  refine List.flatMap_congr fun i hi => h i (by simpa using hi)

lemma rng_nil (a n : ℕ) (f : ℕ → List Tok) (h : ∀ i < n, f (a + i) = []) : rng a n f = [] := by
  rw [rng_congr a n f (fun _ => []) h]; simp [rng]

variable {ts : List Tok}

/-- Copy of the token at position `i`. -/
def cp (ts : List Tok) (i : ℕ) : List Tok := ts[i]?.toList

lemma rng_cp {a : ℕ} {l R : List Tok} (h : ts.drop a = l ++ R) : rng a l.length (cp ts) = l := by
  induction l generalizing a with
  | nil => rfl
  | cons t l ih =>
    rw [List.length_cons, rng_succ', ih (drop_toks_cons h)]
    have : ts[a]? = some t := by rw [← List.head?_drop, h]; rfl
    simp [cp, this]

lemma tc_of_drop_append {a i : ℕ} {l R : List Tok} (h : ts.drop a = l ++ R) (hi : i < l.length) :
    tc ts (a + i) = (l[i]).code := by
  have : ts[a + i]? = some l[i] := by
    rw [← List.getElem?_drop, h, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  simp [tc, this]

lemma cp_of_drop_append {a i : ℕ} {l R : List Tok} (h : ts.drop a = l ++ R) (hi : i < l.length) :
    cp ts (a + i) = [l[i]] := by
  have : ts[a + i]? = some l[i] := by
    rw [← List.getElem?_drop, h, List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  simp [cp, this]

lemma natToks_code_le (b : ℕ) : ∀ t ∈ natToks b, t.code ≤ 2 := by
  intro t ht
  simp only [natToks, List.mem_append, List.mem_map, List.mem_singleton] at ht
  rcases ht with ⟨x, -, rfl⟩ | rfl
  · cases x <;> simp [Tok.code]
  · simp [Tok.code]

lemma tc_natToks_le {a i b : ℕ} {R : List Tok} (h : ts.drop a = natToks b ++ R)
    (hi : i < (natToks b).length) : tc ts (a + i) ≤ 2 := by
  rw [tc_of_drop_append h hi]; exact natToks_code_le b _ (List.getElem_mem hi)

lemma CTLStar.toks_length_pos (χ : CTLStar) : 0 < χ.toks.length := by
  cases χ <;> simp [CTLStar.toks]

lemma natToks_length_pos (b : ℕ) : 0 < (natToks b).length := by
  simp [natToks]

/-! ## Erasing path quantifiers -/

/-- Emission for `erase`: every token except `E` is copied. -/
def eraseAt (ts : List Tok) (x : ℕ) : List Tok := if tc ts x = 11 then [] else cp ts x

lemma eraseAt_digits {a b : ℕ} {R : List Tok} (h : ts.drop a = natToks b ++ R) :
    rng a (natToks b).length (eraseAt ts) = natToks b := by
  refine (rng_congr _ _ _ _ fun i hi => ?_).trans (rng_cp h)
  have := tc_natToks_le h hi
  simp only [eraseAt, if_neg (show tc ts (a + i) ≠ 11 by omega)]

lemma erase_emit (χ : CTLStar) : ∀ a R, ts.drop a = χ.toks ++ R →
    rng a χ.toks.length (eraseAt ts) = (Shallow.erase χ).toks := by
  induction χ with
  | ap b =>
    intro a R h
    have h' : ts.drop a = Tok.tag 0 :: (natToks b ++ R) := by simpa [CTLStar.toks] using h
    simp only [CTLStar.toks, List.length_cons]
    rw [rng_succ', eraseAt_digits (drop_succ_of_drop h')]
    simp [eraseAt, tc_of_drop h', cp, ← List.head?_drop, h', Shallow.erase, LTL.toks, Tok.code]
  | tt =>
    intro a R h
    have h' : ts.drop a = Tok.tag 1 :: R := by simpa [CTLStar.toks] using h
    simp [CTLStar.toks, rng, eraseAt, tc_of_drop h', cp, ← List.head?_drop, h', Shallow.erase,
      LTL.toks, Tok.code]
  | neg ψ ih =>
    intro a R h
    have h' : ts.drop a = Tok.tag 2 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    simp only [CTLStar.toks, List.length_cons]
    rw [rng_succ', ih _ _ (drop_succ_of_drop h')]
    simp [eraseAt, tc_of_drop h', cp, ← List.head?_drop, h', Shallow.erase, LTL.toks, Tok.code]
  | and ψ₁ ψ₂ ih1 ih2 =>
    intro a R h
    have h' : ts.drop a = Tok.tag 3 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    simp only [CTLStar.toks, List.length_cons, List.length_append]
    rw [rng_succ', rng_add, ih1 _ _ h1, ih2 _ _ (drop_append_of_drop h1)]
    simp [eraseAt, tc_of_drop h', cp, ← List.head?_drop, h', Shallow.erase, LTL.toks, Tok.code]
  | X ψ ih =>
    intro a R h
    have h' : ts.drop a = Tok.tag 4 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    simp only [CTLStar.toks, List.length_cons]
    rw [rng_succ', ih _ _ (drop_succ_of_drop h')]
    simp [eraseAt, tc_of_drop h', cp, ← List.head?_drop, h', Shallow.erase, LTL.toks, Tok.code]
  | U ψ₁ ψ₂ ih1 ih2 =>
    intro a R h
    have h' : ts.drop a = Tok.tag 5 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    simp only [CTLStar.toks, List.length_cons, List.length_append]
    rw [rng_succ', rng_add, ih1 _ _ h1, ih2 _ _ (drop_append_of_drop h1)]
    simp [eraseAt, tc_of_drop h', cp, ← List.head?_drop, h', Shallow.erase, LTL.toks, Tok.code]
  | E ψ ih =>
    intro a R h
    have h' : ts.drop a = Tok.tag 6 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    simp only [CTLStar.toks, List.length_cons]
    rw [rng_succ', ih _ _ (drop_succ_of_drop h')]
    simp [eraseAt, tc_of_drop h', Shallow.erase, Tok.code]

/-- Tokens of `erase χ` for the formula at position `j`. -/
def eraseToks (ts : List Tok) (j : ℕ) : List Tok := rng j (fend ts j - j) (eraseAt ts)

theorem eraseToks_eq (χ : CTLStar) {j : ℕ} {R : List Tok} (h : ts.drop j = χ.toks ++ R) :
    eraseToks ts j = (Shallow.erase χ).toks := by
  rw [eraseToks, fend_formula χ h, Nat.add_sub_cancel_left, erase_emit χ j R h]

/-! ## The positional translation -/

lemma bits_gm (m a : ℕ) : Nat.bits (gm m a) = List.replicate m true ++ Nat.bits a := by
  induction m with
  | zero => simp [gm]
  | succ m ih =>
    have e : gm (m + 1) a = 2 * gm m a + 1 := by
      simp only [gm, pow_succ]
      have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      generalize 2 ^ m = t at *
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [show (s + 1) * 2 - 1 = 2 * s + 1 by omega, show s + 1 - 1 = s by omega]
      ring
    rw [e, LS.Nat.bits_of_ne_zero' _ (by omega), show (2 * gm m a + 1) / 2 = gm m a by omega, ih]
    simp [List.replicate_succ]

lemma natToks_gm (m a : ℕ) : natToks (gm m a) = List.replicate m Tok.one ++ natToks a := by
  simp [natToks, bits_gm, List.map_replicate]

/-- The position `x` starts the second argument of a `U` at a position in `[j₀, x)`. -/
def secU (ts : List Tok) (j₀ x : ℕ) : Bool :=
  (List.range (x - j₀)).any fun i => decide (tc ts (j₀ + i) = 10 ∧ fend ts (j₀ + i + 1) = x)

lemma secU_false {j₀ x : ℕ} (h : ∀ k, j₀ ≤ k → k < x → tc ts k = 10 → fend ts (k + 1) ≠ x) :
    secU ts j₀ x = false := by
  simp only [secU, List.any_eq_false, List.mem_range, decide_eq_true_eq, not_and]
  intro i hi h10
  exact h (j₀ + i) (by omega) (by omega) h10

lemma secU_true {j₀ x k : ℕ} (h1 : j₀ ≤ k) (h2 : k < x) (h3 : tc ts k = 10)
    (h4 : fend ts (k + 1) = x) : secU ts j₀ x = true := by
  simp only [secU, List.any_eq_true, List.mem_range, decide_eq_true_eq]
  exact ⟨k - j₀, by omega, by rw [Nat.add_sub_cancel' h1]; exact ⟨h3, h4⟩⟩

/-- Emission for the translation, without the possible leading `neg`. -/
def trBody (ts : List Tok) (m x : ℕ) : List Tok :=
  if tc ts x = 5 then Tok.tag 0 :: List.replicate m Tok.one
  else if tc ts x = 6 then [Tok.tag 1]
  else if tc ts x = 7 then [Tok.tag 2]
  else if tc ts x = 8 then [Tok.tag 3]
  else if tc ts x = 9 then
    [Tok.tag 2, Tok.tag 3, Tok.tag 2] ++ (Tok.tag 0 :: natToks (x + 2)) ++ [Tok.tag 2, Tok.tag 3] ++
      (Tok.tag 0 :: natToks (x + 2))
  else if tc ts x = 10 then [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3] ++ (Tok.tag 0 :: natToks (x + 1))
  else if tc ts x = 11 then [Tok.tag 5, Tok.tag 1]
  else cp ts x

/-- Emission for the translation of the formula at `j₀`, at position `x`. -/
def trAt (ts : List Tok) (m j₀ x : ℕ) : List Tok :=
  (if secU ts j₀ x then [Tok.tag 2] else []) ++ trBody ts m x

/-- Internal `U`s end their first argument inside the formula. -/
lemma U_inside (χ : CTLStar) : ∀ a R, ts.drop a = χ.toks ++ R → ∀ k, a ≤ k →
    k < a + χ.toks.length → tc ts k = 10 → fend ts (k + 1) < a + χ.toks.length := by
  induction χ with
  | ap b =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 0 :: (natToks b ++ R) := by simpa [CTLStar.toks] using h
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · have := tc_natToks_le (i := k - (a + 1)) (drop_succ_of_drop h')
        (by simp [CTLStar.toks] at hk2; omega)
      rw [show a + 1 + (k - (a + 1)) = k by omega] at this; omega
  | tt =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 1 :: R := by simpa [CTLStar.toks] using h
    simp [CTLStar.toks] at hk2
    rw [show k = a by omega, tc_of_drop h'] at h10; simp [Tok.code] at h10
  | neg ψ ih =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 2 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    simp only [CTLStar.toks, List.length_cons] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · have := ih _ _ (drop_succ_of_drop h') k (by omega) (by omega) h10; omega
  | and ψ₁ ψ₂ ih1 ih2 =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 3 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    simp only [CTLStar.toks, List.length_cons, List.length_append] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · by_cases hk : k < a + 1 + ψ₁.toks.length
      · have := ih1 _ _ h1 k (by omega) hk h10; omega
      · have := ih2 _ _ (drop_append_of_drop h1) k (by omega) (by omega) h10; omega
  | X ψ ih =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 4 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    simp only [CTLStar.toks, List.length_cons] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · have := ih _ _ (drop_succ_of_drop h') k (by omega) (by omega) h10; omega
  | U ψ₁ ψ₂ ih1 ih2 =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 5 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    have hp2 := CTLStar.toks_length_pos ψ₂
    simp only [CTLStar.toks, List.length_cons, List.length_append] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [fend_formula ψ₁ h1]; omega
    · by_cases hk : k < a + 1 + ψ₁.toks.length
      · have := ih1 _ _ h1 k (by omega) hk h10; omega
      · have := ih2 _ _ (drop_append_of_drop h1) k (by omega) (by omega) h10; omega
  | E ψ ih =>
    intro a R h k hk1 hk2 h10
    have h' : ts.drop a = Tok.tag 6 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    simp only [CTLStar.toks, List.length_cons] at hk2 ⊢
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk1
    · rw [tc_of_drop h'] at h10; simp [Tok.code] at h10
    · have := ih _ _ (drop_succ_of_drop h') k (by omega) (by omega) h10; omega

/-- The hypothesis of the emission lemma: no `U` before position `a` (from `j₀` on) has the
start of its second argument strictly inside the span `(a, a + n)`. -/
def NoSec (ts : List Tok) (j₀ a n : ℕ) : Prop :=
  ∀ k, j₀ ≤ k → k < a → tc ts k = 10 → ¬ (a < fend ts (k + 1) ∧ fend ts (k + 1) < a + n)

lemma secU_child {j₀ a n : ℕ} (H : NoSec ts j₀ a n) (hn : 1 < n)
    (h10 : tc ts a ≠ 10) : secU ts j₀ (a + 1) = false := by
  apply secU_false
  intro k hk1 hk2 hk3
  rcases Nat.lt_or_ge k a with hk | hk
  · intro he; exact H k hk1 hk (hk3) ⟨by omega, by omega⟩
  · rw [show k = a by omega] at hk3; exact absurd hk3 h10

lemma NoSec_child {j₀ a n : ℕ} (H : NoSec ts j₀ a n) (h10 : tc ts a ≠ 10) :
    NoSec ts j₀ (a + 1) (n - 1) := by
  intro k hk1 hk2 hk3 ⟨h1, h2⟩
  rcases Nat.lt_or_ge k a with hk | hk
  · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
  · rw [show k = a by omega] at hk3; exact h10 hk3

lemma trBody_digit {x : ℕ} (h : tc ts x ≤ 2) (m : ℕ) : trBody ts m x = cp ts x := by
  simp only [trBody]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **Emission lemma for the translation.** -/
lemma tr_emit (m : ℕ) (χ : CTLStar) : ∀ j₀ a R, ts.drop a = χ.toks ++ R → j₀ ≤ a →
    NoSec ts j₀ a χ.toks.length →
    rng a χ.toks.length (trAt ts m j₀) =
      (if secU ts j₀ a then [Tok.tag 2] else []) ++ (trP m χ a).toks := by
  induction χ with
  | ap b =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 0 :: (natToks b ++ R) := by simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    simp only [CTLStar.toks, List.length_cons]
    rw [rng_succ']
    have hd : rng (a + 1) (natToks b).length (trAt ts m j₀) = natToks b := by
      refine (rng_congr _ _ _ _ fun i hi => ?_).trans (rng_cp h1)
      have hle := tc_natToks_le h1 hi
      have hs : secU ts j₀ (a + 1 + i) = false := by
        apply secU_false
        intro k hk1 hk2 hk3
        rcases Nat.lt_or_ge k a with hk | hk
        · intro he
          exact H k hk1 hk hk3 ⟨by omega, by simp [CTLStar.toks]; omega⟩
        · rcases Nat.eq_or_lt_of_le hk with rfl | hk
          · rw [tc_of_drop h'] at hk3; simp [Tok.code] at hk3
          · have := tc_natToks_le (i := k - (a + 1)) h1 (by omega)
            rw [show a + 1 + (k - (a + 1)) = k by omega] at this; omega
      simp only [trAt, hs, Bool.false_eq_true, if_false, List.nil_append, trBody_digit hle]
    rw [hd]
    simp [trAt, trBody, tc_of_drop h', Tok.code, trP, LTL.toks, natToks_gm]
  | tt =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 1 :: R := by simpa [CTLStar.toks] using h
    simp [CTLStar.toks, rng, trAt, trBody, tc_of_drop h', Tok.code, trP, LTL.toks]
  | neg ψ ih =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 2 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    have h10 : tc ts a ≠ 10 := by rw [tc_of_drop h']; simp [Tok.code]
    have hl := CTLStar.toks_length_pos ψ
    simp only [CTLStar.toks, List.length_cons] at H ⊢
    rw [rng_succ', ih j₀ _ _ (drop_succ_of_drop h') (by omega) (by simpa using NoSec_child H h10),
      secU_child H (by omega) h10]
    simp [trAt, trBody, tc_of_drop h', Tok.code, trP, LTL.toks]
  | and ψ₁ ψ₂ ih1 ih2 =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 3 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    have h2 := drop_append_of_drop h1
    have h10 : tc ts a ≠ 10 := by rw [tc_of_drop h']; simp [Tok.code]
    have hl1 := CTLStar.toks_length_pos ψ₁
    have hl2 := CTLStar.toks_length_pos ψ₂
    simp only [CTLStar.toks, List.length_cons, List.length_append] at H ⊢
    have H1 : NoSec ts j₀ (a + 1) ψ₁.toks.length := by
      intro k hk1 hk2 hk3 hh
      exact NoSec_child H h10 k hk1 hk2 hk3 ⟨hh.1, by omega⟩
    have H2 : NoSec ts j₀ (a + 1 + ψ₁.toks.length) ψ₂.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · exact h10 hk3
        · have := U_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega
    have hs2 : secU ts j₀ (a + 1 + ψ₁.toks.length) = false := by
      apply secU_false
      intro k hk1 hk2 hk3 he
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · exact h10 hk3
        · have := U_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega
    rw [rng_succ', rng_add, ih1 j₀ _ _ h1 (by omega) H1, ih2 j₀ _ _ h2 (by omega) H2, hs2,
      secU_child H (by omega) h10]
    simp [trAt, trBody, tc_of_drop h', Tok.code, trP, LTL.toks]
  | X ψ ih =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 4 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    have h10 : tc ts a ≠ 10 := by rw [tc_of_drop h']; simp [Tok.code]
    have hl := CTLStar.toks_length_pos ψ
    simp only [CTLStar.toks, List.length_cons] at H ⊢
    rw [rng_succ', ih j₀ _ _ (drop_succ_of_drop h') (by omega) (by simpa using NoSec_child H h10),
      secU_child H (by omega) h10]
    simp [trAt, trBody, tc_of_drop h', Tok.code, trP, LTL.toks]
  | U ψ₁ ψ₂ ih1 ih2 =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 5 :: (ψ₁.toks ++ (ψ₂.toks ++ R)) := by
      simpa [CTLStar.toks] using h
    have h1 := drop_succ_of_drop h'
    have h2 := drop_append_of_drop h1
    have h10 : tc ts a = 10 := by rw [tc_of_drop h']; simp [Tok.code]
    have hfe := fend_formula ψ₁ h1
    have hl1 := CTLStar.toks_length_pos ψ₁
    have hl2 := CTLStar.toks_length_pos ψ₂
    simp only [CTLStar.toks, List.length_cons, List.length_append] at H ⊢
    have H1 : NoSec ts j₀ (a + 1) ψ₁.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · obtain rfl : k = a := by omega
        rw [hfe] at hh2; omega
    have H2 : NoSec ts j₀ (a + 1 + ψ₁.toks.length) ψ₂.toks.length := by
      intro k hk1 hk2 hk3 ⟨hh1, hh2⟩
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rcases Nat.eq_or_lt_of_le hk with rfl | hk
        · rw [hfe] at hh1; omega
        · have := U_inside ψ₁ _ _ h1 k (by omega) (by omega) hk3; omega
    have hs1 : secU ts j₀ (a + 1) = false := by
      apply secU_false
      intro k hk1 hk2 hk3 he
      rcases Nat.lt_or_ge k a with hk | hk
      · exact H k hk1 hk hk3 ⟨by omega, by omega⟩
      · rw [show k = a by omega, hfe] at he; omega
    have hs2 : secU ts j₀ (a + 1 + ψ₁.toks.length) = true :=
      secU_true hj (by omega) h10 hfe
    rw [rng_succ', rng_add, ih1 j₀ _ _ h1 (by omega) H1, ih2 j₀ _ _ h2 (by omega) H2, hs1, hs2]
    simp [trAt, trBody, h10, trP, LTL.toks]
  | E ψ ih =>
    intro j₀ a R h hj H
    have h' : ts.drop a = Tok.tag 6 :: (ψ.toks ++ R) := by simpa [CTLStar.toks] using h
    have h10 : tc ts a ≠ 10 := by rw [tc_of_drop h']; simp [Tok.code]
    have hl := CTLStar.toks_length_pos ψ
    simp only [CTLStar.toks, List.length_cons] at H ⊢
    rw [rng_succ', ih j₀ _ _ (drop_succ_of_drop h') (by omega) (by simpa using NoSec_child H h10),
      secU_child H (by omega) h10]
    simp [trAt, trBody, tc_of_drop h', Tok.code, trP, LTL.toks]

/-- Tokens of the translation of the formula at position `j`. -/
def trToks (ts : List Tok) (m j : ℕ) : List Tok := rng j (fend ts j - j) (trAt ts m j)

theorem trToks_eq (m : ℕ) (χ : CTLStar) {j : ℕ} {R : List Tok} (h : ts.drop j = χ.toks ++ R) :
    trToks ts m j = (trP m χ j).toks := by
  rw [trToks, fend_formula χ h, Nat.add_sub_cancel_left,
    tr_emit m χ j j R h le_rfl (fun k hk1 hk2 => absurd hk2 (by omega))]
  rw [secU_false (fun k hk1 hk2 => absurd hk2 (by omega))]
  simp

end ShallowP

end PathChecking
