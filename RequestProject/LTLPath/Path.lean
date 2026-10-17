module

public import RequestProject.LTLPath.TokTree
public import RequestProject.LTLPath.FE

/-!
# Letters of an encoded lasso path

Token-level functions locating the letters of the lasso path that follows the formula, by
counting brackets: `cnt c a b` counts the tokens with code `c` in `[a, b)`, `ffind P a n` is the
least `j ∈ [a, n)` with `P j` (or `n`).
-/

@[expose] public section

namespace PathChecking

open CTLP

namespace LTok

variable {ts : List Tok}

/-- Number of positions `j ∈ [a, b)` with token code `c`. -/
def cnt (ts : List Tok) (c a b : ℕ) : ℕ :=
  (List.range (b - a)).countP (fun m => tc ts (a + m) = c)

/-- Least `j ∈ [a, n)` with `P j`, or `n`. -/
def ffind (P : ℕ → Bool) (a n : ℕ) : ℕ :=
  a + FE.findF (n - a) (fun m => if P (a + m) then 1 else 0)

lemma findF_eq_of {f : ℕ → ℕ} {k : ℕ} (hk : f k ≠ 0) (hlt : ∀ i < k, f i = 0) :
    ∀ N, FE.findF N f = if k < N then k else N := by
  intro N
  induction N with
  | zero => simp [FE.findF]
  | succ N ih =>
    rw [FE.findF_succ, ih]
    by_cases h1 : k < N
    · simp [h1, show k < N + 1 by omega]
    · rw [if_neg h1]
      by_cases h2 : k = N
      · subst h2; simp [hk]
      · have := hlt N (by omega); simp [this, show ¬ k < N + 1 by omega]

lemma ffind_eq {P : ℕ → Bool} {a n x : ℕ} (hax : a ≤ x) (hxn : x < n) (hP : P x = true)
    (hlt : ∀ j, a ≤ j → j < x → P j = false) : ffind P a n = x := by
  unfold ffind
  rw [findF_eq_of (k := x - a) (by simp [show a + (x - a) = x by omega, hP])
    (fun i hi => by simp [hlt (a + i) (by omega) (by omega)]), if_pos (by omega)]
  omega

lemma cnt_self (c a : ℕ) : cnt ts c a a = 0 := by simp [cnt]

lemma cnt_succ (c : ℕ) {a b : ℕ} (h : a ≤ b) :
    cnt ts c a (b + 1) = cnt ts c a b + if tc ts b = c then 1 else 0 := by
  unfold cnt
  rw [show b + 1 - a = (b - a) + 1 by omega, List.range_succ, List.countP_append]
  simp [show a + (b - a) = b by omega]

lemma cnt_add (c : ℕ) {a m b : ℕ} (h1 : a ≤ m) (h2 : m ≤ b) :
    cnt ts c a b = cnt ts c a m + cnt ts c m b := by
  obtain ⟨d, rfl⟩ : ∃ d, b = m + d := ⟨b - m, by omega⟩
  clear h2
  induction d with
  | zero => simp [cnt_self]
  | succ d ih => rw [← Nat.add_assoc, cnt_succ c (by omega), cnt_succ c (by omega), ih]; ring

/-- Token codes of a segment. -/
lemma tc_seg {q : ℕ} {l rest : List Tok} (h : ts.drop q = l ++ rest) {m : ℕ} (hm : m < l.length) :
    tc ts (q + m) = (l[m]'hm).code := by
  have : ts.drop (q + m) = l[m] :: (l.drop (m + 1) ++ rest) := by
    rw [← List.drop_drop, h, List.drop_append_of_le_length (by omega), List.drop_eq_getElem_cons hm]
    rfl
  exact tc_of_drop this

/-- Counting over a segment. -/
lemma cnt_seg {q : ℕ} {l rest : List Tok} (h : ts.drop q = l ++ rest) (c : ℕ) {k : ℕ}
    (hk : k ≤ l.length) : cnt ts c q (q + k) = (l.take k).countP (fun t => t.code = c) := by
  induction k with
  | zero => simp [cnt_self]
  | succ k ih =>
    rw [← Nat.add_assoc, cnt_succ c (by omega), ih (by omega), List.take_succ,
      List.countP_append, tc_seg h (by omega), List.getElem?_eq_getElem (by omega)]
    simp

/-! ## Finite sets of propositions -/

lemma finsetToks_eq (s : Finset ℕ) :
    finsetToks s = Tok.lpar :: ((s.sort (· ≤ ·)).flatMap natToks ++ [Tok.rpar]) := rfl

lemma nums_code (xs : List ℕ) : ∀ t ∈ xs.flatMap natToks, t.code ≤ 2 := by
  intro t ht
  obtain ⟨a, -, ha⟩ := List.mem_flatMap.1 ht
  exact natToks_code a t ha

lemma finsetToks_len (s : Finset ℕ) : 2 ≤ (finsetToks s).length := by
  simp [finsetToks_eq]

end LTok

end PathChecking
