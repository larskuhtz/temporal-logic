module

public import RequestProject.LogLang.Out
public import RequestProject.ACRound.Defs
public import RequestProject.CTLStarP.Scan

/-!
# Reading packed inputs in the loop language

The query and decision functions of the round algorithm read inputs `pack w q a`.  This file
fixes the variable layout of these programs, proves the basic facts about `pack` and defines
the expression `tokE p` reading the code of the `p`-th token of `w`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP

/-- Number of variables of the programs. -/
abbrev V : ℕ := 64

/-- `|w|` -/
abbrev vN : Fin V := 0

/-! ## Packed inputs -/

lemma pack_get_unary (w : Word) (q : ℕ) (a : List Bool) {i : ℕ} (hi : i < w.length) :
    (pack w q a)[i]? = some true := by
  simp only [pack, List.append_assoc]
  rw [List.getElem?_append_left (by simpa using hi)]
  simp [hi]

lemma pack_get_sep (w : Word) (q : ℕ) (a : List Bool) : (pack w q a)[w.length]? = some false := by
  simp only [pack, List.append_assoc]
  rw [List.getElem?_append_right (by simp)]
  simp

lemma pack_eq (w : Word) (q : ℕ) (a : List Bool) : pack w q a = List.replicate w.length true ++
    false :: (w ++ (a ++ (List.replicate (a.length - q) false ++ List.replicate q true))) := by
  simp [pack]

lemma pack_get_w (w : Word) (q : ℕ) (a : List Bool) {k : ℕ} (hk : k < w.length) :
    (pack w q a)[w.length + 1 + k]? = w[k]? := by
  rw [pack_eq, List.getElem?_append_right (by simp; omega), List.length_replicate,
    show w.length + 1 + k - w.length = k + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_left hk]

lemma pack_get_a (w : Word) (q : ℕ) (a : List Bool) {k : ℕ} (hk : k < a.length) :
    (pack w q a)[2 * w.length + 1 + k]? = a[k]? := by
  rw [pack_eq, List.getElem?_append_right (by simp; omega), List.length_replicate,
    show 2 * w.length + 1 + k - w.length = (w.length + k) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by omega), show w.length + k - w.length = k by omega,
    List.getElem?_append_left hk]

lemma pack_get_q (w : Word) (q : ℕ) (a : List Bool) (hq : q ≤ a.length) {k : ℕ}
    (hk : k < a.length) :
    (pack w q a)[2 * w.length + 1 + a.length + k]? = some (decide (a.length - q ≤ k)) := by
  rw [pack_eq, List.getElem?_append_right (by simp; omega), List.length_replicate,
    show 2 * w.length + 1 + a.length + k - w.length = (w.length + a.length + k) + 1 by omega,
    List.getElem?_cons_succ, List.getElem?_append_right (by omega),
    show w.length + a.length + k - w.length = a.length + k by omega,
    List.getElem?_append_right (by omega), show a.length + k - a.length = k by omega]
  by_cases h : a.length - q ≤ k
  · rw [List.getElem?_append_right (by simp; omega), List.length_replicate,
      List.getElem?_replicate, if_pos (by omega)]
    simp [h]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_replicate, if_pos (by omega)]
    simp [h]

lemma symNum_some (x : Word) (i : ℕ) (b : Bool) (h : x[i]? = some b) :
    symNum (inputSym x (i + 1)) = if b then 1 else 0 := by
  simp only [inputSym, Nat.add_sub_cancel, Nat.add_one_ne_zero, if_false, h]
  cases b <;> rfl

lemma symNum_le (x : Word) (p : ℕ) : symNum (inputSym x p) ≤ 3 := by
  unfold inputSym
  split_ifs
  · simp [symNum]
  · split
    · rename_i b _; cases b <;> simp [symNum]
    · simp [symNum]

/-! ## Expressions -/

/-- `if g ≠ 0 then a else b` for `g ∈ {0, 1}`. -/
def iteE (g a b : Ex V) : Ex V := .bin .add (.bin .mul g a) (.bin .mul (.bin .eq g (.c 0)) b)

lemma eval_iteE {x : Word} {C : ℕ} {ρ : Fin V → ℕ} (g a b : Ex V)
    (hg : g.eval x C ρ = 0 ∨ g.eval x C ρ = 1) (ha : a.eval x C ρ ≤ C) (hb : b.eval x C ρ ≤ C) :
    (iteE g a b).eval x C ρ = if g.eval x C ρ = 1 then a.eval x C ρ else b.eval x C ρ := by
  rcases hg with h | h <;> simp [iteE, h] <;> omega

/-- Code of the input bit at 0-based position `e` (`3` past the end). -/
def bitE (e : Ex V) : Ex V := .inp (.bin .add e (.c 1))

/-- The sum of the token bits. -/
def tokSum (p : Ex V) : Ex V :=
  ((List.range 5).map fun b => (Ex.bin .mul (.c (2 ^ b))
      (bitE (.bin .add (.bin .add (.v vN) (.c (1 + b))) (.bin .mul (.c 5) p))))).foldr
        (fun e acc => .bin .add e acc) (.c 0)

/-- Code of the token number `p` of `w` in `pack w q a` (`29` if there is none). -/
def tokE (p : Ex V) : Ex V :=
  iteE (.bin .lt (.bin .add (.bin .mul (.c 5) p) (.c 4)) (.v vN)) (tokSum p) (.c 29)

/-! ## Token codes from bits -/

lemma code_bits_sum (t : Tok) :
    ((List.range 5).map fun b => 2 ^ b * (if t.code.testBit b then 1 else 0)).sum = t.code := by
  have h := Tok.code_lt t
  generalize t.code = k at h ⊢
  interval_cases k <;> decide

lemma encodeToks_getElem? (ts : List Tok) (p b : ℕ) (hp : p < ts.length) (hb : b < 5) :
    (encodeToks ts)[5 * p + b]? = some ((ts[p]).code.testBit b) := by
  induction ts generalizing p with
  | nil => simp at hp
  | cons t ts ih =>
    rw [LS.encodeToks_cons]
    rcases p with _ | p
    · rw [List.getElem?_append_left (by simp [LS.Tok.bits_length]; omega)]
      simp [Tok.bits, hb]
    · rw [List.getElem?_append_right (by simp [LS.Tok.bits_length]; omega), LS.Tok.bits_length,
        show 5 * (p + 1) + b - 5 = 5 * p + b by omega, ih p (by simpa using hp)]
      simp

lemma encodeToks_length (ts : List Tok) : (encodeToks ts).length = 5 * ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [LS.encodeToks_cons, List.length_append, LS.Tok.bits_length, ih]; simp; ring

lemma foldr_add_eval {x : Word} {C : ℕ} {ρ : Fin V → ℕ} (l : List (Ex V))
    (h : (l.map fun e => e.eval x C ρ).sum ≤ C) :
    (l.foldr (fun e acc => Ex.bin .add e acc) (.c 0)).eval x C ρ =
      (l.map fun e => e.eval x C ρ).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldr_cons, eval_bin, ap_add, List.map_cons, List.sum_cons] at h ⊢
    rw [ih (by omega)]; omega

/-- **Reading tokens.**  If the cap is large enough, `tokE p` evaluates to `tc ts p`. -/
lemma eval_tokE (ts : List Tok) (q : ℕ) (a : List Bool) (C : ℕ) (ρ : Fin V → ℕ) (p : Ex V)
    (hq : q ≤ a.length) (hC : 2 * (pack (encodeToks ts) q a).length + 40 ≤ C)
    (hN : ρ vN = 5 * ts.length) (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ C) :
    (tokE p).eval (pack (encodeToks ts) q a) C ρ = tc ts (p.eval (pack (encodeToks ts) q a) C ρ) := by
  set x := pack (encodeToks ts) q a
  set pv := p.eval x C ρ
  have hlen := pack_length (encodeToks ts) q a hq
  rw [encodeToks_length] at hlen
  rw [hlen] at hC
  by_cases hg : 5 * pv + 4 < 5 * ts.length
  · have hpl : pv < ts.length := by omega
    have hbits : ∀ b < 5, (bitE (.bin .add (.bin .add (.v vN) (.c (1 + b))) (.bin .mul (.c 5) p))).eval
        x C ρ = if (ts[pv]).code.testBit b then 1 else 0 := by
      intro b hb
      simp only [bitE, eval_inp, eval_bin, ap_add, ap_mul, eval_v, eval_c, hN]
      simp (disch := omega) only [min_eq_left]
      rw [show 5 * ts.length + (1 + b) + 5 * pv + 1 = (5 * ts.length + 1 + (5 * pv + b)) + 1 by
        omega, symNum_some x _ ((ts[pv]).code.testBit b)]
      have := pack_get_w (encodeToks ts) q a (k := 5 * pv + b)
        (by rw [encodeToks_length]; omega)
      rw [encodeToks_length] at this
      rw [this, encodeToks_getElem? ts pv b hpl hb]
    have hsum : (((List.range 5).map fun b => (Ex.bin .mul (.c (2 ^ b))
        (bitE (.bin .add (.bin .add (.v vN) (.c (1 + b))) (.bin .mul (.c 5) p))) : Ex V)).map
          fun e => e.eval x C ρ).sum = (ts[pv]).code := by
      rw [← code_bits_sum (ts[pv]), List.map_map]
      congr 1
      refine List.map_congr_left fun b hb => ?_
      simp only [List.mem_range] at hb
      simp only [Function.comp, eval_bin, ap_mul, eval_c, hbits b hb]
      have : 2 ^ b ≤ 16 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show b ≤ 4 by omega); simpa using this
      rw [min_eq_left (by omega : 2 ^ b ≤ C)]
      split_ifs <;> simp; omega
    have hcode := Tok.code_lt (ts[pv])
    have hts : (tokSum p).eval x C ρ = (ts[pv]).code := by
      rw [tokSum, foldr_add_eval _ (by rw [hsum]; omega), hsum]
    have hg' : (Ex.bin .lt (.bin .add (.bin .mul (.c 5) p) (.c 4)) (.v vN) : Ex V).eval x C ρ = 1 := by
      simp only [eval_bin, ap_lt, ap_add, ap_mul, eval_c, eval_v, hN]
      simp (disch := omega) only [min_eq_left]
      exact if_pos hg
    unfold tokE
    rw [eval_iteE _ _ _ (Or.inr hg') (by rw [hts]; omega) (by simp), if_pos hg', hts]
    simp [tc, List.getElem?_eq_getElem hpl]
  · have hg' : (Ex.bin .lt (.bin .add (.bin .mul (.c 5) p) (.c 4)) (.v vN) : Ex V).eval x C ρ = 0 := by
      simp only [eval_bin, ap_lt, ap_add, ap_mul, eval_c, eval_v, hN]
      simp (disch := omega) only [min_eq_left]
      rw [if_neg]
      intro h
      have h1 : min (5 * pv) C = 5 * pv := by
        rcases le_total (5 * pv) C with h' | h'
        · exact min_eq_left h'
        · exfalso; rw [min_eq_right h'] at h
          have := min_le_right (C + 4) C
          have := min_le_left (C + 4) C
          omega
      rw [h1] at h
      have : min (5 * pv + 4) C ≥ 5 * ts.length := by
        rcases le_total (5 * pv + 4) C with h' | h'
        · rw [min_eq_left h']; omega
        · rw [min_eq_right h']; omega
      omega
    unfold tokE
    have hle : (tokSum p).eval x C ρ ≤ C := by
      have : ∀ (e acc : Ex V), (Ex.bin .add e acc).eval x C ρ ≤ C := fun e acc => by simp
      exact this _ _
    rw [eval_iteE _ _ _ (Or.inl hg') hle (by simp)]
    rw [if_neg (by rw [hg']; simp)]
    simp [tc, List.getElem?_eq_none (show ts.length ≤ pv by omega)]
    omega

end SQ

end PathChecking
