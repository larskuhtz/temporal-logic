module

public import RequestProject.Shallow.Prog.DRec

/-!
# Decoding the input into tokens

A word `w` is the encoding of a nonempty token list iff its length is a positive multiple of
`5` and every block of `5` bits has value `< 29` (`decOK`).  `badP` checks the blocks.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

/-- The value of the `p`-th block of `5` bits of `w`. -/
def chunk (w : Word) (p : ℕ) : ℕ :=
  ((List.range 5).map fun b => 2 ^ b * (if w.getD (5 * p + b) false then 1 else 0)).sum

/-- The token with a given code (`≤ 28`). -/
def Tok.ofCode (k : ℕ) : Tok :=
  if k = 0 then .zero else if k = 1 then .one else if k = 2 then .sep else if k = 3 then .lpar
  else if k = 4 then .rpar else .tag ⟨(k - 5) % 24, Nat.mod_lt _ (by decide)⟩

lemma Tok.code_ofCode {k : ℕ} (hk : k < 29) : (Tok.ofCode k).code = k := by
  unfold Tok.ofCode
  split_ifs <;> simp [Tok.code] <;> omega

/-- The input is the encoding of a nonempty list of tokens. -/
def decOK (w : Word) : Prop :=
  w.length % 5 = 0 ∧ 0 < w.length / 5 ∧ ∀ p < w.length / 5, chunk w p < 29

lemma testBit_five : ∀ (c0 c1 c2 c3 c4 : Bool), ∀ b < 5,
    (1 * (if c0 then 1 else 0) + 2 * (if c1 then 1 else 0) + 4 * (if c2 then 1 else 0) +
      8 * (if c3 then 1 else 0) + 16 * (if c4 then 1 else 0)).testBit b =
      [c0, c1, c2, c3, c4].getD b false := by
  decide

lemma chunk_testBit (w : Word) (p : ℕ) {b : ℕ} (hb : b < 5) :
    (chunk w p).testBit b = w.getD (5 * p + b) false := by
  have h := testBit_five (w.getD (5 * p + 0) false) (w.getD (5 * p + 1) false)
    (w.getD (5 * p + 2) false) (w.getD (5 * p + 3) false) (w.getD (5 * p + 4) false) b hb
  have hc : chunk w p = 1 * (if w.getD (5 * p + 0) false then 1 else 0) +
      2 * (if w.getD (5 * p + 1) false then 1 else 0) +
      4 * (if w.getD (5 * p + 2) false then 1 else 0) +
      8 * (if w.getD (5 * p + 3) false then 1 else 0) +
      16 * (if w.getD (5 * p + 4) false then 1 else 0) := by
    simp [chunk, List.range_succ]; ring
  rw [hc, h]
  interval_cases b <;> rfl

lemma chunk_encode (ts : List Tok) {p : ℕ} (hp : p < ts.length) : chunk (encodeToks ts) p =
    (ts[p]).code := by
  rw [← code_bits_sum (ts[p])]
  unfold chunk
  congr 1
  refine List.map_congr_left fun b hb => ?_
  simp only [List.mem_range] at hb
  rw [List.getD_eq_getElem?_getD, encodeToks_getElem? ts p b hp hb]
  simp

lemma decOK_encode {ts : List Tok} (h : ts ≠ []) : decOK (encodeToks ts) := by
  have hl : 0 < ts.length := List.length_pos_iff.2 h
  refine ⟨by rw [encodeToks_length]; omega, by rw [encodeToks_length]; omega, fun p hp => ?_⟩
  rw [encodeToks_length] at hp
  rw [chunk_encode ts (by omega)]
  exact Tok.code_lt _

lemma decode_of_decOK {w : Word} (h : decOK w) : ∃ ts : List Tok, w = encodeToks ts ∧ ts ≠ [] := by
  obtain ⟨h5, hpos, hc⟩ := h
  set L := w.length / 5
  refine ⟨(List.range L).map fun p => Tok.ofCode (chunk w p), ?_, by
    simp [L]; omega⟩
  apply List.ext_getElem?
  intro i
  by_cases hi : i < w.length
  · have hp : i / 5 < L := by simp only [L]; omega
    have hi' : i = 5 * (i / 5) + i % 5 := by omega
    rw [hi', encodeToks_getElem? _ _ _ (by simpa using hp) (Nat.mod_lt _ (by omega))]
    simp only [List.getElem_map, List.getElem_range]
    rw [Tok.code_ofCode (hc _ hp), chunk_testBit w _ (Nat.mod_lt _ (by omega)),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    simp
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none]
    rw [encodeToks_length]; simp [L]; omega

lemma chunk_le (w : Word) (p : ℕ) : chunk w p ≤ 31 := by
  have h : chunk w p = 1 * (if w.getD (5 * p + 0) false then 1 else 0) +
      2 * (if w.getD (5 * p + 1) false then 1 else 0) +
      4 * (if w.getD (5 * p + 2) false then 1 else 0) +
      8 * (if w.getD (5 * p + 3) false then 1 else 0) +
      16 * (if w.getD (5 * p + 4) false then 1 else 0) := by
    simp [chunk, List.range_succ]; ring
  rw [h]; split_ifs <;> omega

/-- **Reading blocks of arbitrary inputs.** -/
lemma eval_tokE_raw (w : Word) (q : ℕ) (a : List Bool) (C : ℕ) (ρ : Fin V → ℕ) (p : Ex V)
    (hq : q ≤ a.length) (hC : 2 * (pack w q a).length + 40 ≤ C)
    (hN : ρ vN = w.length) (hp : 5 * p.eval (pack w q a) C ρ + 4 < w.length) :
    (tokE p).eval (pack w q a) C ρ = chunk w (p.eval (pack w q a) C ρ) := by
  set x := pack w q a
  set pv := p.eval x C ρ
  have hlen := pack_length w q a hq
  rw [hlen] at hC
  have hbits : ∀ b < 5, (bitE (.bin .add (.bin .add (.v vN) (.c (1 + b))) (.bin .mul (.c 5) p))).eval
      x C ρ = if w.getD (5 * pv + b) false then 1 else 0 := by
    intro b hb
    simp only [bitE, eval_inp, eval_bin, ap_add, ap_mul, eval_v, eval_c, hN]
    simp (disch := omega) only [min_eq_left]
    have hk : 5 * pv + b < w.length := by omega
    rw [show w.length + (1 + b) + 5 * pv + 1 = (w.length + 1 + (5 * pv + b)) + 1 by omega,
      symNum_some x _ (w.getD (5 * pv + b) false)]
    rw [pack_get_w w q a hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    simp
  have hsum : (((List.range 5).map fun b => (Ex.bin .mul (.c (2 ^ b))
      (bitE (.bin .add (.bin .add (.v vN) (.c (1 + b))) (.bin .mul (.c 5) p))) : Ex V)).map
        fun e => e.eval x C ρ).sum = chunk w pv := by
    unfold chunk
    rw [List.map_map]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    simp only [List.mem_range] at hb
    simp only [Function.comp, eval_bin, ap_mul, eval_c, hbits b hb]
    have : 2 ^ b ≤ 16 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show b ≤ 4 by omega); simpa using this
    rw [min_eq_left (by omega : 2 ^ b ≤ C)]
    split_ifs <;> simp <;> omega
  have hts : (tokSum p).eval x C ρ = chunk w pv := by
    rw [tokSum, foldr_add_eval _ (by rw [hsum]; have := chunk_le w pv; omega), hsum]
  have hg' : (Ex.bin .lt (.bin .add (.bin .mul (.c 5) p) (.c 4)) (.v vN) : Ex V).eval x C ρ = 1 := by
    simp only [eval_bin, ap_lt, ap_add, ap_mul, eval_c, eval_v, hN]
    simp (disch := omega) only [min_eq_left]
    exact if_pos hp
  unfold tokE
  rw [eval_iteE _ _ _ (Or.inr hg') (by rw [hts]; have := chunk_le w pv; omega) (by simp),
    if_pos hg', hts]

/-- error flag of the decoding -/
abbrev vBad : Fin V := 44
/-- loop counter of the decoding and of the answers -/
abbrev aI : Fin V := 51

/-- One step of the decoding check. -/
def badBody : Pr V := .ite (.bin .lt (.c 28) (tokE (.v aI))) (.set vBad (.c 1)) .skip

/-- `vBad := 1` iff some block has value `≥ 29`. -/
def badP : Pr V := .seq (.set vBad (.c 0)) (.loop aI (.v vL) badBody)

lemma sp_badP {w : Word} {q : ℕ} {a : List Bool} {C : ℕ} {ρ : Fin V → ℕ} (hq : q ≤ a.length)
    (hC : 2 * (pack w q a).length + 40 ≤ C) (hN : ρ vN = w.length) (hL : ρ vL = w.length / 5) :
    Sp (pack w q a) C badP ρ [vBad, aI] []
      (fun r => r vBad = if ∀ p < w.length / 5, chunk w p < 29 then 0 else 1) := by
  have hlen := pack_length w q a hq
  unfold badP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vBad 0)
    (by decide) (by simp)) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  have := sp_loop_inv (x := pack w q a) (C := C) aI (.v vL) badBody (Function.update ρ vBad 0)
    [vBad, aI] (fun k r => r vBad = if ∀ p < k, chunk w p < 29 then 0 else 1) (by decide)
    (by simp) (fun k hk r fr hI => by
      simp only [eval_v, Function.update_of_ne (show vL ≠ vBad by decide), hL] at hk
      have hN' : (Function.update r aI k) vN = w.length := by
        rw [Function.update_of_ne (by decide), fr vN (by decide),
          Function.update_of_ne (by decide), hN]
      have ht := eval_tokE_raw w q a C (Function.update r aI k) (.v aI) hq hC hN'
        (by simp; omega)
      simp only [eval_v, Function.update_self] at ht
      unfold badBody
      have hcl := chunk_le w k
      by_cases hc : chunk w k < 29
      · refine sp_ite_neg (by simp [ht, min_eq_left (show 28 ≤ C by omega)]; omega)
          (sp_skip ?_)
        beta_reduce
        rw [Function.update_of_ne (by decide), hI]
        congr 1
        apply propext
        constructor
        · intro h p hp
          rcases Nat.lt_succ_iff_lt_or_eq.1 hp with hp | rfl
          · exact h p hp
          · exact hc
        · intro h p hp; exact h p (by omega)
      · refine sp_ite_pos (by simp [ht, min_eq_left (show 28 ≤ C by omega)]; omega)
          (sp_set (by decide) ?_)
        beta_reduce
        rw [Function.update_self, if_neg (fun h => hc (h k (by omega)))]
        simp [min_eq_left (show 1 ≤ C by omega)])
  refine this.mono (fun _ h => h) (fun r _ h => ?_)
  rw [h]
  simp (disch := decide) [Function.update_of_ne, hL]

end SQ

end PathChecking
