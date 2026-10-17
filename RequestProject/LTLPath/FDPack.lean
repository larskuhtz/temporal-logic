module

public import RequestProject.LTLPath.FDLib
public import RequestProject.ACRound.Pack

/-!
# Reading packed inputs

Terms reading the parts of an input `pack w q a`: the length `|w|` (`nwT`), the bits of `w`, the
token codes of `w` (`wcodeT`, five bits per token), the length of `a`, the answers `a` and the
query index `q`.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL CTLP

/-- Bit `i` of the input (`3` past the end). -/
def xbitT (i : T) : T := inpT (addT i (cT 1))

/-- `|w|` for inputs `pack w q a`. -/
def nwT : T := findT lenT fun i => neT (xbitT i) (cT 1)

/-- Bit `k` of `w`. -/
def wbitT (k : T) : T := xbitT (addT (addT nwT (cT 1)) k)

/-- Token code from five bits. -/
def code5 (b0 b1 b2 b3 b4 : ℕ) : ℕ := b0 + (2 * b1 + (4 * b2 + (8 * b3 + 16 * b4)))

/-- Code of token `p` of `w` (`29` if `w` has fewer than `5 (p + 1)` bits). -/
def wcode (w : Word) (p : ℕ) : ℕ :=
  if 5 * p + 5 ≤ w.length then
    code5 (w.getD (5 * p) false).toNat (w.getD (5 * p + 1) false).toNat
      (w.getD (5 * p + 2) false).toNat (w.getD (5 * p + 3) false).toNat
      (w.getD (5 * p + 4) false).toNat
  else 29

/-- Term for the code of token `p` of `w`. -/
def wcodeT (p : T) : T := lettT p fun pv =>
  iteT (leT (addT (mulT (cT 5) pv) (cT 5)) nwT)
    (addT (wbitT (mulT (cT 5) pv)) (addT (mulT (cT 2) (wbitT (addT (mulT (cT 5) pv) (cT 1))))
      (addT (mulT (cT 4) (wbitT (addT (mulT (cT 5) pv) (cT 2))))
        (addT (mulT (cT 8) (wbitT (addT (mulT (cT 5) pv) (cT 3))))
          (mulT (cT 16) (wbitT (addT (mulT (cT 5) pv) (cT 4))))))))
    (cT 29)

/-- `|a|` for inputs `pack w q a`. -/
def aLenT : T := divT (subT lenT (addT (mulT (cT 2) nwT) (cT 1))) (cT 2)

/-- Answer `k` (`0` if `k ≥ |a|`). -/
def ansT (k : T) : T := lettT k fun kv =>
  iteT (ltT kv aLenT) (xbitT (addT (addT (mulT (cT 2) nwT) (cT 1)) kv)) (cT 0)

/-- The query index `q`. -/
def qT : T := subT aLenT (findT aLenT fun k =>
  eqT (xbitT (addT (addT (addT (mulT (cT 2) nwT) (cT 1)) aLenT) k)) (cT 1))

/-! ## Denotations -/

variable {x : Word} {Γ : Ctx} {w : Word} {q : ℕ} {a : List Bool}

lemma symNum_bit (x : Word) (i : ℕ) (b : Bool) (h : x[i]? = some b) :
    symNum (inputSym x (i + 1)) = b.toNat := by
  rw [SQ.symNum_some x i b h]; cases b <;> rfl

lemma den_xbit {i : T} {I : ℕ} (hi : Den x Γ i I) : Den x Γ (xbitT i) (symNum (inputSym x (I + 1))) :=
  den_inp (den_add hi (den_c 1))

lemma den_nw (hx : x = pack w q a) : Den x Γ nwT w.length := by
  subst hx
  refine (show findF _ _ = w.length from ?_) ▸ den_find den_len (fun k i _ => den_ne (den_xbit den_var0)
    (den_c 1))
  refine findF_eq_of_spec (by rw [SQ.pack_eq]; simp) (fun h => ?_) (fun j hj => ?_)
  · rw [symNum_bit _ _ false (SQ.pack_get_sep w q a)]; simp
  · rw [symNum_bit _ _ true (SQ.pack_get_unary w q a hj)]; simp

lemma den_wbit (hx : x = pack w q a) {k : T} {K : ℕ} (hk : Den x Γ k K) (hK : K < w.length) :
    Den x Γ (wbitT k) (w.getD K false).toNat := by
  have := den_xbit (den_add (den_add (den_nw (Γ := Γ) hx) (den_c 1)) hk)
  convert this using 1
  subst hx
  rw [symNum_bit _ _ (w[K]'hK) (by rw [SQ.pack_get_w w q a hK]; simp [hK])]
  simp [List.getD_eq_getElem?_getD, hK]

lemma den_wcode (hx : x = pack w q a) {p : T} {P : ℕ} (hp : Den x Γ p P) :
    Den x Γ (wcodeT p) (wcode w P) := by
  refine den_lett hp fun k => ?_
  have hv : Den x ((k, P) :: Γ) (varT k) P := den_var0
  have hc := den_le (den_add (den_mul (den_c 5) hv) (den_c 5)) (den_nw (Γ := (k, P) :: Γ) hx)
  refine den_ite_eq hc (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    unfold wcode; rw [if_pos h]
    have b := fun (j : ℕ) (hj : j < 5) => den_wbit (Γ := (k, P) :: Γ) hx
      (den_add (den_mul (den_c 5) hv) (den_c j)) (by omega)
    have b0 := den_wbit (Γ := (k, P) :: Γ) hx (den_mul (den_c 5) hv) (by omega)
    unfold code5
    exact den_add b0 (den_add (den_mul (den_c 2) (b 1 (by omega))) (den_add (den_mul (den_c 4)
      (b 2 (by omega))) (den_add (den_mul (den_c 8) (b 3 (by omega)))
        (den_mul (den_c 16) (b 4 (by omega))))))
  · simp only [bv_eq_zero] at h
    unfold wcode; rw [if_neg h]; exact den_c 29

lemma code5_eq (c : ℕ) (hc : c < 32) : code5 (c.testBit 0).toNat (c.testBit 1).toNat
    (c.testBit 2).toNat (c.testBit 3).toNat (c.testBit 4).toNat = c := by
  interval_cases c <;> decide

/-- Token codes of an encoded token list. -/
lemma wcode_encodeToks (ts : List Tok) (p : ℕ) : wcode (encodeToks ts) p = tc ts p := by
  unfold wcode
  rw [SQ.encodeToks_length]
  by_cases hp : p < ts.length
  · rw [if_pos (by omega)]
    have hb : ∀ b < 5, (encodeToks ts).getD (5 * p + b) false = (ts[p]).code.testBit b := by
      intro b hb
      rw [List.getD_eq_getElem?_getD, SQ.encodeToks_getElem? ts p b hp hb]; rfl
    rw [show 5 * p = 5 * p + 0 by rfl, hb 0 (by omega), hb 1 (by omega), hb 2 (by omega),
      hb 3 (by omega), hb 4 (by omega), code5_eq _ (by have := Tok.code_lt ts[p]; omega)]
    simp [tc, List.getElem?_eq_getElem hp]
  · rw [if_neg (by omega)]
    simp [tc, List.getElem?_eq_none (show ts.length ≤ p by omega)]

lemma den_aLen (hx : x = pack w q a) (hq : q ≤ a.length) : Den x Γ aLenT a.length := by
  have := den_div (den_sub (den_len (x := x) (Γ := Γ)) (den_add (den_mul (den_c 2) (den_nw hx))
    (den_c 1))) (den_c 2)
  convert this using 1
  subst hx
  rw [pack_length w q a hq]; omega

lemma den_ans (hx : x = pack w q a) (hq : q ≤ a.length) {k : T} {K : ℕ} (hk : Den x Γ k K) :
    Den x Γ (ansT k) (a.getD K false).toNat := by
  refine den_lett hk fun kk => ?_
  have hv : Den x ((kk, K) :: Γ) (varT kk) K := den_var0
  refine den_ite_eq (den_lt' hv (den_aLen hx hq)) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    have := den_xbit (den_add (den_add (den_mul (den_c 2) (den_nw (Γ := (kk, K) :: Γ) hx))
      (den_c 1)) hv)
    convert this using 1
    subst hx
    rw [symNum_bit _ _ (a[K]'h) (by rw [SQ.pack_get_a w q a h]; simp [h])]
    simp [List.getD_eq_getElem?_getD, h]
  · simp only [bv_eq_zero] at h
    refine (den_c 0).of_eq ?_
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show a.length ≤ K by omega)]

lemma den_q (hx : x = pack w q a) (hq : q ≤ a.length) : Den x Γ qT q := by
  have hA := den_aLen (Γ := Γ) hx hq
  refine (show a.length - findF a.length _ = q from ?_) ▸ den_sub hA (den_find hA fun k i hi =>
    den_eq' (den_xbit (den_add (den_add (den_add (den_mul (den_c 2) (den_nw hx)) (den_c 1))
      (hA.cons _)) den_var0)) (den_c 1))
  subst hx
  have key : ∀ i < a.length, symNum (inputSym (pack w q a) (2 * w.length + 1 + a.length + i + 1)) =
      (decide (a.length - q ≤ i)).toNat := fun i hi =>
    symNum_bit _ _ _ (SQ.pack_get_q w q a hq hi)
  rw [findF_eq_of_spec (k := a.length - q) (by omega) (fun h => ?_) (fun j hj => ?_)]
  · omega
  · rw [key _ (by omega)]; simp
  · rw [key _ (by omega)]; simp; omega

end FD

end PathChecking
