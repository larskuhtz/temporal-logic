module

public import RequestProject.Shallow.Prog.Query

/-!
# The prologue of the round programs

Reading `|w|`, the number of tokens, the query index `q`, the root position and the depth bound
from a packed input `pack w q a`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {w : Word} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- done flag of `lenP` -/
abbrev vDn : Fin V := 57
/-- loop counter of the prologue -/
abbrev vI4 : Fin V := 58
/-- `|a|` -/
abbrev vA : Fin V := 59
/-- `q` -/
abbrev vQ : Fin V := 60
/-- power of two in `logP` -/
abbrev vP : Fin V := 61
/-- `⌊log₂ |w|⌋` -/
abbrev vLg : Fin V := 62

lemma eval_bitE_of {x : Word} {ρ : Fin V → ℕ} (e : Ex V) {i : ℕ} {b : Bool}
    (he : e.eval x C ρ = i) (hC : i + 1 ≤ C) (hb : x[i]? = some b) :
    (bitE e).eval x C ρ = if b then 1 else 0 := by
  simp only [bitE, eval_inp, eval_bin, ap_add, eval_c, he]
  rw [min_eq_left (show 1 ≤ C by omega), min_eq_left hC, symNum_some x i b hb]

/-! ## `|w|` -/

/-- `vN := |w|` (number of leading `1`s). -/
def lenBody : Pr V :=
  .ite (.v vDn) .skip (.ite (.bin .eq (bitE (.v vI4)) (.c 1))
      (.set vN (.bin .add (.v vN) (.c 1))) (.set vDn (.c 1)))

/-- `vN := |w|` (number of leading `1`s). -/
def lenP : Pr V :=
  .seq (.set vN (.c 0)) (.seq (.set vDn (.c 0)) (.loop vI4 .len lenBody))

lemma sp_lenP (hq : q ≤ a.length) (hC : 2 * (pack w q a).length + 40 ≤ C) :
    Sp (pack w q a) C lenP ρ [vN, vDn, vI4] [] (fun r => r vN = w.length) := by
  have hlen := pack_length w q a hq
  unfold lenP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vN 0)
    (by decide) (by simp)) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r vN = 0 ∧ r vDn = 0)
    (by decide) (by simp (disch := decide) [Function.update_of_ne])) (fun ρ2 _ h2 => ?_) rfl
  have := sp_loop_inv (x := pack w q a) (C := C) vI4 .len lenBody ρ2 [vN, vDn, vI4]
    (fun i r => r vN = min i w.length ∧ r vDn = if i ≤ w.length then 0 else 1) (by decide)
    (by simp [h2.1, h2.2]) (fun k hk ρ' _ hI => by
      simp only [eval_len] at hk
      have hk' : k < (pack w q a).length := lt_of_lt_of_le hk (min_le_left _ _)
      have e1 : Function.update ρ' vI4 k vDn = ρ' vDn := Function.update_of_ne (by decide) _ _
      have e2 : Function.update ρ' vI4 k vN = ρ' vN := Function.update_of_ne (by decide) _ _
      unfold lenBody
      rcases lt_trichotomy k w.length with hlt | heq | hgt
      · have hb := eval_bitE_of (x := pack w q a) (C := C) (ρ := Function.update ρ' vI4 k)
          (.v vI4) (by simp) (by omega) (pack_get_unary w q a hlt)
        refine sp_ite_neg (by simp [e1, hI.2, show k ≤ w.length by omega]) ?_
        refine sp_ite_pos (by simp [hb, min_eq_left (show 1 ≤ C by omega)]) ?_
        refine sp_set (by decide) ⟨?_, ?_⟩
        · simp only [Function.update_self, eval_bin, ap_add, eval_v, eval_c, e2, hI.1]
          rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega), min_eq_left (by omega),
            min_eq_left (by omega)]
        · rw [Function.update_of_ne (by decide), e1, hI.2, if_pos (by omega), if_pos (by omega)]
      · subst heq
        have hb := eval_bitE_of (x := pack w q a) (C := C) (ρ := Function.update ρ' vI4 w.length)
          (.v vI4) (by simp) (by omega) (pack_get_sep w q a)
        refine sp_ite_neg (by simp [e1, hI.2]) ?_
        refine sp_ite_neg (by simp [hb, min_eq_left (show 1 ≤ C by omega)]) ?_
        refine sp_set (by decide) ⟨?_, ?_⟩
        · rw [Function.update_of_ne (by decide), e2, hI.1]; omega
        · simp [min_eq_left (show 1 ≤ C by omega)]
      · refine sp_ite_pos (by simp [e1, hI.2, show ¬ k ≤ w.length by omega]) (sp_skip ⟨?_, ?_⟩)
        · rw [e2, hI.1]; omega
        · rw [e1, hI.2, if_neg (by omega), if_neg (by omega)])
  refine this.mono (fun _ h => h) (fun r _ h => ?_)
  rw [h.1, eval_len, min_eq_left (show (pack w q a).length ≤ C by omega)]
  omega

/-! ## `q` -/

/-- `vA := |a|`, `vQ := q` (number of `1`s in the last `|a|` positions). -/
def qBody : Pr V :=
  .ite (.bin .eq (bitE (.bin .add (.bin .add (.bin .add (.bin .mul (.c 2) (.v vN)) (.c 1))
        (.v vA)) (.v vI4))) (.c 1))
      (.set vQ (.bin .add (.v vQ) (.c 1))) .skip

/-- `vA := |a|`, `vQ := q` (number of `1`s in the last `|a|` positions). -/
def qP : Pr V :=
  .seq (.set vA (.bin .div (.bin .sub (.bin .sub .len (.bin .mul (.c 2) (.v vN))) (.c 1)) (.c 2)))
  (.seq (.set vQ (.c 0)) (.loop vI4 (.v vA) qBody))

lemma sp_qP (hq : q ≤ a.length) (hC : 2 * (pack w q a).length + 40 ≤ C)
    (hN : ρ vN = w.length) :
    Sp (pack w q a) C qP ρ [vA, vQ, vI4] [] (fun r => r vQ = q ∧ r vA = a.length) := by
  have hlen := pack_length w q a hq
  unfold qP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vA a.length)
    (by decide) (by
      congr 1
      simp only [eval_bin, ap_div, ap_sub, ap_mul, eval_len, eval_c, eval_v, hN]
      rw [min_eq_left (show 2 ≤ C by omega), min_eq_left (show 1 ≤ C by omega),
        min_eq_left (show (pack w q a).length ≤ C by omega),
        min_eq_left (show 2 * w.length ≤ C by omega), hlen]
      omega)) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  refine sp_seqE (o1 := []) (o2 := [])
    (sp_set (Q := fun r => r = Function.update (Function.update ρ vA a.length) vQ 0)
    (by decide) (by simp)) (fun ρ2 _ h2 => ?_) rfl
  subst h2
  set ρ2 := Function.update (Function.update ρ vA a.length) vQ 0
  have hA2 : ρ2 vA = a.length := by simp (disch := decide) [ρ2, Function.update_of_ne]
  have hN2 : ρ2 vN = w.length := by simp (disch := decide) [ρ2, Function.update_of_ne, hN]
  have := sp_loop_inv (x := pack w q a) (C := C) vI4 (.v vA) qBody ρ2 [vA, vQ, vI4]
    (fun i r => r vQ = i - (a.length - q) ∧ r vA = a.length ∧ r vN = w.length) (by decide)
    (by simp (disch := decide) [ρ2, Function.update_of_ne, hN]) (fun k hk ρ' _ hI => by
      simp only [eval_v, hA2] at hk
      have e1 : Function.update ρ' vI4 k vQ = ρ' vQ := Function.update_of_ne (by decide) _ _
      have e2 : Function.update ρ' vI4 k vA = ρ' vA := Function.update_of_ne (by decide) _ _
      have e3 : Function.update ρ' vI4 k vN = ρ' vN := Function.update_of_ne (by decide) _ _
      have hpos : (Ex.bin .add (.bin .add (.bin .add (.bin .mul (.c 2) (.v vN)) (.c 1))
          (.v vA)) (.v vI4) : Ex V).eval (pack w q a) C (Function.update ρ' vI4 k) =
            2 * w.length + 1 + a.length + k := by
        simp only [eval_bin, ap_add, ap_mul, eval_c, eval_v, e2, e3, hI.2.1, hI.2.2,
          Function.update_self]
        rw [min_eq_left (show 2 ≤ C by omega), min_eq_left (show 1 ≤ C by omega)]
        simp (disch := omega) only [min_eq_left]
      have hb := eval_bitE_of (x := pack w q a) (C := C) _ hpos (by omega)
        (pack_get_q w q a hq hk)
      unfold qBody
      by_cases hd : a.length - q ≤ k
      · refine sp_ite_pos (by simp [hb, hd, min_eq_left (show 1 ≤ C by omega)])
          (sp_set (by decide) ⟨?_, ?_, ?_⟩)
        · simp only [Function.update_self, eval_bin, ap_add, eval_v, eval_c, e1, hI.1]
          rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega)]; omega
        · rw [Function.update_of_ne (by decide), e2, hI.2.1]
        · rw [Function.update_of_ne (by decide), e3, hI.2.2]
      · refine sp_ite_neg (by simp [hb, hd, min_eq_left (show 1 ≤ C by omega)])
          (sp_skip ⟨?_, ?_, ?_⟩)
        · rw [e1, hI.1]; omega
        · rw [e2, hI.2.1]
        · rw [e3, hI.2.2])
  refine this.mono (fun _ h => h) (fun r _ h => ?_)
  simp only [eval_v, hA2] at h
  exact ⟨by rw [h.1]; omega, h.2.1⟩

/-! ## The depth bound -/

/-- `vLg := ⌊log₂ |w|⌋` (`|w|` in `vN`). -/
def logBody : Pr V :=
  .ite (.bin .lt (.bin .mul (.v vP) (.c 2)) (.bin .add (.v vN) (.c 1)))
      (.seq (.set vP (.bin .mul (.v vP) (.c 2))) (.set vLg (.bin .add (.v vLg) (.c 1)))) .skip

/-- `vLg := ⌊log₂ |w|⌋` (`|w|` in `vN`). -/
def logP : Pr V :=
  .seq (.set vP (.c 1)) (.seq (.set vLg (.c 0)) (.loop vI4 (.v vN) logBody))

lemma sp_logP {x : Word} (hC : 2 * ρ vN + 4 ≤ C) :
    Sp x C logP ρ [vP, vLg, vI4] [] (fun r => r vLg = Nat.log 2 (ρ vN)) := by
  unfold logP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vP 1)
    (by decide) (by simp [min_eq_left (show 1 ≤ C by omega)])) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  refine sp_seqE (o1 := []) (o2 := [])
    (sp_set (Q := fun r => r = Function.update (Function.update ρ vP 1) vLg 0)
    (by decide) (by simp)) (fun ρ2 _ h2 => ?_) rfl
  subst h2
  set n := ρ vN
  set ρ2 := Function.update (Function.update ρ vP 1) vLg 0
  have hN2 : ρ2 vN = n := by simp (disch := decide) [ρ2, Function.update_of_ne, n]
  have hlog := Nat.log_le_self 2 n
  have := sp_loop_inv (x := x) (C := C) vI4 (.v vN) logBody ρ2 [vP, vLg, vI4]
    (fun i r => r vLg = min i (Nat.log 2 n) ∧ r vP = 2 ^ r vLg ∧ r vN = n) (by decide)
    (by simp (disch := decide) [ρ2, Function.update_of_ne, n]) (fun k hk ρ' _ hI => by
      simp only [eval_v, hN2] at hk
      have e1 : Function.update ρ' vI4 k vP = ρ' vP := Function.update_of_ne (by decide) _ _
      have e2 : Function.update ρ' vI4 k vLg = ρ' vLg := Function.update_of_ne (by decide) _ _
      have e3 : Function.update ρ' vI4 k vN = ρ' vN := Function.update_of_ne (by decide) _ _
      obtain ⟨h1, h2, h3⟩ := hI
      have hpl : 2 ^ ρ' vLg ≤ max n 1 := by
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · rw [h0] at h1; simp at h1; rw [h1]; simp
        · calc 2 ^ ρ' vLg ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ ≤ n := Nat.pow_log_le_self 2 (by omega)
            _ ≤ max n 1 := le_max_left _ _
      have hcond : (Ex.bin .lt (.bin .mul (.v vP) (.c 2)) (.bin .add (.v vN) (.c 1)) : Ex V).eval
          x C (Function.update ρ' vI4 k) = if 2 ^ (ρ' vLg + 1) ≤ n then 1 else 0 := by
        simp only [eval_bin, ap_lt, ap_mul, ap_add, eval_c, eval_v, e1, e3, h2, h3]
        rw [min_eq_left (show 2 ≤ C by omega), min_eq_left (show 1 ≤ C by omega),
          min_eq_left (show n + 1 ≤ C by omega), min_eq_left (show 2 ^ ρ' vLg * 2 ≤ C by omega),
          pow_succ]
        by_cases h : 2 ^ ρ' vLg * 2 ≤ n
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      unfold logBody
      by_cases hc : 2 ^ (ρ' vLg + 1) ≤ n
      · have hlt : ρ' vLg < Nat.log 2 n := by
          by_contra hge
          have := Nat.lt_pow_succ_log_self (show 1 < 2 by norm_num) n
          have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show Nat.log 2 n + 1 ≤ ρ' vLg + 1 by
            omega)
          omega
        refine sp_ite_pos (by rw [hcond, if_pos hc]; simp) ?_
        refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update
          (Function.update ρ' vI4 k) vP (2 ^ (ρ' vLg + 1))) (by decide) (by
            congr 1
            simp only [eval_bin, ap_mul, eval_v, eval_c, e1, h2]
            rw [min_eq_left (show 2 ≤ C by omega), pow_succ]
            exact min_eq_left (by rw [← pow_succ]; omega))) (fun ρ3 _ h3 => ?_) rfl
        subst h3
        refine sp_set (by decide) ⟨?_, ?_, ?_⟩
        · simp only [Function.update_self, eval_bin, ap_add, eval_v, eval_c,
            Function.update_of_ne (show vLg ≠ vP by decide), e2, h1]
          rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega)]; omega
        · simp only [Function.update_self, Function.update_of_ne (show vP ≠ vLg by decide)]
          simp only [eval_bin, ap_add, eval_v, eval_c, Function.update_of_ne
            (show vLg ≠ vP by decide), e2]
          rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (by omega)]
        · simp only [Function.update_of_ne (show vN ≠ vLg by decide),
            Function.update_of_ne (show vN ≠ vP by decide), e3, h3]
      · refine sp_ite_neg (by rw [hcond, if_neg hc]) (sp_skip ⟨?_, ?_, ?_⟩)
        · rw [e2, h1]
          have : Nat.log 2 n ≤ ρ' vLg := by
            by_contra hlt
            push_neg at hlt
            have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show ρ' vLg + 1 ≤ Nat.log 2 n
              by omega)
            have := Nat.pow_log_le_self 2 (show n ≠ 0 by
              intro h0; rw [h0] at hlt; simp at hlt)
            omega
          omega
        · rw [e1, e2, h2]
        · rw [e3, h3])
  refine this.mono (fun _ h => h) (fun r _ h => ?_)
  simp only [eval_v, hN2] at h
  rw [h.1]; omega

/-- `vD := (vLg + 1)^k`. -/
def powP (k : ℕ) : Pr V :=
  .seq (.set vD (.c 1)) (.loop vI4 (.c k) (.set vD (.bin .mul (.v vD) (.bin .add (.v vLg) (.c 1)))))

lemma sp_powP {x : Word} (k : ℕ) (hC : (ρ vLg + 1) ^ k + k + 1 ≤ C) :
    Sp x C (powP k) ρ [vD, vI4] [] (fun r => r vD = (ρ vLg + 1) ^ k) := by
  unfold powP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vD 1)
    (by decide) (by simp [min_eq_left (show 1 ≤ C by omega)])) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  have hL1 : Function.update ρ vD 1 vLg = ρ vLg := Function.update_of_ne (by decide) _ _
  have := sp_loop_inv (x := x) (C := C) vI4 (.c k)
    (.set vD (.bin .mul (.v vD) (.bin .add (.v vLg) (.c 1)))) (Function.update ρ vD 1) [vD, vI4]
    (fun i r => r vD = (ρ vLg + 1) ^ i ∧ r vLg = ρ vLg) (by decide)
    (by simp [hL1]) (fun i hi ρ' _ hI => by
      simp only [eval_c] at hi
      have e1 : Function.update ρ' vI4 i vD = ρ' vD := Function.update_of_ne (by decide) _ _
      have e2 : Function.update ρ' vI4 i vLg = ρ' vLg := Function.update_of_ne (by decide) _ _
      have hpow : (ρ vLg + 1) ^ (i + 1) ≤ (ρ vLg + 1) ^ k :=
        Nat.pow_le_pow_right (by omega) (by omega)
      refine sp_set (by decide) ⟨?_, ?_⟩
      · simp only [Function.update_self, eval_bin, ap_mul, ap_add, eval_v, eval_c, e1, e2, hI.1,
          hI.2]
        rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (show ρ vLg + 1 ≤ C by
          have : ρ vLg + 1 ≤ (ρ vLg + 1) ^ k ∨ k = 0 := by
            rcases Nat.eq_zero_or_pos k with h | h
            · exact Or.inr h
            · exact Or.inl (by
                calc ρ vLg + 1 = (ρ vLg + 1) ^ 1 := (pow_one _).symm
                  _ ≤ _ := Nat.pow_le_pow_right (by omega) h)
          rcases this with h | h
          · omega
          · omega), pow_succ]
        exact min_eq_left (by rw [← pow_succ]; omega)
      · rw [Function.update_of_ne (by decide), e2, hI.2])
  refine this.mono (fun _ h => h) (fun r _ h => ?_)
  simp only [eval_c] at h
  rw [min_eq_left (show k ≤ C by omega)] at h
  exact h.1

end SQ

end PathChecking
