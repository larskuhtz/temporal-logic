module

public import RequestProject.Shallow.Prog.SpLib
public import RequestProject.Shallow.Glue

/-!
# Emitting the letters of a branching query

`letterP` emits `letterToks ts m N u A ℓ'` for the node position `u` (in `vU`), the target
position `ℓ'` (in `vLp`), `m` (in `vM`), `N = |ts| + 1` (in `vNq`), where the answers `A` of the
previous round are read from the packed input.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

lemma sp_seqE {x : Word} {s t : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {o1 o2 o : List Bool}
    {Q1 Q : (Fin V → ℕ) → Prop} (h1 : Sp x C s ρ W o1 Q1)
    (h2 : ∀ ρ1, (∀ v, v ∉ W → ρ1 v = ρ v) → Q1 ρ1 → Sp x C t ρ1 W o2 Q)
    (e : o1 ++ o2 = o) : Sp x C (.seq s t) ρ W o Q :=
  e ▸ sp_seq h1 h2

/-- `m` (number of digits `1` prefixed to renamed atoms) -/
abbrev vM : Fin V := 32
/-- `N = |ts| + 1` -/
abbrev vNq : Fin V := 33
/-- result of `nxtP` -/
abbrev vC3 : Fin V := 34
/-- target position `ℓ'` of the current letter -/
abbrev vLp : Fin V := 35
/-- loop counter of `freshP` -/
abbrev vK3 : Fin V := 36
/-- value for `emitNat` -/
abbrev vZ : Fin V := 37
/-- temporary of `emitNat` -/
abbrev vZy : Fin V := 38
/-- loop counter of `emitNat` -/
abbrev vZi : Fin V := 39
/-- loop counter of `onesP` -/
abbrev vK4 : Fin V := 40
/-- position temporary of `labGAtP` -/
abbrev vX2 : Fin V := 41
/-- loop counter of `labGP` -/
abbrev vK5 : Fin V := 42
/-- length temporary of `labGP` -/
abbrev vE5 : Fin V := 43
/-- loop counter of `lettersP` -/
abbrev vK6 : Fin V := 44
/-- length temporary of `lettersP` -/
abbrev vE6 : Fin V := 45
/-- `ℓ` (target position of the query) -/
abbrev vLl : Fin V := 46

/-! ## Digits `1` -/

/-- Emit `m` digits `1` (`m` in `vM`). -/
def onesP : Pr V := .loop vK4 (.v vM) (outToks [Tok.one])

lemma flatMap_const_replicate (n : ℕ) (t : Tok) :
    (List.range n).flatMap (fun _ => encodeToks [t]) = encodeToks (List.replicate n t) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', LS.encodeToks_append]
    simp

lemma sp_onesP {x : Word} : Sp x C onesP ρ [vK4] (encodeToks (List.replicate (ρ vM) Tok.one))
    (fun _ => True) := by
  have := sp_loop (x := x) (C := C) vK4 (.v vM) (outToks [Tok.one]) ρ [vK4]
    (fun _ => encodeToks [Tok.one]) (by decide) (fun k _ ρ' _ => sp_outToks trivial)
  simpa [flatMap_const_replicate] using this

/-! ## One step towards a target -/

/-- `vC3 := nxt ts ℓ' u` (`u` in `vU`, `ℓ'` in `vLp`). -/
def nxtP : Pr V :=
  .seq (isLeafP (.v vU)) (.ite (.v vLf) (.set vC3 (.v vU))
    (.seq (tendP (.bin .add (.v vU) (.c 1))) (.seq (ctwP (.v sR) (.v vLp)) (.set vC3 (.v wC)))))

/-- Frame of `nxtP`. -/
abbrev nxtW : List (Fin V) := [vLf, sR, sP, sC, sD, sI, wC, wL, wD, wI, vC3]

lemma sp_nxtP (hE : Env ts q a C ρ) (hu : ρ vU ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C nxtP ρ nxtW [] (fun ρ' => ρ' vC3 = nxt ts (ρ vLp) (ρ vU)) := by
  have hC := hE.len_le
  unfold nxtP
  refine sp_seqE (o2 := []) ((sp_isLeafP hE (.v vU) (by simpa using hu)).mono (by decide)
    (fun _ _ h => h)) (fun ρ1 f1 h1 => ?_) rfl
  simp only [eval_v] at h1
  have hE1 := hE.of_frame f1 (by decide) (by decide)
  have hU1 : ρ1 vU = ρ vU := f1 _ (by decide)
  have hL1 : ρ1 vLp = ρ vLp := f1 _ (by decide)
  by_cases hl : isLeaf ts (ρ vU) = true
  · refine sp_ite_pos (by simp [h1, hl]) (sp_set (by decide) ?_)
    simp [nxt, hl, hU1]
  · refine sp_ite_neg (by simp [h1, hl]) ?_
    refine sp_seqE (o2 := []) ((sp_tendP hE1 (.bin .add (.v vU) (.c 1))
      (by simp only [eval_bin, ap_add, eval_v, eval_c, hU1]; omega)).mono (by decide)
      (fun _ _ h => h)) (fun ρ2 f2 h2 => ?_) rfl
    have hE2 := hE1.of_frame f2 (by decide) (by decide)
    have hU2 : ρ2 vU = ρ vU := (f2 _ (by decide)).trans hU1
    have hL2 : ρ2 vLp = ρ vLp := (f2 _ (by decide)).trans hL1
    have hev : (Ex.bin .add (.v vU) (.c 1) : Ex V).eval (pack (encodeToks ts) q a) C ρ1 =
        ρ vU + 1 := by
      simp only [eval_bin, ap_add, eval_v, eval_c, hU1]
      simp (disch := omega) only [min_eq_left]
    rw [hev] at h2
    refine sp_seqE (o2 := []) ((sp_ctwP hE2 (.v sR) (.v vLp)
      (by simp only [eval_v, h2]; exact tend_le_succ ts (by omega))).mono (by decide)
      (fun _ _ h => h)) (fun ρ3 f3 h3 => ?_) rfl
    refine sp_set (by decide) ?_
    simp only [eval_v, Function.update_self, h3, h2,
      Function.update_of_ne (show vLp ≠ wC by decide), hL2]
    simp [nxt, hl]

/-! ## Reading answers -/

/-- The answer bit `A c ℓ k` of the previous round (value in `{0, 1}`). -/
def ansE (c l k : Ex V) : Ex V :=
  .bin .mul (.bin .mul (.bin .lt c (.v vNq)) (.bin .mul (.bin .lt l (.v vNq)) (.bin .lt k (.v vNq))))
    (.inp (.bin .add (.bin .add (.bin .mul (.c 2) (.v vN)) (.c 2))
      (.bin .add (.bin .mul (.bin .add (.bin .mul c (.v vNq)) l) (.v vNq)) k)))

lemma eval_ansE (hE : Env ts q a C ρ) (hM : ρ vNq = ts.length + 1)
    (ha : (ts.length + 1) ^ 3 ≤ a.length) (c l k : Ex V) :
    (ansE c l k).eval (pack (encodeToks ts) q a) C ρ =
      if ansF (ts.length + 1) a (c.eval (pack (encodeToks ts) q a) C ρ)
        (l.eval (pack (encodeToks ts) q a) C ρ) (k.eval (pack (encodeToks ts) q a) C ρ)
      then 1 else 0 := by
  have hC := hE.hC
  rw [pack_length _ _ _ hE.hq, encodeToks_length] at hC
  set x := pack (encodeToks ts) q a
  set M := ts.length + 1
  generalize hcv : c.eval x C ρ = cv
  generalize hlv : l.eval x C ρ = lv
  generalize hkv : k.eval x C ρ = kv
  unfold ansE
  simp only [eval_bin, ap_mul, ap_lt, ap_add, eval_c, eval_v, eval_inp, hcv, hlv, hkv, hM,
    hE.hN]
  by_cases hg : cv < M ∧ lv < M ∧ kv < M
  · obtain ⟨h1, h2, h3⟩ := hg
    have hq3 := qIdx_lt h1 h2 h3
    have hM3 : M * M * M = M ^ 3 := by ring
    have hb1 : cv * M ≤ M * M := Nat.mul_le_mul_right _ h1.le
    have hb2 : (cv * M + lv) * M ≤ M * M * M := Nat.mul_le_mul_right _ (by nlinarith)
    have hMC : M ^ 3 ≤ C := by omega
    simp only [if_pos h1, if_pos h2, if_pos h3]
    rw [min_eq_left (show cv * M ≤ C by nlinarith), min_eq_left (show cv * M + lv ≤ C by nlinarith),
      min_eq_left (show (cv * M + lv) * M ≤ C by nlinarith)]
    have hidx : qIdx M cv lv kv < a.length := lt_of_lt_of_le hq3 ha
    have hget := pack_get_a (encodeToks ts) q a hidx
    rw [encodeToks_length, List.getElem?_eq_getElem hidx] at hget
    rw [show (cv * M + lv) * M + kv = qIdx M cv lv kv from rfl]
    revert hget
    generalize hI : qIdx M cv lv kv = I at hidx ⊢
    intro hget
    simp (disch := omega) only [min_eq_left, one_mul]
    rw [show 2 * (5 * ts.length) + 2 + I = (2 * (5 * ts.length) + 1 + I) + 1 by omega,
      symNum_some x _ _ hget]
    simp only [ansF, h1, h2, h3, and_self, if_true, List.getD_eq_getElem?_getD, hI,
      List.getElem?_eq_getElem hidx, Option.getD_some]
    split_ifs <;> omega
  · have : ¬ (cv < M ∧ lv < M ∧ kv < M) := hg
    have h0 : min ((if cv < M then 1 else 0) * min ((if lv < M then 1 else 0) *
        (if kv < M then 1 else 0)) C) C = 0 := by
      by_cases h1 : cv < M <;> by_cases h2 : lv < M <;> by_cases h3 : kv < M <;> simp_all
    rw [h0]
    simp only [ansF, if_neg hg, zero_mul, Nat.zero_min]
    simp

/-! ## Fresh names -/

/-- Emit `freshToks N (A c ℓ')` (`c` in `vC3`, `ℓ'` in `vLp`, `N` in `vNq`). -/
def freshBody : Pr V :=
  .ite (ansE (.v vC3) (.v vLp) (.v vK3))
    (.seq (.set vZ (.bin .add (.v vK3) (.c 1))) (emitNat vZ vZy vZi)) .skip

/-- Emit `freshToks N (A c ℓ')` (`c` in `vC3`, `ℓ'` in `vLp`, `N` in `vNq`). -/
def freshP : Pr V := .loop vK3 (.v vNq) freshBody

/-- Frame of `freshP`. -/
abbrev freshW : List (Fin V) := [vK3, vZ, vZy, vZi]

lemma sp_freshP (hE : Env ts q a C ρ) (hM : ρ vNq = ts.length + 1)
    (ha : (ts.length + 1) ^ 3 ≤ a.length) :
    Sp (pack (encodeToks ts) q a) C freshP ρ freshW
      (encodeToks (freshToks (ts.length + 1) (ansF (ts.length + 1) a (ρ vC3) (ρ vLp))))
      (fun _ => True) := by
  have hC := hE.len_le
  have := sp_loop (x := pack (encodeToks ts) q a) (C := C) vK3 (.v vNq) freshBody ρ freshW
    (fun k => encodeToks (if ansF (ts.length + 1) a (ρ vC3) (ρ vLp) k then natToks (k + 1) else []))
    (by decide) (fun k hk ρ' f' => by
      simp only [eval_v, hM] at hk
      have hE' : Env ts q a C (Function.update ρ' vK3 k) :=
        (hE.of_frame f' (by decide) (by decide)).congr (Function.update_of_ne (by decide) _ _)
          (Function.update_of_ne (by decide) _ _)
      have hM' : (Function.update ρ' vK3 k) vNq = ts.length + 1 := by
        rw [Function.update_of_ne (by decide), f' _ (by decide), hM]
      have hev := eval_ansE hE' hM' ha (.v vC3) (.v vLp) (.v vK3)
      simp only [eval_v, Function.update_self, Function.update_of_ne (show vC3 ≠ vK3 by decide),
        Function.update_of_ne (show vLp ≠ vK3 by decide), f' vC3 (by decide),
        f' vLp (by decide)] at hev
      unfold freshBody
      by_cases hb : ansF (ts.length + 1) a (ρ vC3) (ρ vLp) k = true
      · refine sp_ite_pos (by rw [hev, if_pos hb]; simp) ?_
        simp only [hb, if_true]
        refine sp_seqE (o1 := []) (o2 := encodeToks (natToks (k + 1))) (sp_set (Q := fun r => r vZ = k + 1) (by decide) (by
            simp only [Function.update_self, eval_bin, ap_add, eval_v, eval_c]
            simp (disch := omega) only [min_eq_left])) (fun ρ1 _ h1 => ?_) (by simp)
        have := (sp_emitNat (x := pack (encodeToks ts) q a) (C := C) (ρ := ρ1) vZ vZy vZi
          (by decide) (by omega)).mono (W' := freshW) (by decide) (fun _ _ h => h)
        rw [h1] at this
        exact this
      · refine sp_ite_neg (by rw [hev, if_neg hb]) ?_
        simp only [hb]
        exact sp_skip trivial)
  simp only [eval_v, hM] at this
  simpa [freshP, freshToks, encodeToks_flatMap] using this

/-! ## Renamed labels -/

/-- Emit `labGAt ts m p` (`m` in `vM`). -/
def labGAtP (p : Ex V) : Pr V :=
  .seq (.set vX2 p) (.seq (.ite (.bin .lt (.c 0) (.bin .add
      (.bin .eq (tokE (.bin .sub (.v vX2) (.c 1))) (.c 2))
      (.bin .eq (tokE (.bin .sub (.v vX2) (.c 1))) (.c 3)))) onesP .skip) (cpP (.v vX2)))

/-- Frame of `labGAtP`. -/
abbrev labGAtW : List (Fin V) := [vX2, vK4, vT]

lemma sp_labGAtP (hE : Env ts q a C ρ) (p : Ex V)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1) :
    Sp (pack (encodeToks ts) q a) C (labGAtP p) ρ labGAtW
      (encodeToks (labGAt ts (ρ vM) (p.eval (pack (encodeToks ts) q a) C ρ))) (fun _ => True) := by
  have hC := hE.len_le
  unfold labGAtP
  generalize hpv : p.eval (pack (encodeToks ts) q a) C ρ = pv at hp
  refine sp_seqE (o1 := []) (o2 := encodeToks (labGAt ts (ρ vM) pv))
    (sp_set (Q := fun r => r = Function.update ρ vX2 pv) (by decide) (by rw [hpv]))
    (fun ρ1 _ h1 => ?_) (by simp)
  subst h1
  have hE1 : Env ts q a C (Function.update ρ vX2 pv) :=
    hE.congr (Function.update_of_ne (by decide) _ _) (Function.update_of_ne (by decide) _ _)
  have ht : (tokE (.bin .sub (.v vX2) (.c 1))).eval (pack (encodeToks ts) q a) C
      (Function.update ρ vX2 pv) = tc ts (pv - 1) := by
    rw [eval_tokE ts q a C _ _ hE1.hq hE1.hC hE1.hN (by simp; omega)]
    simp [min_eq_left (show 1 ≤ C by omega)]
  have hcond : (Ex.bin .lt (.c 0) (.bin .add
      (.bin .eq (tokE (.bin .sub (.v vX2) (.c 1))) (.c 2))
      (.bin .eq (tokE (.bin .sub (.v vX2) (.c 1))) (.c 3))) : Ex V).eval
        (pack (encodeToks ts) q a) C (Function.update ρ vX2 pv) =
      if (tc ts (pv - 1) = 2 ∨ tc ts (pv - 1) = 3) then 1 else 0 := by
    simp only [eval_bin, ap_lt, ap_add, ap_eq, eval_c, ht]
    rw [min_eq_left (show 2 ≤ C by omega), min_eq_left (show 3 ≤ C by omega),
      min_eq_left (show 0 ≤ C by omega)]
    by_cases h2 : tc ts (pv - 1) = 2 <;> by_cases h3 : tc ts (pv - 1) = 3 <;> simp [h2, h3] <;>
      omega
  have hMv : (Function.update ρ vX2 pv) vM = ρ vM := Function.update_of_ne (by decide) _ _
  rw [labGAt, LS.encodeToks_append]
  have hcont : ∀ ρ2 : Fin V → ℕ, (∀ v, v ∉ labGAtW → ρ2 v = Function.update ρ vX2 pv v) →
      (True ∧ ∀ v, v ∉ [vK4] → ρ2 v = Function.update ρ vX2 pv v) →
      Sp (pack (encodeToks ts) q a) C (cpP (.v vX2)) ρ2 labGAtW (encodeToks (cp ts pv))
        (fun _ => True) := by
    intro ρ2 f2 q2
    have hE2 : Env ts q a C ρ2 := hE1.of_frame f2 (by decide) (by decide)
    have hcp2 := (sp_cpP (ts := ts) (q := q) (a := a) (C := C) hE2 (.v vX2)).mono
      (W' := labGAtW) (by decide) (fun _ _ h => h)
    rwa [eval_v, q2.2 vX2 (by decide), Function.update_self] at hcp2
  by_cases hc : tc ts (pv - 1) = 2 ∨ tc ts (pv - 1) = 3
  · have h1 := (sp_onesP (x := pack (encodeToks ts) q a) (C := C)
      (ρ := Function.update ρ vX2 pv)).frame.mono (W' := labGAtW) (by decide) (fun _ _ h => h)
    rw [hMv] at h1
    rw [if_pos hc]
    exact sp_seqE (sp_ite_pos (by rw [hcond, if_pos hc]; simp) h1) hcont rfl
  · rw [if_neg hc]
    exact sp_seqE (sp_ite_neg (by rw [hcond, if_neg hc])
      (sp_skip ⟨trivial, fun _ _ => rfl⟩)) hcont (by simp [encodeToks])

/-- Emit `labG ts m u` (`u` in `vU`, `m` in `vM`). -/
def labGP : Pr V :=
  .seq (tendP (.bin .add (.v vU) (.c 1))) (.seq (.set vE5 (.bin .sub (.bin .sub (.v sR) (.c 1))
    (.bin .add (.v vU) (.c 2)))) (.loop vK5 (.v vE5)
      (labGAtP (.bin .add (.bin .add (.v vU) (.c 2)) (.v vK5)))))

/-- Frame of `labGP`. -/
abbrev labGW : List (Fin V) := [sR, sP, sC, sD, sI, vE5, vK5, vX2, vK4, vT]

lemma sp_labGP (hE : Env ts q a C ρ) (hu : ρ vU ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C labGP ρ labGW (encodeToks (labG ts (ρ vM) (ρ vU)))
      (fun _ => True) := by
  have hC := hE.len_le
  unfold labGP
  have hev : (Ex.bin .add (.v vU) (.c 1) : Ex V).eval (pack (encodeToks ts) q a) C ρ =
      ρ vU + 1 := by
    simp only [eval_bin, ap_add, eval_v, eval_c]; simp (disch := omega) only [min_eq_left]
  refine sp_seqE (o2 := encodeToks (labG ts (ρ vM) (ρ vU)))
    ((sp_tendP hE _ (by rw [hev]; omega)).mono (by decide) (fun _ _ h => h))
    (fun ρ1 f1 h1 => ?_) (by simp)
  rw [hev] at h1
  have hte := tend_le_succ ts (show ρ vU + 1 ≤ ts.length + 1 by omega)
  have hU1 : ρ1 vU = ρ vU := f1 _ (by decide)
  refine sp_seqE (o1 := []) (o2 := encodeToks (labG ts (ρ vM) (ρ vU)))
    (sp_set (Q := fun r => r vE5 = tend ts (ρ vU + 1) - 1 - (ρ vU + 2)) (by decide) (by
      simp only [Function.update_self, eval_bin, ap_sub, ap_add, eval_v, eval_c, h1, hU1]
      simp (disch := omega) only [min_eq_left])) (fun ρ2 f2 h2 => ?_) (by simp)
  have := sp_rng (x := pack (encodeToks ts) q a) (C := C) vK5 (.v vE5)
    (labGAtP (.bin .add (.bin .add (.v vU) (.c 2)) (.v vK5))) ρ2 labGW (ρ vU + 2)
    (labGAt ts (ρ vM)) (by decide) (fun k hk ρ' f' => by
      simp only [eval_v, h2] at hk
      have hE' : Env ts q a C (Function.update ρ' vK5 k) :=
        (hE.of_frame (fun v hv => (f' v hv).trans ((f2 v hv).trans (f1 v hv))) (by decide)
          (by decide)).congr (Function.update_of_ne (by decide) _ _)
          (Function.update_of_ne (by decide) _ _)
      have hU' : (Function.update ρ' vK5 k) vU = ρ vU := by
        rw [Function.update_of_ne (by decide), f' _ (by decide), f2 _ (by decide), hU1]
      have hM' : (Function.update ρ' vK5 k) vM = ρ vM := by
        rw [Function.update_of_ne (by decide), f' _ (by decide), f2 _ (by decide),
          f1 _ (by decide)]
      have hpe : (Ex.bin .add (.bin .add (.v vU) (.c 2)) (.v vK5) : Ex V).eval
          (pack (encodeToks ts) q a) C (Function.update ρ' vK5 k) = ρ vU + 2 + k := by
        simp only [eval_bin, ap_add, eval_v, eval_c, hU', Function.update_self]
        simp (disch := omega) only [min_eq_left]
      have := (sp_labGAtP hE' _ (by rw [hpe]; omega)).mono (W' := labGW) (by decide)
        (fun _ _ h => h)
      rwa [hpe, hM'] at this)
  simpa [h2, labG] using this

/-! ## Letters -/

/-- Emit `letterToks ts m N u A ℓ'`. -/
def letterP : Pr V :=
  .seq nxtP (.seq (outToks [Tok.lpar]) (.seq freshP (.seq labGP (outToks [Tok.rpar]))))

/-- Frame of `letterP`. -/
abbrev letterW : List (Fin V) :=
  [vLf, sR, sP, sC, sD, sI, wC, wL, wD, wI, vC3, vK3, vZ, vZy, vZi, vE5, vK5, vX2, vK4, vT]

lemma sp_letterP (hE : Env ts q a C ρ) (hM : ρ vNq = ts.length + 1)
    (ha : (ts.length + 1) ^ 3 ≤ a.length) (hu : ρ vU ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C letterP ρ letterW
      (encodeToks (letterToks ts (ρ vM) (ts.length + 1) (ρ vU) (ansF (ts.length + 1) a) (ρ vLp)))
      (fun _ => True) := by
  unfold letterP
  refine sp_seqE (o2 := encodeToks [Tok.lpar] ++ (encodeToks (freshToks (ts.length + 1)
      (ansF (ts.length + 1) a (nxt ts (ρ vLp) (ρ vU)) (ρ vLp))) ++
      (encodeToks (labG ts (ρ vM) (ρ vU)) ++ encodeToks [Tok.rpar])))
    ((sp_nxtP hE hu).mono (by decide) (fun _ _ h => h)) (fun ρ1 f1 h1 => ?_)
    (by simp [letterToks, encodeToks])
  have hE1 := hE.of_frame f1 (by decide) (by decide)
  refine sp_seqE (sp_outToks (Q := fun r => r = ρ1) rfl) (fun ρ2 _ h2 => ?_) rfl
  subst h2
  refine sp_seqE ((sp_freshP hE1 (by rw [f1 _ (by decide), hM]) ha).mono (by decide)
    (fun _ _ h => h)) (fun ρ3 f3 _ => ?_) (by rw [h1, f1 vLp (by decide)])
  have hE3 := hE1.of_frame f3 (by decide) (by decide)
  have hU3 : ρ3 vU = ρ vU := (f3 _ (by decide)).trans (f1 _ (by decide))
  have hM3 : ρ3 vM = ρ vM := (f3 _ (by decide)).trans (f1 _ (by decide))
  refine sp_seqE ((sp_labGP hE3 (by rw [hU3]; exact hu)).mono (by decide) (fun _ _ h => h))
    (fun ρ4 _ _ => sp_outToks trivial) (by rw [hU3, hM3])

/-- Emit the letter for `ℓ` (in `vLl`) followed by the letters for the positions of the
subtree at `u`. -/
def lettersP : Pr V :=
  .seq (.set vLp (.v vLl)) (.seq letterP (.seq (tendP (.v vU))
    (.seq (.set vE6 (.bin .sub (.v sR) (.v vU)))
      (.loop vK6 (.v vE6) (.seq (.set vLp (.bin .add (.v vU) (.v vK6))) letterP)))))

/-- Frame of `lettersP`. -/
abbrev lettersW : List (Fin V) := vLp :: vE6 :: vK6 :: letterW

lemma sp_lettersP (hE : Env ts q a C ρ) (hM : ρ vNq = ts.length + 1)
    (ha : (ts.length + 1) ^ 3 ≤ a.length) (hu : ρ vU ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C lettersP ρ lettersW
      (encodeToks (letterToks ts (ρ vM) (ts.length + 1) (ρ vU) (ansF (ts.length + 1) a) (ρ vLl) ++
        rng (ρ vU) (tend ts (ρ vU) - ρ vU)
          (letterToks ts (ρ vM) (ts.length + 1) (ρ vU) (ansF (ts.length + 1) a))))
      (fun _ => True) := by
  have hC := hE.len_le
  unfold lettersP
  set L := letterToks ts (ρ vM) (ts.length + 1) (ρ vU) (ansF (ts.length + 1) a)
  refine sp_seqE (o1 := []) (o2 := encodeToks (L (ρ vLl) ++ rng (ρ vU) (tend ts (ρ vU) - ρ vU) L))
    (sp_set (Q := fun r => r = Function.update ρ vLp (ρ vLl)) (by decide) rfl)
    (fun ρ1 _ h1 => ?_) (by simp)
  subst h1
  have hE1 : Env ts q a C (Function.update ρ vLp (ρ vLl)) :=
    hE.congr (Function.update_of_ne (by decide) _ _) (Function.update_of_ne (by decide) _ _)
  have e1 : ∀ v, v ≠ vLp → Function.update ρ vLp (ρ vLl) v = ρ v :=
    fun v hv => Function.update_of_ne hv _ _
  have h1 := (sp_letterP hE1 (by rw [e1 _ (by decide), hM]) ha (by rw [e1 _ (by decide)]; exact hu)).mono
    (W' := lettersW) (by decide) (fun _ _ h => h)
  rw [Function.update_self, e1 _ (by decide), e1 _ (by decide)] at h1
  rw [LS.encodeToks_append]
  refine sp_seqE h1 (fun ρ2 f2 _ => ?_) rfl
  have f2' : ∀ v, v ∉ lettersW → ρ2 v = ρ v := fun v hv =>
    (f2 v hv).trans (e1 v (ne_of_nmem hv (by decide)))
  have hE2 := hE.of_frame f2' (by decide) (by decide)
  have hU2 : ρ2 vU = ρ vU := f2' _ (by decide)
  refine sp_seqE (o2 := encodeToks (rng (ρ vU) (tend ts (ρ vU) - ρ vU) L))
    ((sp_tendP hE2 (.v vU) (by simp only [eval_v]; omega)).mono (by decide) (fun _ _ h => h))
    (fun ρ3 f3 h3 => ?_) (by simp)
  simp only [eval_v, hU2] at h3
  have hU3 : ρ3 vU = ρ vU := (f3 _ (by decide)).trans hU2
  have hte := tend_le' ts hu
  refine sp_seqE (o1 := []) (o2 := encodeToks (rng (ρ vU) (tend ts (ρ vU) - ρ vU) L))
    (sp_set (Q := fun r => r vE6 = tend ts (ρ vU) - ρ vU) (by decide) (by
      simp only [Function.update_self, eval_bin, ap_sub, eval_v, h3, hU3]))
    (fun ρ4 f4 h4 => ?_) (by simp)
  have f4' : ∀ v, v ∉ lettersW → ρ4 v = ρ v := fun v hv =>
    (f4 v hv).trans ((f3 v hv).trans (f2' v hv))
  have := sp_rng (x := pack (encodeToks ts) q a) (C := C) vK6 (.v vE6)
    (.seq (.set vLp (.bin .add (.v vU) (.v vK6))) letterP) ρ4 lettersW (ρ vU) L (by decide)
    (fun k hk ρ' f' => by
      simp only [eval_v, h4] at hk
      have g : ∀ v, v ∉ lettersW → Function.update ρ' vK6 k v = ρ v := fun v hv => by
        rw [Function.update_of_ne (ne_of_nmem hv (by decide)), f' v hv, f4' v hv]
      have hU' : Function.update ρ' vK6 k vU = ρ vU := g _ (by decide)
      refine sp_seqE (o1 := []) (o2 := encodeToks (L (ρ vU + k)))
        (sp_set (Q := fun r => r = Function.update (Function.update ρ' vK6 k) vLp (ρ vU + k))
          (by decide) (by
            congr 1
            simp only [eval_bin, ap_add, eval_v, hU', Function.update_self]
            exact min_eq_left (by omega))) (fun ρ5 _ h5 => ?_) (by simp)
      subst h5
      have g5 : ∀ v, v ∉ lettersW →
          Function.update (Function.update ρ' vK6 k) vLp (ρ vU + k) v = ρ v := fun v hv => by
        rw [Function.update_of_ne (ne_of_nmem hv (by decide)), g v hv]
      have hE5 := hE.of_frame g5 (by decide) (by decide)
      have := (sp_letterP hE5 (by rw [g5 _ (by decide), hM]) ha
        (by rw [g5 _ (by decide)]; exact hu)).mono (W' := lettersW) (by decide) (fun _ _ h => h)
      rwa [g5 vM (by decide), g5 vU (by decide), Function.update_self] at this)
  simpa [h4] using this

end SQ

end PathChecking
