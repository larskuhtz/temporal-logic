module

public import RequestProject.Shallow.Prog.Letter

/-!
# Emitting the positional translation of a formula

`trLoopP` emits `trToks ts m j` (`j` in `vJ`, `m` in `vM`).
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- current position of the translation -/
abbrev vX3 : Fin V := 47
/-- flag of `secUP` -/
abbrev vF : Fin V := 48
/-- loop counter of `secUP` -/
abbrev vI3 : Fin V := 49
/-- token code temporary of `trBodyP` -/
abbrev vCd : Fin V := 50
/-- loop counter of `trLoopP` -/
abbrev vK7 : Fin V := 51
/-- length temporary of `trLoopP` -/
abbrev vE7 : Fin V := 52

lemma any_range_succ (f : ℕ → Bool) (k : ℕ) :
    (List.range (k + 1)).any f = ((List.range k).any f || f k) := by
  simp [List.range_succ, List.any_append]

/-! ## Second arguments of `U` -/

/-- The body of `secUP`. -/
def secBody : Pr V :=
  .ite (.bin .eq (tokE (.bin .add (.v vJ) (.v vI3))) (.c 10))
    (.seq (fendP (.bin .add (.bin .add (.v vJ) (.v vI3)) (.c 1)))
      (.ite (.bin .eq (.v sR) (.v vX3)) (.set vF (.c 1)) .skip)) .skip

/-- `vF := [secU ts j₀ x]` (`j₀` in `vJ`, `x` in `vX3`). -/
def secUP : Pr V := .seq (.set vF (.c 0)) (.loop vI3 (.bin .sub (.v vX3) (.v vJ)) secBody)

/-- Frame of `secUP`. -/
abbrev secW : List (Fin V) := [vF, vI3, sR, sP, sC, sD, sI]

lemma sp_secUP (hE : Env ts q a C ρ) (hx : ρ vX3 ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C secUP ρ secW []
      (fun ρ' => ρ' vF = if secU ts (ρ vJ) (ρ vX3) then 1 else 0) := by
  have hC := hE.len_le
  unfold secUP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vF 0)
    (by decide) (by simp)) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  set f : ℕ → Bool := fun i => decide (tc ts (ρ vJ + i) = 10 ∧ fend ts (ρ vJ + i + 1) = ρ vX3)
  have g0 : ∀ v, v ∉ secW → Function.update ρ vF 0 v = ρ v :=
    fun v hv => Function.update_of_ne (ne_of_nmem hv (by decide)) _ _
  have hev : (Ex.bin .sub (.v vX3) (.v vJ) : Ex V).eval (pack (encodeToks ts) q a) C
      (Function.update ρ vF 0) = ρ vX3 - ρ vJ := by
    simp only [eval_bin, ap_sub, eval_v, g0 vX3 (by decide), g0 vJ (by decide)]
  have := sp_loop_inv (x := pack (encodeToks ts) q a) (C := C) vI3 (.bin .sub (.v vX3) (.v vJ))
    secBody (Function.update ρ vF 0) secW
    (fun i r => r vF = if (List.range i).any f then 1 else 0) (by decide) (by simp)
    (fun k hk ρ' f' hI => by
      rw [hev] at hk
      have g : ∀ v, v ∉ secW → Function.update ρ' vI3 k v = ρ v := fun v hv => by
        rw [Function.update_of_ne (ne_of_nmem hv (by decide)), f' v hv, g0 v hv]
      have hE' := hE.of_frame g (by decide) (by decide)
      have hF' : Function.update ρ' vI3 k vF = if (List.range k).any f then 1 else 0 := by
        rw [Function.update_of_ne (by decide), hI]
      have hpos : (Ex.bin .add (.v vJ) (.v vI3) : Ex V).eval (pack (encodeToks ts) q a) C
          (Function.update ρ' vI3 k) = ρ vJ + k := by
        simp only [eval_bin, ap_add, eval_v, g vJ (by decide), Function.update_self]
        exact min_eq_left (by omega)
      have htok : (tokE (.bin .add (.v vJ) (.v vI3))).eval (pack (encodeToks ts) q a) C
          (Function.update ρ' vI3 k) = tc ts (ρ vJ + k) := by
        rw [eval_tokE ts q a C _ _ hE'.hq hE'.hC hE'.hN (by rw [hpos]; omega), hpos]
      unfold secBody
      beta_reduce
      rw [any_range_succ]
      by_cases h10 : tc ts (ρ vJ + k) = 10
      · refine sp_ite_pos (by simp [htok, h10, min_eq_left (show 10 ≤ C by omega)]) ?_
        have hp1 : (Ex.bin .add (.bin .add (.v vJ) (.v vI3)) (.c 1) : Ex V).eval
            (pack (encodeToks ts) q a) C (Function.update ρ' vI3 k) = ρ vJ + k + 1 := by
          simp only [eval_bin, ap_add, eval_v, eval_c, g vJ (by decide), Function.update_self]
          simp (disch := omega) only [min_eq_left]
        refine sp_seqE (o1 := []) (o2 := []) ((sp_fendP hE' _ (by rw [hp1]; omega)).frame.mono
          (by decide) (fun _ _ h => h)) (fun ρ2 _ h2 => ?_) rfl
        rw [hp1] at h2
        have hX2 : ρ2 vX3 = ρ vX3 := by rw [h2.2 vX3 (by decide), g vX3 (by decide)]
        have hF2 : ρ2 vF = if (List.range k).any f then 1 else 0 := by
          rw [h2.2 vF (by decide), hF']
        by_cases hx' : fend ts (ρ vJ + k + 1) = ρ vX3
        · refine sp_ite_pos (by simp [h2.1, hX2, hx']) (sp_set (by decide) ?_)
          have : f k = true := by simp [f, h10, hx']
          simp [this, min_eq_left (show 1 ≤ C by omega)]
        · refine sp_ite_neg (by simp [h2.1, hX2, hx']) (sp_skip ?_)
          have : f k = false := by simp [f, hx']
          simp [this, hF2]
      · refine sp_ite_neg (by simp [htok, h10, min_eq_left (show 10 ≤ C by omega)]) (sp_skip ?_)
        have : f k = false := by simp [f, h10]
        simp [this, hF'])
  rw [hev] at this
  refine this.mono (fun z h => h) (fun r _ h => ?_)
  rw [h]
  rfl

/-! ## The body of the translation -/

/-- Emit `trBody ts m x` (`x` in `vX3`, `m` in `vM`). -/
def trBodyP : Pr V :=
  .seq (.set vCd (tokE (.v vX3)))
  (.ite (.bin .eq (.v vCd) (.c 5)) (.seq (outToks [Tok.tag 0]) onesP)
  (.ite (.bin .eq (.v vCd) (.c 6)) (outToks [Tok.tag 1])
  (.ite (.bin .eq (.v vCd) (.c 7)) (outToks [Tok.tag 2])
  (.ite (.bin .eq (.v vCd) (.c 8)) (outToks [Tok.tag 3])
  (.ite (.bin .eq (.v vCd) (.c 9)) (.seq (outToks [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 0])
      (.seq (.set vZ (.bin .add (.v vX3) (.c 2))) (.seq (emitNat vZ vZy vZi)
        (.seq (outToks [Tok.tag 2, Tok.tag 3, Tok.tag 0]) (emitNat vZ vZy vZi)))))
  (.ite (.bin .eq (.v vCd) (.c 10))
      (.seq (outToks [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3, Tok.tag 0])
        (.seq (.set vZ (.bin .add (.v vX3) (.c 1))) (emitNat vZ vZy vZi)))
  (.ite (.bin .eq (.v vCd) (.c 11)) (outToks [Tok.tag 5, Tok.tag 1])
    (cpP (.v vX3)))))))))

/-- Frame of `trBodyP`. -/
abbrev trBodyW : List (Fin V) := [vCd, vK4, vZ, vZy, vZi, vT]

lemma sp_trBodyP (hE : Env ts q a C ρ) (hx : ρ vX3 ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C trBodyP ρ trBodyW
      (encodeToks (trBody ts (ρ vM) (ρ vX3))) (fun _ => True) := by
  have hC := hE.len_le
  unfold trBodyP
  refine sp_seqE (o1 := []) (o2 := encodeToks (trBody ts (ρ vM) (ρ vX3)))
    (sp_set (Q := fun r => r = Function.update ρ vCd (tc ts (ρ vX3))) (by decide) (by
      rw [eval_tokE_v hE vX3 (by omega)])) (fun ρ1 _ h1 => ?_) (by simp)
  subst h1
  set ρ1 := Function.update ρ vCd (tc ts (ρ vX3))
  have g1 : ∀ v, v ≠ vCd → ρ1 v = ρ v := fun v hv => Function.update_of_ne hv _ _
  have hE1 : Env ts q a C ρ1 := hE.congr (g1 _ (by decide)) (g1 _ (by decide))
  have hc : ∀ k ≤ 30, (Ex.bin .eq (.v vCd) (.c k) : Ex V).eval (pack (encodeToks ts) q a) C ρ1 =
      if tc ts (ρ vX3) = k then 1 else 0 := by
    intro k hk
    simp only [eval_bin, ap_eq, eval_v, eval_c, ρ1, Function.update_self,
      min_eq_left (show k ≤ C by omega)]
  have hX1 : ρ1 vX3 = ρ vX3 := g1 _ (by decide)
  have hM1 : ρ1 vM = ρ vM := g1 _ (by decide)
  have hpos : ∀ k, (h : tc ts (ρ vX3) = k) → k ≤ 30 →
      (Ex.bin .eq (.v vCd) (.c k) : Ex V).eval (pack (encodeToks ts) q a) C ρ1 ≠ 0 := by
    intro k h hk; rw [hc k hk, if_pos h]; simp
  have hneg : ∀ k, tc ts (ρ vX3) ≠ k → k ≤ 30 →
      (Ex.bin .eq (.v vCd) (.c k) : Ex V).eval (pack (encodeToks ts) q a) C ρ1 = 0 := by
    intro k h hk; rw [hc k hk, if_neg h]
  have hz : ∀ (c : ℕ) (ρ' : Fin V → ℕ), ρ' vX3 = ρ vX3 → c ≤ 2 →
      Sp (pack (encodeToks ts) q a) C (.seq (.set vZ (.bin .add (.v vX3) (.c c)))
        (emitNat vZ vZy vZi)) ρ' trBodyW (encodeToks (natToks (ρ vX3 + c)))
        (fun r => r vZ = ρ vX3 + c ∧ r vX3 = ρ vX3) := by
    intro c ρ' hx' hc2
    refine sp_seqE (o1 := []) (o2 := encodeToks (natToks (ρ vX3 + c)))
      (sp_set (Q := fun r => r = Function.update ρ' vZ (ρ vX3 + c)) (by decide) (by
        congr 1
        simp only [eval_bin, ap_add, eval_v, eval_c, hx']
        simp (disch := omega) only [min_eq_left])) (fun ρ2 _ h2 => ?_) (by simp)
    subst h2
    have := (sp_emitNat (x := pack (encodeToks ts) q a) (C := C)
      (ρ := Function.update ρ' vZ (ρ vX3 + c)) vZ vZy vZi (by decide) (by omega)).frame.mono
      (W' := trBodyW) (by decide) (fun _ _ h => h)
    refine this.out_eq (by rw [Function.update_self]) |>.mono (fun _ h => h) (fun r _ h => ?_)
    rw [h.2 vZ (by decide), h.2 vX3 (by decide), Function.update_self,
      Function.update_of_ne (by decide), hx']
    exact ⟨rfl, rfl⟩
  by_cases h5 : tc ts (ρ vX3) = 5
  · have ht : trBody ts (ρ vM) (ρ vX3) = Tok.tag 0 :: List.replicate (ρ vM) Tok.one := by
      simp [trBody, h5]
    rw [ht]
    refine sp_ite_pos (hpos 5 h5 (by norm_num)) (sp_seqE
      (o2 := encodeToks (List.replicate (ρ vM) Tok.one))
      (sp_outToks (Q := fun r => r = ρ1) rfl) (fun ρ2 _ h2 => ?_) (by simp [encodeToks]))
    subst h2
    have := (sp_onesP (x := pack (encodeToks ts) q a) (C := C) (ρ := ρ1)).mono (W' := trBodyW)
      (by decide) (fun _ _ h => h)
    rwa [hM1] at this
  refine sp_ite_neg (hneg 5 h5 (by norm_num)) ?_
  by_cases h6 : tc ts (ρ vX3) = 6
  · have ht : trBody ts (ρ vM) (ρ vX3) = [Tok.tag 1] := by simp [trBody, h6]
    rw [ht]
    exact sp_ite_pos (hpos 6 h6 (by norm_num)) (sp_outToks trivial)
  refine sp_ite_neg (hneg 6 h6 (by norm_num)) ?_
  by_cases h7 : tc ts (ρ vX3) = 7
  · have ht : trBody ts (ρ vM) (ρ vX3) = [Tok.tag 2] := by simp [trBody, h7]
    rw [ht]
    exact sp_ite_pos (hpos 7 h7 (by norm_num)) (sp_outToks trivial)
  refine sp_ite_neg (hneg 7 h7 (by norm_num)) ?_
  by_cases h8 : tc ts (ρ vX3) = 8
  · have ht : trBody ts (ρ vM) (ρ vX3) = [Tok.tag 3] := by simp [trBody, h8]
    rw [ht]
    exact sp_ite_pos (hpos 8 h8 (by norm_num)) (sp_outToks trivial)
  refine sp_ite_neg (hneg 8 h8 (by norm_num)) ?_
  by_cases h9 : tc ts (ρ vX3) = 9
  · have ht : trBody ts (ρ vM) (ρ vX3) = [Tok.tag 2, Tok.tag 3, Tok.tag 2] ++
        (Tok.tag 0 :: natToks (ρ vX3 + 2)) ++ [Tok.tag 2, Tok.tag 3] ++
        (Tok.tag 0 :: natToks (ρ vX3 + 2)) := by simp [trBody, h9]
    rw [ht]
    refine sp_ite_pos (hpos 9 h9 (by norm_num)) (sp_seqE
      (o2 := encodeToks (natToks (ρ vX3 + 2)) ++
        (encodeToks [Tok.tag 2, Tok.tag 3, Tok.tag 0] ++ encodeToks (natToks (ρ vX3 + 2))))
      (sp_outToks (Q := fun r => r = ρ1) rfl) (fun ρ2 _ h2 => ?_) (by simp [encodeToks]))
    subst h2
    refine sp_seq_assoc (sp_seqE (hz 2 ρ1 hX1 (by norm_num)) (fun ρ3 _ h3 => ?_) rfl)
    refine sp_seqE (o2 := encodeToks (natToks (ρ vX3 + 2)))
      (sp_outToks (Q := fun r => r = ρ3) rfl) (fun ρ4 _ h4 => ?_) rfl
    subst h4
    have := (sp_emitNat (x := pack (encodeToks ts) q a) (C := C) (ρ := ρ4) vZ vZy vZi
      (by decide) (by omega)).mono (W' := trBodyW) (by decide) (fun _ _ h => h)
    rwa [h3.1] at this
  refine sp_ite_neg (hneg 9 h9 (by norm_num)) ?_
  by_cases h10 : tc ts (ρ vX3) = 10
  · have ht : trBody ts (ρ vM) (ρ vX3) = [Tok.tag 2, Tok.tag 3, Tok.tag 2, Tok.tag 3] ++
        (Tok.tag 0 :: natToks (ρ vX3 + 1)) := by simp [trBody, h10]
    rw [ht]
    refine sp_ite_pos (hpos 10 h10 (by norm_num)) (sp_seqE
      (o2 := encodeToks (natToks (ρ vX3 + 1)))
      (sp_outToks (Q := fun r => r = ρ1) rfl) (fun ρ2 _ h2 => ?_) (by simp [encodeToks]))
    subst h2
    exact hz 1 ρ1 hX1 (by norm_num) |>.mono (fun _ h => h) (fun _ _ _ => trivial)
  refine sp_ite_neg (hneg 10 h10 (by norm_num)) ?_
  by_cases h11 : tc ts (ρ vX3) = 11
  · have ht : trBody ts (ρ vM) (ρ vX3) = [Tok.tag 5, Tok.tag 1] := by simp [trBody, h11]
    rw [ht]
    exact sp_ite_pos (hpos 11 h11 (by norm_num)) (sp_outToks trivial)
  refine sp_ite_neg (hneg 11 h11 (by norm_num)) ?_
  have ht : trBody ts (ρ vM) (ρ vX3) = cp ts (ρ vX3) := by
    simp [trBody, h5, h6, h7, h8, h9, h10, h11]
  rw [ht]
  have := (sp_cpP hE1 (.v vX3)).mono (W' := trBodyW) (by decide) (fun _ _ h => h)
  rwa [eval_v, hX1] at this

/-- Emit `trAt ts m j₀ x` (`j₀` in `vJ`, `x` in `vX3`). -/
def trAtP : Pr V := .seq secUP (.seq (.ite (.v vF) (outToks [Tok.tag 2]) .skip) trBodyP)

/-- Frame of `trAtP`. -/
abbrev trAtW : List (Fin V) := [vF, vI3, sR, sP, sC, sD, sI, vCd, vK4, vZ, vZy, vZi, vT]

lemma sp_trAtP (hE : Env ts q a C ρ) (hx : ρ vX3 ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C trAtP ρ trAtW
      (encodeToks (trAt ts (ρ vM) (ρ vJ) (ρ vX3))) (fun _ => True) := by
  unfold trAtP
  rw [trAt, LS.encodeToks_append]
  refine sp_seqE (o1 := []) (o2 := encodeToks (if secU ts (ρ vJ) (ρ vX3) then [Tok.tag 2]
      else []) ++ encodeToks (trBody ts (ρ vM) (ρ vX3)))
    ((sp_secUP hE hx).mono (by decide) (fun _ _ h => h)) (fun ρ1 f1 h1 => ?_) (by simp)
  have hE1 := hE.of_frame f1 (by decide) (by decide)
  have hX1 : ρ1 vX3 = ρ vX3 := f1 _ (by decide)
  have hM1 : ρ1 vM = ρ vM := f1 _ (by decide)
  have hcont : ∀ ρ2 : Fin V → ℕ, (∀ v, v ∉ trAtW → ρ2 v = ρ1 v) → ρ2 = ρ1 →
      Sp (pack (encodeToks ts) q a) C trBodyP ρ2 trAtW
        (encodeToks (trBody ts (ρ vM) (ρ vX3))) (fun _ => True) := by
    intro ρ2 _ h2
    subst h2
    have := (sp_trBodyP hE1 (by rw [hX1]; exact hx)).mono (W' := trAtW) (by decide)
      (fun _ _ h => h)
    rwa [hX1, hM1] at this
  by_cases hs : secU ts (ρ vJ) (ρ vX3) = true
  · rw [if_pos hs]
    exact sp_seqE (sp_ite_pos (by simp [h1, hs]) (sp_outToks (Q := fun r => r = ρ1) rfl)) hcont rfl
  · rw [if_neg hs]
    exact sp_seqE (sp_ite_neg (by simp [h1, hs]) (sp_skip (Q := fun r => r = ρ1) rfl)) hcont
      (by simp [encodeToks])

/-- Emit `trToks ts m j` (`j` in `vJ`, `m` in `vM`). -/
def trLoopP : Pr V := .seq (fendP (.v vJ)) (.seq (.set vE7 (.bin .sub (.v sR) (.v vJ)))
  (.loop vK7 (.v vE7) (.seq (.set vX3 (.bin .add (.v vJ) (.v vK7))) trAtP)))

/-- Frame of `trLoopP`. -/
abbrev trLoopW : List (Fin V) := vE7 :: vK7 :: vX3 :: trAtW

lemma sp_trLoopP (hE : Env ts q a C ρ) (hj : ρ vJ ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C trLoopP ρ trLoopW
      (encodeToks (trToks ts (ρ vM) (ρ vJ))) (fun _ => True) := by
  have hC := hE.len_le
  unfold trLoopP
  refine sp_seqE (o2 := encodeToks (trToks ts (ρ vM) (ρ vJ)))
    ((sp_fendP hE (.v vJ) (by simp only [eval_v]; omega)).mono (by decide) (fun _ _ h => h))
    (fun ρ1 f1 h1 => ?_) (by simp)
  simp only [eval_v] at h1
  have hJ1 : ρ1 vJ = ρ vJ := f1 _ (by decide)
  have hfe := fend_le' ts hj
  refine sp_seqE (o1 := []) (o2 := encodeToks (trToks ts (ρ vM) (ρ vJ)))
    (sp_set (Q := fun r => r vE7 = fend ts (ρ vJ) - ρ vJ) (by decide) (by
      simp only [Function.update_self, eval_bin, ap_sub, eval_v, h1, hJ1]))
    (fun ρ2 f2 h2 => ?_) (by simp)
  have f2' : ∀ v, v ∉ trLoopW → ρ2 v = ρ v := fun v hv => (f2 v hv).trans (f1 v hv)
  have := sp_rng (x := pack (encodeToks ts) q a) (C := C) vK7 (.v vE7)
    (.seq (.set vX3 (.bin .add (.v vJ) (.v vK7))) trAtP) ρ2 trLoopW (ρ vJ)
    (trAt ts (ρ vM) (ρ vJ)) (by decide) (fun k hk ρ' f' => by
      simp only [eval_v, h2] at hk
      have g : ∀ v, v ∉ trLoopW → Function.update ρ' vK7 k v = ρ v := fun v hv => by
        rw [Function.update_of_ne (ne_of_nmem hv (by decide)), f' v hv, f2' v hv]
      refine sp_seqE (o1 := []) (o2 := encodeToks (trAt ts (ρ vM) (ρ vJ) (ρ vJ + k)))
        (sp_set (Q := fun r => r = Function.update (Function.update ρ' vK7 k) vX3 (ρ vJ + k))
          (by decide) (by
            congr 1
            simp only [eval_bin, ap_add, eval_v, g vJ (by decide), Function.update_self]
            exact min_eq_left (by omega))) (fun ρ5 _ h5 => ?_) (by simp)
      subst h5
      have g5 : ∀ v, v ∉ trLoopW →
          Function.update (Function.update ρ' vK7 k) vX3 (ρ vJ + k) v = ρ v := fun v hv => by
        rw [Function.update_of_ne (ne_of_nmem hv (by decide)), g v hv]
      have hE5 := hE.of_frame g5 (by decide) (by decide)
      have := (sp_trAtP hE5 (by rw [Function.update_self]; omega)).mono (W' := trLoopW)
        (by decide) (fun _ _ h => h)
      rwa [g5 vM (by decide), g5 vJ (by decide), Function.update_self] at this)
  simpa [h2, trToks] using this

end SQ

end PathChecking
