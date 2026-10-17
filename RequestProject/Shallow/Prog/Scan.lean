module

public import RequestProject.ACRound.Pack

/-!
# Bracket-counting scans in the loop language

`scanP` computes `CTLP.scan ts up down p c` (and thus `fend`, `tend`, `numEnd`) into the
variable `sR`, using the variables `sP sC sD sI`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP

/-- number of tokens `|w| / 5` -/
abbrev vL : Fin V := 3
/-- scan: result -/
abbrev sR : Fin V := 10
/-- scan: position -/
abbrev sP : Fin V := 11
/-- scan: counter -/
abbrev sC : Fin V := 12
/-- scan: done flag -/
abbrev sD : Fin V := 13
/-- scan: loop counter -/
abbrev sI : Fin V := 14

/-- The environment of the programs: the input is `pack (encodeToks ts) q a`, the cap is large
and the variables `vN`, `vL` hold `|w|` and the number of tokens. -/
structure Env (ts : List Tok) (q : ℕ) (a : List Bool) (C : ℕ) (ρ : Fin V → ℕ) : Prop where
  hq : q ≤ a.length
  hC : 2 * (pack (encodeToks ts) q a).length + 40 ≤ C
  hN : ρ vN = 5 * ts.length
  hL : ρ vL = ts.length

lemma Env.congr {ts : List Tok} {q : ℕ} {a : List Bool} {C : ℕ} {ρ ρ' : Fin V → ℕ}
    (h : Env ts q a C ρ) (hN : ρ' vN = ρ vN) (hL : ρ' vL = ρ vL) : Env ts q a C ρ' :=
  ⟨h.hq, h.hC, hN.trans h.hN, hL.trans h.hL⟩

lemma Env.len_le {ts : List Tok} {q : ℕ} {a : List Bool} {C : ℕ} {ρ : Fin V → ℕ}
    (h : Env ts q a C ρ) : 10 * ts.length + 40 ≤ C := by
  have := h.hC
  rw [pack_length _ _ _ h.hq, encodeToks_length] at this
  omega

/-- A predicate on token codes, as an expression with values in `{0, 1}`. -/
structure CodePred (P : ℕ → Bool) where
  e : Ex V → Ex V
  spec : ∀ (x : Word) (C : ℕ) (ρ : Fin V → ℕ) (g : Ex V), 30 ≤ C →
    (e g).eval x C ρ = if P (g.eval x C ρ) then 1 else 0

/-- The scan program. -/
def scanP {up down : ℕ → Bool} (U : CodePred up) (D : CodePred down) (p : Ex V) (c : ℕ) :
    Pr V :=
  .seq (.set sP p) (.seq (.set sC (.c c)) (.seq (.set sD (.c 0)) (.loop sI (.bin .add (.v vL) (.c 2))
    (.ite (.v sD) .skip
      (.ite (.bin .eq (.bin .lt (.v sP) (.v vL)) (.c 0)) (.seq (.set sR (.v sP)) (.set sD (.c 1)))
        (.seq (.set sC (.bin .sub (.bin .add (.v sC) (U.e (tokE (.v sP)))) (D.e (tokE (.v sP)))))
          (.ite (.bin .eq (.v sC) (.c 0)) (.seq (.set sR (.bin .add (.v sP) (.c 1))) (.set sD (.c 1)))
            (.set sP (.bin .add (.v sP) (.c 1))))))))))

lemma scanP_wr {up down : ℕ → Bool} (U : CodePred up) (D : CodePred down) (p : Ex V) (c : ℕ) :
    ∀ z ∈ (scanP U D p c).wr, z = sR ∨ z = sP ∨ z = sC ∨ z = sD ∨ z = sI := by
  intro z hz
  simp [scanP, Pr.wr] at hz
  omega

lemma cstep_le (up down : ℕ → Bool) (k c : ℕ) : cstep up down k c ≤ c + 1 := by
  unfold cstep; split_ifs <;> omega

/-- **Correctness of the scan.** -/
theorem run_scanP {up down : ℕ → Bool} (U : CodePred up) (D : CodePred down)
    (hud : ∀ k, ¬ (up k = true ∧ down k = true)) (p : Ex V) (c : ℕ) (hc : c ≤ 2)
    {ts : List Tok} {q : ℕ} {a : List Bool} {C : ℕ} {ρ : Fin V → ℕ} (hE : Env ts q a C ρ)
    (hp : p.eval (pack (encodeToks ts) q a) C ρ ≤ ts.length + 1) :
    ((scanP U D p c).run (pack (encodeToks ts) q a) C ρ).1 sR =
      scan ts up down (p.eval (pack (encodeToks ts) q a) C ρ) c
    ∧ ((scanP U D p c).run (pack (encodeToks ts) q a) C ρ).2 = [] ∧
    ∀ z, z ≠ sR → z ≠ sP → z ≠ sC → z ≠ sD → z ≠ sI →
      ((scanP U D p c).run (pack (encodeToks ts) q a) C ρ).1 z = ρ z := by
  set x := pack (encodeToks ts) q a
  set pv := p.eval x C ρ
  set L := ts.length
  set S := scan ts up down pv c
  have hC := hE.len_le
  refine ⟨?_, Pr.run_silent _ (by simp [scanP, Pr.silent]) _,
    fun z h1 h2 h3 h4 h5 => Pr.run_frame _ _ _ (fun hz => by
      rcases scanP_wr U D p c z hz with h | h | h | h | h <;> contradiction)⟩
  simp only [scanP, run_seq, run_set]
  set ρ1 := Function.update (Function.update (Function.update ρ sP pv) sC
    ((Ex.c c : Ex V).eval x C (Function.update ρ sP pv))) sD ((Ex.c 0 : Ex V).eval x C
      (Function.update (Function.update ρ sP pv) sC ((Ex.c c : Ex V).eval x C
        (Function.update ρ sP pv)))) with hρ1
  set body : Pr V := (.ite (.v sD) .skip
      (.ite (.bin .eq (.bin .lt (.v sP) (.v vL)) (.c 0)) (.seq (.set sR (.v sP)) (.set sD (.c 1)))
        (.seq (.set sC (.bin .sub (.bin .add (.v sC) (U.e (tokE (.v sP)))) (D.e (tokE (.v sP)))))
          (.ite (.bin .eq (.v sC) (.c 0)) (.seq (.set sR (.bin .add (.v sP) (.c 1))) (.set sD (.c 1)))
            (.set sP (.bin .add (.v sP) (.c 1))))))) with hbody
  let I : ℕ → (Fin V → ℕ) → Prop := fun i ρ' => ρ' vN = ρ vN ∧ ρ' vL = ρ vL ∧
    ((ρ' sD = 1 ∧ ρ' sR = S) ∨ (ρ' sD = 0 ∧ ρ' sP = pv + i ∧ (i = 0 ∨ ρ' sP ≤ L) ∧
      ρ' sC ≤ c + i ∧ scan ts up down (ρ' sP) (ρ' sC) = S))
  have hb : (Ex.bin .add (.v vL) (.c 2) : Ex V).eval x C ρ1 = L + 2 := by
    simp (config := {decide := true}) [ρ1, Function.update_apply, hE.hL]; omega
  have key := run_loop_inv (w := x) (C := C) sI (.bin .add (.v vL) (.c 2)) body ρ1 I
    (by
      refine ⟨by simp (config := {decide := true}) [ρ1, Function.update_apply], by simp (config := {decide := true}) [ρ1, Function.update_apply], ?_⟩
      right
      simp (config := {decide := true}) only [ρ1, Function.update_apply]
      simp (config := {decide := true}) (disch := omega) [min_eq_left, S])
    (by
      intro i hi ρ' hI
      obtain ⟨hIN, hIL, hI⟩ := hI
      set ρ'' := Function.update ρ' sI i with hρ''
      have e'' : ∀ z, z ≠ sI → ρ'' z = ρ' z := fun z hz => Function.update_of_ne hz _ _
      have hE'' : Env ts q a C ρ'' := hE.congr (by rw [e'' _ (by decide), hIN])
        (by rw [e'' _ (by decide), hIL])
      rcases hI with ⟨hd, hr⟩ | ⟨hd, hpos, hpl, hcnt, hsc⟩
      · rw [hbody, run_ite_pos (by simp [e'' sD (by decide), hd])]
        exact ⟨by simp [e'' vN (by decide), hIN], by simp [e'' vL (by decide), hIL],
          Or.inl ⟨by simp [e'' sD (by decide), hd], by simp [e'' sR (by decide), hr]⟩⟩
      · rw [hbody, run_ite_neg (by simp [e'' sD (by decide), hd])]
        have hsP : ρ'' sP = ρ' sP := e'' sP (by decide)
        have hsC : ρ'' sC = ρ' sC := e'' sC (by decide)
        have hvL : ρ'' vL = L := by rw [e'' vL (by decide), hIL, hE.hL]
        by_cases hlt : ρ' sP < L
        · rw [run_ite_neg (by simp [hsP, hvL, hlt])]
          have htok : (tokE (.v sP)).eval x C ρ'' = tc ts (ρ' sP) := by
            rw [eval_tokE ts q a C ρ'' _ hE.hq hE.hC hE''.hN (by simp [hsP]; omega)]
            simp [hsP]
          set k' := cstep up down (tc ts (ρ' sP)) (ρ' sC) with hk'
          have hnew : (Ex.bin .sub (.bin .add (.v sC) (U.e (tokE (.v sP)))) (D.e (tokE (.v sP))) :
              Ex V).eval x C ρ'' = k' := by
            simp only [eval_bin, ap_sub, ap_add, eval_v, U.spec x C ρ'' _ (by omega),
              D.spec x C ρ'' _ (by omega), htok, hsC]
            have := hud (tc ts (ρ' sP))
            rw [hk', cstep]
            split_ifs <;> simp_all <;> omega
          simp only [run_seq, run_set, hnew]
          have hk'le : k' ≤ ρ' sC + 1 := cstep_le _ _ _ _
          by_cases hk0 : k' = 0
          · rw [run_ite_pos (by simp [hk0])]
            simp only [run_seq, run_set]
            refine ⟨by simp (config := {decide := true}) [Function.update_apply, e'' vN (by decide), hIN],
              by simp (config := {decide := true}) [Function.update_apply, e'' vL (by decide), hIL], Or.inl ⟨by simp; omega, ?_⟩⟩
            simp (config := {decide := true}) only [Function.update_apply]
            simp (disch := first | decide | omega) [Function.update_of_ne, Function.update_self, min_eq_left, hsP]
            rw [← hsc, scan_eq, if_neg (by omega), if_pos hk0]
          · rw [run_ite_neg (by simp [hk0])]
            simp only [run_set]
            refine ⟨by simp (config := {decide := true}) [Function.update_apply, e'' vN (by decide), hIN],
              by simp (config := {decide := true}) [Function.update_apply, e'' vL (by decide), hIL], Or.inr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
            · simp (config := {decide := true}) [Function.update_apply, e'' sD (by decide), hd]
            · simp (config := {decide := true}) only [Function.update_apply]
              simp (disch := first | decide | omega) [Function.update_of_ne, Function.update_self, min_eq_left, hsP]; omega
            · right; simp (config := {decide := true}) only [Function.update_apply]
              simp (disch := first | decide | omega) [Function.update_of_ne, Function.update_self, min_eq_left, hsP]; omega
            · simp (config := {decide := true}) only [Function.update_apply]; simp; omega
            · simp (config := {decide := true}) only [Function.update_apply]
              simp (disch := first | decide | omega) [Function.update_of_ne, Function.update_self, min_eq_left, hsP]
              rw [← hsc, scan_eq (p := ρ' sP), if_neg (by omega), if_neg hk0]
        · rw [run_ite_pos (by simp [hsP, hvL, hlt])]
          simp only [run_seq, run_set]
          refine ⟨by simp (config := {decide := true}) [Function.update_apply, e'' vN (by decide), hIN],
            by simp (config := {decide := true}) [Function.update_apply, e'' vL (by decide), hIL], Or.inl ⟨by simp; omega, ?_⟩⟩
          simp (config := {decide := true}) [Function.update_apply, hsP]
          rw [← hsc, scan_eq, if_pos (by omega)])
  rw [hb] at key
  obtain ⟨-, -, key⟩ := key
  rcases key with ⟨-, h⟩ | ⟨-, h1, h2, -, -⟩
  · exact h
  · omega

end SQ

end PathChecking
