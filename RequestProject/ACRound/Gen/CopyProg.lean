module

public import RequestProject.ACRound.Gen.Copy
public import RequestProject.ACRound.LLBasic

/-!
# The copy transducer in the loop language

`GenP.stepP` implements one step `GenC.stepTok` of the copy transducer on the token code held
in the variable `vc` (`GenP.run_stepP`).
-/

@[expose] public section

namespace PathChecking

namespace GenP

open LL GenC

/-- Number of variables of the generator program. -/
abbrev V : ℕ := 48

/-! ## Variable layout -/

/-- `n` -/
abbrev vn : Fin V := 0
/-- queries per round -/
abbrev vNq : Fin V := 1
/-- rounds -/
abbrev vR : Fin V := 2
/-- query length bound -/
abbrev vL : Fin V := 3
/-- block size -/
abbrev vS : Fin V := 4
/-- group size -/
abbrev vW : Fin V := 5
/-- round loop -/
abbrev vr : Fin V := 6
/-- query loop -/
abbrev vq : Fin V := 7
/-- inner loop -/
abbrev vi : Fin V := 8
/-- block loop -/
abbrev vl : Fin V := 9
/-- emit: value -/
abbrev ex : Fin V := 10
/-- emit: temporary -/
abbrev ey : Fin V := 11
/-- emit: counter -/
abbrev ei : Fin V := 12
/-- segment pointer -/
abbrev vpp : Fin V := 13
/-- segment length -/
abbrev vT : Fin V := 14
/-- found flag -/
abbrev vfd : Fin V := 15
/-- scan loop -/
abbrev vj : Fin V := 16
/-- token loop -/
abbrev vt : Fin V := 17
/-- token code -/
abbrev vc : Fin V := 18
/-- transducer: mode -/
abbrev md : Fin V := 19
/-- transducer: oracle flag -/
abbrev orc : Fin V := 20
/-- transducer: number -/
abbrev num : Fin V := 21
/-- transducer: weight -/
abbrev pw : Fin V := 22
/-- transducer: input index -/
abbrev inp : Fin V := 23
/-- transducer: gate count -/
abbrev gc : Fin V := 24
/-- block offset -/
abbrev vb0 : Fin V := 25
/-- group offset -/
abbrev vg0 : Fin V := 26

/-! ## Emitting a token with a computed code -/

/-- Emit the token whose code is held in `x`. -/
def emitCode (x : Fin V) : Pr V :=
  .seq (.out (.bin .mod (.bin .div (.v x) (.c 1)) (.c 2)))
    (.seq (.out (.bin .mod (.bin .div (.v x) (.c 2)) (.c 2)))
      (.seq (.out (.bin .mod (.bin .div (.v x) (.c 4)) (.c 2)))
        (.seq (.out (.bin .mod (.bin .div (.v x) (.c 8)) (.c 2)))
          (.out (.bin .mod (.bin .div (.v x) (.c 16)) (.c 2))))))

lemma run_emitCode {z : Word} {C : ℕ} (x : Fin V) (ρ : Fin V → ℕ) (hC : 16 ≤ C)
    (hx : 5 ≤ ρ x ∧ ρ x < 29) :
    (emitCode x).run z C ρ = (ρ, encodeToks [codeTok (ρ x)]) := by
  have hct : (codeTok (ρ x)).code = ρ x := by
    unfold codeTok; rw [dif_pos hx]; simp [Tok.code]; omega
  simp only [emitCode, run_seq, run_out, eval_bin, eval_v, eval_c, ap_mod, ap_div]
  simp only [min_eq_left (by omega : 1 ≤ C), min_eq_left (by omega : 2 ≤ C),
    min_eq_left (by omega : 4 ≤ C), min_eq_left (by omega : 8 ≤ C),
    min_eq_left (by omega : 16 ≤ C)]
  simp only [encodeToks, List.flatMap_cons, List.flatMap_nil, List.append_nil, Tok.bits, hct]
  simp [List.range_succ, Nat.testBit_eq_decide_div_mod_eq]

/-! ## One step of the transducer -/

/-- One step of the copy transducer on the code in `vc`. -/
def stepP : Pr V :=
  .ite (.bin .lt (.v vc) (.c 2))
    (.seq (.ite (.bin .eq (.v vc) (.c 1)) (.set num (.bin .add (.v num) (.v pw))) .skip)
      (.set pw (.bin .add (.v pw) (.v pw))))
  (.ite (.bin .eq (.v vc) (.c 2))
    (.ite (.v md) (.seq (.set inp (.v num)) (.seq (.set num (.c 0)) (.set pw (.c 1))))
      (.seq (.set ex (.bin .add (.v vb0) (.v num))) (.seq (emitNat ex ey ei)
        (.seq (.set num (.c 0)) (.set pw (.c 1))))))
  (.ite (.bin .eq (.v vc) (.c 3))
    (.ite (.v md) .skip (.seq (outToks [Tok.lpar]) (.ite (.v orc) (outToks (natToks 0)) .skip)))
  (.ite (.bin .eq (.v vc) (.c 4))
    (.seq (.ite (.v md)
        (.seq (outToks [Tok.tag 5, Tok.lpar]) (.seq (.set ex (.bin .add (.v vg0) (.v inp)))
          (.seq (emitNat ex ey ei) (outToks [Tok.rpar]))))
        (outToks [Tok.rpar]))
      (.seq (.set md (.c 0)) (.set gc (.bin .add (.v gc) (.c 1)))))
  (.ite (.bin .eq (.v vc) (.c 5)) (.set md (.c 1))
    (.seq (.set md (.c 0)) (.seq (.set orc (.bin .eq (.v vc) (.c 11))) (emitCode vc)))))))

/-- The variables encode the state `s`. -/
def Enc (ρ : Fin V → ℕ) (s : CS) : Prop :=
  ρ md = (if s.mode then 1 else 0) ∧ ρ orc = (if s.orc then 1 else 0) ∧ ρ num = s.num ∧
    ρ pw = s.pw ∧ ρ inp = s.inp ∧ ρ gc = s.gc

@[simp] lemma encodeToks_nil' : encodeToks [] = [] := rfl

lemma emitNat_run_eq {z : Word} {C : ℕ} (x y i : Fin V) (hyi : y ≠ i) (hC : 2 ≤ C)
    (ρ : Fin V → ℕ) : ∃ ρ', (emitNat x y i).run z C ρ = (ρ', encodeToks (natToks (ρ x))) ∧
      ∀ v, v ≠ y → v ≠ i → ρ' v = ρ v :=
  ⟨_, Prod.ext rfl (run_emitNat x y i hyi hC ρ).1, (run_emitNat x y i hyi hC ρ).2⟩

/-- Variables written by `stepP`. -/
def stepW : List (Fin V) := [md, orc, num, pw, inp, gc, ex, ey, ei]

lemma stepP_wr : ∀ v ∈ stepP.wr, v ∈ stepW := by
  simp [stepP, Pr.wr, emitNat_wr, emitCode, outToks, stepW]

/-- **Correctness of one step.** -/
lemma run_stepP {z : Word} {C : ℕ} (ρ : Fin V → ℕ) (s : CS) (hs : Enc ρ s) (hC : 30 ≤ C)
    (hc : ρ vc < 29) :
    (stepP.run z C ρ).2 = encodeToks (stepTok C (ρ vb0) (ρ vg0) s (ρ vc)).2 ∧
      Enc (stepP.run z C ρ).1 (stepTok C (ρ vb0) (ρ vg0) s (ρ vc)).1 ∧
      ∀ v, v ∉ stepW → (stepP.run z C ρ).1 v = ρ v := by
  refine ⟨?_, ?_, fun v hv => Pr.run_frame _ _ _ (fun h => hv (stepP_wr v h))⟩ <;>
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hs
    obtain ⟨m, o, nu, p, i, g⟩ := s
    simp only at h1 h2 h3 h4 h5 h6
    have hC2 : 2 ≤ C := by omega
    simp only [stepP, stepTok]
    by_cases c2 : ρ vc < 2
    · simp only [run_ite, eval_bin, eval_v, eval_c, ap_lt, ap_eq, ap_add,
        min_eq_left (show 2 ≤ C by omega), min_eq_left (show 1 ≤ C by omega), c2, if_true,
        ne_eq, one_ne_zero, not_false_eq_true, run_seq, run_set, run_skip]
      by_cases c1 : ρ vc = 1 <;> simp [c1, Enc, h1, h2, h3, h4, h5, h6,
        md, orc, num, pw, inp, gc]
    have e2 : min 2 C = 2 := min_eq_left (by omega)
    have e3 : min 3 C = 3 := min_eq_left (by omega)
    have e4 : min 4 C = 4 := min_eq_left (by omega)
    have e5 : min 5 C = 5 := min_eq_left (by omega)
    have e11 : min 11 C = 11 := min_eq_left (by omega)
    have e1 : min 1 C = 1 := min_eq_left (by omega)
    have e0 : min 0 C = 0 := min_eq_left (by omega)
    simp only [run_ite, eval_bin, eval_v, eval_c, ap_lt, ap_eq, ap_add, e0, e1, e2, e3, e4, e5,
      e11, c2, if_false, run_seq, run_set, run_skip, run_outToks, h1, h2]
    by_cases c3 : ρ vc = 2
    · simp only [c3, if_true, ne_eq, one_ne_zero, not_false_eq_true]
      cases m
      · obtain ⟨ρ', hr, hf⟩ := emitNat_run_eq (z := z) ex ey ei (by decide) (by omega)
          (Function.update ρ ex (min (ρ vb0 + ρ num) C))
        simp only [hr]
        simp [Enc, hf, h1, h2, h3, h5, h6, md, orc, num, pw, inp, gc, ex, ey, ei]
      · simp [Enc, h1, h2, h3, h6, md, orc, num, pw, inp, gc]
    simp only [c3, if_false]
    by_cases c4 : ρ vc = 3
    · simp only [c4, if_true, ne_eq, one_ne_zero, not_false_eq_true]
      cases m <;> cases o <;> simp [Enc, h1, h2, h3, h4, h5, h6, md, orc, num, pw, inp, gc, LS.encodeToks_cons]
    simp only [c4, if_false]
    by_cases c5 : ρ vc = 4
    · simp only [c5, if_true, ne_eq, one_ne_zero, not_false_eq_true]
      cases m
      · simp [Enc, h2, h3, h4, h5, h6, md, orc, num, pw, inp, gc, LS.encodeToks_cons]
      · obtain ⟨ρ', hr, hf⟩ := emitNat_run_eq (z := z) ex ey ei (by decide) (by omega)
          (Function.update ρ ex (min (ρ vg0 + ρ inp) C))
        simp only [one_ne_zero, not_false_eq_true, if_true, hr]
        simp [Enc, hf, h2, h3, h4, h5, h6, md, orc, num, pw, inp, gc, ex, ey, ei,
          LS.encodeToks_append, LS.encodeToks_cons]
    simp only [c5, if_false]
    by_cases c6 : ρ vc = 5
    · simp [c6, Enc, h2, h3, h4, h5, h6, md, orc, num, pw, inp, gc]
    simp only [c6, if_false]
    rw [run_emitCode _ _ (by omega) (by
      simp only [Function.update_of_ne (show vc ≠ md by decide),
        Function.update_of_ne (show vc ≠ orc by decide)]; omega)]
    simp [Enc, h3, h4, h5, h6, md, orc, num, pw, inp, gc, vc]

end GenP

end PathChecking
