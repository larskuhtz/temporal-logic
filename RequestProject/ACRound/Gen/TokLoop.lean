module

public import RequestProject.ACRound.Gen.CopyProg
public import RequestProject.ACRound.Pack

/-!
# The token loop of the copy transducer

`GenP.tokLoopP` reads the tokens of a segment `ts` of the input, written with every bit `b` as
the pair `[true, b]` starting at position `ρ vpp`, and runs the copy transducer on their codes
(`GenP.run_tokLoopP`).
-/

@[expose] public section

namespace PathChecking

namespace GenP

open LL GenC

lemma foldr_add_eval' {W : ℕ} {x : Word} {C : ℕ} {ρ : Fin W → ℕ} (l : List (Ex W))
    (h : (l.map fun e => e.eval x C ρ).sum ≤ C) :
    (l.foldr (fun e acc => Ex.bin .add e acc) (.c 0)).eval x C ρ =
      (l.map fun e => e.eval x C ρ).sum := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldr_cons, eval_bin, ap_add, List.map_cons, List.sum_cons] at h ⊢
    rw [ih (by omega)]; omega

/-- Code of token `vt` of the segment at `vpp` (bit `b` of the token is at position
`vpp + 10 vt + 2 b + 1`). -/
def tokCodeE : Ex V :=
  ((List.range 5).map fun b => (Ex.bin .mul (.c (2 ^ b))
      (.inp (.bin .add (.v vpp) (.bin .add (.bin .mul (.c 10) (.v vt)) (.c (2 * b + 2))))))).foldr
        (fun e acc => .bin .add e acc) (.c 0)

lemma eval_tokCodeE {z : Word} {C : ℕ} (ρ : Fin V → ℕ) (t : Tok)
    (hz : ∀ b < 5, z[ρ vpp + 10 * ρ vt + 2 * b + 1]? = some (t.code.testBit b))
    (hC : ρ vpp + 10 * ρ vt + 12 ≤ C) (hC' : 30 ≤ C) :
    tokCodeE.eval z C ρ = t.code := by
  have hbits : ∀ b < 5, (Ex.inp (.bin .add (.v vpp) (.bin .add (.bin .mul (.c 10) (.v vt))
      (.c (2 * b + 2)))) : Ex V).eval z C ρ = if t.code.testBit b then 1 else 0 := by
    intro b hb
    simp only [eval_inp, eval_bin, ap_add, ap_mul, eval_v, eval_c]
    rw [min_eq_left (show 10 ≤ C by omega), min_eq_left (show 2 * b + 2 ≤ C by omega),
      min_eq_left (show 10 * ρ vt ≤ C by omega), min_eq_left (show 10 * ρ vt + (2 * b + 2) ≤ C by omega),
      min_eq_left (show ρ vpp + (10 * ρ vt + (2 * b + 2)) ≤ C by omega),
      show ρ vpp + (10 * ρ vt + (2 * b + 2)) = (ρ vpp + 10 * ρ vt + 2 * b + 1) + 1 by omega]
    exact SQ.symNum_some z _ _ (hz b hb)
  have hsum : (((List.range 5).map fun b => (Ex.bin .mul (.c (2 ^ b))
      (.inp (.bin .add (.v vpp) (.bin .add (.bin .mul (.c 10) (.v vt)) (.c (2 * b + 2))))) :
        Ex V)).map fun e => e.eval z C ρ).sum = t.code := by
    rw [← SQ.code_bits_sum t, List.map_map]
    congr 1
    refine List.map_congr_left fun b hb => ?_
    simp only [List.mem_range] at hb
    simp only [Function.comp, eval_bin, ap_mul, eval_c, hbits b hb]
    have : 2 ^ b ≤ 16 := by
      have := Nat.pow_le_pow_right (show 0 < 2 by omega) (show b ≤ 4 by omega); simpa using this
    rw [min_eq_left (by omega : 2 ^ b ≤ C)]
    split_ifs <;> simp <;> omega
  have hcode := CTLP.Tok.code_lt t
  rw [tokCodeE, foldr_add_eval' _ (by rw [hsum]; omega), hsum]

/-- The token loop. -/
def tokLoopP : Pr V := .loop vt (.bin .div (.v vT) (.c 5)) (.seq (.set vc tokCodeE) stepP)

lemma runToks_take_succ (C b0 g0 : ℕ) (s : CS) (cs : List ℕ) (t : ℕ) (ht : t < cs.length) :
    runToks C b0 g0 s (cs.take (t + 1)) =
      ((stepTok C b0 g0 (runToks C b0 g0 s (cs.take t)).1 cs[t]).1,
        (runToks C b0 g0 s (cs.take t)).2 ++
          (stepTok C b0 g0 (runToks C b0 g0 s (cs.take t)).1 cs[t]).2) := by
  rw [List.take_succ_eq_append_getElem ht, runToks_append]
  simp [runToks]

/-- **The token loop.** -/
lemma run_tokLoopP {z : Word} {C : ℕ} (ρ : Fin V → ℕ) (ts : List Tok) (s : CS) (hs : Enc ρ s)
    (hT : ρ vT = 5 * ts.length)
    (hz : ∀ t (ht : t < ts.length), ∀ b < 5,
      z[ρ vpp + 10 * t + 2 * b + 1]? = some ((ts[t]).code.testBit b))
    (hC : ρ vpp + 10 * ts.length + 12 ≤ C) (hC' : 30 ≤ C) :
    (tokLoopP.run z C ρ).2 = encodeToks (runToks C (ρ vb0) (ρ vg0) s (ts.map Tok.code)).2 ∧
      Enc (tokLoopP.run z C ρ).1 (runToks C (ρ vb0) (ρ vg0) s (ts.map Tok.code)).1 ∧
      ∀ v, v ∉ stepW → v ≠ vt → v ≠ vc → (tokLoopP.run z C ρ).1 v = ρ v := by
  unfold tokLoopP
  set cs := ts.map Tok.code with hcs
  have hlen : (Ex.bin .div (.v vT) (.c 5) : Ex V).eval z C ρ = ts.length := by
    simp [hT, min_eq_left (show 5 ≤ C by omega)]
  have key := run_loop_spec (w := z) (C := C) vt (.bin .div (.v vT) (.c 5))
    (.seq (.set vc tokCodeE) stepP) ρ
    (fun t ρ' => Enc ρ' (runToks C (ρ vb0) (ρ vg0) s (cs.take t)).1 ∧
      ∀ v, v ∉ stepW → v ≠ vt → v ≠ vc → ρ' v = ρ v)
    (fun t => encodeToks (stepTok C (ρ vb0) (ρ vg0) (runToks C (ρ vb0) (ρ vg0) s (cs.take t)).1
      (cs[t]!)).2)
    ⟨by simpa [runToks] using hs, fun _ _ _ _ => rfl⟩ (by
      intro t ht ρ' ⟨hE, hfr⟩
      rw [hlen] at ht
      have htc : t < cs.length := by simpa [hcs] using ht
      set ρ1 := Function.update (Function.update ρ' vt t) vc (tokCodeE.eval z C
        (Function.update ρ' vt t))
      have hpp : Function.update ρ' vt t vpp = ρ vpp := by
        rw [Function.update_of_ne (by decide)]; exact hfr _ (by decide) (by decide) (by decide)
      have hcode : tokCodeE.eval z C (Function.update ρ' vt t) = cs[t] := by
        rw [eval_tokCodeE _ (ts[t]'(by simpa [hcs] using htc))]
        · simp [hcs]
        · intro b hb
          rw [hpp, Function.update_self]
          exact hz t (by simpa [hcs] using htc) b hb
        · rw [hpp, Function.update_self]; omega
        · exact hC'
      have hE1 : Enc ρ1 (runToks C (ρ vb0) (ρ vg0) s (cs.take t)).1 := by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hE
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
          simp [ρ1, Function.update_of_ne, h1, h2, h3, h4, h5, h6, md, orc, num, pw, inp, gc, vt, vc]
      have hvc : ρ1 vc = cs[t] := by simp [ρ1, hcode]
      have hb0 : ρ1 vb0 = ρ vb0 := by
        simp only [ρ1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact hfr _ (by decide) (by decide) (by decide)
      have hg0 : ρ1 vg0 = ρ vg0 := by
        simp only [ρ1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
        exact hfr _ (by decide) (by decide) (by decide)
      have hct : cs[t] < 29 := by simp [hcs]; exact CTLP.Tok.code_lt _
      obtain ⟨o1, o2, o3⟩ := run_stepP (z := z) ρ1 _ hE1 hC' (by rw [hvc]; exact hct)
      simp only [run_seq, run_set]
      refine ⟨⟨?_, fun v hv1 hv2 hv3 => ?_⟩, ?_⟩
      · rw [runToks_take_succ _ _ _ _ _ _ htc]
        rw [hvc, hb0, hg0] at o2
        exact o2
      · rw [o3 v hv1]; simp only [ρ1]
        rw [Function.update_of_ne hv3, Function.update_of_ne hv2]; exact hfr v hv1 hv2 hv3
      · simp only [List.nil_append]
        rw [o1, hvc, hb0, hg0, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem htc]
        rfl)
  rw [hlen] at key
  obtain ⟨⟨k1, k2⟩, k3⟩ := key
  have htake : cs.take ts.length = cs := by simp [hcs]
  rw [htake] at k1
  refine ⟨?_, k1, k2⟩
  rw [k3]
  have : ∀ j ≤ cs.length, (List.range j).flatMap (fun t => encodeToks (stepTok C (ρ vb0) (ρ vg0)
      (runToks C (ρ vb0) (ρ vg0) s (cs.take t)).1 (cs[t]!)).2) =
        encodeToks (runToks C (ρ vb0) (ρ vg0) s (cs.take j)).2 := by
    intro j
    induction j with
    | zero => intro; simp [runToks]
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.flatMap_append, ih (by omega),
        runToks_take_succ _ _ _ _ _ _ (by omega), LS.encodeToks_append]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (show j < cs.length by omega)]
  have h2 := this ts.length (by simp [hcs])
  rw [htake] at h2
  exact h2

end GenP

end PathChecking
