module

public import RequestProject.ACRound.Gen.TokLoop
public import RequestProject.ACRound.Gen.Util

/-!
# Generating one block of the round circuit

`GenP.blockP` writes the gates of one block: a copy of `CB ℓ` with offsets, padding gates and
the selection gate (`GenP.run_blockP`).  The encoding of `CB ℓ` is read from the input segment
starting at position `ρ vpp`; afterwards `vpp` points to the next segment.
-/

@[expose] public section

namespace PathChecking

namespace GenP

open LL GenC

variable {z : Word} {C : ℕ}

lemma seq_eq {s t : Pr V} {ρ ρ1 ρ2 : Fin V → ℕ} {o1 o2 : List Bool}
    (h1 : s.run z C ρ = (ρ1, o1)) (h2 : t.run z C ρ1 = (ρ2, o2)) :
    (Pr.seq s t).run z C ρ = (ρ2, o1 ++ o2) := by
  simp [run_seq, h1, h2]

/-- Emit `natToks` of the value of `e`. -/
def emitE (e : Ex V) : Pr V := .seq (.set ex e) (emitNat ex ey ei)

lemma run_emitE (e : Ex V) (ρ : Fin V → ℕ) (hC : 2 ≤ C) :
    ∃ ρ', (emitE e).run z C ρ = (ρ', encodeToks (natToks (e.eval z C ρ))) ∧
      ∀ v, v ≠ ex → v ≠ ey → v ≠ ei → ρ' v = ρ v := by
  obtain ⟨ρ', h1, h2⟩ := emitNat_run_eq (z := z) ex ey ei (by decide) hC
    (Function.update ρ ex (e.eval z C ρ))
  refine ⟨ρ', ?_, fun v hv1 hv2 hv3 => ?_⟩
  · unfold emitE
    rw [seq_eq (o1 := []) rfl h1]
    simp
  · rw [h2 v hv2 hv3, Function.update_of_ne hv1]

/-- The block program. -/
def blockP : Pr V :=
  .seq (.set vb0 (.bin .add (.bin .add (.v vg0) (.bin .mul (.c 2) (.bin .add (.v vL) (.c 1))))
    (.bin .mul (.v vl) (.v vS))))
  (.seq (findP vT vfd vj .len (.inp (.bin .add (.v vpp) (.bin .add (.bin .mul (.c 2) (.v vj))
    (.c 1)))))
  (.seq (.set md (.c 0)) (.seq (.set orc (.c 0)) (.seq (.set num (.c 0)) (.seq (.set pw (.c 1))
  (.seq (.set gc (.c 0))
  (.seq tokLoopP
  (.seq (.loop vj (.bin .sub (.bin .sub (.v vS) (.c 1)) (.v gc))
    (outToks [Tok.tag 1, Tok.lpar, Tok.rpar]))
  (.seq (outToks [Tok.tag 4, Tok.lpar])
  (.seq (emitE (.bin .add (.bin .add (.v vg0) (.bin .add (.v vL) (.c 1))) (.v vl)))
  (.seq (emitE (.bin .sub (.bin .add (.v vb0) (.v gc)) (.c 1)))
  (.seq (outToks [Tok.rpar])
  (.set vpp (.bin .add (.bin .add (.v vpp) (.bin .mul (.c 2) (.v vT))) (.c 2)))))))))))))))

/-- Variables written by the block program. -/
def blockW : List (Fin V) :=
  [vb0, vT, vfd, vj, md, orc, num, pw, gc, inp, ex, ey, ei, vt, vc, vpp]

lemma blockP_wr : ∀ v ∈ blockP.wr, v ∈ blockW := by
  simp [blockP, Pr.wr, findP, emitE, emitNat_wr, tokLoopP, stepP, emitCode, outToks, blockW]

/-- The gates of a block, with block offset `b0` and group offset `g0`. -/
def blockList (CB : Circuit) (L S g0 b0 ℓ : ℕ) : List Gate :=
  CB.map (Lay.copyGate b0 g0) ++ List.replicate (S - 1 - CB.length) ⟨.const false, []⟩ ++
    [⟨.and, [g0 + (L + 1) + ℓ, b0 + CB.length - 1]⟩]

lemma flatMap_range_encode (m : ℕ) (g : Gate) :
    (List.range m).flatMap (fun _ => encodeToks g.toks) =
      encodeToks ((List.replicate m g).flatMap Gate.toks) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', List.flatMap_append,
      LS.encodeToks_append]
    simp

/-- **Correctness of the block program.** -/
lemma run_blockP (CB : Circuit) (ρ : Fin V → ℕ) (L S g0 ℓ pp : ℕ)
    (hL : ρ vL = L) (hS : ρ vS = S) (hg : ρ vg0 = g0) (hl : ρ vl = ℓ) (hpp : ρ vpp = pp)
    (hev : ∀ j < CB.encode.length, z[pp + 2 * j]? = some true)
    (hod : ∀ j < CB.encode.length, z[pp + 2 * j + 1]? = CB.encode[j]?)
    (hend : z[pp + 2 * CB.encode.length]? = some false)
    (hwf : CB.WellFormed ℓ) (hsz : CB.length + 1 ≤ S) (hℓL : ℓ ≤ L)
    (hcap : g0 + 2 * (L + 1) + (L + 1) * S + 2 * S + 2 * L + 4 ≤ C)
    (hz : 4 * z.length + 40 ≤ C) :
    ∃ ρ', blockP.run z C ρ =
        (ρ', encodeToks ((blockList CB L S g0 (g0 + 2 * (L + 1) + ℓ * S) ℓ).flatMap Gate.toks)) ∧
      ρ' vpp = pp + 2 * CB.encode.length + 2 := by
  set enc := CB.encode with henc
  set toks := CB.flatMap Gate.toks with htoks
  have hlenc : enc.length = 5 * toks.length := SQ.encodeToks_length toks
  have hzl : pp + 2 * enc.length < z.length := by
    obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hend; exact h
  set b0 := g0 + 2 * (L + 1) + ℓ * S with hb0
  have hℓS : ℓ * S ≤ (L + 1) * S := Nat.mul_le_mul_right _ (by omega)
  have hC2 : 40 ≤ C := by omega
  -- stage 1: `vb0 := b0`
  set ρ1 := Function.update ρ vb0 b0 with hρ1
  have r1 : (Pr.set vb0 (.bin .add (.bin .add (.v vg0) (.bin .mul (.c 2) (.bin .add (.v vL) (.c 1))))
      (.bin .mul (.v vl) (.v vS)))).run z C ρ = (ρ1, []) := by
    simp only [run_set, eval_bin, eval_v, eval_c, ap_add, ap_mul, hg, hL, hl, hS]
    simp (disch := omega) only [min_eq_left]
    rfl
  -- stage 2: find the segment length
  have hlen1 : (Ex.len : Ex V).eval z C ρ1 = z.length := by simp; omega
  obtain ⟨f1, f2, f3⟩ := run_findP (z := z) (C := C) vT vfd vj .len
    (.inp (.bin .add (.v vpp) (.bin .add (.bin .mul (.c 2) (.v vj)) (.c 1)))) (by decide) (by decide)
    (by decide) ρ1 (fun j => symNum (inputSym z (pp + 2 * j + 1))) enc.length (by omega)
    (fun ρ' _ => by simp) (fun i hi ρ' hρ' => by
      rw [hlen1] at hi
      have hpp' : Function.update ρ' vj i vpp = pp := by
        rw [Function.update_of_ne (by decide), hρ' vpp (by decide) (by decide) (by decide), hρ1,
          Function.update_of_ne (by decide), hpp]
      simp only [eval_inp, eval_bin, eval_v, eval_c, ap_add, ap_mul, hpp', Function.update_self]
      simp (disch := omega) only [min_eq_left]
      rw [← Nat.add_assoc])
    (by rw [hlen1]; omega) (by
      show symNum (inputSym z (pp + 2 * enc.length + 1)) = 0
      rw [SQ.symNum_some z _ false hend]; rfl) (fun i hi => by
      show symNum (inputSym z (pp + 2 * i + 1)) ≠ 0
      rw [SQ.symNum_some z _ true (hev i hi)]; simp)
  set ρ2 := ((findP vT vfd vj .len (.inp (.bin .add (.v vpp) (.bin .add (.bin .mul (.c 2) (.v vj))
    (.c 1))))).run z C ρ1).1 with hρ2
  have r2 : (findP vT vfd vj .len (.inp (.bin .add (.v vpp) (.bin .add (.bin .mul (.c 2) (.v vj))
      (.c 1))))).run z C ρ1 = (ρ2, []) := Prod.ext rfl f2
  have h2pp : ρ2 vpp = pp := by
    rw [f3 _ (by decide) (by decide) (by decide), hρ1, Function.update_of_ne (by decide), hpp]
  have h2 : ∀ v, v ≠ vT → v ≠ vfd → v ≠ vj → v ≠ vb0 → ρ2 v = ρ v := fun v a b c d => by
    rw [f3 _ a b c, hρ1, Function.update_of_ne d]
  have h2b0 : ρ2 vb0 = b0 := by
    rw [f3 _ (by decide) (by decide) (by decide), hρ1, Function.update_self]
  -- stage 3: initial transducer state
  set ρ3 := Function.update (Function.update (Function.update (Function.update
    (Function.update ρ2 md 0) orc 0) num 0) pw 1) gc 0 with hρ3
  have r3 : (Pr.seq (.set md (.c 0)) (.seq (.set orc (.c 0)) (.seq (.set num (.c 0))
      (.seq (.set pw (.c 1)) (.set gc (.c 0)))))).run z C ρ2 = (ρ3, []) := by
    simp only [run_seq, run_set, eval_c, min_eq_left (show 0 ≤ C by omega),
      min_eq_left (show 1 ≤ C by omega)]
    rfl
  have h3 : ∀ v, v ≠ md → v ≠ orc → v ≠ num → v ≠ pw → v ≠ gc → ρ3 v = ρ2 v :=
    fun v a b c d e => by simp [hρ3, Function.update_of_ne, a, b, c, d, e]
  set s0 : CS := ⟨false, false, 0, 1, ρ2 inp, 0⟩ with hs0
  have hE3 : Enc ρ3 s0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hρ3, hs0, md, orc, num, pw, inp, gc]
  -- stage 4: the token loop
  have hT3 : ρ3 vT = 5 * toks.length := by
    rw [h3 _ (by decide) (by decide) (by decide) (by decide) (by decide), f1, hlenc]
  have hpp3 : ρ3 vpp = pp := by
    rw [h3 _ (by decide) (by decide) (by decide) (by decide) (by decide), h2pp]
  obtain ⟨t1, t2, t3⟩ := run_tokLoopP (z := z) (C := C) ρ3 toks s0 hE3 hT3 (fun t ht b hb => by
      rw [hpp3, show pp + 10 * t + 2 * b + 1 = pp + 2 * (5 * t + b) + 1 by ring,
        hod _ (by omega), henc, Circuit.encode, SQ.encodeToks_getElem? toks t b ht hb])
    (by rw [hpp3]; omega) (by omega)
  have hb03 : ρ3 vb0 = b0 := by
    rw [h3 _ (by decide) (by decide) (by decide) (by decide) (by decide), h2b0]
  have hg03 : ρ3 vg0 = g0 := by
    rw [h3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      h2 _ (by decide) (by decide) (by decide) (by decide), hg]
  rw [hb03, hg03] at t1 t2
  have hok : ∀ g ∈ CB, GateOk C b0 g0 g := by
    intro g hgm
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hgm
    obtain ⟨ha, hk⟩ := hwf.2 i hi
    refine ⟨fun k hk' => ?_, fun a haa => ?_⟩
    · rw [hk'] at hk
      obtain ⟨hk1, hk2⟩ := hk
      exact ⟨hk2, by omega, by omega⟩
    · have := ha a haa
      constructor <;> omega
  obtain ⟨s', hs'c, hs'gc, hrun⟩ := runToks_gates C b0 g0 CB s0 ⟨rfl, rfl, rfl⟩ hok
    (by simp [hs0]; omega)
  rw [hrun] at t1 t2
  set ρ4 := (tokLoopP.run z C ρ3).1 with hρ4
  have r4 : tokLoopP.run z C ρ3 =
      (ρ4, encodeToks (CB.flatMap fun g => (Lay.copyGate b0 g0 g).toks)) := Prod.ext rfl t1
  have hgc4 : ρ4 gc = CB.length := by rw [t2.2.2.2.2.2, hs'gc]; simp [hs0]
  have h4 : ∀ v, v ∉ stepW → v ≠ vt → v ≠ vc → ρ4 v = ρ3 v := t3
  have hS4 : ρ4 vS = S := by
    rw [h4 _ (by decide) (by decide) (by decide),
      h3 _ (by decide) (by decide) (by decide) (by decide) (by decide),
      h2 _ (by decide) (by decide) (by decide) (by decide), hS]
  -- stage 5: padding
  have hpad := run_loop_spec (w := z) (C := C) vj (.bin .sub (.bin .sub (.v vS) (.c 1)) (.v gc))
    (outToks [Tok.tag 1, Tok.lpar, Tok.rpar]) ρ4 (fun _ ρ' => ∀ v, v ≠ vj → ρ' v = ρ4 v)
    (fun _ => encodeToks [Tok.tag 1, Tok.lpar, Tok.rpar]) (fun _ _ => rfl)
    (fun i _ ρ' hρ' => ⟨fun v hv => by simp [Function.update_of_ne hv, hρ' v hv], by simp⟩)
  have hpadE : (Ex.bin .sub (.bin .sub (.v vS) (.c 1)) (.v gc) : Ex V).eval z C ρ4 =
      S - 1 - CB.length := by
    simp [hS4, hgc4, min_eq_left (show 1 ≤ C by omega)]
  rw [hpadE] at hpad
  set ρ5 := ((Pr.loop vj (.bin .sub (.bin .sub (.v vS) (.c 1)) (.v gc))
    (outToks [Tok.tag 1, Tok.lpar, Tok.rpar])).run z C ρ4).1 with hρ5
  have r5 : (Pr.loop vj (.bin .sub (.bin .sub (.v vS) (.c 1)) (.v gc))
      (outToks [Tok.tag 1, Tok.lpar, Tok.rpar])).run z C ρ4 =
      (ρ5, encodeToks ((List.replicate (S - 1 - CB.length) (⟨.const false, []⟩ : Gate)).flatMap
        Gate.toks)) := by
    refine Prod.ext rfl ?_
    rw [hpad.2, show [Tok.tag 1, Tok.lpar, Tok.rpar] = Gate.toks ⟨.const false, []⟩ by rfl,
      flatMap_range_encode]
  have h5 : ∀ v, v ≠ vj → ρ5 v = ρ4 v := hpad.1
  -- values after the token loop and the padding
  have hv5 : ∀ v, v ∉ stepW → v ≠ vt → v ≠ vc → v ≠ vj → v ≠ md → v ≠ orc → v ≠ num → v ≠ pw →
      v ≠ gc → v ≠ vT → v ≠ vfd → v ≠ vb0 → ρ5 v = ρ v := fun v a b c d e f g h i j k l => by
    rw [h5 v d, h4 v a b c, h3 v e f g h i, h2 v j k d l]
  have hg5 : ρ5 vg0 = g0 := by rw [hv5 vg0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), hg]
  have hL5 : ρ5 vL = L := by rw [hv5 vL (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), hL]
  have hl5 : ρ5 vl = ℓ := by rw [hv5 vl (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide), hl]
  have hb05 : ρ5 vb0 = b0 := by
    rw [h5 _ (by decide), h4 _ (by decide) (by decide) (by decide), hb03]
  have hgc5 : ρ5 gc = CB.length := by rw [h5 _ (by decide), hgc4]
  have hpp5 : ρ5 vpp = pp := by
    rw [h5 _ (by decide), h4 _ (by decide) (by decide) (by decide), hpp3]
  have hT5 : ρ5 vT = enc.length := by
    rw [h5 _ (by decide), h4 _ (by decide) (by decide) (by decide),
      h3 _ (by decide) (by decide) (by decide) (by decide) (by decide), f1]
  -- stage 7, 8: the selection gate
  obtain ⟨ρ7, r7, h7⟩ := run_emitE (z := z) (C := C)
    (.bin .add (.bin .add (.v vg0) (.bin .add (.v vL) (.c 1))) (.v vl)) ρ5 (by omega)
  have e7 : (Ex.bin .add (.bin .add (.v vg0) (.bin .add (.v vL) (.c 1))) (.v vl) : Ex V).eval
      z C ρ5 = g0 + (L + 1) + ℓ := by
    simp only [eval_bin, eval_v, eval_c, ap_add, hg5, hL5, hl5]
    simp (disch := omega) only [min_eq_left]
  rw [e7] at r7
  obtain ⟨ρ8, r8, h8⟩ := run_emitE (z := z) (C := C)
    (.bin .sub (.bin .add (.v vb0) (.v gc)) (.c 1)) ρ7 (by omega)
  have e8 : (Ex.bin .sub (.bin .add (.v vb0) (.v gc)) (.c 1) : Ex V).eval z C ρ7 =
      b0 + CB.length - 1 := by
    simp only [eval_bin, eval_v, eval_c, ap_add, ap_sub,
      h7 vb0 (by decide) (by decide) (by decide), h7 gc (by decide) (by decide) (by decide),
      hb05, hgc5]
    simp (disch := omega) only [min_eq_left]
  rw [e8] at r8
  have hpp8 : ρ8 vpp = pp := by
    rw [h8 _ (by decide) (by decide) (by decide), h7 _ (by decide) (by decide) (by decide), hpp5]
  have hT8 : ρ8 vT = enc.length := by
    rw [h8 _ (by decide) (by decide) (by decide), h7 _ (by decide) (by decide) (by decide), hT5]
  -- stage 10
  have r10 : (Pr.set vpp (.bin .add (.bin .add (.v vpp) (.bin .mul (.c 2) (.v vT))) (.c 2))).run
      z C ρ8 = (Function.update ρ8 vpp (pp + 2 * enc.length + 2), []) := by
    simp only [run_set, eval_bin, eval_v, eval_c, ap_add, ap_mul, hpp8, hT8]
    simp (disch := omega) only [min_eq_left]
  refine ⟨Function.update ρ8 vpp (pp + 2 * enc.length + 2), ?_, by simp⟩
  have rmd : (Pr.set md (.c 0)).run z C ρ2 = (Function.update ρ2 md 0, []) := by
    simp
  have rorc : (Pr.set orc (.c 0)).run z C (Function.update ρ2 md 0) =
      (Function.update (Function.update ρ2 md 0) orc 0, []) := by
    simp
  have rnum : (Pr.set num (.c 0)).run z C (Function.update (Function.update ρ2 md 0) orc 0) =
      (Function.update (Function.update (Function.update ρ2 md 0) orc 0) num 0, []) := by
    simp
  have rpw : (Pr.set pw (.c 1)).run z C
      (Function.update (Function.update (Function.update ρ2 md 0) orc 0) num 0) =
      (Function.update (Function.update (Function.update (Function.update ρ2 md 0) orc 0) num 0)
        pw 1, []) := by
    simp [min_eq_left (show 1 ≤ C by omega)]
  have rgc : (Pr.set gc (.c 0)).run z C
      (Function.update (Function.update (Function.update (Function.update ρ2 md 0) orc 0) num 0)
        pw 1) = (ρ3, []) := by
    simp [hρ3]
  have r6 : (outToks [Tok.tag 4, Tok.lpar] : Pr V).run z C ρ5 =
      (ρ5, encodeToks [Tok.tag 4, Tok.lpar]) := by simp
  have r9 : (outToks [Tok.rpar] : Pr V).run z C ρ8 = (ρ8, encodeToks [Tok.rpar]) := by simp
  unfold blockP
  rw [seq_eq r1 (seq_eq r2 (seq_eq rmd (seq_eq rorc (seq_eq rnum (seq_eq rpw (seq_eq rgc
    (seq_eq r4 (seq_eq r5 (seq_eq r6 (seq_eq r7 (seq_eq r8 (seq_eq r9 r10))))))))))))]
  simp only [blockList, List.flatMap_append, List.flatMap_map, LS.encodeToks_append,
    List.nil_append, List.append_nil, List.append_assoc]
  simp [Gate.toks, LS.encodeToks_append, LS.encodeToks_cons]

end GenP

end PathChecking
