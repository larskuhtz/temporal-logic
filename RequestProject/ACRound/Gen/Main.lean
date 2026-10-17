module

public import RequestProject.ACRound.Gen.Setup

/-!
# The generator of the round circuit

`GenP.mainP G` writes the encoding of the round circuit `(G.lay CB n).circ` when run on the
generator input `1ⁿ 0 ⋯` (`GenP.run_mainP`).
-/

@[expose] public section

namespace PathChecking

namespace GenP

open LL GenC

variable {z : Word} {C : ℕ}

/-! ## The prefix gates -/

/-- Constants and input gates. -/
def prefixP : Pr V :=
  .seq (outToks [Tok.tag 1, Tok.lpar, Tok.rpar, Tok.tag 2, Tok.lpar, Tok.rpar])
    (.loop vi (.v vn) (.seq (outToks [Tok.tag 0]) (.seq (emitE (.v vi)) (outToks [Tok.lpar, Tok.rpar]))))

lemma run_prefixP (P : Lay) (ρ : Fin V → ℕ) (hE : Env P ρ) (hC : 2 ≤ C) :
    ∃ ρ', prefixP.run z C ρ = (ρ', encodeToks (P.prefixGates.flatMap Gate.toks)) ∧
      ∀ v, v ∉ vi :: qW → ρ' v = ρ v := by
  obtain ⟨ρ', h1, h2⟩ := run_loop_emit (z := z) (C := C) vi (.v vn)
    (.seq (outToks [Tok.tag 0]) (.seq (emitE (.v vi)) (outToks [Tok.lpar, Tok.rpar]))) ρ (vi :: qW)
    (fun i => encodeToks (Gate.toks ⟨.input i, []⟩)) (fun i _ ρ' hρ' => by
      obtain ⟨ρ'', g1, g2⟩ := run_emitE (z := z) (C := C) (.v vi) (Function.update ρ' vi i) hC
      refine ⟨ρ'', ?_, fun v hv => ?_⟩
      · rw [seq_eq (run_outToks_eq _ _) (seq_eq g1 (run_outToks_eq _ _))]
        simp [Gate.toks, LS.encodeToks_append, LS.encodeToks_cons]
      · rw [g2 v (ne_of_nmem hv (by decide)) (ne_of_nmem hv (by decide))
          (ne_of_nmem hv (by decide)), Function.update_of_ne (ne_of_nmem hv (by decide)),
          hρ' v hv])
  refine ⟨ρ', ?_, h2⟩
  unfold prefixP
  rw [seq_eq (run_outToks_eq _ _) h1]
  simp only [eval_v, hE.1, Lay.prefixGates, List.flatMap_append, LS.encodeToks_append,
    encodeToks_flatMap, List.flatMap_map]
  simp [Gate.toks, LS.encodeToks_append, LS.encodeToks_cons]

/-! ## The groups -/

/-- All groups. -/
def groupsP : Pr V := .loop vr (.v vR) (.loop vq (.v vNq) groupP)

lemma run_groupsP (P : Lay) (ρ : Fin V → ℕ) (hE : Env P ρ)
    (hseg : ∀ ℓ ≤ P.L, SegOk z (P.CB ℓ) (P.n + 1 + GenI.offW P.CB ℓ))
    (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ) (hsz : P.SizeOk)
    (hcap : P.F0 + 2 * P.S + 2 * P.L + 10 ≤ C) (hz : 4 * z.length + 40 ≤ C) :
    ∃ ρ', groupsP.run z C ρ = (ρ', encodeToks (((List.range P.R).flatMap
        (fun r => (List.range P.Nq).flatMap (P.groupGates r))).flatMap Gate.toks)) ∧
      ∀ v, v ∉ vr :: vq :: groupW → ρ' v = ρ v := by
  obtain ⟨ρ', h1, h2⟩ := run_loop_emit (z := z) (C := C) vr (.v vR) (.loop vq (.v vNq) groupP) ρ
    (vr :: vq :: groupW)
    (fun r => encodeToks (((List.range P.Nq).flatMap (P.groupGates r)).flatMap Gate.toks))
    (fun r hr ρ' hρ' => by
      simp only [eval_v, hE.2.2.1] at hr
      have hfr : ∀ v, v ∉ vr :: vq :: groupW → Function.update ρ' vr r v = ρ v := fun v hv => by
        rw [Function.update_of_ne (ne_of_nmem hv (by simp)), hρ' v hv]
      obtain ⟨ρ'', g1, g2⟩ := run_loop_emit (z := z) (C := C) vq (.v vNq) groupP
        (Function.update ρ' vr r) (vq :: groupW)
        (fun q => encodeToks ((P.groupGates r q).flatMap Gate.toks)) (fun q hq ρ2 hρ2 => by
          have hfr2 : ∀ v, v ∉ vq :: groupW → Function.update ρ2 vq q v =
              Function.update ρ' vr r v := fun v hv => by
            rw [Function.update_of_ne (ne_of_nmem hv (by simp)), hρ2 v hv]
          have hE2 : Env P (Function.update ρ2 vq q) := hE.frame (vr :: vq :: groupW) (by decide)
            (fun v hv => by rw [hfr2 v (fun h => hv (List.mem_cons_of_mem _ h)), hfr v hv])
          have hq' : q < P.Nq := by
            simp only [eval_v] at hq
            rwa [hfr vNq (by decide), hE.2.1] at hq
          obtain ⟨ρ3, k1, k2⟩ := run_groupP (z := z) (C := C) P (Function.update ρ2 vq q) hE2 r q
            (by rw [hfr2 vr (by decide), Function.update_self]) (by simp) hr hq' hseg hwf hsz
            hcap hz
          refine ⟨ρ3, k1, fun v hv => ?_⟩
          rw [k2 v (fun h => hv (List.mem_cons_of_mem _ h)), hfr2 v hv])
      refine ⟨ρ'', ?_, fun v hv => ?_⟩
      · rw [g1]
        simp only [eval_v, hfr vNq (by decide), hE.2.1, List.flatMap_assoc, encodeToks_flatMap]
      · rw [g2 v (fun h => hv (List.mem_cons_of_mem _ h)), hfr v hv])
  refine ⟨ρ', ?_, h2⟩
  unfold groupsP
  rw [h1]
  simp only [eval_v, hE.2.2.1, List.flatMap_assoc, encodeToks_flatMap]

/-! ## The final gates -/

/-- `F0` -/
def F0E : Ex V :=
  .bin .add (.bin .add (.v vn) (.c 2)) (.bin .mul (.bin .mul (.v vR) (.v vNq)) (.v vW))

/-- The final gates. -/
def finalP : Pr V :=
  .seq (.set vr (.v vR)) (.seq (.set vq (.c 0)) (.seq (.set vi (.c 0))
  (.seq (oracleGateP true false) (.seq (.set vi (.c 1)) (.seq (oracleGateP true true)
  (.seq (outToks [Tok.tag 4, Tok.lpar]) (.seq (emitE F0E)
  (.seq (emitE (.bin .add F0E (.c 1))) (outToks [Tok.rpar])))))))))

lemma run_oracleGateP (P : Lay) (t b : Bool) (ρ : Fin V → ℕ) (hE : Env P ρ) (r q i : ℕ)
    (hr : ρ vr = r) (hq : ρ vq = q) (hi : ρ vi = i) (hrR : r ≤ P.R)
    (hcap : P.P0 + P.R * P.Nq * P.W + 2 ≤ C) :
    ∃ ρ', (oracleGateP t b).run z C ρ =
        (ρ', encodeToks (Gate.toks ⟨.oracle, P.qArgs t b i r q⟩)) ∧
      ∀ v, v ∉ qW → ρ' v = ρ v := by
  obtain ⟨ρ', g1, g2⟩ := run_qArgsP (z := z) (C := C) P t b vr vq vi (by decide) (by decide) ρ hE
    r q i hr hq hi hrR hcap
  refine ⟨ρ', ?_, g2⟩
  unfold oracleGateP
  rw [seq_eq (run_outToks_eq _ _) (seq_eq g1 (run_outToks_eq _ _))]
  simp [Gate.toks, LS.encodeToks_append, LS.encodeToks_cons]

lemma eval_F0E (P : Lay) (ρ : Fin V → ℕ) (hE : Env P ρ) (hcap : P.F0 + 2 ≤ C) :
    F0E.eval z C ρ = P.F0 := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hE
  have hW := Lay.W_pos (P := P)
  have hRN : P.R * P.Nq ≤ P.R * P.Nq * P.W := Nat.le_mul_of_pos_right _ hW
  have hF : P.F0 = P.n + 2 + P.R * P.Nq * P.W := rfl
  simp only [F0E, eval_bin, eval_v, eval_c, ap_add, ap_mul, e1, e2, e3, e6]
  simp (disch := omega) only [min_eq_left]
  omega

lemma run_finalP (P : Lay) (ρ : Fin V → ℕ) (hE : Env P ρ) (hcap : P.F0 + 4 ≤ C) :
    (finalP.run z C ρ).2 = encodeToks (P.finalGates.flatMap Gate.toks) := by
  have hF : P.F0 = P.P0 + P.R * P.Nq * P.W := rfl
  have hE1 : Env P (Function.update (Function.update (Function.update ρ vr P.R) vq 0) vi 0) :=
    hE.frame [vr, vq, vi] (by decide) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hv
      rw [Function.update_of_ne hv.2.2, Function.update_of_ne hv.2.1, Function.update_of_ne hv.1])
  obtain ⟨ρ4, g4, f4⟩ := run_oracleGateP (z := z) (C := C) P true false _ hE1 P.R 0 0
    (by rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
      Function.update_self])
    (by rw [Function.update_of_ne (by decide), Function.update_self]) (by simp) le_rfl (by omega)
  have hE4 : Env P (Function.update ρ4 vi 1) := (hE1.frame qW (by decide) f4).frame [vi]
    (by decide) (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [Function.update_of_ne hv])
  obtain ⟨ρ6, g6, f6⟩ := run_oracleGateP (z := z) (C := C) P true true _ hE4 P.R 0 1
    (by rw [Function.update_of_ne (by decide), f4 _ (by decide), Function.update_of_ne (by decide),
      Function.update_of_ne (by decide), Function.update_self])
    (by rw [Function.update_of_ne (by decide), f4 _ (by decide), Function.update_of_ne (by decide),
      Function.update_self])
    (by simp) le_rfl (by omega)
  have hE6 : Env P ρ6 := hE4.frame qW (by decide) f6
  obtain ⟨ρ8, g8, f8⟩ := run_emitE (z := z) (C := C) F0E ρ6 (by omega)
  have hE8 : Env P ρ8 := hE6.frame qW (by decide) (fun v hv =>
    f8 v (ne_of_nmem hv (by decide)) (ne_of_nmem hv (by decide)) (ne_of_nmem hv (by decide)))
  obtain ⟨ρ9, g9, -⟩ := run_emitE (z := z) (C := C) (.bin .add F0E (.c 1)) ρ8 (by omega)
  have r1 : (Pr.set vr (.v vR) : Pr V).run z C ρ = (Function.update ρ vr P.R, []) := by
    simp [hE.2.2.1]
  have r2 : (Pr.set vq (.c 0) : Pr V).run z C (Function.update ρ vr P.R) =
      (Function.update (Function.update ρ vr P.R) vq 0, []) := by simp
  have r3 : (Pr.set vi (.c 0) : Pr V).run z C (Function.update (Function.update ρ vr P.R) vq 0) =
      (Function.update (Function.update (Function.update ρ vr P.R) vq 0) vi 0, []) := by simp
  have r5 : (Pr.set vi (.c 1) : Pr V).run z C ρ4 = (Function.update ρ4 vi 1, []) := by
    simp [min_eq_left (show 1 ≤ C by omega)]
  unfold finalP
  rw [seq_eq r1 (seq_eq r2 (seq_eq r3 (seq_eq g4 (seq_eq r5 (seq_eq g6 (seq_eq
    (run_outToks_eq _ _) (seq_eq g8 (seq_eq g9 (run_outToks_eq _ _)))))))))]
  have h8 : F0E.eval z C ρ6 = P.F0 := eval_F0E P ρ6 hE6 (by omega)
  have h9 : (Ex.bin .add F0E (.c 1) : Ex V).eval z C ρ8 = P.F0 + 1 := by
    rw [eval_bin, ap_add, eval_c, eval_F0E (z := z) (C := C) P ρ8 hE8 (by omega)]
    simp (disch := omega) only [min_eq_left]
  rw [h8, h9]
  simp [Lay.finalGates, Gate.toks, LS.encodeToks_append, LS.encodeToks_cons]

/-! ## The generator -/

/-- The generator of the round circuit. -/
def mainP (G : GCst) : Pr V := .seq (paramsP G) (.seq prefixP (.seq groupsP finalP))

/-- **Correctness of the generator.** -/
lemma run_mainP (G : GCst) (CB : ℕ → Circuit) (n : ℕ) (ρ : Fin V → ℕ)
    (hun : ∀ i < n, z[i]? = some true) (hsep : z[n]? = some false)
    (hseg : ∀ ℓ ≤ G.L n, SegOk z (CB ℓ) (n + 1 + GenI.offW CB ℓ))
    (hwf : ∀ ℓ ≤ G.L n, (CB ℓ).WellFormed ℓ) (hsz : (G.lay CB n).SizeOk)
    (hC : G.Mb n ≤ C) (hz : 4 * z.length + 40 ≤ C) :
    ((mainP G).run z C ρ).2 = (G.lay CB n).circ.encode := by
  set P := G.lay CB n
  have hcap : P.F0 + 2 * P.S + 2 * P.L + 10 ≤ C := by
    unfold GCst.Mb at hC
    simp only [P, GCst.lay_F0]
    exact le_trans (by simp only [GCst.lay]; omega) hC
  obtain ⟨ρ1, r1, hE1⟩ := run_paramsP (z := z) (C := C) G CB n ρ hun hsep hC hz
  obtain ⟨ρ2, r2, f2⟩ := run_prefixP (z := z) (C := C) P ρ1 hE1 (by omega)
  have hE2 : Env P ρ2 := hE1.frame _ (by decide) f2
  obtain ⟨ρ3, r3, f3⟩ := run_groupsP (z := z) (C := C) P ρ2 hE2 hseg hwf hsz hcap hz
  have hE3 : Env P ρ3 := hE2.frame _ (by decide) f3
  have r4 := run_finalP (z := z) (C := C) P ρ3 hE3 (by omega)
  unfold mainP
  rw [run_seq, r1]
  simp only [run_seq, r2, r3, r4, List.nil_append]
  simp only [Circuit.encode, Lay.circ, List.flatMap_append, LS.encodeToks_append, List.append_assoc]

end GenP

end PathChecking
