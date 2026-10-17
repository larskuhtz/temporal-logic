module

public import RequestProject.LTLPath.FDLG

/-!
# Denotation of the output programs for grid drawings

`LC.Ok.deno_circO`: the program `circO c M Cmax h0` writes the encoding of the grid drawing
`LSys.circ M Cmax h0`.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL Classical LG Grid

variable {x : Word} {Γ : Ctx}

namespace LC.Ok

variable {c : LC} {L : LSys} {s : LSem} {NG : ℕ} (hc : c.Ok x Γ L s NG)
  {M Cm : T} {MV CV : ℕ} (hM : Den x Γ M MV) (hC : Den x Γ Cm CV)
include hc hM hC

lemma den_nodeK {cc t : T} {CC TT : ℕ} (hcc : Den x Γ cc CC) (ht : Den x Γ t TT) :
    Den x Γ (nodeKT c M Cm cc t) (kcode (L.node MV CV CC TT).kind) := by
  have hb : Den x Γ (bndT Cm cc t) ((TT + CC - CV) / 10) :=
    den_div (den_sub (den_add ht hcc) hC) (den_c 10)
  have hp : Den x Γ (phT Cm cc t) ((TT + CC - CV) % 10) :=
    den_mod (den_sub (den_add ht hcc) hC) (den_c 10)
  unfold nodeKT LSys.node
  refine den_ite_eq (den_eq' ht (den_c 0)) (fun h0 => ?_) (fun h0 => ?_)
  · rw [bv_ne_zero] at h0; rw [if_pos h0]
    exact (den_add (den_c 1) (hc.den_colConst hM hcc)).of_eq (by
      cases L.colConst MV CC <;> rfl)
  rw [bv_eq_zero] at h0; rw [if_neg h0]
  refine den_ite_eq (den_lt' (den_add ht hcc) hC) (fun h1 => ?_) (fun h1 => ?_)
  · rw [bv_ne_zero] at h1; rw [if_pos h1]; exact den_c 4
  rw [bv_eq_zero] at h1; rw [if_neg h1]
  refine den_ite_eq (den_eq' hp (den_c 0)) (fun h2 => ?_) (fun h2 => ?_)
  · rw [bv_ne_zero] at h2; rw [if_pos h2]
    refine den_ite_eq (den_eq' (den_mod hcc (den_c 2)) (den_c 0)) (fun h3 => ?_) (fun h3 => ?_)
    · rw [bv_ne_zero] at h3; rw [if_pos h3]
      refine den_ite_eq (hc.den_exG hM hb hcc) (fun h4 => ?_) (fun h4 => ?_)
      · rw [bv_ne_zero] at h4; rw [dif_pos h4]
        exact (hc.dkc (hc.den_findG hM hb hcc h4)).of_eq
          (hc.ag.kc _ (hc.ag.gateAt_iff.1 (Nat.find_spec h4)).1)
      · rw [bv_eq_zero] at h4; rw [dif_neg h4]; exact den_c 4
    · rw [bv_eq_zero] at h3; rw [if_neg h3]
      split_ifs <;> exact den_c 4
  · rw [bv_eq_zero] at h2; rw [if_neg h2]
    split_ifs <;> exact den_c 4

lemma den_nodeS {cc t : T} {CC TT : ℕ} (hcc : Den x Γ cc CC) (ht : Den x Γ t TT) :
    Den x Γ (nodeST c M Cm cc t) (L.node MV CV CC TT).sf.toNat := by
  have hb : Den x Γ (bndT Cm cc t) ((TT + CC - CV) / 10) :=
    den_div (den_sub (den_add ht hcc) hC) (den_c 10)
  have hp : Den x Γ (phT Cm cc t) ((TT + CC - CV) % 10) :=
    den_mod (den_sub (den_add ht hcc) hC) (den_c 10)
  unfold nodeST LSys.node
  refine den_ite_eq (den_eq' ht (den_c 0)) (fun h0 => ?_) (fun h0 => ?_)
  · rw [bv_ne_zero] at h0; rw [if_pos h0]; exact den_c 0
  rw [bv_eq_zero] at h0; rw [if_neg h0]
  refine den_ite_eq (den_lt' (den_add ht hcc) hC) (fun h1 => ?_) (fun h1 => ?_)
  · rw [bv_ne_zero] at h1; rw [if_pos h1]; exact den_c 1
  rw [bv_eq_zero] at h1; rw [if_neg h1]
  refine den_ite_eq (den_eq' hp (den_c 0)) (fun h2 => ?_) (fun h2 => ?_)
  · rw [bv_ne_zero] at h2; rw [if_pos h2]
    refine den_ite_eq (den_eq' (den_mod hcc (den_c 2)) (den_c 0)) (fun h3 => ?_) (fun h3 => ?_)
    · rw [bv_ne_zero] at h3; rw [if_pos h3]
      refine den_ite_eq (hc.den_exG hM hb hcc) (fun h4 => ?_) (fun h4 => ?_)
      · rw [bv_ne_zero] at h4; rw [dif_pos h4]
        have hl := (hc.ag.gateAt_iff.1 (Nat.find_spec h4)).1
        refine (hc.den_sS (hc.den_findG hM hb hcc h4)).of_eq ?_
        rw [GN.sf, hc.ag.sArg_eq hl, bv_bool]
        apply bv_congr
        split_ifs with h5 <;> simp [h5]
      · rw [bv_eq_zero] at h4; rw [dif_neg h4]; exact den_c 1
    · rw [bv_eq_zero] at h3; rw [if_neg h3]
      refine den_ite_eq (hc.den_exGR hM hb (den_sub hcc (den_c 1))) (fun h4 => ?_) (fun h4 => ?_)
      · rw [bv_ne_zero] at h4; rw [if_pos h4]; exact den_c 0
      · rw [bv_eq_zero] at h4; rw [if_neg h4]; exact den_c 1
  · rw [bv_eq_zero] at h2; rw [if_neg h2]
    refine den_ite_eq (hc.den_DDes hM hb hp hcc) (fun h4 => ?_) (fun h4 => ?_)
    · rw [bv_ne_zero] at h4; rw [if_pos h4]; exact den_c 0
    · rw [bv_eq_zero] at h4; rw [if_neg h4]; exact den_c 1

lemma den_nodeD {cc t : T} {CC TT : ℕ} (hcc : Den x Γ cc CC) (ht : Den x Γ t TT) :
    Den x Γ (nodeDT c M Cm cc t) (L.node MV CV CC TT).df.toNat := by
  have hb : Den x Γ (bndT Cm cc t) ((TT + CC - CV) / 10) :=
    den_div (den_sub (den_add ht hcc) hC) (den_c 10)
  have hp : Den x Γ (phT Cm cc t) ((TT + CC - CV) % 10) :=
    den_mod (den_sub (den_add ht hcc) hC) (den_c 10)
  unfold nodeDT LSys.node
  refine den_ite_eq (den_eq' ht (den_c 0)) (fun h0 => ?_) (fun h0 => ?_)
  · rw [bv_ne_zero] at h0; rw [if_pos h0]; exact den_c 0
  rw [bv_eq_zero] at h0; rw [if_neg h0]
  refine den_ite_eq (den_lt' (den_add ht hcc) hC) (fun h1 => ?_) (fun h1 => ?_)
  · rw [bv_ne_zero] at h1; rw [if_pos h1]; exact den_c 0
  rw [bv_eq_zero] at h1; rw [if_neg h1]
  refine den_ite_eq (den_eq' hp (den_c 0)) (fun h2 => ?_) (fun h2 => ?_)
  · rw [bv_ne_zero] at h2; rw [if_pos h2]
    refine den_ite_eq (den_eq' (den_mod hcc (den_c 2)) (den_c 0)) (fun h3 => ?_) (fun h3 => ?_)
    · rw [bv_ne_zero] at h3; rw [if_pos h3]
      refine den_ite_eq (hc.den_exG hM hb hcc) (fun h4 => ?_) (fun h4 => ?_)
      · rw [bv_ne_zero] at h4; rw [dif_pos h4]
        have hl := (hc.ag.gateAt_iff.1 (Nat.find_spec h4)).1
        refine (den_or (hc.den_hasR (hc.den_findG hM hb hcc h4))
          (hc.den_dS (hc.den_findG hM hb hcc h4))).of_eq ?_
        rw [GN.df, hc.ag.dArg_eq hl, hc.ag.hasR_eq hl, bv_bool]
        apply bv_congr
        split_ifs with h5 <;> simp [h5]
      · rw [bv_eq_zero] at h4; rw [dif_neg h4]; exact den_c 0
    · rw [bv_eq_zero] at h3; rw [if_neg h3]
      refine den_ite_eq (hc.den_exGR hM hb (den_sub hcc (den_c 1))) (fun h4 => ?_) (fun h4 => ?_)
      · rw [bv_ne_zero] at h4; rw [if_pos h4]; exact den_c 1
      · rw [bv_eq_zero] at h4; rw [if_neg h4]; exact den_c 0
  · rw [bv_eq_zero] at h2; rw [if_neg h2]
    refine den_ite_eq (hc.den_DDes hM hb hp hcc) (fun h4 => ?_) (fun h4 => ?_)
    · rw [bv_ne_zero] at h4; rw [if_pos h4]; exact den_c 1
    · rw [bv_eq_zero] at h4; rw [if_neg h4]; exact den_c 0

omit hc hM hC in
lemma flatMap_ite_single (b : Bool) (v : ℕ) :
    encodeToks ((if b = true then [v] else []).flatMap natToks) =
      if b = true then encodeToks (natToks v) else [] := by
  cases b <;> simp [encodeToks]

omit hc hM hC in
lemma deno_optNat {f : T} {b : Bool} {i : T} {I : ℕ} (hf : Den x Γ f b.toNat)
    (hi : Den x Γ i I) :
    DenO x Γ (iteO f (natO i) nilO) (if b = true then encodeToks (natToks I) else []) := by
  refine deno_ite_eq hf (fun h => ?_) (fun h => ?_)
  · rw [if_pos (by revert h; cases b <;> simp)]; exact deno_nat hi
  · rw [if_neg (by revert h; cases b <;> simp)]; exact deno_nil

lemma deno_gateN {c0 W n : T} {C0 WV N : ℕ} (hc0 : Den x Γ c0 C0) (hW : Den x Γ W WV)
    (hn : Den x Γ n N) :
    DenO x Γ (gateNO c M Cm c0 W n)
      (encodeToks (Gate.toks (gateOf (fun t j => L.node MV CV (C0 + j) t) WV N))) := by
  unfold gateNO
  refine deno_lett (den_div hn hW) fun kt => ?_
  refine deno_lett (den_sub (den_sub (hW.cons _) (den_c 1)) (den_mod (hn.cons _) (hW.cons _)))
    fun kj => ?_
  set Γ2 := (kj, WV - 1 - N % WV) :: (kt, N / WV) :: Γ
  have s2 : Γ ⊆ Γ2 := fun y hy => by simp [Γ2, hy]
  have hc2 := hc.mono s2
  have hM2 := hM.mono s2
  have hC2 := hC.mono s2
  have hW2 := hW.mono s2
  have hj : Den x Γ2 (varT kj) (WV - 1 - N % WV) := den_var0
  have ht : Den x Γ2 (varT kt) (N / WV) := den_var (by simp [Γ2])
  have hcc : Den x Γ2 (addT c0 (varT kj)) (C0 + (WV - 1 - N % WV)) := den_add (hc0.mono s2) hj
  rw [gateOf_eq, encode_gate_toks (hc.ag.node_kind _ _ _), List.flatMap_append, encodeToks_append,
    flatMap_ite_single, flatMap_ite_single]
  exact deno_seq (deno_tok (den_add (den_c 5) (hc2.den_nodeK hM2 hC2 hcc ht))) (deno_seq
    (deno_tok (den_c 3)) (deno_seq (deno_seq
      (deno_optNat (hc2.den_nodeD hM2 hC2 hcc ht)
        (den_add (den_mul (den_sub ht (den_c 1)) hW2)
          (den_sub (den_sub hW2 (den_c 1)) (den_add hj (den_c 1)))))
      (deno_optNat (hc2.den_nodeS hM2 hC2 hcc ht)
        (den_add (den_mul (den_sub ht (den_c 1)) hW2) (den_sub (den_sub hW2 (den_c 1)) hj))))
      (deno_tok (den_c 4))))

/-- **The output program of the grid drawing.** -/
theorem deno_circO (hB : L.Bd MV CV) {h0 : T} {H0 : ℕ} (hh0 : Den x Γ h0 H0) :
    DenO x Γ (circO c M Cm h0) (L.circ MV CV H0).encode := by
  unfold circO LSys.circ
  refine deno_ite_eq (hc.dliveN hh0) (fun hl => ?_) (fun hl => ?_)
  · have hl' : L.live H0 = true := by revert hl; cases L.live H0 <;> simp
    rw [if_pos hl', Grid.circ, encode_pre]
    have hcol := hc.ag.col_eq (M := MV) hl'
    have hB0 := (hB H0 hl').2
    refine deno_lett (hc.den_col hM hh0) fun k0 => ?_
    refine deno_lett (den_sub (den_add (hC.cons _) (den_c 1)) den_var0) fun kW => ?_
    set Γ2 := (kW, CV + 1 - s.col MV H0) :: (k0, s.col MV H0) :: Γ
    have s2 : Γ ⊆ Γ2 := fun y hy => by simp [Γ2, hy]
    have hc2 := hc.mono s2
    have htim : Den x Γ2 (timT c M Cm h0) (L.tim MV CV H0) := by
      refine (den_sub (den_add (den_mul (den_c 10) (hc2.dY (hh0.mono s2))) (hC.mono s2))
        (hc2.den_col (hM.mono s2) (hh0.mono s2))).of_eq ?_
      unfold LSys.tim; rw [hcol, hc.ag.Y _ hl']
    have hpos : 0 < (L.tim MV CV H0 + 1) * (CV + 1 - s.col MV H0) :=
      Nat.mul_pos (by omega) (by omega)
    rw [hcol, Nat.sub_add_cancel hpos]
    refine deno_loop (den_mul (den_add htim (den_c 1)) den_var0) fun kn i _ => ?_
    exact (hc2.cons _).deno_gateN ((hM.mono s2).cons _) ((hC.mono s2).cons _)
      (den_var (by simp [Γ2])) (den_var (by simp [Γ2])) den_var0
  · have hl' : L.live H0 = false := by revert hl; cases L.live H0 <;> simp
    rw [if_neg (by simp [hl'])]
    exact deno_tick ((hc.dcv hh0).of_eq (hc.ag.cv _ hl'))

end LC.Ok

end FD

end PathChecking
