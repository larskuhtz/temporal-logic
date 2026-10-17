module

public import RequestProject.ACRound.Gen.Block
public import RequestProject.ACRound.WF
public import RequestProject.ACRound.Gen.Input

/-!
# Generating the oracle-gate arguments and the groups of the round circuit

* `GenP.qArgsP`: the arguments `Lay.qArgs t b i r q` of an oracle gate;
* `GenP.groupP`: all gates of the group of round `r` and query `q`.
-/

@[expose] public section

namespace PathChecking

namespace GenP

open LL GenC

variable {z : Word} {C : ℕ}

/-- Generic loop rule with a frame `Wr` of written variables. -/
lemma run_loop_emit (x : Fin V) (e : Ex V) (body : Pr V) (ρ : Fin V → ℕ) (Wr : List (Fin V))
    (out : ℕ → List Bool)
    (hbody : ∀ k < e.eval z C ρ, ∀ ρ', (∀ v, v ∉ Wr → ρ' v = ρ v) →
      ∃ ρ'', body.run z C (Function.update ρ' x k) = (ρ'', out k) ∧ ∀ v, v ∉ Wr → ρ'' v = ρ v) :
    ∃ ρ', (Pr.loop x e body).run z C ρ = (ρ', (List.range (e.eval z C ρ)).flatMap out) ∧
      ∀ v, v ∉ Wr → ρ' v = ρ v := by
  have h := run_loop_spec (w := z) (C := C) x e body ρ (fun _ ρ' => ∀ v, v ∉ Wr → ρ' v = ρ v) out
    (fun _ _ => rfl) (fun k hk ρ' hρ' => by
      obtain ⟨ρ'', h1, h2⟩ := hbody k hk ρ' hρ'
      rw [h1]; exact ⟨h2, rfl⟩)
  exact ⟨_, Prod.ext rfl h.2, h.1⟩

/-- Environment: the variables holding the layout parameters. -/
def Env (P : Lay) (ρ : Fin V → ℕ) : Prop :=
  ρ vn = P.n ∧ ρ vNq = P.Nq ∧ ρ vR = P.R ∧ ρ vL = P.L ∧ ρ vS = P.S ∧ ρ vW = P.W

/-- inner loop counter -/
abbrev vk : Fin V := 27

/-- `ans r k` for `r` in `ri` and `k` in `vk`, if `r ≠ 0`. -/
def ansE (ri : Fin V) : Ex V :=
  .bin .sub (.bin .add (.bin .add (.v vn) (.c 2))
    (.bin .mul (.bin .add (.bin .add (.bin .mul (.bin .sub (.v ri) (.c 1)) (.v vNq)) (.v vk)) (.c 1))
      (.v vW))) (.c 1)

/-- The arguments of `packArgs r q` (`r` in `ri`, `q` in `qi`). -/
def packP (ri qi : Fin V) : Pr V :=
  .seq (.loop vk (.v vn) (outToks (natToks 1)))
  (.seq (outToks (natToks 0))
  (.seq (.loop vk (.v vn) (emitE (.bin .add (.c 2) (.v vk))))
  (.seq (.loop vk (.v vNq) (.ite (.bin .eq (.v ri) (.c 0)) (outToks (natToks 0)) (emitE (ansE ri))))
  (.seq (.loop vk (.bin .sub (.v vNq) (.v qi)) (outToks (natToks 0)))
    (.loop vk (.v qi) (outToks (natToks 1)))))))

/-- The arguments of `qArgs t b i r q` (`i` in `ii`). -/
def qArgsP (t b : Bool) (ri qi ii : Fin V) : Pr V :=
  .seq (outToks (natToks 1 ++ natToks (Lay.bitIdx t) ++ natToks (Lay.bitIdx b)))
  (.seq (.loop vk (.v ii) (outToks (natToks 1)))
  (.seq (outToks (natToks 0)) (packP ri qi)))

/-- Variables written by `qArgsP`. -/
def qW : List (Fin V) := [vk, ex, ey, ei]

lemma encodeToks_replicate_flatMap (m : ℕ) (a : ℕ) :
    (List.range m).flatMap (fun _ => encodeToks (natToks a)) =
      encodeToks ((List.replicate m a).flatMap natToks) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ', List.flatMap_append,
      LS.encodeToks_append]
    simp

lemma encodeToks_range_flatMap (m : ℕ) (f : ℕ → ℕ) :
    (List.range m).flatMap (fun k => encodeToks (natToks (f k))) =
      encodeToks (((List.range m).map f).flatMap natToks) := by
  rw [encodeToks_flatMap, List.flatMap_map]

lemma ne_of_nmem {W : List (Fin V)} {v x : Fin V} (hv : v ∉ W) (hx : x ∈ W) : v ≠ x :=
  fun h => hv (h ▸ hx)

lemma run_outToks_eq (ts : List Tok) (ρ : Fin V → ℕ) :
    (outToks ts : Pr V).run z C ρ = (ρ, encodeToks ts) := by simp

/-- A loop emitting a constant number. -/
lemma run_loop_const (x : Fin V) (e : Ex V) (a : ℕ) (ρ : Fin V → ℕ) (hx : x ∈ qW) :
    ∃ ρ', (Pr.loop x e (outToks (natToks a))).run z C ρ =
        (ρ', encodeToks ((List.replicate (e.eval z C ρ) a).flatMap natToks)) ∧
      ∀ v, v ∉ qW → ρ' v = ρ v := by
  obtain ⟨ρ', h1, h2⟩ := run_loop_emit (z := z) (C := C) x e (outToks (natToks a)) ρ qW
    (fun _ => encodeToks (natToks a)) (fun k _ ρ' hρ' => ⟨_, run_outToks_eq _ _, fun v hv => by
      rw [Function.update_of_ne (ne_of_nmem hv hx), hρ' v hv]⟩)
  exact ⟨ρ', by rw [h1, encodeToks_replicate_flatMap], h2⟩

/-- **The arguments of `packArgs`.** -/
lemma run_packP (P : Lay) (ri qi : Fin V) (hri : ri ∉ qW) (hqi : qi ∉ qW)
    (ρ : Fin V → ℕ) (hE : Env P ρ) (r q : ℕ) (hr : ρ ri = r) (hq : ρ qi = q)
    (hrR : r ≤ P.R) (hcap : P.P0 + P.R * P.Nq * P.W + 2 ≤ C) :
    ∃ ρ', (packP ri qi).run z C ρ = (ρ', encodeToks ((P.packArgs r q).flatMap natToks)) ∧
      ∀ v, v ∉ qW → ρ' v = ρ v := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hE
  have hW := Lay.W_pos (P := P)
  have hRN : P.R * P.Nq ≤ P.R * P.Nq * P.W := Nat.le_mul_of_pos_right _ hW
  have hP0 : P.P0 = P.n + 2 := rfl
  have hvk : vk ∈ qW := by decide
  -- the six loops
  obtain ⟨ρ1, r1, f1⟩ := run_loop_const (z := z) (C := C) vk (.v vn) 1 ρ hvk
  obtain ⟨ρ3, r3, f3⟩ := run_loop_emit (z := z) (C := C) vk (.v vn)
    (emitE (.bin .add (.c 2) (.v vk))) ρ1 qW (fun k => encodeToks (natToks (2 + k)))
    (fun k hk ρ' hρ' => by
      obtain ⟨ρ'', h1, h2⟩ := run_emitE (z := z) (C := C) (.bin .add (.c 2) (.v vk))
        (Function.update ρ' vk k) (by omega)
      refine ⟨ρ'', ?_, fun v hv => ?_⟩
      · rw [h1]; congr 3
        simp only [eval_bin, eval_c, eval_v, ap_add, Function.update_self] at hk ⊢
        rw [f1 vn (by decide), e1] at hk
        simp (disch := omega) only [min_eq_left]
      · rw [h2 v (ne_of_nmem hv (by decide)) (ne_of_nmem hv (by decide))
          (ne_of_nmem hv (by decide)), Function.update_of_ne (ne_of_nmem hv hvk), hρ' v hv])
  have g1 : ∀ v, v ∉ qW → ρ3 v = ρ v := fun v hv => by rw [f3 v hv, f1 v hv]
  obtain ⟨ρ4, r4, f4⟩ := run_loop_emit (z := z) (C := C) vk (.v vNq)
    (.ite (.bin .eq (.v ri) (.c 0)) (outToks (natToks 0)) (emitE (ansE ri))) ρ3 qW
    (fun k => encodeToks (natToks (P.ans r k))) (fun k hk ρ' hρ' => by
      simp only [eval_v, g1 vNq (by decide), e2] at hk
      have hri' : Function.update ρ' vk k ri = r := by
        rw [Function.update_of_ne (ne_of_nmem hri hvk), hρ' ri hri, g1 ri hri, hr]
      rcases r with _ | r'
      · rw [run_ite_pos (by simp [hri'])]
        exact ⟨_, run_outToks_eq _ _, fun v hv => by
          rw [Function.update_of_ne (ne_of_nmem hv hvk), hρ' v hv, g1 v hv]⟩
      · rw [run_ite_neg (by simp [hri'])]
        obtain ⟨ρ'', h1, h2⟩ := run_emitE (z := z) (C := C) (ansE ri) (Function.update ρ' vk k)
          (by omega)
        refine ⟨ρ'', ?_, fun v hv => ?_⟩
        · rw [h1]; congr 3
          have hn' : Function.update ρ' vk k vn = P.n := by
            rw [Function.update_of_ne (by decide), hρ' vn (by decide), g1 vn (by decide), e1]
          have hN' : Function.update ρ' vk k vNq = P.Nq := by
            rw [Function.update_of_ne (by decide), hρ' vNq (by decide), g1 vNq (by decide), e2]
          have hW' : Function.update ρ' vk k vW = P.W := by
            rw [Function.update_of_ne (by decide), hρ' vW (by decide), g1 vW (by decide), e6]
          have hk2 : r' * P.Nq + k + 1 ≤ P.R * P.Nq := by
            have : (r' + 1) * P.Nq ≤ P.R * P.Nq := Nat.mul_le_mul_right _ hrR
            nlinarith
          have hk3 : (r' * P.Nq + k + 1) * P.W ≤ P.R * P.Nq * P.W := Nat.mul_le_mul_right _ hk2
          have hk4 : r' * P.Nq + k + 1 ≤ (r' * P.Nq + k + 1) * P.W := Nat.le_mul_of_pos_right _ hW
          simp only [ansE, eval_bin, eval_v, eval_c, ap_add, ap_sub, ap_mul, hn', hN', hW', hri',
            Function.update_self]
          simp (disch := omega) only [min_eq_left, Nat.add_sub_cancel]
          simp only [Lay.ans, Lay.gb, hP0]
          have : (r' * P.Nq + k + 1) * P.W = (r' * P.Nq + k) * P.W + P.W := by ring
          omega
        · rw [h2 v (ne_of_nmem hv (by decide)) (ne_of_nmem hv (by decide))
            (ne_of_nmem hv (by decide)), Function.update_of_ne (ne_of_nmem hv hvk), hρ' v hv,
            g1 v hv])
  obtain ⟨ρ5, r5, f5⟩ := run_loop_const (z := z) (C := C) vk (.bin .sub (.v vNq) (.v qi)) 0 ρ4 hvk
  obtain ⟨ρ6, r6, f6⟩ := run_loop_const (z := z) (C := C) vk (.v qi) 1 ρ5 hvk
  have g4 : ∀ v, v ∉ qW → ρ4 v = ρ v := fun v hv => by rw [f4 v hv, g1 v hv]
  have g5 : ∀ v, v ∉ qW → ρ5 v = ρ v := fun v hv => by rw [f5 v hv, g4 v hv]
  refine ⟨ρ6, ?_, fun v hv => by rw [f6 v hv, g5 v hv]⟩
  unfold packP
  rw [seq_eq r1 (seq_eq (run_outToks_eq _ _) (seq_eq r3 (seq_eq r4 (seq_eq r5 r6))))]
  simp only [eval_v, eval_bin, ap_sub, e1, f1 vn (by decide), g1 vNq (by decide), e2,
    g4 vNq (by decide), g4 qi hqi, hq, g5 qi hqi]
  simp only [Lay.packArgs, List.flatMap_append, LS.encodeToks_append, encodeToks_range_flatMap,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- **The arguments of an oracle gate.** -/
lemma run_qArgsP (P : Lay) (t b : Bool) (ri qi ii : Fin V) (hri : ri ∉ qW) (hqi : qi ∉ qW)
    (ρ : Fin V → ℕ) (hE : Env P ρ) (r q i : ℕ) (hr : ρ ri = r) (hq : ρ qi = q)
    (hi : ρ ii = i) (hrR : r ≤ P.R) (hcap : P.P0 + P.R * P.Nq * P.W + 2 ≤ C) :
    ∃ ρ', (qArgsP t b ri qi ii).run z C ρ =
        (ρ', encodeToks ((P.qArgs t b i r q).flatMap natToks)) ∧
      ∀ v, v ∉ qW → ρ' v = ρ v := by
  have hvk : vk ∈ qW := by decide
  obtain ⟨ρ2, r2, f2⟩ := run_loop_const (z := z) (C := C) vk (.v ii) 1 ρ hvk
  obtain ⟨ρ4, r4, f4⟩ := run_packP (z := z) (C := C) P ri qi hri hqi ρ2
    (by obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hE
        exact ⟨by rw [f2 _ (by decide), e1], by rw [f2 _ (by decide), e2],
          by rw [f2 _ (by decide), e3], by rw [f2 _ (by decide), e4],
          by rw [f2 _ (by decide), e5], by rw [f2 _ (by decide), e6]⟩)
    r q (by rw [f2 _ hri, hr]) (by rw [f2 _ hqi, hq]) hrR hcap
  refine ⟨ρ4, ?_, fun v hv => by rw [f4 v hv, f2 v hv]⟩
  unfold qArgsP
  rw [seq_eq (run_outToks_eq _ _) (seq_eq r2 (seq_eq (run_outToks_eq _ _) r4))]
  simp only [eval_v, hi, Lay.qArgs, List.flatMap_append, LS.encodeToks_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-! ## Groups -/

/-- `L + 1` -/
def L1E : Ex V := .bin .add (.v vL) (.c 1)

/-- An oracle gate with arguments `qArgs t b i r q` (`i` in `vi`). -/
def oracleGateP (t b : Bool) : Pr V :=
  .seq (outToks [Tok.tag 6, Tok.lpar]) (.seq (qArgsP t b vr vq vi) (outToks [Tok.rpar]))

/-- The group program (round in `vr`, query in `vq`). -/
def groupP : Pr V :=
  .seq (.set vg0 (.bin .add (.bin .add (.v vn) (.c 2))
    (.bin .mul (.bin .add (.bin .mul (.v vr) (.v vNq)) (.v vq)) (.v vW))))
  (.seq (.loop vi L1E (oracleGateP false false))
  (.seq (.loop vi L1E (oracleGateP false true))
  (.seq (.set vpp (.bin .add (.v vn) (.c 1)))
  (.seq (.loop vl L1E blockP)
  (.seq (outToks [Tok.tag 5, Tok.lpar])
  (.seq (.loop vl L1E (emitE (.bin .sub (.bin .add (.bin .add (.bin .add (.v vg0)
      (.bin .mul (.c 2) L1E)) (.bin .mul (.v vl) (.v vS))) (.v vS)) (.c 1))))
    (outToks [Tok.rpar])))))))

/-- Variables written by the group program. -/
def groupW : List (Fin V) := [vg0, vi, vl] ++ qW ++ blockW

lemma Lay.gb_add_W_le (P : Lay) (r q : ℕ) (hr : r < P.R) (hq : q < P.Nq) :
    P.gb r q + P.W ≤ P.F0 := by
  unfold Lay.gb Lay.F0
  have : (r * P.Nq + q + 1) * P.W ≤ P.R * P.Nq * P.W := by
    apply Nat.mul_le_mul_right
    have : (r + 1) * P.Nq ≤ P.R * P.Nq := Nat.mul_le_mul_right _ hr
    nlinarith
  nlinarith

lemma Env.frame {P : Lay} {ρ ρ' : Fin V → ℕ} (hE : Env P ρ) (W : List (Fin V))
    (hW : vn ∉ W ∧ vNq ∉ W ∧ vR ∉ W ∧ vL ∉ W ∧ vS ∉ W ∧ vW ∉ W)
    (h : ∀ v, v ∉ W → ρ' v = ρ v) : Env P ρ' := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hE
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hW
  exact ⟨by rw [h _ w1, e1], by rw [h _ w2, e2], by rw [h _ w3, e3], by rw [h _ w4, e4],
    by rw [h _ w5, e5], by rw [h _ w6, e6]⟩

/-- **The oracle gates of a group.** -/
lemma run_oracleLoop (P : Lay) (t b : Bool) (ρ : Fin V → ℕ) (hE : Env P ρ) (r q : ℕ)
    (hr : ρ vr = r) (hq : ρ vq = q) (hrR : r ≤ P.R) (hcap : P.F0 + 2 * P.S + 2 * P.L + 10 ≤ C) :
    ∃ ρ', (Pr.loop vi L1E (oracleGateP t b)).run z C ρ =
        (ρ', encodeToks (((List.range (P.L + 1)).map fun i =>
          (⟨.oracle, P.qArgs t b i r q⟩ : Gate)).flatMap Gate.toks)) ∧
      ∀ v, v ∉ vi :: qW → ρ' v = ρ v := by
  have hL1 : L1E.eval z C ρ = P.L + 1 := by
    obtain ⟨-, -, -, e4, -, -⟩ := hE
    have : P.L + 1 ≤ C := by omega
    simp [L1E, e4, min_eq_left (show 1 ≤ C by omega), min_eq_left this]
  obtain ⟨ρ', h1, h2⟩ := run_loop_emit (z := z) (C := C) vi L1E (oracleGateP t b) ρ (vi :: qW)
    (fun i => encodeToks (⟨.oracle, P.qArgs t b i r q⟩ : Gate).toks) (fun i hi ρ' hρ' => by
      have hfr : ∀ v, v ∉ vi :: qW → Function.update ρ' vi i v = ρ v := fun v hv => by
        rw [Function.update_of_ne (ne_of_nmem hv (by decide)), hρ' v hv]
      obtain ⟨ρ'', g1, g2⟩ := run_qArgsP (z := z) (C := C) P t b vr vq vi (by decide) (by decide)
        (Function.update ρ' vi i) (hE.frame (vi :: qW) (by decide) hfr) r q i
        (by rw [hfr vr (by decide), hr]) (by rw [hfr vq (by decide), hq]) (by simp) hrR
        (by unfold Lay.F0 at hcap; omega)
      refine ⟨ρ'', ?_, fun v hv => ?_⟩
      · unfold oracleGateP
        rw [seq_eq (run_outToks_eq _ _) (seq_eq g1 (run_outToks_eq _ _))]
        simp [Gate.toks, LS.encodeToks_append, LS.encodeToks_cons]
      · rw [g2 v (fun h => hv (List.mem_cons_of_mem _ h)), hfr v hv])
  refine ⟨ρ', ?_, h2⟩
  rw [h1, hL1, encodeToks_flatMap, List.flatMap_map]

/-- The segment facts for block `ℓ`. -/
def SegOk (z : Word) (CB : Circuit) (pp : ℕ) : Prop :=
  (∀ j < CB.encode.length, z[pp + 2 * j]? = some true) ∧
    (∀ j < CB.encode.length, z[pp + 2 * j + 1]? = CB.encode[j]?) ∧
    z[pp + 2 * CB.encode.length]? = some false

lemma offW_succ (CB : ℕ → Circuit) (ℓ : ℕ) :
    GenI.offW CB (ℓ + 1) = GenI.offW CB ℓ + 2 * (CB ℓ).encode.length + 2 := by
  simp [GenI.offW, List.range_succ, GenI.segW_length]; ring

/-- **The blocks of a group.** -/
lemma run_blockLoop (P : Lay) (ρ : Fin V → ℕ) (hE : Env P ρ) (g0 : ℕ) (hg : ρ vg0 = g0)
    (hpp : ρ vpp = P.n + 1)
    (hseg : ∀ ℓ ≤ P.L, SegOk z (P.CB ℓ) (P.n + 1 + GenI.offW P.CB ℓ))
    (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ) (hsz : P.SizeOk)
    (hcap : g0 + P.W + 2 * P.S + 2 * P.L + 4 ≤ C) (hz : 4 * z.length + 40 ≤ C) :
    ∃ ρ', (Pr.loop vl L1E blockP).run z C ρ =
        (ρ', encodeToks ((List.range (P.L + 1)).flatMap (fun ℓ =>
          blockList (P.CB ℓ) P.L P.S g0 (g0 + 2 * (P.L + 1) + ℓ * P.S) ℓ) |>.flatMap Gate.toks)) ∧
      ∀ v, v ∉ blockW → v ≠ vl → ρ' v = ρ v := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hE
  have hL1 : L1E.eval z C ρ = P.L + 1 := by
    simp [L1E, e4, min_eq_left (show 1 ≤ C by omega), min_eq_left (show P.L + 1 ≤ C by omega)]
  have h := run_loop_spec (w := z) (C := C) vl L1E blockP ρ
    (fun ℓ ρ' => ρ' vpp = P.n + 1 + GenI.offW P.CB ℓ ∧ ∀ v, v ∉ blockW → v ≠ vl → ρ' v = ρ v)
    (fun ℓ => encodeToks ((blockList (P.CB ℓ) P.L P.S g0 (g0 + 2 * (P.L + 1) + ℓ * P.S) ℓ).flatMap
      Gate.toks))
    ⟨by simp [hpp, GenI.offW], fun _ _ _ => rfl⟩ (by
      intro ℓ hℓ ρ' ⟨i1, i2⟩
      rw [hL1] at hℓ
      have hfr : ∀ v, v ∉ blockW → v ≠ vl → Function.update ρ' vl ℓ v = ρ v := fun v a b => by
        rw [Function.update_of_ne b, i2 v a b]
      obtain ⟨s1, s2, s3⟩ := hseg ℓ (by omega)
      obtain ⟨ρ'', b1, b2⟩ := run_blockP (z := z) (C := C) (P.CB ℓ) (Function.update ρ' vl ℓ)
        P.L P.S g0 ℓ (P.n + 1 + GenI.offW P.CB ℓ)
        (by rw [hfr vL (by decide) (by decide), e4]) (by rw [hfr vS (by decide) (by decide), e5])
        (by rw [hfr vg0 (by decide) (by decide), hg]) (by simp)
        (by rw [Function.update_of_ne (by decide), i1]) s1 s2 s3 (hwf ℓ (by omega))
        (hsz ℓ (by omega)).2 (by omega)
        (by
          have : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
          omega) hz
      rw [b1]
      refine ⟨⟨by simp only; rw [b2, offW_succ]; ring, fun v a b => ?_⟩, rfl⟩
      have := Pr.run_frame (w := z) (C := C) blockP (Function.update ρ' vl ℓ) v
        (fun hv => a (blockP_wr v hv))
      rw [b1] at this
      rw [this, hfr v a b])
  rw [hL1] at h
  refine ⟨_, Prod.ext rfl ?_, h.1.2⟩
  rw [h.2, List.flatMap_assoc, encodeToks_flatMap]

/-- **The group program.** -/
lemma run_groupP (P : Lay) (ρ : Fin V → ℕ) (hE : Env P ρ) (r q : ℕ) (hr : ρ vr = r)
    (hq : ρ vq = q) (hrR : r < P.R) (hqN : q < P.Nq)
    (hseg : ∀ ℓ ≤ P.L, SegOk z (P.CB ℓ) (P.n + 1 + GenI.offW P.CB ℓ))
    (hwf : ∀ ℓ ≤ P.L, (P.CB ℓ).WellFormed ℓ) (hsz : P.SizeOk)
    (hcap : P.F0 + 2 * P.S + 2 * P.L + 10 ≤ C) (hz : 4 * z.length + 40 ≤ C) :
    ∃ ρ', groupP.run z C ρ = (ρ', encodeToks ((P.groupGates r q).flatMap Gate.toks)) ∧
      ∀ v, v ∉ groupW → ρ' v = ρ v := by
  have hgb := Lay.gb_add_W_le P r q hrR hqN
  have hF0 : P.n + 2 ≤ P.F0 := by unfold Lay.F0 Lay.P0; omega
  have sub1 : ∀ v, v ∉ groupW → v ∉ vi :: qW := fun v hv h => hv (by
    simp only [List.mem_cons, qW, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h <;> subst h <;> decide)
  have sub2 : ∀ v, v ∉ groupW → v ∉ vl :: qW := fun v hv h => hv (by
    simp only [List.mem_cons, qW, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h <;> subst h <;> decide)
  have hW : P.W = 2 * (P.L + 1) + (P.L + 1) * P.S + 1 := rfl
  have hEc := hE
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hEc
  -- stage 1
  have hrq : r * P.Nq + q ≤ (r * P.Nq + q) * P.W := Nat.le_mul_of_pos_right _ (Lay.W_pos)
  have hrq' : r * P.Nq ≤ r * P.Nq + q := by omega
  have r1 : (Pr.set vg0 (.bin .add (.bin .add (.v vn) (.c 2))
      (.bin .mul (.bin .add (.bin .mul (.v vr) (.v vNq)) (.v vq)) (.v vW)))).run z C ρ =
      (Function.update ρ vg0 (P.gb r q), []) := by
    simp only [run_set, eval_bin, eval_v, eval_c, ap_add, ap_mul, e1, e2, e6, hr, hq]
    have : P.gb r q = P.n + 2 + (r * P.Nq + q) * P.W := rfl
    simp (disch := omega) only [min_eq_left]
    rw [this]
  set ρ1 := Function.update ρ vg0 (P.gb r q)
  have f1 : ∀ v, v ∉ groupW → ρ1 v = ρ v := fun v hv => by
    simp only [ρ1]; rw [Function.update_of_ne (ne_of_nmem hv (by decide))]
  obtain ⟨ρ2, r2, f2⟩ := run_oracleLoop (z := z) (C := C) P false false ρ1
    (hE.frame groupW (by decide) f1) r q (by rw [f1 _ (by decide), hr])
    (by rw [f1 _ (by decide), hq]) hrR.le hcap
  obtain ⟨ρ3, r3, f3⟩ := run_oracleLoop (z := z) (C := C) P false true ρ2
    (hE.frame groupW (by decide) (fun v hv => by rw [f2 v (sub1 v hv), f1 v hv])) r q
    (by rw [f2 _ (by decide), f1 _ (by decide), hr])
    (by rw [f2 _ (by decide), f1 _ (by decide), hq]) hrR.le hcap
  have g3 : ∀ v, v ∉ groupW → ρ3 v = ρ v := fun v hv => by
    rw [f3 v (sub1 v hv), f2 v (sub1 v hv), f1 v hv]
  have hg3 : ρ3 vg0 = P.gb r q := by
    rw [f3 _ (by decide), f2 _ (by decide)]; simp [ρ1]
  have r4 : (Pr.set vpp (.bin .add (.v vn) (.c 1))).run z C ρ3 =
      (Function.update ρ3 vpp (P.n + 1), []) := by
    simp only [run_set, eval_bin, eval_v, eval_c, ap_add, g3 vn (by decide), e1]
    simp (disch := omega) only [min_eq_left]
  set ρ4 := Function.update ρ3 vpp (P.n + 1)
  have g4 : ∀ v, v ∉ groupW → ρ4 v = ρ v := fun v hv => by
    simp only [ρ4]; rw [Function.update_of_ne (ne_of_nmem hv (by decide)), g3 v hv]
  obtain ⟨ρ5, r5, f5⟩ := run_blockLoop (z := z) (C := C) P ρ4 (hE.frame groupW (by decide) g4)
    (P.gb r q) (by simp only [ρ4]; rw [Function.update_of_ne (by decide), hg3]) (by simp [ρ4])
    hseg hwf hsz (by omega) hz
  have g5 : ∀ v, v ∉ groupW → ρ5 v = ρ v := fun v hv => by
    rw [f5 v (fun h => hv (by simp [groupW, h])) (ne_of_nmem hv (by decide)), g4 v hv]
  have hg5 : ρ5 vg0 = P.gb r q := by
    rw [f5 _ (by decide) (by decide)]; simp only [ρ4]; rw [Function.update_of_ne (by decide), hg3]
  have hL1 : L1E.eval z C ρ5 = P.L + 1 := by
    simp [L1E, g5 vL (by decide), e4, min_eq_left (show 1 ≤ C by omega),
      min_eq_left (show P.L + 1 ≤ C by omega)]
  obtain ⟨ρ7, r7, f7⟩ := run_loop_emit (z := z) (C := C) vl L1E
    (emitE (.bin .sub (.bin .add (.bin .add (.bin .add (.v vg0) (.bin .mul (.c 2) L1E))
      (.bin .mul (.v vl) (.v vS))) (.v vS)) (.c 1))) ρ5 (vl :: qW)
    (fun ℓ => encodeToks (natToks (P.bb r q ℓ + P.S - 1))) (fun ℓ hℓ ρ' hρ' => by
      rw [hL1] at hℓ
      obtain ⟨ρ'', h1, h2⟩ := run_emitE (z := z) (C := C) (.bin .sub (.bin .add (.bin .add
        (.bin .add (.v vg0) (.bin .mul (.c 2) L1E)) (.bin .mul (.v vl) (.v vS))) (.v vS)) (.c 1))
        (Function.update ρ' vl ℓ) (by omega)
      refine ⟨ρ'', ?_, fun v hv => ?_⟩
      · rw [h1]; congr 3
        have hρg : ρ' vg0 = P.gb r q := by rw [hρ' vg0 (by decide), hg5]
        have hℓS : ℓ * P.S ≤ (P.L + 1) * P.S := Nat.mul_le_mul_right _ (by omega)
        simp only [L1E, eval_bin, eval_v, eval_c, ap_add, ap_sub, ap_mul, Function.update_self,
          Function.update_of_ne (show vg0 ≠ vl by decide), Function.update_of_ne (show vL ≠ vl by decide),
          Function.update_of_ne (show vS ≠ vl by decide), hρ' vL (by decide), hρ' vS (by decide),
          g5 vL (by decide), g5 vS (by decide), e4, e5, hρg]
        have : P.bb r q ℓ = P.gb r q + 2 * (P.L + 1) + ℓ * P.S := rfl
        simp (disch := omega) only [min_eq_left]
        rfl
      · rw [h2 v (ne_of_nmem hv (by decide)) (ne_of_nmem hv (by decide))
          (ne_of_nmem hv (by decide)), Function.update_of_ne (ne_of_nmem hv (by decide)),
          hρ' v hv])
  rw [hL1] at r7
  refine ⟨ρ7, ?_, fun v hv => by rw [f7 v (sub2 v hv), g5 v hv]⟩
  unfold groupP
  rw [seq_eq r1 (seq_eq r2 (seq_eq r3 (seq_eq r4 (seq_eq r5 (seq_eq (run_outToks_eq _ _)
    (seq_eq r7 (run_outToks_eq _ _)))))))]
  simp only [Lay.groupGates, List.flatMap_append, LS.encodeToks_append, Lay.ansGate,
    encodeToks_range_flatMap, List.nil_append, List.append_assoc]
  simp [Gate.toks, LS.encodeToks_append, LS.encodeToks_cons]
  rfl

end GenP

end PathChecking
