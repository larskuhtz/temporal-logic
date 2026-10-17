module

public import RequestProject.LTLPath.QueryStrat
public import RequestProject.LTLPath.Assembly

/-!
# The round algorithm with stratified query circuits

The round algorithm of `RequestProject/LTLPath/Assembly.lean`, except that the query for gate
`h0` and `β` is the stratified drawing `FT.stratQ` of the query circuit instead of the query
circuit itself.

* `FT.oseqS`: the statuses computed with an oracle `B`; if `B` is correct on stratified
  instances (`FT.StratCorrect`), they are the intended statuses (`FT.oseqS_eq`).
* `QSpecS`: the specification of the query function.
* `roundDecidable_of_specsS`: logspace functions with the specifications `QSpecS` and `DSpec`
  witness `RoundDecidable LTLPathChecking B 1` for every oracle `B` correct on stratified
  monotone planar instances.
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-- The answer of the oracle `B` to the stratified query for gate `h0` and `β`. -/
noncomputable def oansS (T : FT) (B : Language) (S Qd : ℕ → Prop) (st : ℕ → Option Bool)
    (h0 : ℕ) (β : Bool) : Bool :=
  decide ((T.stratQ S Qd st h0 β).encode ∈ B)

/-- Statuses computed from the answers of the oracle. -/
noncomputable def ostepS (T : FT) (B : Language) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) :
    ℕ → Option Bool :=
  fun h0 => GS.dec (T.oansS B S Qd st h0 false) (T.oansS B S Qd st h0 true)

/-- An oracle that is correct on stratified monotone planar instances. -/
def StratCorrect (B : Language) : Prop :=
  ∀ C : Circuit, StratMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true)

lemma oansS_eq {B : Language} (hB : StratCorrect B) {S Qd : ℕ → Prop} {st : ℕ → Option Bool}
    (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) (h0 : ℕ) (β : Bool) :
    T.oansS B S Qd st h0 β = T.ans S Qd st h0 β := by
  unfold oansS ans
  have h1 := hB _ (query_strat (h0 := h0) (Qd := Qd) (β := β) hck hd hcl)
  rw [query_strat_eval hck hd hcl] at h1
  cases hv : GS.val (T.qsysR S Qd st h0 β) h0
  · exact decide_eq_false fun hm => by have := h1.1 hm; rw [hv] at this; exact absurd this (by simp)
  · exact decide_eq_true (h1.2 hv)

/-- Statuses computed with the oracle. -/
noncomputable def oseqS (T : FT) (B : Language) : ℕ → ℕ → Option Bool
  | 0 => T.init
  | t + 1 => T.ostepS B (T.rS t) (T.rQ t) (T.oseqS B t)

/-- **With an oracle that is correct on stratified instances, the computed statuses are the
intended ones.** -/
theorem oseqS_eq {B : Language} (hB : StratCorrect B) (t : ℕ) : T.oseqS B t = T.seq t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨-, hck, hd, hcl⟩ := round_hyps (T := T) t
    show T.ostepS B (T.rS t) (T.rQ t) (T.oseqS B t) = T.step (T.rS t) (T.rQ t) (T.seq t)
    rw [ih]
    funext h0
    unfold ostepS step
    rw [oansS_eq hB hck hd hcl, oansS_eq hB hck hd hcl]

/-- **Correctness of the abstract algorithm with stratified queries.** -/
theorem oseqS_root {B : Language} (hB : StratCorrect B) {sat : ℕ → ℕ → Bool} (hS : T.Sem sat)
    (hpol : T.pol 1 = false) {R t : ℕ} (hR : T.L ≤ 2 ^ R) (ht : 4 * R + 1 ≤ t) :
    T.oseqS B t (T.idx 1 0 1) = some (sat 1 0) := by
  have h1N : 1 < T.N := nd_lt_N T.nd_one
  have hpos : T.pos (T.idx 1 0 1) = 1 := (decode_idx h1N Wm_pos le_rfl).1
  rw [oseqS_eq hB, seq_root hR ht hpos, gate_sem hS 1 T.nd_one 0 (by unfold W; nlinarith [T.hℓ]),
    hpol, Bool.xor_false]

end FT

open LTok

/-- Specification of the query function with stratified query circuits. -/
def QSpecS (Q : Word → Word) : Prop :=
  ∀ (φ : LTL) (p : LassoPath) (a : List Bool),
    a.length = nQ (encodeToks (instToks φ p)) →
    (∀ q < nTicks (encodeToks (instToks φ p)),
      Q (pack (encodeToks (instToks φ p)) q a) =
        (constCirc (decide (q ≤ tcount (nTicks (encodeToks (instToks φ p))) a))).encode) ∧
    (∀ h0 < (instFT φ p).Ng, ∀ β : Bool,
      Q (pack (encodeToks (instToks φ p)) (nTicks (encodeToks (instToks φ p)) + 2 * h0 + β.toNat) a) =
        ((instFT φ p).stratQ ((instFT φ p).rS (tcount (nTicks (encodeToks (instToks φ p))) a))
          ((instFT φ p).rQ (tcount (nTicks (encodeToks (instToks φ p))) a))
          (stA (instFT φ p) (nTicks (encodeToks (instToks φ p)))
            (tcount (nTicks (encodeToks (instToks φ p))) a) a) h0 β).encode)

/-- One-gate circuits are stratified instances. -/
lemma constCirc_strat (b : Bool) : StratMCVPInstance (constCirc b) := by
  refine ⟨⟨by simp [constCirc], fun i hi => ?_⟩, fun g hg => ?_, ⟨fun _ => 0, ?_⟩⟩
  · simp only [constCirc, List.length_singleton, Nat.lt_one_iff] at hi; subst hi
    simp [constCirc]
  · simp only [constCirc, List.mem_singleton] at hg; subst hg; left; exact ⟨_, rfl, rfl⟩
  · refine ⟨fun _ _ _ _ => le_rfl, fun i hi => ?_, fun i hi j hj => ?_, fun i hi => ?_,
      fun i i' hi hi' hii' _ => ?_⟩
    · simp only [constCirc, List.length_singleton, Nat.lt_one_iff] at hi; subst hi
      simp [Gate.IsInput, constCirc]
    · simp only [constCirc, List.length_singleton, Nat.lt_one_iff] at hi; subst hi
      simp [constCirc] at hj
    · simp only [constCirc, List.length_singleton, Nat.lt_one_iff] at hi; subst hi
      simp [constCirc]
    · simp only [constCirc, List.length_singleton, Nat.lt_one_iff] at hi hi'; omega

section Rounds

variable {B : Language} (hB : FT.StratCorrect B)
  {Q : Word → Word} (hQS : QSpecS Q) (φ : LTL) (p : LassoPath)

include hB hQS in
/-- **The invariant of the rounds.** -/
theorem rounds_invS (r : ℕ) (hr : r ≤ nTicks (encodeToks (instToks φ p))) :
    tcount (nTicks (encodeToks (instToks φ p)))
        (roundAns B Q (nQ (encodeToks (instToks φ p))) (encodeToks (instToks φ p)) r) = r ∧
      stA (instFT φ p) (nTicks (encodeToks (instToks φ p))) r
        (roundAns B Q (nQ (encodeToks (instToks φ p))) (encodeToks (instToks φ p)) r) =
        (instFT φ p).oseqS B r := by
  obtain ⟨hbd, -, -⟩ := instFT_bounds φ p
  set w := encodeToks (instToks φ p)
  set T := instFT φ p
  set K := nTicks w
  induction r with
  | zero =>
    refine ⟨?_, ?_⟩
    · unfold tcount
      refine List.countP_eq_zero.2 fun j hj => ?_
      simp [roundAns, List.getD_eq_getElem?_getD]
    · funext h; simp [stA, FT.oseqS]
  | succ r ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlen := ltl_roundAns_length (B := B) (Q := Q) w (nQ w) r
    obtain ⟨hT, hG⟩ := hQS φ p _ hlen
    refine ⟨?_, ?_⟩
    · unfold tcount
      rw [countP_range_congr (Q := fun j => decide (j ≤ r)) fun j hj => ?_]
      · exact countP_range_le K r hr
      · rw [roundAns_getD w (nQ w) r (by unfold K at hj; omega), hT j hj, ih1]
        have := hB _ (constCirc_strat (decide (j ≤ r)))
        rw [constCirc_eval] at this
        by_cases hjr : j ≤ r <;> simp [hjr] at this ⊢ <;> simpa using this
    · funext h
      have hseq : T.oseqS B (r + 1) = T.seq (r + 1) := FT.oseqS_eq hB (r + 1)
      unfold stA
      rw [if_neg (by omega)]
      split_ifs with hh
      · rw [roundAns_getD w (nQ w) r (by omega), roundAns_getD w (nQ w) r (by omega)]
        have e0 := hG h hh false
        have e1 := hG h hh true
        simp only [Bool.toNat_false, Bool.toNat_true, add_zero] at e0 e1
        rw [e0, e1, ih1, ih2]
        rfl
      · rw [hseq]
        obtain ⟨-, hck, -, -⟩ := FT.round_hyps (T := T) (r + 1)
        have hg : (T.gate h).kind = .const false := by simp [FT.gate, hh, FT.cF]
        rw [hck h false hg]
        simp [FT.init, hg]

end Rounds

lemma root_iffS {B : Language} (hB : FT.StratCorrect B)
    {Q : Word → Word} (hQS : QSpecS Q) (φ : LTL) (p : LassoPath) :
    ((roundAns B Q (nQ (encodeToks (instToks φ p))) (encodeToks (instToks φ p))
          (5 * (Nat.log 2 (encodeToks (instToks φ p)).length + 1))).getD
          (nTicks (encodeToks (instToks φ p)) + 2 * (instFT φ p).idx 1 0 1) false = true ∧
        (roundAns B Q (nQ (encodeToks (instToks φ p))) (encodeToks (instToks φ p))
          (5 * (Nat.log 2 (encodeToks (instToks φ p)).length + 1))).getD
          (nTicks (encodeToks (instToks φ p)) + 2 * (instFT φ p).idx 1 0 1 + 1) false = true) ↔
        LTL.Sat p.letter φ 0 := by
  obtain ⟨hbd, hL, hidx⟩ := instFT_bounds φ p
  have hRK : 5 * (Nat.log 2 (encodeToks (instToks φ p)).length + 1) ≤
      nTicks (encodeToks (instToks φ p)) := by
    have := Nat.log_le_self 2 (encodeToks (instToks φ p)).length
    unfold nTicks; omega
  obtain ⟨-, hst⟩ := rounds_invS hB hQS φ p _ hRK
  have hroot := FT.oseqS_root (T := instFT φ p) (B := B) hB
    (LTok.tokFT_sem (instToks_enc φ p)) (LTok.tokFT_pol_one (instToks_enc φ p)) hL
    (t := 5 * (Nat.log 2 (encodeToks (instToks φ p)).length + 1)) (by omega)
  have h1 := congrFun hst ((instFT φ p).idx 1 0 1)
  rw [hroot] at h1
  unfold stA at h1
  rw [if_neg (by omega), if_pos hidx] at h1
  have hsat := LTok.tokSat_root (p := p) (instToks_enc φ p)
  unfold GS.dec at h1
  rw [← hsat]
  split_ifs at h1 with he
  simp only [Option.some.injEq] at h1
  rw [← h1, ← he]; simp

/-- Logspace functions with the specifications `QSpecS` and `DSpec` witness the round
algorithm for any oracle correct on stratified instances. -/
theorem roundDecidable_of_specsS (B : Language)
    (hB : ∀ C : Circuit, StratMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true))
    (Q D : Word → Word) (hQ : LogspaceComputable Q) (hD : LogspaceComputable D)
    (hQS : QSpecS Q) (hDS : DSpec D) : RoundDecidable LTLPathChecking B 1 := by
  refine ⟨6, 5, Q, D, hQ, hD, fun w => ?_⟩
  rw [hDS]
  simp only [pow_one]
  constructor
  · rintro ⟨φ, p, rfl, hsat⟩
    exact ⟨φ, p, rfl, (root_iffS hB hQS φ p).2 hsat⟩
  · rintro ⟨φ, p, rfl, h1, h2⟩
    exact ⟨φ, p, rfl, (root_iffS hB hQS φ p).1 ⟨h1, h2⟩⟩

end PathChecking
