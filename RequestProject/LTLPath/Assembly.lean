module

public import RequestProject.LTLPath.TokSem
public import RequestProject.LTLPath.Abstract
public import RequestProject.LTLPath.OIF
public import RequestProject.ACRound.Defs

/-!
# Assembly of the round algorithm for LTL path checking

The query function `Q` and the decision function `D` are specified by `QSpec` and `DSpec`:

* answers `[0, K)` are *ticks*: query `q < K` is the one-gate circuit with constant value
  `q ≤ t`, where `t` is the number of ticks answered `true` in the previous round, so that after
  `t` rounds exactly the ticks `j < t` are answered `true`;
* answers `K + 2h + β` are the queries for gate `h` and the value `β` of unknown non-live gates;
  the statuses of the previous round are decoded from the previous answers (`stA`);
* `D` accepts iff the input encodes an instance and the root gate is known `true`.

`roundDecidable_of_specs`: logspace functions with these specifications witness
`RoundDecidable LTLPathChecking B 1` for every oracle `B` correct on one-input-face instances.
-/

@[expose] public section

namespace PathChecking

open LTok

/-- Encodings of instances. -/
def instToks (φ : LTL) (p : LassoPath) : List Tok := Tok.lpar :: (φ.toks ++ (Tok.rpar :: p.toks))

lemma instToks_enc (φ : LTL) (p : LassoPath) : Enc (instToks φ p) φ p := rfl

/-- The formula tree of an instance. -/
def instFT (φ : LTL) (p : LassoPath) : FT := tokFT (instToks_enc φ p)

/-- Number of ticks. -/
def nTicks (w : Word) : ℕ := 5 * (w.length + 1)

/-- Number of queries per round. -/
def nQ (w : Word) : ℕ := (w.length + 1) ^ 6

/-- Number of ticks answered `true`. -/
def tcount (K : ℕ) (a : List Bool) : ℕ := (List.range K).countP fun j => a.getD j false

/-- Statuses decoded from the answers `a` of round `t`. -/
def stA (T : FT) (K t : ℕ) (a : List Bool) (h : ℕ) : Option Bool :=
  if t = 0 then T.init h
  else if h < T.Ng then GS.dec (a.getD (K + 2 * h) false) (a.getD (K + 2 * h + 1) false)
  else T.init h

/-- The one-gate circuit with constant value `b`. -/
def constCirc (b : Bool) : Circuit := [⟨.const b, []⟩]

/-- Specification of the query function. -/
def QSpec (Q : Word → Word) : Prop :=
  ∀ (φ : LTL) (p : LassoPath) (a : List Bool),
    a.length = nQ (encodeToks (instToks φ p)) →
    (∀ q < nTicks (encodeToks (instToks φ p)),
      Q (pack (encodeToks (instToks φ p)) q a) =
        (constCirc (decide (q ≤ tcount (nTicks (encodeToks (instToks φ p))) a))).encode) ∧
    (∀ h0 < (instFT φ p).Ng, ∀ β : Bool,
      Q (pack (encodeToks (instToks φ p)) (nTicks (encodeToks (instToks φ p)) + 2 * h0 + β.toNat) a) =
        (GS.pre ((instFT φ p).qsysR ((instFT φ p).rS (tcount (nTicks (encodeToks (instToks φ p))) a))
          ((instFT φ p).rQ (tcount (nTicks (encodeToks (instToks φ p))) a))
          (stA (instFT φ p) (nTicks (encodeToks (instToks φ p)))
            (tcount (nTicks (encodeToks (instToks φ p))) a) a) h0 β) h0).encode)

/-- Specification of the decision function. -/
def DSpec (D : Word → Word) : Prop :=
  ∀ (w : Word) (a : List Bool), D (pack w 0 a) = [true] ↔
    ∃ (φ : LTL) (p : LassoPath), w = encodeToks (instToks φ p) ∧
      a.getD (nTicks w + 2 * (instFT φ p).idx 1 0 1) false = true ∧
      a.getD (nTicks w + 2 * (instFT φ p).idx 1 0 1 + 1) false = true

/-! ## One-gate circuits -/

lemma constCirc_oif (b : Bool) : OIFMCVPInstance (constCirc b) := by
  have hv : ∀ v : Option (Fin (constCirc b).length), v = none ∨ v = some ⟨0, by simp [constCirc]⟩ := by
    rintro (_ | ⟨i, hi⟩)
    · left; rfl
    · right; simp [constCirc] at hi; subst hi; rfl
  have hadj : ∀ u v, (constCirc b).apexAdj u v → u ≠ v := by
    rintro (_ | ⟨i, hi⟩) (_ | ⟨j, hj⟩) h
    · exact h.elim
    · simp
    · simp
    · simp [constCirc] at hi hj; subst hi; subst hj
      simp [Circuit.apexAdj, constCirc] at h
  refine ⟨⟨by simp [constCirc], fun i hi => ?_⟩, fun g hg => ?_, ⟨?_⟩⟩
  · simp [constCirc] at hi; subst hi; simp [constCirc]
  · simp [constCirc] at hg; subst hg; left; exact ⟨b, rfl, rfl⟩
  · refine ⟨fun v => if v = none then ((0 : ℝ), (0 : ℝ)) else (1, 0), ?_, ?_, ?_⟩
    · intro u v h
      rcases hv u with rfl | rfl <;> rcases hv v with rfl | rfl <;> simp_all
    · intro u v w h hwu hwv
      have := hadj u v h
      exfalso
      rcases hv u with rfl | rfl <;> rcases hv v with rfl | rfl <;> rcases hv w with rfl | rfl <;>
        simp_all
    · intro u v u' v' h h' h1 h2
      have := hadj u v h
      have := hadj u' v' h'
      exfalso
      rcases hv u with rfl | rfl <;> rcases hv v with rfl | rfl <;> rcases hv u' with rfl | rfl <;>
        rcases hv v' with rfl | rfl <;> simp_all

lemma constCirc_eval (b : Bool) : (constCirc b).eval ∅ [] = b := by
  simp [constCirc, Circuit.eval, Circuit.values, Gate.eval]

/-! ## Size bounds -/

lemma instFT_bounds (φ : LTL) (p : LassoPath) :
    nTicks (encodeToks (instToks φ p)) + 2 * (instFT φ p).Ng ≤ nQ (encodeToks (instToks φ p)) ∧
    (instFT φ p).L ≤ 2 ^ (Nat.log 2 (encodeToks (instToks φ p)).length + 1) ∧
    (instFT φ p).idx 1 0 1 < (instFT φ p).Ng := by
  have h := instToks_enc φ p
  set ts := instToks φ p
  set T := instFT φ p
  have hlenw : (encodeToks ts).length = 5 * ts.length := by
    unfold encodeToks
    induction ts with
    | nil => rfl
    | cons t l ih => simp [List.flatMap_cons, Tok.bits]; omega
  have hN : T.N = ts.length := rfl
  have hF : T.F = tF ts := rfl
  have hFl := enc_tF_le h
  have hF2 : 2 ≤ tF ts := by rw [enc_tF h]; have := φ.toks_pos; omega
  have hs : T.s ≤ ts.length := by
    show sLen ts ≤ ts.length
    unfold sLen cnt
    have := enc_sE h
    have := enc_length h
    unfold lB at *
    refine (List.countP_le_length).trans ?_
    simp; omega
  have hl : T.ℓ ≤ ts.length := by
    show lLen ts ≤ ts.length
    unfold lLen cnt
    refine (List.countP_le_length).trans ?_
    simp; omega
  have hL : T.L ≤ ts.length := by
    show T.lix T.F ≤ _
    unfold PT.lix
    refine (List.length_filter_le _ _).trans ?_
    simp [hF]; omega
  refine ⟨?_, ?_, FT.idx_lt_Ng (by rw [hN]; omega) FT.Wm_pos le_rfl⟩
  · unfold nTicks nQ FT.Ng FT.Wm
    rw [hlenw, hN]
    set N := ts.length
    set m := 5 * N + 1 with hmdef
    have hm : 6 ≤ m := by have : 1 ≤ N := by omega
                          omega
    have hWm : T.s + (N + 1) * T.ℓ ≤ m * m := by
      have := Nat.mul_le_mul_left (N + 1) hl
      rw [hmdef]; nlinarith
    have h1 : 2 * (2 * N * (T.s + (N + 1) * T.ℓ)) ≤ 4 * m * (m * m) := by
      have : N ≤ m := by omega
      have := Nat.mul_le_mul this hWm
      nlinarith
    have h2 : 5 * m + 4 * m * (m * m) ≤ m ^ 6 := by
      have e : m ^ 6 = (m * m * m) * (m * m * m) := by ring
      rw [e]
      have : 36 * m ≤ m * m * m := by nlinarith
      nlinarith
    omega
  · rw [hlenw]
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (5 * ts.length)
    omega

/-! ## The rounds -/

section Rounds

variable {B : Language} (hB : ∀ C : Circuit, OIFMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true))
  {Q : Word → Word} (hQS : QSpec Q) (φ : LTL) (p : LassoPath)

lemma ltl_roundAns_length (w : Word) (Nq : ℕ) (r : ℕ) : (roundAns B Q Nq w r).length = Nq := by
  cases r <;> simp [roundAns]

lemma roundAns_getD (w : Word) (Nq : ℕ) (r : ℕ) {q : ℕ} (hq : q < Nq) :
    (roundAns B Q Nq w (r + 1)).getD q false =
      @decide (Q (pack w q (roundAns B Q Nq w r)) ∈ B) (Classical.dec _) := by
  simp [roundAns, List.getD_eq_getElem?_getD, hq]

lemma countP_range_le (K r : ℕ) (hr : r + 1 ≤ K) :
    (List.range K).countP (fun j => decide (j ≤ r)) = r + 1 := by
  rw [show K = (r + 1) + (K - (r + 1)) by omega, LTok.countP_range_add,
    List.countP_eq_length.2 (fun j hj => by simp at hj ⊢; omega),
    List.countP_eq_zero.2 (fun j hj => by simp; omega)]
  simp

include hB hQS in
/-- **The invariant of the rounds.** -/
theorem rounds_inv (r : ℕ) (hr : r ≤ nTicks (encodeToks (instToks φ p))) :
    tcount (nTicks (encodeToks (instToks φ p)))
        (roundAns B Q (nQ (encodeToks (instToks φ p))) (encodeToks (instToks φ p)) r) = r ∧
      stA (instFT φ p) (nTicks (encodeToks (instToks φ p))) r
        (roundAns B Q (nQ (encodeToks (instToks φ p))) (encodeToks (instToks φ p)) r) =
        (instFT φ p).oseq B r := by
  obtain ⟨hbd, -, -⟩ := instFT_bounds φ p
  set w := encodeToks (instToks φ p)
  set T := instFT φ p
  set K := nTicks w
  have hOIF : FT.OIFCorrect B := hB
  induction r with
  | zero =>
    refine ⟨?_, ?_⟩
    · unfold tcount
      refine List.countP_eq_zero.2 fun j hj => ?_
      simp [roundAns, List.getD_eq_getElem?_getD]
    · funext h; simp [stA, FT.oseq]
  | succ r ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hlen := ltl_roundAns_length (B := B) (Q := Q) w (nQ w) r
    obtain ⟨hT, hG⟩ := hQS φ p _ hlen
    refine ⟨?_, ?_⟩
    · unfold tcount
      rw [countP_range_congr (Q := fun j => decide (j ≤ r)) fun j hj => ?_]
      · exact countP_range_le K r hr
      · rw [roundAns_getD w (nQ w) r (by unfold K at hj; omega), hT j hj, ih1]
        have := hB _ (constCirc_oif (decide (j ≤ r)))
        rw [constCirc_eval] at this
        by_cases hjr : j ≤ r <;> simp [hjr] at this ⊢ <;> simpa using this
    · funext h
      have hseq : T.oseq B (r + 1) = T.seq (r + 1) := FT.oseq_eq hOIF (r + 1)
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

lemma root_iff {B : Language}
    (hB : ∀ C : Circuit, OIFMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true))
    {Q : Word → Word} (hQS : QSpec Q) (φ : LTL) (p : LassoPath) :
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
  obtain ⟨-, hst⟩ := rounds_inv hB hQS φ p _ hRK
  have hroot := FT.oseq_root (T := instFT φ p) (B := B) hB (LTok.tokFT_sem (instToks_enc φ p))
    (LTok.tokFT_pol_one (instToks_enc φ p)) hL
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

theorem roundDecidable_of_specs (B : Language)
    (hB : ∀ C : Circuit, OIFMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true))
    (Q D : Word → Word) (hQ : LogspaceComputable Q) (hD : LogspaceComputable D)
    (hQS : QSpec Q) (hDS : DSpec D) : RoundDecidable LTLPathChecking B 1 := by
  refine ⟨6, 5, Q, D, hQ, hD, fun w => ?_⟩
  rw [hDS]
  simp only [pow_one]
  constructor
  · rintro ⟨φ, p, rfl, hsat⟩
    exact ⟨φ, p, rfl, (root_iff hB hQS φ p).2 hsat⟩
  · rintro ⟨φ, p, rfl, h1, h2⟩
    exact ⟨φ, p, rfl, (root_iff hB hQS φ p).1 ⟨h1, h2⟩⟩

end PathChecking
