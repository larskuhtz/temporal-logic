module

public import RequestProject.LTLPath.QueryOIF

/-!
# The sequence of rounds, and the oracle

Round `0` queries all regions of `S0 0`; round `4r + 1 + j` is round A of the first phase of
stage `r` (`j = 0`), round B of it (`j = 1`), round A of the second phase (`j = 2`) and its
round B (`j = 3`).  `rS t` is the leaf set and `rQ t` the set of queried regions of round `t`;
`seq t` are the statuses before round `t`.

In every round the statuses satisfy the hypotheses of `query_oif` (`round_hyps`), so an oracle
that is correct on one-input-face instances answers all queries correctly, and the statuses
computed from its answers are `seq t` (`oseq_eq`).  After `4R + 1` rounds with `L ≤ 2^R`, the
gates of the root row are known (`seq_root`).
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-- Leaf set of round `t`. -/
def rS (T : FT) : ℕ → ℕ → Prop
  | 0 => T.S0 0
  | t + 1 => if t % 4 = 0 then T.S0 (t / 4) else if t % 4 = 1 ∨ t % 4 = 2 then T.S1 (t / 4)
      else T.S0 (t / 4 + 1)

/-- Queried regions of round `t`. -/
def rQ (T : FT) : ℕ → ℕ → Prop
  | 0 => fun _ => True
  | t + 1 => if t % 4 = 0 then T.PSet (T.S0 (t / 4)) (T.DL (t / 4))
      else if t % 4 = 2 then T.PSet (T.S1 (t / 4)) (T.DR (t / 4)) else fun _ => True

/-- Statuses before round `t`. -/
noncomputable def seq (T : FT) : ℕ → ℕ → Option Bool
  | 0 => T.init
  | t + 1 => T.step (T.rS t) (T.rQ t) (T.seq t)

lemma rS_1 (r : ℕ) : T.rS (4 * r + 1) = T.S0 r := by
  simp [rS, show 4 * r % 4 = 0 by omega, show 4 * r / 4 = r by omega]
lemma rS_2 (r : ℕ) : T.rS (4 * r + 2) = T.S1 r := by
  simp [rS, show (4 * r + 1) % 4 = 1 by omega, show (4 * r + 1) / 4 = r by omega]
lemma rS_3 (r : ℕ) : T.rS (4 * r + 3) = T.S1 r := by
  simp [rS, show (4 * r + 2) % 4 = 2 by omega, show (4 * r + 2) / 4 = r by omega]
lemma rS_4 (r : ℕ) : T.rS (4 * r + 4) = T.S0 (r + 1) := by
  simp [rS, show (4 * r + 3) % 4 = 3 by omega, show (4 * r + 3) / 4 = r by omega]
lemma rQ_1 (r : ℕ) : T.rQ (4 * r + 1) = T.PSet (T.S0 r) (T.DL r) := by
  simp [rQ, show 4 * r % 4 = 0 by omega, show 4 * r / 4 = r by omega]
lemma rQ_2 (r : ℕ) : T.rQ (4 * r + 2) = fun _ => True := by
  simp [rQ, show (4 * r + 1) % 4 = 1 by omega]
lemma rQ_3 (r : ℕ) : T.rQ (4 * r + 3) = T.PSet (T.S1 r) (T.DR r) := by
  simp [rQ, show (4 * r + 2) % 4 = 2 by omega, show (4 * r + 2) / 4 = r by omega]
lemma rQ_4 (r : ℕ) : T.rQ (4 * r + 4) = fun _ => True := by
  simp [rQ, show (4 * r + 3) % 4 = 3 by omega]

/-- The statuses at the start of each round of stage `r`. -/
theorem seq_stage (r : ℕ) : T.seq (4 * r + 1) = T.run r ∧
    T.seq (4 * r + 2) = T.roundA (T.S0 r) (T.DL r) (T.run r) ∧
    T.seq (4 * r + 3) = T.roundB (T.S1 r) (T.roundA (T.S0 r) (T.DL r) (T.run r)) ∧
    T.seq (4 * r + 4) = T.roundA (T.S1 r) (T.DR r)
      (T.roundB (T.S1 r) (T.roundA (T.S0 r) (T.DL r) (T.run r))) := by
  induction r with
  | zero =>
    have h1 : T.seq 1 = T.run 0 := rfl
    refine ⟨h1, ?_, ?_, ?_⟩
    · show T.step (T.rS 1) (T.rQ 1) (T.seq 1) = _
      rw [h1, show (1 : ℕ) = 4 * 0 + 1 from rfl, rS_1, rQ_1]; rfl
    · show T.step (T.rS 2) (T.rQ 2) (T.step (T.rS 1) (T.rQ 1) (T.seq 1)) = _
      rw [h1, show (1 : ℕ) = 4 * 0 + 1 from rfl, show (2 : ℕ) = 4 * 0 + 2 from rfl, rS_1, rQ_1,
        rS_2, rQ_2]; rfl
    · show T.step (T.rS 3) (T.rQ 3) (T.step (T.rS 2) (T.rQ 2) (T.step (T.rS 1) (T.rQ 1)
        (T.seq 1))) = _
      rw [h1, show (1 : ℕ) = 4 * 0 + 1 from rfl, show (2 : ℕ) = 4 * 0 + 2 from rfl,
        show (3 : ℕ) = 4 * 0 + 3 from rfl, rS_1, rQ_1, rS_2, rQ_2, rS_3, rQ_3]; rfl
  | succ r ih =>
    obtain ⟨-, -, -, h4⟩ := ih
    have h1 : T.seq (4 * (r + 1) + 1) = T.run (r + 1) := by
      show T.step (T.rS (4 * r + 4)) (T.rQ (4 * r + 4)) (T.seq (4 * r + 4)) = _
      rw [h4, rS_4, rQ_4]; rfl
    have h2 : T.seq (4 * (r + 1) + 2) = T.roundA (T.S0 (r + 1)) (T.DL (r + 1)) (T.run (r + 1)) := by
      show T.step (T.rS (4 * (r + 1) + 1)) (T.rQ (4 * (r + 1) + 1)) (T.seq (4 * (r + 1) + 1)) = _
      rw [h1, rS_1, rQ_1]; rfl
    have h3 : T.seq (4 * (r + 1) + 3) = T.roundB (T.S1 (r + 1))
        (T.roundA (T.S0 (r + 1)) (T.DL (r + 1)) (T.run (r + 1))) := by
      show T.step (T.rS (4 * (r + 1) + 2)) (T.rQ (4 * (r + 1) + 2)) (T.seq (4 * (r + 1) + 2)) = _
      rw [h2, rS_2, rQ_2]; rfl
    refine ⟨h1, h2, h3, ?_⟩
    show T.step (T.rS (4 * (r + 1) + 3)) (T.rQ (4 * (r + 1) + 3)) (T.seq (4 * (r + 1) + 3)) = _
    rw [h3, rS_3, rQ_3]; rfl

/-- The hypotheses of the queries hold in every round. -/
theorem round_hyps (t : ℕ) : GS.Correct T.gate (T.seq t) ∧ T.ConstKnown (T.seq t) ∧
    T.Dead (T.rS t) (T.seq t) ∧ T.Cl (T.rS t) (T.seq t) := by
  rcases t with _ | t
  · exact init_inv0
  obtain ⟨r, j, hj, rfl⟩ : ∃ r j, j < 4 ∧ t = 4 * r + j := ⟨t / 4, t % 4, by omega, by omega⟩
  obtain ⟨e1, e2, e3, e4⟩ := seq_stage (T := T) r
  have hI := run_inv (T := T) r
  have hA1 := roundA_facts (fun k h => h.1) (PT.sep_DL r) (PT.noChain_DL r) hI
  have hI2 := phase (fun k h => h.1) (PT.sep_DL r) (PT.noChain_DL r) hI
  have hA2 := roundA_facts (fun k h => h.1) (PT.sep_DR r) (PT.noChain_DR r) hI2
  interval_cases j
  · rw [show 4 * r + 0 + 1 = 4 * r + 1 by omega, e1, rS_1]
    exact ⟨hI.correct, hI.ck, hI.dead, hI.cl⟩
  · rw [show 4 * r + 1 + 1 = 4 * r + 2 by omega, e2, rS_2]
    exact hA1
  · rw [show 4 * r + 2 + 1 = 4 * r + 3 by omega, e3, rS_3]
    exact ⟨hI2.correct, hI2.ck, hI2.dead, hI2.cl⟩
  · rw [show 4 * r + 3 + 1 = 4 * r + 4 by omega, e4, rS_4, ← S1_diff_DR]
    exact hA2

/-- **The root row is known after enough rounds.** -/
theorem seq_root {R t : ℕ} (hR : T.L ≤ 2 ^ R) (ht : 4 * R + 1 ≤ t) {h : ℕ} (hp : T.pos h = 1) :
    T.seq t h = some (GS.val T.gate h) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = 4 * R + 1 + m := ⟨t - (4 * R + 1), by omega⟩
  clear ht
  induction m with
  | zero => rw [Nat.add_zero, (seq_stage R).1]; exact run_root hR hp
  | succ m ih => exact step_known ih

/-! ## The oracle -/

/-- The answer of the oracle `B` to the query for gate `h0` and `β`. -/
noncomputable def oans (T : FT) (B : Language) (S Qd : ℕ → Prop) (st : ℕ → Option Bool)
    (h0 : ℕ) (β : Bool) : Bool :=
  decide ((GS.pre (T.qsysR S Qd st h0 β) h0).encode ∈ B)

/-- Statuses computed from the answers of the oracle. -/
noncomputable def ostep (T : FT) (B : Language) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) :
    ℕ → Option Bool :=
  fun h0 => GS.dec (T.oans B S Qd st h0 false) (T.oans B S Qd st h0 true)

/-- An oracle that is correct on one-input-face instances. -/
def OIFCorrect (B : Language) : Prop :=
  ∀ C : Circuit, OIFMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true)

lemma oans_eq {B : Language} (hB : OIFCorrect B) {S Qd : ℕ → Prop} {st : ℕ → Option Bool}
    (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) (h0 : ℕ) (β : Bool) :
    T.oans B S Qd st h0 β = T.ans S Qd st h0 β := by
  unfold oans ans
  have h1 := hB _ (query_oif (h0 := h0) (Qd := Qd) (β := β) hck hd hcl)
  have h2 : (GS.pre (T.qsysR S Qd st h0 β) h0).eval ∅ [] = GS.val (T.qsysR S Qd st h0 β) h0 :=
    GS.eval_prefix (g := T.qsysR S Qd st h0 β) (GS.qsys_ordered gate_ordered _ _ _ _) h0
  rw [h2] at h1
  cases hv : GS.val (T.qsysR S Qd st h0 β) h0
  · exact decide_eq_false fun hm => by have := h1.1 hm; rw [hv] at this; exact absurd this (by simp)
  · exact decide_eq_true (h1.2 hv)

/-- Statuses computed with the oracle. -/
noncomputable def oseq (T : FT) (B : Language) : ℕ → ℕ → Option Bool
  | 0 => T.init
  | t + 1 => T.ostep B (T.rS t) (T.rQ t) (T.oseq B t)

/-- **With an oracle that is correct on one-input-face instances, the computed statuses are
the intended ones.** -/
theorem oseq_eq {B : Language} (hB : OIFCorrect B) (t : ℕ) : T.oseq B t = T.seq t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨-, hck, hd, hcl⟩ := round_hyps (T := T) t
    show T.ostep B (T.rS t) (T.rQ t) (T.oseq B t) = T.step (T.rS t) (T.rQ t) (T.seq t)
    rw [ih]
    funext h0
    unfold ostep step
    rw [oans_eq hB hck hd hcl, oans_eq hB hck hd hcl]

end FT

end PathChecking
