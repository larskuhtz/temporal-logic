module

public import RequestProject.MCVP.Gate

/-!
# Validating the input

`validate` decides whether the input is the encoding of a non-empty well-formed monotone
circuit (`ValidCode`), leaving the answer in `rOk` and the number of gates in `rN`.
-/

@[expose] public section

namespace PathChecking

namespace MCVPReduction

open LS
open scoped LS

variable {w : Word} {B : ℕ}

/-! ## Well-formed circuits -/

lemma wellFormed_iff (C : List MGate) : WellFormed C ↔ ∀ k, GateOk (gateAt C k) k := by
  constructor
  · intro h k
    cases hk : gateAt C k with
    | input b => trivial
    | and i j => exact h k i j (Or.inl hk)
    | or i j => exact h k i j (Or.inr hk)
  · intro h k i j hk
    have := h k
    rcases hk with hk | hk <;> rw [hk] at this <;> exact this

lemma gateAt_append_single (C : List MGate) (G : MGate) (k : ℕ) :
    gateAt (C ++ [G]) k = if k < C.length then gateAt C k else
      if k = C.length then G else .input false := by
  unfold gateAt
  split_ifs with h1 h2
  · rw [List.getD_append _ _ _ _ h1]
  · subst h2; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma wellFormed_append_single {C : List MGate} {G : MGate} (hC : WellFormed C)
    (hG : GateOk G C.length) : WellFormed (C ++ [G]) := by
  rw [wellFormed_iff] at hC ⊢
  intro k
  rw [gateAt_append_single]
  split_ifs with h1 h2
  · exact hC k
  · subst h2; exact hG
  · trivial

lemma wellFormed_nil : WellFormed [] := by
  rw [wellFormed_iff]; intro k; simp [gateAt, GateOk]

lemma gateOk_of_wellFormed {C : List MGate} (hC : WellFormed C) (k : ℕ) :
    GateOk (gateAt C k) k := (wellFormed_iff C).1 hC k

lemma length_le_toks (C : List MGate) : C.length ≤ (C.flatMap MGate.toks).length := by
  induction C with
  | nil => simp
  | cons G C ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have := MGate.toks_ne_nil G
    have : 0 < G.toks.length := List.length_pos_iff.2 this
    omega

lemma encodeCircuit_length (C : List MGate) :
    (encodeCircuit C).length = 5 * (C.flatMap MGate.toks).length := by
  rw [encodeCircuit, encodeToks_length]

lemma encodeCircuit_ne_nil {C : List MGate} (hC : C ≠ []) : encodeCircuit C ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [encodeCircuit_length] at this
  have := length_le_toks C
  have : 0 < C.length := List.length_pos_iff.2 hC
  simp at *; omega

lemma at_self (w : Word) : At w 1 w := ⟨le_rfl, by omega, by simp⟩

/-- If the circuit `C` has been parsed and the next gate cannot be parsed, the input is not
valid. -/
lemma not_valid_of_gate_fail {C : List MGate} (hC : At w 1 (encodeCircuit C))
    (hlt : 1 + 5 * (C.flatMap MGate.toks).length < w.length + 1)
    (hno : ∀ G, GateOk G C.length →
      ¬ At w (1 + 5 * (C.flatMap MGate.toks).length) (encodeToks G.toks)) :
    ¬ ValidCode w := by
  rintro ⟨C', hne, hwf, rfl⟩
  have hw := at_self (encodeCircuit C')
  rcases At.toks_compat hC hw with ⟨vs, hvs⟩ | ⟨vs, hvs⟩
  · obtain ⟨D, rfl⟩ := circuit_prefix hvs.symm
    cases D with
    | nil =>
      rw [encodeCircuit_length] at hlt
      simp at hlt
    | cons G D =>
      apply hno G
      · have := gateOk_of_wellFormed hwf C.length
        simpa [gateAt] using this
      · have h1 : At (encodeCircuit (C ++ G :: D)) 1
            (encodeToks (C.flatMap MGate.toks ++ (G.toks ++ D.flatMap MGate.toks))) := by
          simpa [encodeCircuit] using hw
        exact (At.toks_append.1 (At.toks_append.1 h1).2).1
  · have := congrArg List.length hvs
    rw [List.length_append] at this
    rw [encodeCircuit_length] at hlt
    omega

/-! ## The validation loop -/

/-- Decide whether the input is a valid circuit encoding. -/
def validate : Stmt 20 :=
  setOne rOk ⨟ clear rN ⨟ rewind ⨟
  .loop (.not (.sym .rend)) (.ite (.zero rOk) goEnd gateStep) ⨟
  .ite (.zero rN) (clear rOk) .skip

/-- Loop invariant of `validate`. -/
def VInv (w : Word) (σ : St 20) (n : ℕ) (τ : St 20) : Prop :=
  τ.out = σ.out ∧ 1 ≤ τ.pos ∧ τ.pos ≤ w.length + 1 ∧ (∀ x, x ∉ gateClob → τ.reg x = σ.reg x) ∧
  (τ.reg rOk ≠ 0 → ∃ C, WellFormed C ∧ At w 1 (encodeCircuit C) ∧
    τ.pos = 1 + 5 * (C.flatMap MGate.toks).length ∧ τ.reg rN = C.length ∧
    n = 2 * (w.length + 1 - τ.pos) + 2) ∧
  (τ.reg rOk = 0 → ¬ ValidCode w ∧ (τ.pos = w.length + 1 ∨ n = 1))

lemma vinv_step (σ : St 20) (hB : w.length + 1 ≤ B) (n : ℕ) (τ : St 20) (hI : VInv w σ n τ)
    (hlt : τ.pos < w.length + 1) :
    Ach w B (.ite (.zero rOk) goEnd gateStep) τ (fun τ' => ∃ m < n, VInv w σ m τ') := by
  obtain ⟨ho, hp1, hp2, hfr, hok, hbad⟩ := hI
  refine ach_ite ?_
  by_cases h0 : τ.reg rOk = 0
  · rw [if_pos (by simp [Cond.eval, h0])]
    obtain ⟨hnv, hn⟩ := hbad h0
    refine ach_goEnd _ _ hp2 ⟨0, by omega, by simp [ho], by simp, by simp, hfr,
      fun h' => absurd h0 h', fun _ => ⟨hnv, Or.inl rfl⟩⟩
  · rw [if_neg (by simp [Cond.eval, h0])]
    obtain ⟨C, hwf, hC, hpos, hN, hn⟩ := hok h0
    have hCl := length_le_toks C
    refine ach_gateStep τ _ hp1 hp2 h0 (by omega) (by omega) ?_
    intro τ' ho' hq1 hq2 hfr' hres
    have hfr2 : ∀ x, x ∉ gateClob → τ'.reg x = σ.reg x := fun x hx => (hfr' x hx).trans (hfr x hx)
    rcases hres with ⟨G, hG, hGat, hpos', hok', hN'⟩ | ⟨hok', hno⟩
    · have hGl : 0 < G.toks.length := List.length_pos_iff.2 (MGate.toks_ne_nil G)
      refine ⟨2 * (w.length + 1 - τ'.pos) + 2, by omega, ho'.trans ho, hq1, hq2, hfr2,
        fun _ => ⟨C ++ [G], wellFormed_append_single hwf (by rwa [← hN]), ?_, ?_, ?_, rfl⟩,
        fun h' => absurd h' hok'⟩
      · simp only [encodeCircuit, List.flatMap_append, List.flatMap_singleton]
        rw [At.toks_append]
        exact ⟨hC, by rw [← hpos]; exact hGat⟩
      · rw [hpos', hpos]; simp; ring
      · rw [hN', hN]; simp
    · refine ⟨1, by omega, ho'.trans ho, hq1, hq2, hfr2, fun h' => absurd hok' h',
        fun _ => ⟨?_, Or.inr rfl⟩⟩
      refine not_valid_of_gate_fail hC (by omega) ?_
      rw [← hN, ← hpos]; exact hno

lemma ach_validate (σ : St 20) (Q : St 20 → Prop) (hB : w.length + 1 ≤ B)
    (h : ∀ τ : St 20, τ.out = σ.out → (∀ x, x ∉ gateClob → τ.reg x = σ.reg x) →
      (τ.reg rOk ≠ 0 ↔ ValidCode w) →
      (∀ C, w = encodeCircuit C → τ.reg rOk ≠ 0 → τ.reg rN = C.length) → Q τ) :
    Ach w B validate σ Q := by
  have hB1 : 1 ≤ B := by omega
  unfold validate
  refine ach_seq (ach_setOne _ _ _ hB1 (ach_seq (ach_clear _ _ _ (ach_seq (ach_rewind _ _ ?_)))))
  refine ach_seq (Ach.mono (ach_loop (VInv w σ)
    (fun τ => ∃ n, VInv w σ n τ ∧ τ.pos = w.length + 1) ?_ (2 * (w.length + 1 - 1) + 2) _ ?_) ?_)
  · intro n τ hI
    have hp1 := hI.2.1
    have hp2 := hI.2.2.1
    by_cases hend : τ.pos = w.length + 1
    · left
      refine ⟨?_, n, hI, hend⟩
      simp [Cond.eval, (inputSym_eq_rend hp1 hp2).2 hend]
    · right
      refine ⟨?_, vinv_step σ hB n τ hI (by omega)⟩
      simp [Cond.eval]
      rw [inputSym_eq_rend hp1 hp2]; exact hend
  · refine ⟨by simp, by simp, by simp, ?_, ?_, ?_⟩
    · intro x hx
      have h1 : x ≠ rOk := by rintro rfl; exact hx (by decide)
      have h2 : x ≠ rN := by rintro rfl; exact hx (by decide)
      simp [St.setReg_apply, h1, h2]
    · intro _
      have h0 : At w 1 [] := At.nil le_rfl (by omega)
      exact ⟨[], wellFormed_nil, by simpa [encodeCircuit, encodeToks] using h0, by simp,
        by simp [St.setReg_apply], by simp⟩
    · intro h'; simp [St.setReg_apply] at h'
  · rintro τ ⟨n, ⟨ho, hp1, hp2, hfr, hok, hbad⟩, hend⟩
    -- the final check that the circuit is non-empty
    have hfin : ∀ τ' : St 20, τ'.out = τ.out → (∀ x, x ≠ rOk → τ'.reg x = τ.reg x) →
        (τ'.reg rOk ≠ 0 ↔ ValidCode w) →
        (∀ C, w = encodeCircuit C → τ'.reg rOk ≠ 0 → τ'.reg rN = C.length) → Q τ' := by
      intro τ' h1 h2 h3 h4
      refine h τ' (h1.trans ho) ?_ h3 h4
      intro x hx
      rw [h2 x (by rintro rfl; exact hx (by decide))]; exact hfr x hx
    refine ach_ite ?_
    by_cases h0 : τ.reg rOk = 0
    · have hnv := (hbad h0).1
      split_ifs
      · exact ach_clear _ _ _ (hfin _ (by simp) (fun x hx => by simp [St.setReg_apply, hx])
          (by simp [St.setReg_apply, hnv]) (fun C _ h' => by simp [St.setReg_apply] at h'))
      · exact ach_skip (hfin _ rfl (fun _ _ => rfl) (by simp [h0, hnv])
          (fun C _ h' => absurd h0 h'))
    · obtain ⟨C, hwf, hC, hpos, hN, -⟩ := hok h0
      have hw : encodeCircuit C = w := by
        refine At.eq_of_length hC (at_self w) ?_
        rw [encodeCircuit_length]; omega
      have huniq : ∀ C', w = encodeCircuit C' → C' = C := fun C' hC' =>
        encodeCircuit_injective (hC'.symm.trans hw.symm)
      split_ifs with hN0
      · have hC0 : C = [] := by
          rw [Cond.eval] at hN0; simp at hN0; rw [hN0] at hN
          exact List.length_eq_zero_iff.1 hN.symm
        subst hC0
        refine ach_clear _ _ _ (hfin _ (by simp) (fun x hx => by simp [St.setReg_apply, hx])
          ?_ (fun C _ h' => by simp [St.setReg_apply] at h'))
        simp only [St.setReg_apply, if_true, ne_eq, not_true_eq_false, false_iff]
        rintro ⟨C', hne, -, hC'⟩
        rw [← hw] at hC'
        exact hne (encodeCircuit_injective hC'.symm)
      · refine ach_skip (hfin _ rfl (fun _ _ => rfl) ?_ ?_)
        · simp only [ne_eq, h0, not_false_eq_true, true_iff]
          refine ⟨C, ?_, hwf, hw.symm⟩
          rintro rfl
          simp [Cond.eval, hN] at hN0
        · intro C' hC' _
          rw [huniq C' hC', hN]

end MCVPReduction

end PathChecking
