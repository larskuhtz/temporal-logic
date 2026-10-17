module

public import RequestProject.Logspace.VSim

/-!
# Simulating a machine on a prefix of the real input

The virtual input is the prefix `x.take L` of the real input `x`; the virtual head is the real
head, and the register `rR` holds `L + 1 - p` (so that the end of the prefix is detected).
Every output bit `b` of the simulated machine is emitted as the bit string `enc b`.

`runPrefix enc M` runs `M` on the prefix whose length is in register `rL`.
-/

@[expose] public section

namespace PathChecking

open Classical

namespace LS

open scoped LS

namespace VR

/-- Number of registers of the programs of this file. -/
abbrev KR : ℕ := 13

/-- Simulation registers. -/
def ρs (i : Fin 8) : Fin KR := ⟨i.val, lt_of_lt_of_le i.isLt (by decide)⟩

lemma ρs_injective : Function.Injective ρs := by
  intro i j h; simp only [ρs, Fin.mk.injEq] at h; exact Fin.ext h

/-- `L + 1 - p` -/
abbrev rR : Fin KR := 8
/-- the length of the input -/
abbrev rN : Fin KR := 9
/-- the length of the prefix -/
abbrev rL : Fin KR := 10
/-- a loop counter -/
abbrev rK : Fin KR := 11
/-- a temporary -/
abbrev rT : Fin KR := 12

@[simp] lemma ρs_val (i : Fin 8) : (ρs i).val = i.val := rfl

lemma ne_ρs {y : Fin KR} (h : 8 ≤ y.val) (i : Fin 8) : y ≠ ρs i := by
  intro e; have := congrArg Fin.val e; simp at this; omega

@[simp] lemma rR_ne_ρs (i : Fin 8) : rR ≠ ρs i := ne_ρs (by decide) i
@[simp] lemma rN_ne_ρs (i : Fin 8) : rN ≠ ρs i := ne_ρs (by decide) i
@[simp] lemma rL_ne_ρs (i : Fin 8) : rL ≠ ρs i := ne_ρs (by decide) i
@[simp] lemma rK_ne_ρs (i : Fin 8) : rK ≠ ρs i := ne_ρs (by decide) i
@[simp] lemma rT_ne_ρs (i : Fin 8) : rT ≠ ρs i := ne_ρs (by decide) i
@[simp] lemma ρs_ne_rR (i : Fin 8) : ρs i ≠ rR := (rR_ne_ρs i).symm
@[simp] lemma ρs_ne_rN (i : Fin 8) : ρs i ≠ rN := (rN_ne_ρs i).symm
@[simp] lemma ρs_ne_rL (i : Fin 8) : ρs i ≠ rL := (rL_ne_ρs i).symm
@[simp] lemma ρs_ne_rK (i : Fin 8) : ρs i ≠ rK := (rK_ne_ρs i).symm
@[simp] lemma ρs_ne_rT (i : Fin 8) : ρs i ≠ rT := (rT_ne_ρs i).symm
@[simp] lemma rR_ne_rN : rR ≠ rN := by decide
@[simp] lemma rR_ne_rL : rR ≠ rL := by decide
@[simp] lemma rR_ne_rK : rR ≠ rK := by decide
@[simp] lemma rR_ne_rT : rR ≠ rT := by decide
@[simp] lemma rN_ne_rR : rN ≠ rR := by decide
@[simp] lemma rN_ne_rL : rN ≠ rL := by decide
@[simp] lemma rN_ne_rK : rN ≠ rK := by decide
@[simp] lemma rN_ne_rT : rN ≠ rT := by decide
@[simp] lemma rL_ne_rR : rL ≠ rR := by decide
@[simp] lemma rL_ne_rN : rL ≠ rN := by decide
@[simp] lemma rL_ne_rK : rL ≠ rK := by decide
@[simp] lemma rL_ne_rT : rL ≠ rT := by decide
@[simp] lemma rK_ne_rR : rK ≠ rR := by decide
@[simp] lemma rK_ne_rN : rK ≠ rN := by decide
@[simp] lemma rK_ne_rL : rK ≠ rL := by decide
@[simp] lemma rK_ne_rT : rK ≠ rT := by decide
@[simp] lemma rT_ne_rR : rT ≠ rR := by decide
@[simp] lemma rT_ne_rN : rT ≠ rN := by decide
@[simp] lemma rT_ne_rL : rT ≠ rL := by decide
@[simp] lemma rT_ne_rK : rT ≠ rK := by decide

/-- Fetching the virtual input symbol. -/
noncomputable def cfetch : Stmt KR := .ite (.zero rR) (setC (ρs 7) 1) (getSym (ρs 7))

/-- Moving the virtual input head. -/
def cmv : InSym → Dir → Stmt KR
  | x, .left => if x = .lend then .skip else (.left ⨟ .inc rR)
  | _, .stay => .skip
  | x, .right => if x = .rend then .skip else (.right ⨟ .dec rR)

/-- Handling an output bit. -/
def coa (enc : Bool → List Bool) : Option Bool → Stmt KR
  | none => .skip
  | some b => emitBits (enc b)

/-- The auxiliary invariant. -/
def CAux (L : ℕ) (enc : Bool → List Bool) (out₀ : List Bool) (Extra : St KR → Prop)
    (p : ℕ) (o : List Bool) (σ : St KR) : Prop :=
  σ.pos = p ∧ σ.reg rR = L + 1 - p ∧ p ≤ L + 1 ∧ σ.out = out₀ ++ o.flatMap enc ∧ Extra σ

/-- `Extra` only depends on the registers other than the simulation registers, `rR` and `rT`. -/
def ExtraOK (Extra : St KR → Prop) : Prop :=
  ∀ σ τ : St KR, Extra σ → (∀ y : Fin KR, 8 ≤ y.val → y ≠ rR → y ≠ rT → τ.reg y = σ.reg y) →
    Extra τ

lemma inputSym_take {x : Word} {L p : ℕ} (hp : p ≤ L) :
    inputSym (x.take L) p = inputSym x p := by
  unfold inputSym
  split_ifs with h
  · rfl
  · rw [List.getElem?_take_of_lt]; omega

lemma inputSym_take_end {x : Word} {L : ℕ} (hL : L ≤ x.length) :
    inputSym (x.take L) (L + 1) = .rend := by
  unfold inputSym
  rw [if_neg (by omega), List.getElem?_eq_none (by rw [List.length_take]; omega)]

variable {x : Word} {B : ℕ}

lemma cspec {L : ℕ} {enc : Bool → List Bool} {out₀ : List Bool} {Extra : St KR → Prop}
    (hL : L ≤ x.length) (hB : L + 3 ≤ B) (hEx : ExtraOK Extra) :
    VSpec x B ρs (x.take L) cfetch cmv (coa enc) (CAux L enc out₀ Extra) := by
  have hlen : (x.take L).length = L := by simp; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro p o σ τ ⟨h1, h2, h3, h4, h5⟩ hy hpos hout
    refine ⟨hpos.trans h1, by rw [hy rR (fun i => ne_ρs (by decide) i)]; exact h2, h3,
      hout.trans h4, hEx σ τ h5 (fun y hy8 _ _ => hy y (fun i => ne_ρs hy8 i))⟩
  · rintro p o σ hp ⟨h1, h2, h3, h4, h5⟩
    rw [hlen] at hp
    unfold cfetch
    by_cases hpe : p = L + 1
    · refine ach_iteT (by simp [Cond.eval, h2, hpe]) (ach_setC _ _ _ _ (by omega) ?_)
      refine ⟨?_, fun i hi => ?_, h1, ?_, h3, h4, hEx σ _ h5 (fun y hy8 _ _ => ?_)⟩
      · simp [St.setReg_apply, hpe, inputSym_take_end hL, symCode]
      · simp [St.setReg_apply, ρs_injective.eq_iff, hi]
      · simp [St.setReg_apply, h2]
      · simp [St.setReg_apply, ne_ρs hy8 7]
    · refine ach_iteF (by simp [Cond.eval, h2]; omega) (ach_getSym _ _ _ (by omega) ?_)
      refine ⟨?_, fun i hi => ?_, h1, ?_, h3, h4, hEx σ _ h5 (fun y hy8 _ _ => ?_)⟩
      · simp [St.setReg_apply, h1, inputSym_take (x := x) (show p ≤ L by omega)]
      · simp [St.setReg_apply, ρs_injective.eq_iff, hi]
      · simp [St.setReg_apply, h2]
      · simp [St.setReg_apply, ne_ρs hy8 7]
  · rintro p o σ x' d hp hx ⟨h1, h2, h3, h4, h5⟩
    rw [hlen] at hp ⊢
    cases d with
    | left =>
      show Ach x B (if x' = .lend then .skip else (.left ⨟ .inc rR)) σ _
      by_cases hl : x' = .lend
      · rw [if_pos hl]
        have hp0 : p = 0 := inputSym_eq_lend.1 (hx ▸ hl)
        refine ach_skip ⟨fun i => rfl, ?_⟩
        subst hp0
        simp only [Dir.move]
        exact ⟨by simp [h1], by simp [h2], by omega, h4, h5⟩
      · rw [if_neg hl]
        have hp0 : p ≠ 0 := fun e => hl (by rw [hx, e]; exact inputSym_eq_lend.2 rfl)
        have hR : ({ σ with pos := σ.pos - 1 } : St KR).reg rR < B := by
          show σ.reg rR < B; rw [h2]; omega
        refine ach_seq (ach_left (ach_inc hR ⟨fun i => ?_, ?_⟩))
        · simp [St.setReg_apply, Ne.symm (ne_ρs (show 8 ≤ rR.val by decide) i)]
        · simp only [Dir.move]
          refine ⟨by simp [h1]; omega, by simp [St.setReg_apply, h2]; omega,
            by omega, by simp [h4], hEx σ _ h5 ?_⟩
          intro y hy8 hyR _
          simp [St.setReg_apply, hyR]
    | stay =>
      refine ach_skip ⟨fun i => rfl, ?_⟩
      simp only [Dir.move]
      rw [min_eq_left hp]
      exact ⟨h1, h2, h3, h4, h5⟩
    | right =>
      show Ach x B (if x' = .rend then .skip else (.right ⨟ .dec rR)) σ _
      by_cases hr : x' = .rend
      · rw [if_pos hr]
        have hpL : p = L + 1 := by
          have h1p : 1 ≤ p := by
            rcases Nat.eq_zero_or_pos p with h0 | h0
            · rw [h0, inputSym_eq_lend.2 rfl] at hx; rw [hx] at hr; exact absurd hr (by simp)
            · exact h0
          have := (inputSym_eq_rend (w := x.take L) h1p (by rw [hlen]; exact hp)).1 (hx ▸ hr)
          rw [hlen] at this; exact this
        refine ach_skip ⟨fun i => rfl, ?_⟩
        simp only [Dir.move]
        rw [min_eq_right (by omega)]
        exact ⟨by rw [h1, hpL], by rw [h2, hpL], le_rfl, h4, h5⟩
      · rw [if_neg hr]
        have hpL : p ≠ L + 1 := fun e => hr (by rw [hx, e]; exact inputSym_take_end hL)
        refine ach_seq (ach_right (ach_dec ⟨fun i => ?_, ?_⟩))
        · simp [St.setReg_apply, Ne.symm (ne_ρs (show 8 ≤ rR.val by decide) i)]
        · simp only [Dir.move]
          rw [min_eq_left (by omega)]
          refine ⟨by simp [h1]; omega, by simp [h2]; omega, by omega, by simp [h4],
            hEx σ _ h5 ?_⟩
          intro y hy8 hyR _
          simp [St.setReg_apply, hyR]
  · rintro p o σ ob ⟨h1, h2, h3, h4, h5⟩
    cases ob with
    | none => exact ach_skip ⟨fun i => rfl, h1, h2, h3, by simp [h4], h5⟩
    | some b =>
      refine ach_emitBits _ _ _ ⟨fun i => rfl, h1, h2, h3, by simp [h4], ?_⟩
      exact hEx σ _ h5 (fun y _ _ _ => rfl)

/-- Prepare the simulation on the prefix of length `rL`: `rR := rL + 1`, head on the left end
marker. -/
def prep : Stmt KR := copy rL rR rT ⨟ .inc rR ⨟ rewind ⨟ .left

/-- Run `M` on the prefix of length `rL` of the input, emitting `enc b` for every output bit. -/
noncomputable def runPrefix (enc : Bool → List Bool) (M : TM) : Stmt KR :=
  prep ⨟ vsim M ρs cfetch cmv (coa enc)

/-- **Running a machine on a prefix.** -/
theorem ach_runPrefix (enc : Bool → List Bool) (M : TM) (f : Word → Word) (hM : M.Computes f)
    (σ : St KR) {S : ℕ} (hS : ∀ t, (M.run (x.take (σ.reg rL)) t).workPos ≤ S)
    {Extra : St KR → Prop} (hEx : ExtraOK Extra) (hσ : Extra σ)
    (hL : σ.reg rL ≤ x.length) (hB : M.nQ + S + 2 + M.nG ^ (S + 2) + x.length + 3 ≤ B) :
    Ach x B (runPrefix enc M) σ (fun τ =>
      τ.out = σ.out ++ (f (x.take (σ.reg rL))).flatMap enc ∧ Extra τ) := by
  set L := σ.reg rL with hLdef
  obtain ⟨T, hT⟩ := hM (x.take L)
  unfold runPrefix prep
  refine ach_seq (ach_seq (ach_copy _ _ _ (by decide) (by decide) (by decide) _ _ (by omega)
    (ach_seq (ach_inc ?_ (ach_seq (ach_rewind _ _ (ach_left ?_)))))))
  · simp [St.setReg_apply, show rR ≠ rT by decide]; omega
  · refine (ach_vsim ρs_injective (cspec (out₀ := σ.out) (enc := enc) hL (by omega) hEx) hS
      (by omega) hT _ ?_).mono ?_
    · refine ⟨rfl, by simp [St.setReg_apply, show rR ≠ rT by decide, hLdef], by omega, by simp,
        hEx σ _ hσ ?_⟩
      intro y hy8 hyR hyT
      simp [St.setReg_apply, hyR, hyT]
    · rintro τ ⟨p, -, -, -, h4, h5⟩
      exact ⟨h4, h5⟩

end VR

end LS

end PathChecking
