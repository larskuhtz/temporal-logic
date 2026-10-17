module

public import RequestProject.PTime.HLLib
public import RequestProject.CTLStarP.EvalProof

/-!
# The decision procedure as a structured program: basics and scans

The program has `48` variables.  Variable `0` holds the number of input tokens.  Every program
fragment computing one of the pure functions of `CTLStarP/Scan.lean`, `CTLStarP/Valid.lean`,
`CTLStarP/Eval.lean` uses its own input, output and local variables.
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT

/-- Number of variables. -/
abbrev M : ℕ := 48

notation "vN" => (0 : Fin 48)
notation "vSP" => (1 : Fin 48)
notation "vSC" => (2 : Fin 48)
notation "vSR" => (3 : Fin 48)

/-- Common assumptions: the input is the encoding of `ts` and the bound is large enough. -/
structure Ctx (ts : List Tok) (w : Word) (B : ℕ) : Prop where
  tok : ∀ p, rtok w p = tc ts p
  bnd : 16 * (ts.length + 2) ^ 3 + 64 ≤ B

lemma Ctx.b64 {ts : List Tok} {w : Word} {B : ℕ} (h : Ctx ts w B) : 64 ≤ B := by
  have := h.bnd; omega

lemma Ctx.bn {ts : List Tok} {w : Word} {B : ℕ} (h : Ctx ts w B) : ts.length + 64 ≤ B := by
  have := h.bnd
  have : ts.length ≤ 16 * (ts.length + 2) ^ 3 := by
    have : ts.length ≤ (ts.length + 2) ^ 3 := by
      calc ts.length ≤ ts.length + 2 := by omega
        _ = (ts.length + 2) ^ 1 := by ring
        _ ≤ (ts.length + 2) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

lemma tc_le (ts : List Tok) (p : ℕ) : tc ts p ≤ 29 := by
  unfold tc; split
  · rename_i t _; have := Tok.code_lt t; omega
  · omega

/-- Membership in a list of codes as a predicate. -/
def lmem (L : List ℕ) (k : ℕ) : Bool := decide (k ∈ L)

lemma upF_eq : upF = lmem [8, 10] := by
  funext k; simp only [upF, lmem]; by_cases h1 : k = 8 <;> by_cases h2 : k = 10 <;> simp [h1, h2]
lemma downF_eq : downF = lmem [2, 6] := by
  funext k; simp only [downF, lmem]; by_cases h1 : k = 2 <;> by_cases h2 : k = 6 <;> simp [h1, h2]
lemma upT_eq : upT = lmem [3] := by
  funext k; simp only [upT, lmem]; by_cases h : k = 3 <;> simp [h]
lemma downT_eq : downT = lmem [4] := by
  funext k; simp only [downT, lmem]; by_cases h : k = 4 <;> simp [h]
lemma upN_eq : upN = lmem [] := by funext k; simp [upN, lmem]
lemma downN_eq : downN = lmem [2] := by
  funext k; simp only [downN, lmem]; by_cases h : k = 2 <;> simp [h]

/-! ## Scans -/

/-- One counting step as an expression. -/
def eCs (U D : List ℕ) (k c : Ex M) : Ex M :=
  c + Ex.inL k U - (Ex.const 1 - Ex.inL k U) * Ex.inL k D

variable {w : Word} {B : ℕ}

lemma ev_eCs (σ : HSt M) (U D : List ℕ) (k c : Ex M) :
    (eCs U D k c).ev w σ = cstep (lmem U) (lmem D) (k.ev w σ) (c.ev w σ) := by
  simp only [eCs, ev_sub, ev_add, ev_mul, ev_const, ev_inL, cstep, lmem]
  by_cases hu : k.ev w σ ∈ U <;> by_cases hd : k.ev w σ ∈ D <;> simp [hu, hd]

lemma bnd_eCs (σ : HSt M) (U D : List ℕ) (hU : ∀ c ∈ U, c ≤ B) (hD : ∀ c ∈ D, c ≤ B)
    (hB : 2 ≤ B) (k c : Ex M) (hk : k.Bnd w B σ) (hc : c.Bnd w B σ) (hc1 : c.ev w σ + 1 ≤ B) :
    (eCs U D k c).Bnd w B σ := by
  simp only [eCs, bnd_sub, bnd_add, bnd_mul, bnd_const]
  have h1 := bv_le (decide (k.ev w σ ∈ U))
  have h2 := bv_le (decide (k.ev w σ ∈ D))
  refine ⟨⟨hc, bnd_inL σ k hB U hU hk, ?_⟩, ⟨by omega, bnd_inL σ k hB U hU hk⟩,
    bnd_inL σ k hB D hD hk, ?_⟩
  · rw [ev_inL]; omega
  · simp only [ev_sub, ev_const, ev_inL]
    calc (1 - bv (decide (k.ev w σ ∈ U))) * bv (decide (k.ev w σ ∈ D)) ≤ 1 * 1 :=
          Nat.mul_le_mul (by omega) h2
      _ ≤ B := by omega

/-- `SR := scan (SP, SC)` (clobbers `SP`, `SC`). -/
def scanP (U D : List ℕ) : Hs M :=
  .loop (Ex.band (Ex.lt (.var vSP) (.var vN)) (Ex.lt (.const 0) (eCs U D (.tok (.var vSP)) (.var vSC))))
    (.seq (.set vSC (eCs U D (.tok (.var vSP)) (.var vSC))) (.set vSP (.var vSP + .const 1))) ;;
  .ite (Ex.lt (.var vSP) (.var vN)) (.set vSR (.var vSP + .const 1)) (.set vSR (.var vSP))

theorem hach_scanP {ts : List Tok} (hc : Ctx ts w B) (U D : List ℕ) (hU : ∀ c ∈ U, c ≤ 30)
    (hD : ∀ c ∈ D, c ≤ 30) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hp : σ.v vSP ≤ ts.length + 1) (hcnt : σ.v vSC ≤ 1) :
    HAch w B (scanP U D) σ (fun σ' =>
      σ'.v vSR = scan ts (lmem U) (lmem D) (σ.v vSP) (σ.v vSC) ∧ Frame [vSP, vSC, vSR] σ σ') := by
  have hB := hc.bnd
  have hB64 := hc.b64
  have hBn := hc.bn
  have hU' : ∀ c ∈ U, c ≤ B := fun c h => by have := hU c h; omega
  have hD' : ∀ c ∈ D, c ≤ B := fun c h => by have := hD c h; omega
  set n := ts.length
  let inv : HSt M → Prop := fun σ1 => Frame [vSP, vSC] σ σ1 ∧
    scan ts (lmem U) (lmem D) (σ.v vSP) (σ.v vSC) =
      scan ts (lmem U) (lmem D) (σ1.v vSP) (σ1.v vSC) ∧
    σ1.v vSP ≤ n + 1 ∧ σ1.v vSC ≤ 1 + σ1.v vSP
  refine hach_seq (hach_while inv (fun σ1 => n + 1 - σ1.v vSP) _ ?_ ?_ ?_ σ
    ⟨Frame.refl _ _, rfl, hp, by omega⟩)
  · rintro σ1 ⟨hf, -, h1, h2⟩
    have hN1 : σ1.v vN = n := by rw [hf.1 vN (by decide), hN]
    rw [bnd_band σ1 _ _ (by omega) _ _ (ev_lt σ1 _ _) (ev_lt σ1 _ _)]
    refine ⟨?_, ?_⟩
    · simp; omega
    · simp only [bnd_lt, bnd_const]
      exact ⟨by omega, bnd_eCs σ1 U D hU' hD' (by omega) _ _ (by simp; omega)
        (by simp; omega) (by simp; omega)⟩
  · rintro σ1 ⟨hf, hs, h1, h2⟩ hcond
    have hN1 : σ1.v vN = n := by rw [hf.1 vN (by decide), hN]
    rw [ev_band σ1 _ _ _ _ (ev_lt σ1 _ _) (ev_lt σ1 _ _)] at hcond
    simp only [bv_eq_zero, Bool.and_eq_false_iff, decide_eq_false_iff_not, ev_var, hN1,
      ev_eCs, ev_tok, ev_const, hc.tok, not_lt, Nat.le_zero] at hcond
    refine hach_ite (by simp; omega) ?_
    by_cases hlt : σ1.v vSP < n
    · have hcs : cstep (lmem U) (lmem D) (tc ts (σ1.v vSP)) (σ1.v vSC) = 0 := by
        rcases hcond with h | h
        · omega
        · exact h
      rw [if_pos (by simp [hN1, hlt])]
      refine hach_set (by simp; omega) ⟨?_, (hf.mono (by simp)).set (by simp) _⟩
      simp only [HSt.set_v, Function.update_self, ev_add, ev_var, ev_const]
      rw [hs, scan_eq, if_neg (by omega), if_pos hcs]
    · rw [if_neg (by simp [hN1, hlt])]
      refine hach_set (by simp; omega) ⟨?_, (hf.mono (by simp)).set (by simp) _⟩
      simp only [HSt.set_v, Function.update_self, ev_var]
      rw [hs, scan_eq, if_pos (by omega)]
  · rintro σ1 ⟨hf, hs, h1, h2⟩ hcond
    have hN1 : σ1.v vN = n := by rw [hf.1 vN (by decide), hN]
    rw [ev_band σ1 _ _ _ _ (ev_lt σ1 _ _) (ev_lt σ1 _ _)] at hcond
    simp only [ne_eq, bv_eq_zero, Bool.and_eq_false_iff, decide_eq_false_iff_not, ev_var, hN1,
      ev_eCs, ev_tok, ev_const, hc.tok, not_lt, Nat.le_zero, not_or, not_le] at hcond
    obtain ⟨hlt, hpos⟩ := hcond
    have hcsle : cstep (lmem U) (lmem D) (tc ts (σ1.v vSP)) (σ1.v vSC) ≤ σ1.v vSC + 1 := by
      unfold cstep; split_ifs <;> omega
    refine hach_seq (hach_set (bnd_eCs σ1 U D hU' hD' (by omega) _ _ (by simp; omega)
      (by simp; omega) (by simp; omega)) (hach_set ?_ ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩))
    · simp only [bnd_add, bnd_var, bnd_const, ev_var, ev_const, HSt.set_v, Function.update_apply,
        Fin.reduceEq, if_false]
      omega
    · exact (hf.set (by simp) _).set (by simp) _
    · simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const, ev_eCs, ev_tok, hc.tok]
      simp only [Fin.reduceEq, if_true, if_false]
      rw [hs, scan_eq (p := σ1.v vSP), if_neg (by omega), if_neg (by omega)]
    · simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const]
      simp only [Fin.reduceEq, if_true, if_false]; omega
    · simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const, ev_eCs, ev_tok, hc.tok]
      simp only [Fin.reduceEq, if_true, if_false]
      omega
    · simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const]
      simp only [Fin.reduceEq, if_true, if_false]; omega

end CTLP

end PathChecking
