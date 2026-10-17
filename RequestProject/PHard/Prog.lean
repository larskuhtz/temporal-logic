module

public import RequestProject.PHard.Tableau
public import RequestProject.PHard.Lib

/-!
# A logspace program producing the tableau circuit

`tabProg M c` first computes the parameters `n`, `T`, `NE`, `S`, `N` of the tableau circuit
into registers, and then, for every gate index `g < N`, recomputes the gate `gateFn M c w g`
from `g` alone (by divisions and comparisons) and outputs its encoding.

Register layout: `0 = n`, `1 = T`, `2 = NE`, `3 = S`, `4 = N`, `5 = g`, `6 =` loop counter,
`7 = (T + 1) · nZ`; registers `8 … 26` are scratch registers of the gate computation.
-/

@[expose] public section

namespace PathChecking

namespace PHardness

open Classical MCVPReduction LS
open scoped LS

noncomputable section

variable (M : TM) (c : ℕ)

/-- Register expression. -/
abbrev rg (i : ℕ) : AE := .reg i
/-- Constant expression. -/
abbrev cst (k : ℕ) : AE := .const k

/-- Decoding of the gate index `g` (register `5`) into scratch registers. -/
def decodeList : List (ℕ × AE) :=
  [(8, .div (rg 5) (rg 3)),
   (9, .mod (rg 5) (rg 3)),
   (10, .div (rg 8) (rg 2)),
   (11, .mod (rg 8) (rg 2)),
   (12, .div (.sub (rg 9) (cst 1)) (cst 2)),
   (13, .mod (.sub (rg 9) (cst 1)) (cst 2)),
   (14, .div (rg 12) (rg 2)),
   (15, .mod (rg 12) (rg 2)),
   (16, .div (rg 11) (rg 7)),
   (17, .mod (.div (rg 11) (cst (nZ M))) (.add (rg 1) (cst 1))),
   (18, .mod (rg 11) (cst (nZ M))),
   (19, .div (rg 14) (rg 7)),
   (20, .mod (.div (rg 14) (cst (nZ M))) (.add (rg 1) (cst 1))),
   (21, .mod (rg 14) (cst (nZ M))),
   (22, .div (rg 15) (rg 7)),
   (23, .mod (.div (rg 15) (cst (nZ M))) (.add (rg 1) (cst 1))),
   (24, .mod (rg 15) (cst (nZ M)))]

/-- The values of the decoded registers. -/
structure Glob (n g : ℕ) (ρ : Fin 64 → ℕ) : Prop where
  h0 : ρ (R 0) = n
  h1 : ρ (R 1) = Tb c n
  h2 : ρ (R 2) = NE M c n
  h3 : ρ (R 3) = Sb M c n
  h4 : ρ (R 4) = Nb M c n
  h5 : ρ (R 5) = g
  h7 : ρ (R 7) = (Tb c n + 1) * nZ M

/-- Bound on all register values. -/
def Bd (n : ℕ) : ℕ := Nb M c n

lemma nZ_le_NE (n : ℕ) : nZ M ≤ NE M c n := by
  unfold NE; exact Nat.le_mul_of_pos_left _ (by positivity)

lemma NE_le_Sb (n : ℕ) : NE M c n ≤ Sb M c n := by
  unfold Sb; have := NE_pos M c n; nlinarith

lemma Sb_le_Nb (n : ℕ) : Sb M c n ≤ Nb M c n := by
  unfold Nb; exact Nat.le_mul_of_pos_left _ (by positivity)

lemma JZ_le_NE (n : ℕ) : (Tb c n + 1) * nZ M ≤ NE M c n := by
  rw [NE_eq]; exact Nat.le_mul_of_pos_left _ (by omega)

lemma n_le_NE (n : ℕ) : n + 2 ≤ NE M c n := by
  unfold NE; have := nZ_pos M
  calc n + 2 ≤ (n + 2) * (Tb c n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ this

lemma T_le_NE (n : ℕ) : Tb c n + 1 ≤ NE M c n := by
  have := JZ_le_NE M c n; have := nZ_pos M
  calc Tb c n + 1 ≤ (Tb c n + 1) * nZ M := Nat.le_mul_of_pos_right _ this
    _ ≤ _ := JZ_le_NE M c n

lemma NE_le_Bd (n : ℕ) : NE M c n ≤ Bd M c n := (NE_le_Sb M c n).trans (Sb_le_Nb M c n)

lemma decode_vals {n g : ℕ} {ρ : Fin 64 → ℕ} (hG : Glob M c n g ρ) :
    let ρ' := updAll (decodeList M) ρ
    ρ' (R 0) = n ∧ ρ' (R 1) = Tb c n ∧ ρ' (R 2) = NE M c n ∧ ρ' (R 3) = Sb M c n ∧
    ρ' (R 5) = g ∧ ρ' (R 7) = (Tb c n + 1) * nZ M ∧
    ρ' (R 8) = g / Sb M c n ∧ ρ' (R 9) = g % Sb M c n ∧
    ρ' (R 10) = g / Sb M c n / NE M c n ∧ ρ' (R 11) = g / Sb M c n % NE M c n ∧
    ρ' (R 12) = (g % Sb M c n - 1) / 2 ∧ ρ' (R 13) = (g % Sb M c n - 1) % 2 ∧
    ρ' (R 14) = (g % Sb M c n - 1) / 2 / NE M c n ∧
    ρ' (R 15) = (g % Sb M c n - 1) / 2 % NE M c n ∧
    ρ' (R 16) = eP M c n (g / Sb M c n % NE M c n) ∧
    ρ' (R 17) = eJ M c n (g / Sb M c n % NE M c n) ∧
    ρ' (R 18) = eZ M (g / Sb M c n % NE M c n) ∧
    ρ' (R 19) = eP M c n ((g % Sb M c n - 1) / 2 / NE M c n) ∧
    ρ' (R 20) = eJ M c n ((g % Sb M c n - 1) / 2 / NE M c n) ∧
    ρ' (R 21) = eZ M ((g % Sb M c n - 1) / 2 / NE M c n) ∧
    ρ' (R 22) = eP M c n ((g % Sb M c n - 1) / 2 % NE M c n) ∧
    ρ' (R 23) = eJ M c n ((g % Sb M c n - 1) / 2 % NE M c n) ∧
    ρ' (R 24) = eZ M ((g % Sb M c n - 1) / 2 % NE M c n) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h7⟩ := hG
  simp only [decodeList, updAll, AE.eval, Function.update_apply]
  simp [R] at h0 h1 h2 h3 h5 h7
  simp [R, h0, h1, h2, h3, h5, h7, eP, eJ, eZ]

lemma decode_ok {n g : ℕ} {ρ : Fin 64 → ℕ} (hG : Glob M c n g ρ) (hg : g < Nb M c n) :
    AllOK (Bd M c n) (decodeList M) ρ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h7⟩ := hG
  simp [R] at h0 h1 h2 h3 h5 h7
  have := NE_pos M c n
  have := nZ_pos M
  have := Sb_pos M c n
  have := NE_le_Bd M c n
  have := nZ_le_NE M c n
  have := T_le_NE M c n
  have := JZ_le_NE M c n
  simp only [decodeList, AllOK, AE.Bnd, AE.eval, AE.RL, AE.ht, Function.update_apply]
  simp [R, h1, h2, h3, h5, h7, Bd]
  have := Sb_le_Nb M c n
  have : NE M c n ≤ Nb M c n := NE_le_Bd M c n
  have := n_le_NE M c n
  have := Nat.mod_le g (Sb M c n)
  have := Nat.div_le_self g (Sb M c n)
  repeat' apply And.intro
  all_goals repeat (first | omega | apply le_trans (Nat.div_le_self _ _) |
    apply le_trans (Nat.mod_le _ _))

end

end PHardness

end PathChecking
