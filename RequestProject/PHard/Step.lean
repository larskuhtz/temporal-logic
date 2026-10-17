module

public import RequestProject.PHard.Body

/-!
# The transition gates of the tableau program

`stepPart M` decides the selector `stepK` of an `∨`-gate of a chain (for layers `1 … T`) and
outputs the corresponding gate (`ach_stepPart`). It branches on the third components of the
two entries, on the input symbol, and then evaluates a boolean expression over the
registers.
-/

@[expose] public section

namespace PathChecking

namespace PHardness

open Classical MCVPReduction LS
open scoped LS

noncomputable section

variable (M : TM) (c : ℕ) (w : Word)

/-- Moving a head, as an expression. -/
def moveE : Dir → AE → AE
  | .left, x => .sub x (cst 1)
  | .stay, x => x
  | .right, x => .add x (cst 1)

lemma moveE_eval (d : Dir) (x : AE) (ρ : Fin 64 → ℕ) : (moveE d x).eval ρ = d.move (x.eval ρ) := by
  cases d <;> rfl

/-- Minimum, as an expression. -/
def minE (x y : AE) : AE := .sub x (.sub x y)

lemma minE_eval (x y : AE) (ρ : Fin 64 → ℕ) : (minE x y).eval ρ = min (x.eval ρ) (y.eval ρ) := by
  simp only [minE, AE.eval]; omega

/-- The selector `stepK` for fixed `za`, `zb` and input symbol, as a boolean expression over
the registers `0` (`n`), `16 … 18` (`pc, jc, zc`), `19, 20` (`pa, ja`), `22, 23` (`pb, jb`). -/
def stepBE (za zb : ℕ) (s : InSym) : BE :=
  .or (.and (.lt (rg 18) (cst (4 * M.nQ)))
        (.and (.eq (rg 22) (cst 0)) (.and (.eq (rg 23) (rg 20))
          (.and (.eq (rg 16) (minE (moveE (res M (qOf M za) s (gOf M zb)).2.2.2.1 (rg 19))
              (.add (rg 0) (cst 1))))
            (.and (.eq (rg 17) (moveE (res M (qOf M za) s (gOf M zb)).2.2.1 (rg 20)))
              (.eq (rg 18) (cst (4 * qc M (res M (qOf M za) s (gOf M zb)).1 +
                updO (za % 4) (res M (qOf M za) s (gOf M zb)).2.2.2.2))))))))
      (.and (.not (.lt (rg 18) (cst (4 * M.nQ))))
        (.and (.eq (rg 16) (cst 0)) (.and (.eq (rg 22) (cst 0)) (.and (.eq (rg 23) (rg 17))
          (.or (.and (.eq (rg 20) (rg 17)) (.eq (.sub (rg 18) (cst (4 * M.nQ)))
              (cst (M.gc (res M (qOf M za) s (gOf M zb)).2.1))))
            (.and (.not (.eq (rg 20) (rg 17))) (.eq (rg 18) (cst zb))))))))

lemma stepBE_eval (za zb : ℕ) (ρ : Fin 64 → ℕ) (h0 : ρ (R 0) = w.length) (hza : za < 4 * M.nQ)
    (hzb : 4 * M.nQ ≤ zb) :
    (stepBE M za zb (inputSym w (ρ (R 19)))).eval ρ ↔
      stepK M w (ρ (R 16)) (ρ (R 17)) (ρ (R 18)) (ρ (R 19)) (ρ (R 20)) za (ρ (R 22)) (ρ (R 23))
        zb := by
  simp only [stepBE, stepK, BE.eval, AE.eval, moveE_eval, minE_eval, h0, hza, hzb, true_and]
  split_ifs <;> constructor <;> intro h <;> simp_all <;> omega


lemma moveE_RL (d : Dir) {x : AE} {k : ℕ} (h : x.RL k) : (moveE d x).RL k := by
  cases d <;> simp [moveE, AE.RL, h]

lemma moveE_ht (d : Dir) (x : AE) : (moveE d x).ht ≤ x.ht + 1 := by
  cases d <;> simp [moveE, AE.ht]

lemma moveE_Bnd (d : Dir) {x : AE} {ρ : Fin 64 → ℕ} {B : ℕ} (h : x.Bnd ρ B)
    (h1 : x.eval ρ + 1 ≤ B) : (moveE d x).Bnd ρ B := by
  cases d <;> simp [moveE, AE.Bnd, AE.eval, h] <;> omega

lemma chainA_lt (n g : ℕ) : (g % Sb M c n - 1) / 2 / NE M c n < NE M c n := by
  have h1 := Nat.mod_lt g (Sb_pos M c n)
  have hN := NE_pos M c n
  generalize g % Sb M c n = r at h1 ⊢
  unfold Sb at h1
  rw [Nat.div_lt_iff_lt_mul hN, Nat.div_lt_iff_lt_mul (by omega)]
  have : NE M c n * NE M c n * 2 = 2 * NE M c n * NE M c n := by ring
  have := Nat.mul_pos hN hN
  omega

lemma Inv.setReg {σ τ : St 64} {g i v : ℕ} (h : Inv M c w σ g τ) (hi : 25 ≤ i) (hi' : i < 64) :
    Inv M c w σ g (τ.setReg (R i) v) :=
  h.transfer M c w rfl (fun x hx => by
    simp only [St.setReg_reg]; exact Function.update_of_ne (ne_R hx hi hi') _ _)

lemma stepBE_RL (za zb : ℕ) (s : InSym) : (stepBE M za zb s).RL 30 := by
  simp [stepBE, BE.RL, AE.RL, minE, moveE_RL]

lemma stepBE_ht (za zb : ℕ) (s : InSym) : (stepBE M za zb s).ht ≤ 12 := by
  have h1 := moveE_ht (res M (qOf M za) s (gOf M zb)).2.2.2.1 (rg 19)
  have h2 := moveE_ht (res M (qOf M za) s (gOf M zb)).2.2.1 (rg 20)
  simp only [AE.ht] at h1 h2
  simp only [stepBE, BE.ht, AE.ht, minE]
  omega

/-- The transition part of the body. -/
def stepPart : Stmt 64 :=
  evalTo (rg 21) 25 30 ⨟ caseReg (R 25) ((List.range (nZ M)).map fun za =>
    if za < 4 * M.nQ then
      evalTo (rg 24) 26 30 ⨟ caseReg (R 26) ((List.range (nZ M)).map fun zb =>
        if 4 * M.nQ ≤ zb then seek 19 ⨟ symCase (fun s => ifB (stepBE M za zb s) emitT emitF 30)
        else emitF)
    else emitF)

lemma ach_stepPart {σ τ : St 64} {g : ℕ} (hI : Inv M c w σ g τ) (Q : St 64 → Prop)
    (h : ∀ b : Bool, (b = true ↔ stepK M w (τ.reg (R 16)) (τ.reg (R 17)) (τ.reg (R 18))
        (τ.reg (R 19)) (τ.reg (R 20)) (τ.reg (R 21)) (τ.reg (R 22)) (τ.reg (R 23))
        (τ.reg (R 24))) →
      ∀ τ', Inv M c w σ g τ' → (∀ x : Fin 64, x.val < 25 → τ'.reg x = τ.reg x) →
        Ach w (Bd M c w.length) (if b then emitT else emitF) τ' Q) :
    Ach w (Bd M c w.length) (stepPart M) τ Q := by
  have hD := hI.2.2
  have hN := NE_pos M c w.length
  have hzN := nZ_le_NE M c w.length
  have hNB := NE_le_Bd M c w.length
  have hnN := n_le_NE M c w.length
  have hTN := T_le_NE M c w.length
  have h21 : τ.reg (R 21) < nZ M := by rw [hD.r21]; exact eZ_lt M _
  have h24 : τ.reg (R 24) < nZ M := by rw [hD.r24]; exact eZ_lt M _
  have h16 : τ.reg (R 16) ≤ w.length + 1 := by
    rw [hD.r16]; have := eP_lt M c (Nat.mod_lt (g / Sb M c w.length) hN); omega
  have h19 : τ.reg (R 19) ≤ w.length + 1 := by
    rw [hD.r19]; have := eP_lt M c (chainA_lt M c w.length g); omega
  have h22 : τ.reg (R 22) ≤ w.length + 1 := by
    rw [hD.r22]; have := eP_lt M c (Nat.mod_lt ((g % Sb M c w.length - 1) / 2) hN); omega
  have h17 : τ.reg (R 17) ≤ Tb c w.length := by
    rw [hD.r17]; have := eJ_lt M c w.length (g / Sb M c w.length % NE M c w.length); omega
  have h20 : τ.reg (R 20) ≤ Tb c w.length := by
    rw [hD.r20]; have := eJ_lt M c w.length ((g % Sb M c w.length - 1) / 2 / NE M c w.length)
    omega
  have h23 : τ.reg (R 23) ≤ Tb c w.length := by
    rw [hD.r23]; have := eJ_lt M c w.length ((g % Sb M c w.length - 1) / 2 % NE M c w.length)
    omega
  have h18 : τ.reg (R 18) < nZ M := by rw [hD.r18]; exact eZ_lt M _
  have h0 := hD.r0
  -- copy `za`
  refine ach_seq (ach_comp (rg 21) 25 30 τ _ (by omega) (by simp [AE.RL]) (by simp [AE.ht])
    (by simp [AE.Bnd]; omega) ?_)
  intro τ1 ho1 _ hv1 hk1
  simp only [AE.eval] at hv1
  have e1 : ∀ x : Fin 64, x.val < 25 → τ1.reg x = τ.reg x :=
    fun x hx => hk1 x (by omega) (ne_R hx (by omega) (by omega))
  have hI1 : Inv M c w σ g τ1 := hI.transfer M c w ho1 e1
  refine ach_caseReg (R 25) _ (τ.reg (R 21)) (by simpa using h21) τ1 hv1 _ ?_
  simp only [List.getElem_map, List.getElem_range]
  have e1' : ∀ x : Fin 64, x.val < 25 → (τ1.setReg (R 25) 0).reg x = τ.reg x := fun x hx => by
    simp only [St.setReg_reg]; rw [Function.update_of_ne (ne_R hx le_rfl (by omega))]; exact e1 x hx
  split_ifs with hza
  swap
  · exact h false (by simp [stepK, hza]) _ (hI1.setReg M c w le_rfl (by omega)) e1'
  -- copy `zb`
  set τ2 := τ1.setReg (R 25) 0
  have hI2 : Inv M c w σ g τ2 := hI1.setReg M c w le_rfl (by omega)
  refine ach_seq (ach_comp (rg 24) 26 30 τ2 _ (by omega) (by simp [AE.RL]) (by simp [AE.ht])
    (by simp [AE.Bnd]; rw [e1' _ (by rw [R_val (by omega)]; omega)]; omega) ?_)
  intro τ3 ho3 _ hv3 hk3
  simp only [AE.eval] at hv3
  rw [e1' _ (by rw [R_val (by omega)]; omega)] at hv3
  have e3 : ∀ x : Fin 64, x.val < 25 → τ3.reg x = τ.reg x :=
    fun x hx => (hk3 x (by omega) (ne_R hx (by omega) (by omega))).trans (e1' x hx)
  have hI3 : Inv M c w σ g τ3 := hI2.transfer M c w ho3
    (fun x hx => hk3 x (by omega) (ne_R hx (by omega) (by omega)))
  refine ach_caseReg (R 26) _ (τ.reg (R 24)) (by simpa using h24) τ3 hv3 _ ?_
  simp only [List.getElem_map, List.getElem_range]
  have e3' : ∀ x : Fin 64, x.val < 25 → (τ3.setReg (R 26) 0).reg x = τ.reg x := fun x hx => by
    simp only [St.setReg_reg]; rw [Function.update_of_ne (ne_R hx (by omega) (by omega))]
    exact e3 x hx
  have hI3' : Inv M c w σ g (τ3.setReg (R 26) 0) := hI3.setReg M c w (by omega) (by omega)
  split_ifs with hzb
  swap
  · exact h false (by simp [stepK, hzb]) _ hI3' e3'
  set τ4 := τ3.setReg (R 26) 0
  refine ach_seq (ach_seek 19 (by omega) τ4 _ (by rw [e3' _ (by rw [R_val (by omega)]; omega)]; omega)
    (by rw [e3' _ (by rw [R_val (by omega)]; omega)]; omega) ?_)
  intro τ5 ho5 hp5 hk5
  have e5 : ∀ x : Fin 64, x.val < 25 → τ5.reg x = τ.reg x :=
    fun x hx => (hk5 x (by omega)).trans (e3' x hx)
  have hI5 : Inv M c w σ g τ5 := hI3'.transfer M c w ho5 (fun x hx => hk5 x (by omega))
  have r5 : ∀ i, i < 25 → τ5.reg (R i) = τ.reg (R i) :=
    fun i hi => e5 _ (by rw [R_val (by omega)]; omega)
  refine ach_symCase _ τ5 Q ?_
  rw [hp5, e3' _ (by rw [R_val (by omega)]; omega)]
  have hev := stepBE_eval M w (τ.reg (R 21)) (τ.reg (R 24)) τ5.reg (by rw [r5 0 (by omega), h0])
    hza hzb
  rw [r5 19 (by omega), r5 16 (by omega), r5 17 (by omega), r5 18 (by omega), r5 20 (by omega),
    r5 22 (by omega), r5 23 (by omega)] at hev
  have hht := stepBE_ht M (τ.reg (R 21)) (τ.reg (R 24)) (inputSym w (τ.reg (R 19)))
  refine ach_ifB _ _ _ 30 τ5 Q (stepBE_RL M _ _ _) (by omega) ?_ ?_ ?_
  · obtain ⟨r, hr⟩ : ∃ r, res M (qOf M (τ.reg (R 21))) (inputSym w (τ.reg (R 19)))
      (gOf M (τ.reg (R 24))) = r := ⟨_, rfl⟩
    have m1 := moveE_Bnd r.2.2.2.1 (x := rg 19) (ρ := τ5.reg) (B := Bd M c w.length)
      (by simp only [AE.Bnd]; rw [r5 19 (by omega)]; omega)
      (by simp only [AE.eval]; rw [r5 19 (by omega)]; omega)
    have m2 := moveE_Bnd r.2.2.1 (x := rg 20) (ρ := τ5.reg) (B := Bd M c w.length)
      (by simp only [AE.Bnd]; rw [r5 20 (by omega)]; omega)
      (by simp only [AE.eval]; rw [r5 20 (by omega)]; omega)
    have hq := qc_lt M r.1
    have ho := updO_lt (o := τ.reg (R 21) % 4) (by omega) r.2.2.2.2
    have hg := M.gc_lt r.2.1
    have hnz : nZ M = 4 * M.nQ + M.nG := rfl
    simp only [stepBE, hr, BE.Bnd, minE, AE.Bnd, AE.eval, m1, m2, r5 0 (by omega), r5 16 (by omega),
      r5 17 (by omega), r5 18 (by omega), r5 20 (by omega), r5 22 (by omega),
      r5 23 (by omega), true_and, and_true]
    repeat' apply And.intro
    all_goals omega
  · intro hb τ' hag
    exact h true (by simpa using hev.1 hb) τ' (hI5.agree M c w hag)
      (fun x hx => (hag.2.2 x (by omega)).trans (e5 x hx))
  · intro hb τ' hag
    exact h false (by simpa using fun h' => hb (hev.2 h')) τ' (hI5.agree M c w hag)
      (fun x hx => (hag.2.2 x (by omega)).trans (e5 x hx))

end

end PHardness

end PathChecking
