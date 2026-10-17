module

public import RequestProject.PHard.Step

/-!
# The loop body of the tableau program

`body M` decodes the gate index `g` (register `5`), computes the gate `gateFn M c w g` and
outputs its encoding (`ach_body`).
-/

@[expose] public section

namespace PathChecking

namespace PHardness

open Classical MCVPReduction LS
open scoped LS

noncomputable section

variable (M : TM) (c : ℕ) (w : Word)

/-! ## The output gate -/

/-- The final part (layer `T + 1`): decides `finalK`. -/
def finalPart : Stmt 64 :=
  evalTo (rg 21) 25 30 ⨟ caseReg (R 25) ((List.range (nZ M)).map fun z =>
    if z < 4 * M.nQ ∧ M.halt (qOf M z) = true ∧ z % 4 = 2 then
      ifB (.eq (rg 14) (rg 15)) emitT emitF 30
    else emitF)

lemma ach_finalPart {σ τ : St 64} {g : ℕ} (hI : Inv M c w σ g τ) (Q : St 64 → Prop)
    (h : ∀ b : Bool, (b = true ↔ finalK M (τ.reg (R 14)) (τ.reg (R 15))) →
      ∀ τ', Inv M c w σ g τ' → Ach w (Bd M c w.length) (if b then emitT else emitF) τ' Q) :
    Ach w (Bd M c w.length) (finalPart M) τ Q := by
  have hD := hI.2.2
  have hN := NE_pos M c w.length
  have hzN := nZ_le_NE M c w.length
  have hNB := NE_le_Bd M c w.length
  have h21 : τ.reg (R 21) < nZ M := by rw [hD.r21]; exact eZ_lt M _
  have h21' : τ.reg (R 21) = eZ M (τ.reg (R 14)) := by rw [hD.r21, hD.r14]
  have h14 : τ.reg (R 14) < NE M c w.length := by rw [hD.r14]; exact chainA_lt M c _ g
  have h15 : τ.reg (R 15) < NE M c w.length := by rw [hD.r15]; exact Nat.mod_lt _ hN
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
  have hI2 : Inv M c w σ g (τ1.setReg (R 25) 0) := hI1.setReg M c w le_rfl (by omega)
  split_ifs with hz
  · have r14 := e1' (R 14) (by rw [R_val (by omega)]; omega)
    have r15 := e1' (R 15) (by rw [R_val (by omega)]; omega)
    refine ach_ifB _ _ _ 30 _ Q (by simp [BE.RL, AE.RL]) (by simp [BE.ht, AE.ht])
      (by simp only [BE.Bnd, AE.Bnd]; rw [r14, r15]; omega) ?_ ?_
    · intro hb τ' hag
      simp only [BE.eval, AE.eval, r14, r15] at hb
      refine h true ?_ τ' (hI2.agree M c w hag)
      simp only [finalK, true_iff]
      rw [← h21']; exact ⟨hb, hz⟩
    · intro hb τ' hag
      simp only [BE.eval, AE.eval, r14, r15] at hb
      refine h false ?_ τ' (hI2.agree M c w hag)
      simp only [finalK, Bool.false_eq_true, false_iff, not_and]
      exact fun h' => absurd h' hb
  · refine h false ?_ _ hI2
    simp only [finalK, Bool.false_eq_true, false_iff, not_and]
    rw [← h21']
    exact fun _ h1 h2 h3 => hz ⟨h1, h2, h3⟩

/-! ## The input layer -/

/-- The predicate `initK` as a boolean expression over the registers `16 … 18`. -/
def initBE : BE :=
  .and (.eq (rg 16) (cst 0)) (.or (.and (.eq (rg 17) (cst 0)) (.eq (rg 18) (cst (4 * qc M M.start))))
    (.eq (rg 18) (cst (4 * M.nQ + M.gc M.blank))))

/-! ## `∧`-gates -/

/-- The index `Vi n te ae` as an expression. -/
def ViE (te ae : AE) : AE :=
  .sub (.mul (.add (.add (.mul te (rg 2)) ae) (cst 1)) (rg 3)) (cst 1)

/-! ## The body -/

/-- The loop body: compute and output gate number `g`. -/
def body : Stmt 64 :=
  assignAll (decodeList M) ⨟
  ifB (.eq (rg 10) (cst 0))
    (ifB (.eq (rg 9) (.sub (rg 3) (cst 1)))
      (ifB (initBE M) (emitIn true) (emitIn false) 30) (emitIn false) 30)
    (ifB (.eq (rg 9) (cst 0)) (emitIn false)
      (ifB (.eq (rg 13) (cst 0))
        (emitAnd (ViE (.sub (rg 10) (cst 1)) (rg 14)) (ViE (.sub (rg 10) (cst 1)) (rg 15)))
        (ifB (.eq (rg 10) (.add (rg 1) (cst 1))) (finalPart M) (stepPart M) 30) 30) 30) 30

lemma updAll_of_not_mem : ∀ (l : List (ℕ × AE)) (ρ : Fin 64 → ℕ) (x : Fin 64),
    (∀ p ∈ l, x ≠ R p.1) → updAll l ρ x = ρ x
  | [], _, _, _ => rfl
  | (i, e) :: l, ρ, x, h => by
    simp only [updAll]
    rw [updAll_of_not_mem l _ x (fun p hp => h p (List.mem_cons_of_mem _ hp)),
      Function.update_of_ne (h _ List.mem_cons_self)]

theorem ach_body (σ : St 64) {g : ℕ} (hG : Glob M c w.length g σ.reg) (hg : g < Nb M c w.length) :
    Ach w (Bd M c w.length) (body M) σ (Post M c w σ g) := by
  have hN := NE_pos M c w.length
  have hS := Sb_pos M c w.length
  have hzN := nZ_le_NE M c w.length
  have hNB := NE_le_Bd M c w.length
  have hSN := NE_le_Sb M c w.length
  have hSB := Sb_le_Nb M c w.length
  have hnN := n_le_NE M c w.length
  have hTN := T_le_NE M c w.length
  have hgS : g / Sb M c w.length ≤ (Tb c w.length + 1) * NE M c w.length := by
    have : g / Sb M c w.length < (Tb c w.length + 1) * NE M c w.length + 1 :=
      (Nat.div_lt_iff_lt_mul hS).2 hg
    omega
  have ht : g / Sb M c w.length / NE M c w.length ≤ Tb c w.length + 1 :=
    Nat.div_le_of_le_mul (by rw [mul_comm]; exact hgS)
  have hrS : g % Sb M c w.length < Sb M c w.length := Nat.mod_lt _ hS
  refine ach_seq (ach_assignAll _ σ _ (decode_ok M c hG hg) ?_)
  intro τ ho _ hv
  obtain ⟨v0, v1, v2, v3, v5, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20,
    v21, v22, v23, v24⟩ := decode_vals M c hG
  have r : ∀ i, i < 30 → τ.reg (R i) = updAll (decodeList M) σ.reg (R i) :=
    fun i hi => hv _ (by rw [R_val (by omega)]; omega)
  have hDV : DV M c w g τ := ⟨by rw [r 0 (by omega), v0], by rw [r 1 (by omega), v1],
    by rw [r 2 (by omega), v2], by rw [r 3 (by omega), v3], by rw [r 5 (by omega), v5],
    by rw [r 9 (by omega), v9], by rw [r 10 (by omega), v10], by rw [r 11 (by omega), v11],
    by rw [r 13 (by omega), v13], by rw [r 14 (by omega), v14], by rw [r 15 (by omega), v15],
    by rw [r 16 (by omega), v16], by rw [r 17 (by omega), v17], by rw [r 18 (by omega), v18],
    by rw [r 19 (by omega), v19], by rw [r 20 (by omega), v20], by rw [r 21 (by omega), v21],
    by rw [r 22 (by omega), v22], by rw [r 23 (by omega), v23], by rw [r 24 (by omega), v24]⟩
  have hmem : ∀ p ∈ decodeList M, 8 ≤ p.1 ∧ p.1 < 64 := by simp [decodeList]
  have hlow : ∀ x : Fin 64, x.val < 8 → τ.reg x = σ.reg x := fun x hx => by
    rw [hv x (by omega)]
    exact updAll_of_not_mem _ _ _ (fun p hp => ne_R hx (hmem p hp).1 (hmem p hp).2)
  have hI : Inv M c w σ g τ := ⟨ho, hlow, hDV⟩
  have hBd : Bd M c w.length = Nb M c w.length := rfl
  have hB1 : 1 ≤ Bd M c w.length := by omega
  have hq := qc_lt M M.start
  have hgb := M.gc_lt M.blank
  have hnz : nZ M = 4 * M.nQ + M.nG := rfl
  have he1 : g / Sb M c w.length % NE M c w.length < NE M c w.length := Nat.mod_lt _ hN
  have he2 := chainA_lt M c w.length g
  have he3 : (g % Sb M c w.length - 1) / 2 % NE M c w.length < NE M c w.length :=
    Nat.mod_lt _ hN
  refine ach_ifB _ _ _ 30 τ _ (by simp [BE.RL, AE.RL]) (by simp [BE.ht, AE.ht])
    (by simp only [BE.Bnd, AE.Bnd]; rw [hDV.r10]; omega) ?_ ?_
  · intro h0 τ1 hag1
    have hI1 := hI.agree M c w hag1
    have D1 := hI1.2.2
    simp only [BE.eval, AE.eval, hDV.r10] at h0
    refine ach_ifB _ _ _ 30 τ1 _ (by simp [BE.RL, AE.RL]) (by simp [BE.ht, AE.ht])
      (by simp only [BE.Bnd, AE.Bnd]; rw [D1.r9, D1.r3]; omega) ?_ ?_
    · intro h1 τ2 hag2
      have hI2 := hI1.agree M c w hag2
      have D2 := hI2.2.2
      simp only [BE.eval, AE.eval, D1.r9, D1.r3] at h1
      have hP := eP_lt M c he1
      have hJ := eJ_lt M c w.length (g / Sb M c w.length % NE M c w.length)
      have hZ := eZ_lt M (g / Sb M c w.length % NE M c w.length)
      have hev : (initBE M).eval τ2.reg ↔ initK M c w.length (g / Sb M c w.length % NE M c w.length) := by
        simp only [initBE, BE.eval, AE.eval, initK, D2.r16, D2.r17, D2.r18]
      refine ach_ifB _ _ _ 30 τ2 _ (by simp [initBE, BE.RL, AE.RL]) (by simp [initBE, BE.ht, AE.ht])
        ?_ ?_ ?_
      · simp only [initBE, BE.Bnd, AE.Bnd]; rw [D2.r16, D2.r17, D2.r18]; omega
      · intro h2 τ3 hag3
        refine ach_emitIn' M c w true (hI2.agree M c w hag3) ?_
        simp [gateFn, h0, h1, hev.1 h2]
      · intro h2 τ3 hag3
        refine ach_emitIn' M c w false (hI2.agree M c w hag3) ?_
        have h2' : ¬ initK M c w.length (g / Sb M c w.length % NE M c w.length) :=
          fun h => h2 (hev.2 h)
        simp [gateFn, h0, h1, h2']
    · intro h1 τ2 hag2
      refine ach_emitIn' M c w false (hI1.agree M c w hag2) ?_
      simp only [BE.eval, AE.eval, D1.r9, D1.r3] at h1
      simp [gateFn, h0, h1]
  · intro h0 τ1 hag1
    have hI1 := hI.agree M c w hag1
    have D1 := hI1.2.2
    simp only [BE.eval, AE.eval, hDV.r10] at h0
    refine ach_ifB _ _ _ 30 τ1 _ (by simp [BE.RL, AE.RL]) (by simp [BE.ht, AE.ht])
      (by simp only [BE.Bnd, AE.Bnd]; rw [D1.r9]; omega) ?_ ?_
    · intro h1 τ2 hag2
      refine ach_emitIn' M c w false (hI1.agree M c w hag2) ?_
      simp only [BE.eval, AE.eval, D1.r9] at h1
      simp [gateFn, h0, h1]
    intro h1 τ2 hag2
    have hI2 := hI1.agree M c w hag2
    have D2 := hI2.2.2
    simp only [BE.eval, AE.eval, D1.r9] at h1
    refine ach_ifB _ _ _ 30 τ2 _ (by simp [BE.RL, AE.RL]) (by simp [BE.ht, AE.ht])
      (by simp only [BE.Bnd, AE.Bnd]; rw [D2.r13]; omega) ?_ ?_
    · intro h2 τ3 hag3
      have hI3 := hI2.agree M c w hag3
      have D3 := hI3.2.2
      simp only [BE.eval, AE.eval, D2.r13] at h2
      have hXa := layer_idx M c w.length (t := g / Sb M c w.length / NE M c w.length - 1)
        (by omega) he2
      have hXb := layer_idx M c w.length (t := g / Sb M c w.length / NE M c w.length - 1)
        (by omega) he3
      have hXa' := Nat.le_mul_of_pos_right ((g / Sb M c w.length / NE M c w.length - 1) *
        NE M c w.length + (g % Sb M c w.length - 1) / 2 / NE M c w.length + 1) hS
      have hXb' := Nat.le_mul_of_pos_right ((g / Sb M c w.length / NE M c w.length - 1) *
        NE M c w.length + (g % Sb M c w.length - 1) / 2 % NE M c w.length + 1) hS
      refine ach_emitAnd _ _ τ3 _ (by simp [ViE, AE.RL]) (by simp [ViE, AE.RL])
        (by simp [ViE, AE.ht]) (by simp [ViE, AE.ht]) ?_ ?_ hB1 ?_
      · simp only [ViE, AE.Bnd, AE.eval]; rw [D3.r10, D3.r2, D3.r14, D3.r3]
        repeat' apply And.intro
        all_goals omega
      · simp only [ViE, AE.Bnd, AE.eval]; rw [D3.r10, D3.r2, D3.r15, D3.r3]
        repeat' apply And.intro
        all_goals omega
      · intro τ' hE
        refine post_of_ext M c w hI3 hE ?_
        simp [ViE, AE.eval, D3.r10, D3.r2, D3.r14, D3.r15, D3.r3, gateFn, h0, h1, h2, Vi]
    · intro h2 τ3 hag3
      have hI3 := hI2.agree M c w hag3
      have D3 := hI3.2.2
      simp only [BE.eval, AE.eval, D2.r13] at h2
      refine ach_ifB _ _ _ 30 τ3 _ (by simp [BE.RL, AE.RL]) (by simp [BE.ht, AE.ht])
        (by simp only [BE.Bnd, AE.Bnd, AE.eval]; rw [D3.r10, D3.r1]; omega) ?_ ?_
      · intro h3 τ4 hag4
        have hI4 := hI3.agree M c w hag4
        simp only [BE.eval, AE.eval, D3.r10, D3.r1] at h3
        refine ach_finalPart M c w hI4 _ ?_
        intro b hb τ5 hI5
        refine ach_emitTF M c w b hI5 hg.le ?_
        rw [hI4.2.2.r14, hI4.2.2.r15] at hb
        have hK : KK M c w (g / Sb M c w.length / NE M c w.length)
            (g / Sb M c w.length % NE M c w.length) ((g % Sb M c w.length - 1) / 2 / NE M c w.length)
            ((g % Sb M c w.length - 1) / 2 % NE M c w.length) ↔ b = true := by
          rw [hb]; simp [KK, h3]
        unfold gateFn
        rw [if_neg h0, if_neg h1, if_neg h2]
        congr 1
        by_cases hb' : b = true <;> simp [hb', hK]
      · intro h3 τ4 hag4
        have hI4 := hI3.agree M c w hag4
        have D4 := hI4.2.2
        simp only [BE.eval, AE.eval, D3.r10, D3.r1] at h3
        refine ach_stepPart M c w hI4 _ ?_
        intro b hb τ5 hI5 _
        refine ach_emitTF M c w b hI5 hg.le ?_
        rw [D4.r16, D4.r17, D4.r18, D4.r19, D4.r20, D4.r21, D4.r22, D4.r23, D4.r24] at hb
        have hK : KK M c w (g / Sb M c w.length / NE M c w.length)
            (g / Sb M c w.length % NE M c w.length) ((g % Sb M c w.length - 1) / 2 / NE M c w.length)
            ((g % Sb M c w.length - 1) / 2 % NE M c w.length) ↔ b = true := by
          rw [hb]; simp [KK, h3]
        unfold gateFn
        rw [if_neg h0, if_neg h1, if_neg h2]
        congr 1
        by_cases hb' : b = true <;> simp [hb', hK]

end

end PHardness

end PathChecking
