module

public import RequestProject.CTLStarP.Prog.Lab

/-!
# Program fragments: label lookup and navigation in the tree
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT

variable {w : Word} {B : ℕ} {ts : List Tok}

/-- Stop with result `e`. -/
def stopE (R G : Fin 48) (e : Ex M) : Hs M := .set R e ;; .set G (.const 0)

lemma hach_stopE (R G : Fin 48) (e : Ex M) (hRG : R ≠ G) (he : e.Bnd w B σ) (cl : List (Fin 48))
    (hR : R ∈ cl) (hG : G ∈ cl) :
    HAch w B (stopE R G e) σ (fun σ' => Frame cl σ σ' ∧ σ'.v G = 0 ∧ σ'.v R = e.ev w σ) := by
  refine hach_seq (hach_set he (hach_set (by simp) ⟨?_, ?_, ?_⟩))
  · exact ((Frame.refl _ _).set hR _).set hG _
  · simp
  · simp [hRG]

/-! ## Label lookup -/

notation "vHP" => (14 : Fin 48)
notation "vHQ" => (15 : Fin 48)
notation "vHR" => (16 : Fin 48)
notation "vHG" => (17 : Fin 48)
notation "vHT" => (18 : Fin 48)

/-- Variables clobbered by `labHasP`. -/
def clH : List (Fin 48) := cl 15 ++ [vHR, vHG, vHT]

/-- `HR := labHas HP HQ`. -/
def labHasP : Hs M :=
  .set vHG (.const 1) ;;
  .loop (.var vHG)
    (.ite (Ex.lt (.var vHP) (.var vN))
      (.ite (Ex.eq (.tok (.var vHP)) (.const 4)) (stopP vHR vHG 0)
        (cmpVP vHP vHQ true ;; .set vHT (.var vCA) ;; cmpVP vHQ vHP true ;;
          .ite (Ex.band (.var vHT) (.var vCA)) (stopP vHR vHG 1)
            (numEndP (.var vHP) ;; .set vHP (.var vSR))))
      (stopP vHR vHG 0))

theorem hach_labHasP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hp : σ.v vHP ≤ ts.length + 1) (hq : σ.v vHQ ≤ ts.length + 1) :
    HAch w B labHasP σ (fun σ' =>
      σ'.v vHR = bv (labHas ts (σ.v vHP) (σ.v vHQ)) ∧ Frame clH σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.bn
  set n := ts.length
  refine hach_seq (hach_set (by simp; omega) ?_)
  refine (hach_goLoop (by omega) clH vHG vHP vHR (fun p => bv (labHas ts p (σ.v vHQ))) (n + 1) _ ?_
    (by simp) (by simp; omega)).mono ?_
  swap
  · rintro σ' ⟨h1, h2⟩
    refine ⟨by simpa using h1, ((Frame.refl _ _).set (by decide) _).trans h2⟩
  intro σ1 hf hG hP
  have hN1 : σ1.v vN = n := by rw [hf.1 _ (by decide)]; simpa using hN
  have hQ1 : σ1.v vHQ = σ.v vHQ := by rw [hf.1 _ (by decide)]; simp
  by_cases hlt : σ1.v vHP < n
  · refine hach_iteT (by bnd_tac <;> (try simp) <;> omega) (by simp [hN1, hlt]) ?_
    by_cases h4 : tc ts (σ1.v vHP) = 4
    · refine hach_iteT (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, h4]) ?_
      refine (hach_stopP vHR vHG 0 (by decide) (by omega) clH (by decide) (by decide) σ1).mono ?_
      rintro σ2 ⟨hf2, hg2, hr2⟩
      refine ⟨hf2, Or.inl ⟨hg2, ?_⟩⟩
      rw [hr2]; try dsimp only; rw [labHas_eq, if_neg (by omega), if_pos h4]; rfl
    refine hach_iteF (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, h4]) ?_
    refine hach_seq ((hach_cmpVP hc σ1 vHP vHQ (by decide) true hP
      (by omega)).mono ?_)
    rintro σ2 ⟨hA2, hf2⟩
    refine hach_seq (hach_set (by simp [hA2]; have := bv_le (cmpScan ts (σ1.v vHP) (σ1.v vHQ) true); omega) ?_)
    refine hach_seq ((hach_cmpVP hc _ vHQ vHP (by decide) true
      (by simp [hf2.1 vHQ (by decide)]; omega)
      (by simp [hf2.1 vHP (by decide)]; omega)).mono ?_)
    rintro σ3 ⟨hA3, hf3⟩
    simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_false,
      hf2.1 vHQ (by decide), hf2.1 vHP (by decide)] at hA3
    have e3N : σ3.v vN = n := by
      rw [hf3.1 _ (by decide)]; simp [hf2.1 vN (by decide), hN1]
    have e3P : σ3.v vHP = σ1.v vHP := by
      rw [hf3.1 _ (by decide)]; simp [hf2.1 vHP (by decide)]
    have e3T : σ3.v vHT = bv (cmpScan ts (σ1.v vHP) (σ1.v vHQ) true) := by
      rw [hf3.1 _ (by decide)]; simp [hA2]
    have hfr : Frame clH σ1 σ3 :=
      ((hf2.mono (by decide)).set (by decide) _).trans (hf3.mono (by decide))
    have hT1 := bv_le (cmpScan ts (σ1.v vHP) (σ1.v vHQ) true)
    have hA1 := bv_le (cmpScan ts (σ1.v vHQ) (σ1.v vHP) true)
    refine hach_ite (by bnd_tac <;> (try simp [hA3, e3T]) <;> omega) ?_
    simp only [ne_eq, ev_band', ev_var, hA3, e3T, bv_mul_bv, bv_eq_zero]
    split_ifs with hcond
    · refine hach_seq ((hach_numEndP hc σ3 e3N _ (by simp; omega) (by simp; omega)).mono ?_)
      rintro σ4 ⟨hE, hf4⟩
      simp only [ev_var, e3P] at hE
      have hEg : σ1.v vHP < numEnd ts (σ1.v vHP) := lt_scan _ _ _ hlt
      have hEl : numEnd ts (σ1.v vHP) ≤ n + 1 := by
        have := scan_le (ts := ts) upN downN (σ1.v vHP) 1; simp only [numEnd]; omega
      refine hach_set (by simp; omega) ⟨(hfr.trans (hf4.mono (by decide))).set (by decide) _,
        Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
      · simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_false]
        rw [hf4.1 _ (by decide), hf3.1 _ (by decide)]
        simp [hf2.1 vHG (by decide), hG]
      · simp [hE]; omega
      · simp [hE]; omega
      · simp only [HSt.set_v, Function.update_self, ev_var, hE, bv_inj]
        rw [labHas_eq (p := σ1.v vHP), if_neg (by omega), if_neg h4, numEq, numLe, numLe, ← hQ1,
          hcond, Bool.false_or]
    · refine (hach_stopP vHR vHG 1 (by decide) (by omega) clH (by decide) (by decide) σ3).mono ?_
      rintro σ4 ⟨hf4, hg4, hr4⟩
      refine ⟨hfr.trans hf4, Or.inl ⟨hg4, ?_⟩⟩
      rw [hr4]
      rw [labHas_eq (p := σ1.v vHP), if_neg (by omega), if_neg h4, numEq, numLe, numLe, ← hQ1]
      simp only [Bool.not_eq_false] at hcond
      simp [hcond]
  · refine hach_iteF (by bnd_tac <;> (try simp) <;> omega) (by simp [hN1, hlt]) ?_
    refine (hach_stopP vHR vHG 0 (by decide) (by omega) clH (by decide) (by decide) σ1).mono ?_
    rintro σ2 ⟨hf2, hg2, hr2⟩
    refine ⟨hf2, Or.inl ⟨hg2, ?_⟩⟩
    rw [hr2]; try dsimp only; rw [labHas_eq, if_pos (by omega)]; rfl

/-! ## Navigation -/

notation "vWC" => (19 : Fin 48)
notation "vWL" => (20 : Fin 48)
notation "vWG" => (21 : Fin 48)
notation "vWR" => (22 : Fin 48)

/-- Variables clobbered by `ctwP`. -/
def clW : List (Fin 48) := cl 20 ++ [vWG, vWR]

/-- `WR := ctw WC WL`. -/
def ctwP : Hs M :=
  .set vWG (.const 1) ;;
  .loop (.var vWG)
    (.ite (Ex.lt (.var vWC) (.var vN))
      (tendP (.var vWC) ;;
        .ite (Ex.band (Ex.bnot (Ex.lt (.var vWL) (.var vSR))) (Ex.bnot (Ex.eq (.tok (.var vSR)) (.const 4))))
          (.set vWC (.var vSR)) (stopE vWR vWG (.var vWC)))
      (stopE vWR vWG (.var vWC)))

theorem hach_ctwP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hp : σ.v vWC ≤ ts.length + 1) (hl : σ.v vWL ≤ ts.length) :
    HAch w B ctwP σ (fun σ' => σ'.v vWR = ctw ts (σ.v vWC) (σ.v vWL) ∧ Frame clW σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.bn
  set n := ts.length
  refine hach_seq (hach_set (by simp; omega) ?_)
  refine (hach_goLoop (by omega) clW vWG vWC vWR (fun p => ctw ts p (σ.v vWL)) (n + 1) _ ?_
    (by simp) (by simp; omega)).mono ?_
  swap
  · rintro σ' ⟨h1, h2⟩
    refine ⟨by simpa using h1, ((Frame.refl _ _).set (by decide) _).trans h2⟩
  intro σ1 hf hG hP
  have hN1 : σ1.v vN = n := by rw [hf.1 _ (by decide)]; simpa using hN
  have hL1 : σ1.v vWL = σ.v vWL := by rw [hf.1 _ (by decide)]; simp
  by_cases hlt : σ1.v vWC < n
  · refine hach_iteT (by bnd_tac <;> (try simp) <;> omega) (by simp [hN1, hlt]) ?_
    refine hach_seq ((hach_tendP hc σ1 hN1 _ (by simp; omega) (by simp; omega)).mono ?_)
    rintro σ2 ⟨hE, hf2⟩
    simp only [ev_var] at hE
    have hEg : σ1.v vWC < tend ts (σ1.v vWC) := tend_gt ts (by omega)
    have hEl : tend ts (σ1.v vWC) ≤ n + 1 := by
      have := scan_le (ts := ts) upT downT (σ1.v vWC) 0; simp only [tend]; omega
    have e2L : σ2.v vWL = σ.v vWL := by rw [hf2.1 _ (by decide), hL1]
    have e2C : σ2.v vWC = σ1.v vWC := hf2.1 _ (by decide)
    refine hach_ite (by bnd_tac <;> (try simp [hE, e2L]) <;> omega) ?_
    simp only [ne_eq, ev_band', ev_bnot', ev_lt, ev_eq, ev_tok, ev_var, ev_const, hc.tok, hE, e2L,
      one_sub_bv, bv_mul_bv, bv_eq_zero]
    split_ifs with hcond
    · refine (hach_stopE vWR vWG (.var vWC) (by decide) (by simp; omega) clW (by decide)
        (by decide)).mono ?_
      rintro σ3 ⟨hf3, hg3, hr3⟩
      refine ⟨(hf2.mono (by decide)).trans hf3, Or.inl ⟨hg3, ?_⟩⟩
      rw [hr3]; try dsimp only
      rw [ev_var, e2C, ctw_eq (c := σ1.v vWC), if_neg (by omega), if_neg]
      simp only [Bool.and_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
        decide_eq_true_eq] at hcond
      omega
    · simp only [Bool.not_eq_false, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, not_lt] at hcond
      refine hach_set (by simp; omega) ⟨(hf2.mono (by decide)).set (by decide) _,
        Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
      · simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_false]
        rw [hf2.1 _ (by decide), hG]
      · simp [hE]; omega
      · simp [hE]; omega
      · simp only [HSt.set_v, Function.update_self, ev_var, hE]
        rw [ctw_eq (c := σ1.v vWC), if_neg (by omega), if_pos ⟨hcond.1, hcond.2⟩]
  · refine hach_iteF (by bnd_tac <;> (try simp) <;> omega) (by simp [hN1, hlt]) ?_
    refine (hach_stopE vWR vWG (.var vWC) (by decide) (by simp; omega) clW (by decide)
      (by decide)).mono ?_
    rintro σ2 ⟨hf2, hg2, hr2⟩
    refine ⟨hf2, Or.inl ⟨hg2, ?_⟩⟩
    rw [hr2]; try dsimp only; rw [ev_var, ctw_eq, if_pos (by omega)]

lemma ctw_le_aux (ℓ : ℕ) : ∀ m c, ts.length + 1 - c = m → c ≤ ts.length + 1 →
    ctw ts c ℓ ≤ ts.length + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hm hc
    rw [ctw_eq]
    split_ifs with h1 h2
    · exact hc
    · have hg := tend_gt ts h1
      have hl := scan_le (ts := ts) upT downT c 0
      simp only [tend] at hg ⊢
      exact ih _ (by omega) _ rfl (by omega)
    · exact hc

lemma ctw_le_succ (c ℓ : ℕ) (h : c ≤ ts.length + 1) : ctw ts c ℓ ≤ ts.length + 1 :=
  ctw_le_aux ℓ _ c rfl h

notation "vXL" => (23 : Fin 48)
notation "vXU" => (24 : Fin 48)
notation "vXR" => (25 : Fin 48)

/-- `XR := nxt XL XU`. -/
def nxtP : Hs M :=
  tendP (.var vXU + .const 1) ;;
  .ite (Ex.eq (.tok (.var vSR)) (.const 4)) (.set vXR (.var vXU))
    (.set vWC (.var vSR) ;; .set vWL (.var vXL) ;; ctwP ;; .set vXR (.var vWR))

theorem hach_nxtP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hu : σ.v vXU ≤ ts.length) (hl : σ.v vXL ≤ ts.length) :
    HAch w B nxtP σ (fun σ' => σ'.v vXR = nxt ts (σ.v vXL) (σ.v vXU) ∧ Frame (cl 26) σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.bn
  set n := ts.length
  refine hach_seq ((hach_tendP hc σ hN _ (by bnd_tac <;> simp <;> omega) (by simp; omega)).mono ?_)
  rintro σ2 ⟨hE, hf2⟩
  simp only [ev_add, ev_var, ev_const] at hE
  have hEl : tend ts (σ.v vXU + 1) ≤ n + 1 := by
    have := scan_le (ts := ts) upT downT (σ.v vXU + 1) 0; simp only [tend]; omega
  have e2U : σ2.v vXU = σ.v vXU := hf2.1 _ (by decide)
  have e2L : σ2.v vXL = σ.v vXL := hf2.1 _ (by decide)
  have e2N : σ2.v vN = n := by rw [hf2.1 _ (by decide), hN]
  refine hach_ite (by bnd_tac <;> (try simp) <;> omega) ?_
  simp only [ne_eq, ev_eq, ev_tok, ev_var, ev_const, hc.tok, hE, bv_eq_zero,
    decide_eq_false_iff_not, not_not]
  split_ifs with h4
  · refine hach_set (by simp; omega) ⟨?_, (Frame.cl_mono hf2 (by omega)).set (by decide) _⟩
    simp only [HSt.set_v, Function.update_self, ev_var, e2U, nxt, isLeaf, h4]; rfl
  · refine hach_seq (hach_set (by simp; omega) (hach_seq (hach_set (by simp; omega) ?_)))
    refine hach_seq ((hach_ctwP hc _
      (by simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_false, e2N]; rfl)
      (by simp [hE]; omega)
      (by simp [e2L]; omega)).mono ?_)
    rintro σ3 ⟨hR, hf3⟩
    have hRl := ctw_le_succ (ts := ts) (tend ts (σ.v vXU + 1)) (σ.v vXL) hEl
    simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_true, if_false, ev_var, hE,
      e2L] at hR
    refine hach_set (by simp [hR]; omega) ⟨?_, ?_⟩
    · simp only [HSt.set_v, Function.update_self, ev_var, hR]
      simp [nxt, isLeaf, h4]
    · exact ((((Frame.cl_mono hf2 (by omega)).set (by decide) _).set (by decide) _).trans
        (hf3.mono (by decide))).set (by decide) _

end CTLP

end PathChecking
