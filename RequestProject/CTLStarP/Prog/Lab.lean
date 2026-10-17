module

public import RequestProject.CTLStarP.Prog.Num

/-!
# Program fragments: wrappers, loops with a stop flag, labels
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT

/-- The variables `1, …, k-1`. -/
def cl (k : ℕ) : List (Fin 48) := (List.finRange 48).filter (fun i => 0 < i.val ∧ i.val < k)

lemma cl_mono {k k' : ℕ} (h : k ≤ k') : cl k ⊆ cl k' := by
  intro i hi; simp only [cl, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at *
  omega

lemma Frame.cl_mono {k k' : ℕ} {σ σ' : HSt 48} (hf : Frame (cl k) σ σ') (h : k ≤ k') :
    Frame (cl k') σ σ' := hf.mono (CTLP.cl_mono h)

/-- A loop controlled by a stop flag `G`: each round either stops, setting `R := f P`, or moves
`P` forward, keeping `f P`. -/
theorem hach_goLoop {m : ℕ} {w : Word} {B : ℕ} (hB : 1 ≤ B) {body : Hs m} (cl : List (Fin m))
    (G P R : Fin m) (f : ℕ → ℕ) (K : ℕ) (σ : HSt m)
    (hbody : ∀ σ1, Frame cl σ σ1 → σ1.v G = 1 → σ1.v P ≤ K →
      HAch w B body σ1 (fun σ2 => Frame cl σ1 σ2 ∧ ((σ2.v G = 0 ∧ σ2.v R = f (σ1.v P)) ∨
        (σ2.v G = 1 ∧ σ1.v P < σ2.v P ∧ σ2.v P ≤ K ∧ f (σ1.v P) = f (σ2.v P)))))
    (hG : σ.v G = 1) (hP : σ.v P ≤ K) :
    HAch w B (.loop (.var G) body) σ (fun σ' => σ'.v R = f (σ.v P) ∧ Frame cl σ σ') := by
  let inv : HSt m → Prop := fun σ1 => Frame cl σ σ1 ∧
    ((σ1.v G = 1 ∧ σ1.v P ≤ K ∧ f (σ.v P) = f (σ1.v P)) ∨ (σ1.v G = 0 ∧ σ1.v R = f (σ.v P)))
  refine hach_while inv (fun σ1 => σ1.v G * (K + 2 - σ1.v P)) _ ?_ ?_ ?_ σ
    ⟨Frame.refl _ _, Or.inl ⟨hG, hP, rfl⟩⟩
  · rintro σ1 ⟨-, h | h⟩ <;> simp [h.1, hB]
  · rintro σ1 ⟨hf, h | h⟩ hc
    · simp [h.1] at hc
    · exact ⟨h.2, hf⟩
  · rintro σ1 ⟨hf, h | h⟩ hc
    · refine (hbody σ1 hf h.1 h.2.1).mono ?_
      rintro σ2 ⟨hf2, h2 | h2⟩
      · refine ⟨⟨hf.trans hf2, Or.inr ⟨h2.1, by rw [h2.2, h.2.2]⟩⟩, ?_⟩
        show σ2.v G * _ < σ1.v G * _
        rw [h2.1, h.1]; have := h.2.1; omega
      · refine ⟨⟨hf.trans hf2, Or.inl ⟨h2.1, h2.2.2.1, by rw [h.2.2, h2.2.2.2]⟩⟩, ?_⟩
        show σ2.v G * _ < σ1.v G * _
        rw [h2.1, h.1]; have := h.2.1; have := h2.2.1; omega
    · simp [h.1] at hc

variable {w : Word} {B : ℕ} {ts : List Tok}

/-! ## Wrappers -/

/-- `SR := numEnd e`. -/
def numEndP (e : Ex M) : Hs M := .set vSP e ;; .set vSC (.const 1) ;; scanP [] [2]
/-- `SR := tend e`. -/
def tendP (e : Ex M) : Hs M := .set vSP e ;; .set vSC (.const 0) ;; scanP [3] [4]
/-- `SR := fend e`. -/
def fendP (e : Ex M) : Hs M := .set vSP e ;; .set vSC (.const 1) ;; scanP [8, 10] [2, 6]
/-- `DR := numOK e`. -/
def numOKP (e : Ex M) : Hs M := .set vDP e ;; .set vDO (.const 1) ;; digP
/-- `CA := cmpScan a b acc`. -/
def cmpVP (a b : Fin 48) (acc : Bool) : Hs M :=
  .set vCP (.var a) ;; .set vCQ (.var b) ;; .set vCA (.const (bv acc)) ;; cmpP

lemma hach_scanW (hc : Ctx ts w B) (U D : List ℕ) (hU : ∀ c ∈ U, c ≤ 30)
    (hD : ∀ c ∈ D, c ≤ 30) (c0 : ℕ) (hc0 : c0 ≤ 1) (σ : HSt M) (hN : σ.v vN = ts.length)
    (e : Ex M) (he : e.Bnd w B σ) (hle : e.ev w σ ≤ ts.length + 1) :
    HAch w B (.set vSP e ;; .set vSC (.const c0) ;; scanP U D) σ (fun σ' =>
      σ'.v vSR = scan ts (lmem U) (lmem D) (e.ev w σ) c0 ∧ Frame (cl 4) σ σ') := by
  have hB64 := hc.b64
  refine hach_seq (hach_set he (hach_seq (hach_set (by simp; omega) ?_)))
  refine (hach_scanP hc U D hU hD _ (by simp [hN])
    (by simp; omega) (by simp; omega)).mono ?_
  rintro σ' ⟨h1, h2⟩
  refine ⟨by simpa [Function.update_apply] using h1, ?_⟩
  exact (((Frame.refl _ σ).set (show vSP ∈ cl 4 by decide) _).set (show vSC ∈ cl 4 by decide) _).trans
    (h2.mono (by decide))

lemma hach_numEndP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (e : Ex M) (he : e.Bnd w B σ) (hle : e.ev w σ ≤ ts.length + 1) :
    HAch w B (numEndP e) σ (fun σ' => σ'.v vSR = numEnd ts (e.ev w σ) ∧ Frame (cl 4) σ σ') := by
  have := hach_scanW hc [] [2] (by simp) (by simp) 1 le_rfl σ hN e he hle
  rwa [← upN_eq, ← downN_eq] at this

lemma hach_tendP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (e : Ex M) (he : e.Bnd w B σ) (hle : e.ev w σ ≤ ts.length + 1) :
    HAch w B (tendP e) σ (fun σ' => σ'.v vSR = tend ts (e.ev w σ) ∧ Frame (cl 4) σ σ') := by
  have := hach_scanW hc [3] [4] (by simp) (by simp) 0 (by omega) σ hN e he hle
  rwa [← upT_eq, ← downT_eq] at this

lemma hach_fendP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (e : Ex M) (he : e.Bnd w B σ) (hle : e.ev w σ ≤ ts.length + 1) :
    HAch w B (fendP e) σ (fun σ' => σ'.v vSR = fend ts (e.ev w σ) ∧ Frame (cl 4) σ σ') := by
  have := hach_scanW hc [8, 10] [2, 6] (by simp) (by simp) 1 le_rfl σ hN e he hle
  rwa [← upF_eq, ← downF_eq] at this

lemma hach_numOKP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (e : Ex M) (he : e.Bnd w B σ) (hle : e.ev w σ ≤ ts.length + 1) :
    HAch w B (numOKP e) σ (fun σ' => σ'.v vDR = bv (numOK ts (e.ev w σ)) ∧ Frame (cl 7) σ σ') := by
  have hB64 := hc.b64
  refine hach_seq (hach_set he (hach_seq (hach_set (by simp; omega) ?_)))
  refine (hach_digP hc _ (by simp [hN])
    (by simp; omega) true (by simp)).mono ?_
  rintro σ' ⟨h1, h2⟩
  refine ⟨by simpa [Function.update_apply, numOK] using h1, ?_⟩
  exact (((Frame.refl _ σ).set (show vDP ∈ cl 7 by decide) _).set (show vDO ∈ cl 7 by decide) _).trans
    (h2.mono (by decide))

lemma hach_cmpVP (hc : Ctx ts w B) (σ : HSt M) (a b : Fin 48) (hb : b ∉ cl 10)
    (acc : Bool) (hav : σ.v a ≤ ts.length + 1) (hbv : σ.v b ≤ ts.length + 1) :
    HAch w B (cmpVP a b acc) σ (fun σ' =>
      σ'.v vCA = bv (cmpScan ts (σ.v a) (σ.v b) acc) ∧ Frame (cl 10) σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.bn
  have hb7 : b ≠ vCP := by rintro rfl; exact hb (by decide)
  refine hach_seq (hach_set (by simp; omega) (hach_seq (hach_set ?_ (hach_seq (hach_set ?_ ?_)))))
  · simp [hb7]; omega
  · have := bv_le acc; simp; omega
  refine (hach_cmpP hc _ (by simp [Function.update_apply]; omega)
    (by simp [hb7]; omega) acc (by simp [Function.update_apply])).mono ?_
  rintro σ' ⟨h1, h2⟩
  refine ⟨by simpa [Function.update_apply, hb7] using h1, ?_⟩
  exact ((((Frame.refl _ σ).set (show vCP ∈ cl 10 by decide) _).set
    (show vCQ ∈ cl 10 by decide) _).set (show vCA ∈ cl 10 by decide) _).trans (h2.mono (by decide))

/-! ## Labels -/

notation "vLQ" => (10 : Fin 48)
notation "vLR" => (11 : Fin 48)
notation "vLG" => (12 : Fin 48)
notation "vLE" => (13 : Fin 48)

/-- Stop with result `r`. -/
def stopP (R G : Fin 48) (r : ℕ) : Hs M := .set R (.const r) ;; .set G (.const 0)

lemma hach_stopP (R G : Fin 48) (r : ℕ) (hRG : R ≠ G) (hr : r ≤ B) (cl : List (Fin 48))
    (hR : R ∈ cl) (hG : G ∈ cl) (σ : HSt M) :
    HAch w B (stopP R G r) σ (fun σ' => Frame cl σ σ' ∧ σ'.v G = 0 ∧ σ'.v R = r) := by
  refine hach_seq (hach_set (by simpa using hr) (hach_set (by simp) ⟨?_, ?_, ?_⟩))
  · exact ((Frame.refl _ _).set hR _).set hG _
  · simp
  · simp [hRG]

/-- `LR := labSuf LQ` (clobbers variables `1 … 13`). -/
def labSufP : Hs M :=
  .set vLG (.const 1) ;;
  .loop (.var vLG)
    (.ite (Ex.lt (.var vLQ) (.var vN))
      (.ite (Ex.eq (.tok (.var vLQ)) (.const 4)) (stopP vLR vLG 1)
        (numEndP (.var vLQ) ;; .set vLE (.var vSR) ;; cmpVP vLQ vLE false ;; numOKP (.var vLQ) ;;
          .ite (Ex.band (.var vDR) (Ex.bor (Ex.eq (.tok (.var vLE)) (.const 4)) (.var vCA)))
            (.set vLQ (.var vLE)) (stopP vLR vLG 0)))
      (stopP vLR vLG 0))

theorem hach_labSufP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hq : σ.v vLQ ≤ ts.length + 1) :
    HAch w B labSufP σ (fun σ' => σ'.v vLR = bv (labSuf ts (σ.v vLQ)) ∧ Frame (cl 14) σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.bn
  set n := ts.length
  refine hach_seq (hach_set (by simp; omega) ?_)
  refine (hach_goLoop (by omega) (cl 14) vLG vLQ vLR (fun p => bv (labSuf ts p)) (n + 1) _ ?_
    (by simp) (by simp; omega)).mono ?_
  swap
  · rintro σ' ⟨h1, h2⟩
    refine ⟨by simpa using h1, ((Frame.refl _ _).set (by decide) _).trans h2⟩
  intro σ1 hf hG hP
  have hN1 : σ1.v vN = n := by rw [hf.1 _ (by decide)]; simpa using hN
  by_cases hlt : σ1.v vLQ < n
  · refine hach_iteT (by bnd_tac <;> (try simp) <;> omega) (by simp [hN1, hlt]) ?_
    by_cases h4 : tc ts (σ1.v vLQ) = 4
    · refine hach_iteT (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, h4]) ?_
      refine (hach_stopP vLR vLG 1 (by decide) (by omega) (cl 14) (by decide) (by decide) σ1).mono ?_
      rintro σ2 ⟨hf2, hg2, hr2⟩
      refine ⟨hf2, Or.inl ⟨hg2, ?_⟩⟩
      rw [hr2]; dsimp only; rw [labSuf_eq, if_neg (by omega), if_pos h4]; rfl
    refine hach_iteF (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, h4]) ?_
    refine hach_seq ((hach_numEndP hc σ1 hN1 _ (by simp; omega) (by simp; omega)).mono ?_)
    rintro σ2 ⟨hE, hf2⟩
    have e2N : σ2.v vN = n := by rw [hf2.1 _ (by decide), hN1]
    have e2Q : σ2.v vLQ = σ1.v vLQ := hf2.1 _ (by decide)
    have hEg : σ1.v vLQ < numEnd ts (σ1.v vLQ) := lt_scan _ _ _ hlt
    have hEl : numEnd ts (σ1.v vLQ) ≤ n + 1 := by
      have := scan_le (ts := ts) upN downN (σ1.v vLQ) 1; simp only [numEnd]; omega
    simp only [ev_var] at hE
    refine hach_seq (hach_set (by simp; omega) ?_)
    refine hach_seq ((hach_cmpVP hc _ vLQ vLE (by decide) false
      (by simp [e2Q]; omega)
      (by simp [hE]; omega)).mono ?_)
    rintro σ3 ⟨hCA, hf3⟩
    have e3N : σ3.v vN = n := by rw [hf3.1 _ (by decide)]; simpa [Function.update_apply] using e2N
    have e3Q : σ3.v vLQ = σ1.v vLQ := by
      rw [hf3.1 _ (by decide)]; simpa [Function.update_apply] using e2Q
    have e3E : σ3.v vLE = numEnd ts (σ1.v vLQ) := by
      rw [hf3.1 _ (by decide)]; simpa [Function.update_apply] using hE
    simp only [HSt.set_v, Function.update_apply, Fin.reduceEq, if_false, if_true, ev_var, e2Q, hE] at hCA
    refine hach_seq ((hach_numOKP hc σ3 e3N _ (by simp; omega) (by simp; omega)).mono ?_)
    rintro σ4 ⟨hDR, hf4⟩
    have e4Q : σ4.v vLQ = σ1.v vLQ := by rw [hf4.1 _ (by decide), e3Q]
    have e4E : σ4.v vLE = numEnd ts (σ1.v vLQ) := by rw [hf4.1 _ (by decide), e3E]
    have e4A : σ4.v vCA = bv (numLt ts (σ1.v vLQ) (numEnd ts (σ1.v vLQ))) := by
      rw [hf4.1 _ (by decide), hCA]; rfl
    simp only [ev_var, e3Q] at hDR
    have hfr : Frame (cl 14) σ1 σ4 :=
      (((Frame.cl_mono hf2 (by omega)).set (by decide) _).trans (Frame.cl_mono hf3 (by omega))).trans
        (Frame.cl_mono hf4 (by omega))
    have hDR1 := bv_le (numOK ts (σ1.v vLQ))
    have hCA1 := bv_le (numLt ts (σ1.v vLQ) (numEnd ts (σ1.v vLQ)))
    refine hach_ite (by bnd_tac <;> (try simp [hDR, e4A, e4E]) <;> omega) ?_
    simp only [ne_eq, ev_band', ev_var, ev_bor', ev_eq, ev_tok, ev_const, hc.tok, hDR, e4A, e4E,
      bv_mul_bv, pos_bv_add_bv, bv_eq_zero]
    split_ifs with hcond
    · refine (hach_stopP vLR vLG 0 (by decide) (by omega) (cl 14) (by decide) (by decide) σ4).mono ?_
      rintro σ5 ⟨hf5, hg5, hr5⟩
      refine ⟨hfr.trans hf5, Or.inl ⟨hg5, ?_⟩⟩
      rw [hr5]; rw [labSuf_eq (q := σ1.v vLQ), if_neg (by omega), if_neg h4]
      rw [eq_comm, bv_eq_zero]; revert hcond
      cases numOK ts (σ1.v vLQ) <;> cases numLt ts (σ1.v vLQ) (numEnd ts (σ1.v vLQ)) <;>
        by_cases h : tc ts (numEnd ts (σ1.v vLQ)) = 4 <;> simp [h]
    · refine hach_set (by simp; omega) ⟨hfr.set (by decide) _, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [HSt.set_v, Function.update_of_ne (by decide)]
        rw [hf4.1 _ (by decide), hf3.1 _ (by decide)]
        simp [hf2.1 _ (show vLG ∉ cl 4 by decide), hG]
      · simp [e4E]; omega
      · simp [e4E]; omega
      · simp only [HSt.set_v, Function.update_self, ev_var, e4E, bv_inj]
        simp only [Bool.not_eq_false] at hcond
        rw [labSuf_eq (q := σ1.v vLQ), if_neg (by omega), if_neg h4]
        simp at hcond ⊢; tauto
  · refine hach_iteF (by bnd_tac <;> (try simp) <;> omega) (by simp [hN1, hlt]) ?_
    refine (hach_stopP vLR vLG 0 (by decide) (by omega) (cl 14) (by decide) (by decide) σ1).mono ?_
    rintro σ2 ⟨hf2, hg2, hr2⟩
    refine ⟨hf2, Or.inl ⟨hg2, ?_⟩⟩
    rw [hr2]; dsimp only; rw [labSuf_eq, if_pos (by omega)]; rfl

end CTLP

end PathChecking
