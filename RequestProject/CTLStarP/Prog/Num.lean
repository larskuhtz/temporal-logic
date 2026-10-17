module

public import RequestProject.CTLStarP.Prog.Base

/-!
# Program fragments: numbers
-/

@[expose] public section

namespace PathChecking

namespace CTLP

open HL PT

attribute [simp] bv_le

notation "vDP" => (4 : Fin 48)
notation "vDO" => (5 : Fin 48)
notation "vDR" => (6 : Fin 48)
notation "vCP" => (7 : Fin 48)
notation "vCQ" => (8 : Fin 48)
notation "vCA" => (9 : Fin 48)

variable {w : Word} {B : ℕ} {ts : List Tok}

/-- `DR := digitsOK (DP, DO)`. -/
def digP : Hs M :=
  .loop (Ex.band (Ex.lt (.var vDP) (.var vN)) (Ex.inL (.tok (.var vDP)) [0, 1]))
    (.set vDO (Ex.eq (.tok (.var vDP)) (.const 1)) ;; .set vDP (.var vDP + .const 1)) ;;
  .set vDR (Ex.band (Ex.lt (.var vDP) (.var vN))
    (Ex.band (Ex.eq (.tok (.var vDP)) (.const 2)) (.var vDO)))

theorem hach_digP (hc : Ctx ts w B) (σ : HSt M) (hN : σ.v vN = ts.length)
    (hp : σ.v vDP ≤ ts.length + 1) (ok : Bool) (hok : σ.v vDO = bv ok) :
    HAch w B digP σ (fun σ' =>
      σ'.v vDR = bv (digitsOK ts (σ.v vDP) ok) ∧ Frame [vDP, vDO, vDR] σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.bn
  set n := ts.length
  let inv : HSt M → Prop := fun σ1 => Frame [vDP, vDO] σ σ1 ∧ σ1.v vDP ≤ n + 1 ∧
    ∃ ok1, σ1.v vDO = bv ok1 ∧ digitsOK ts (σ.v vDP) ok = digitsOK ts (σ1.v vDP) ok1
  refine hach_seq (hach_while inv (fun σ1 => n + 1 - σ1.v vDP) _ ?_ ?_ ?_ σ
    ⟨Frame.refl _ _, hp, ok, hok, rfl⟩)
  · rintro σ1 ⟨hf, h1, -⟩
    have hN1 : σ1.v vN = n := by rw [hf.1 vN (by decide), hN]
    bnd_tac <;> (try simp) <;> omega
  · rintro σ1 ⟨hf, h1, ok1, hok1, hd⟩ hcond
    have hN1 : σ1.v vN = n := by rw [hf.1 vN (by decide), hN]
    simp only [ev_band', ev_lt, ev_var, ev_inL', ev_tok, hc.tok, hN1, bv_mul_bv, bv_eq_zero,
      Bool.and_eq_false_iff, decide_eq_false_iff_not] at hcond
    have hok1' : σ1.v vDO ≤ 1 := by rw [hok1]; exact bv_le _
    refine hach_set (by bnd_tac <;> (try simp [hok1]) <;> omega) ⟨?_, (hf.mono (by simp)).set (by simp) _⟩
    simp only [HSt.set_v, Function.update_self, ev_band', ev_lt, ev_var, ev_eq, ev_tok, ev_const,
      hc.tok, hN1, hok1, bv_mul_bv, bv_inj]
    rw [hd, digitsOK_eq (p := σ1.v vDP)]
    by_cases hlt : σ1.v vDP < n
    · have hnd : tc ts (σ1.v vDP) ∉ [0, 1] := by
        rcases hcond with h | h
        · omega
        · exact h
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd
      rw [if_neg (by omega), if_neg hnd.1, if_neg hnd.2]
      by_cases h2 : tc ts (σ1.v vDP) = 2
      · simp [h2, hlt]
      · simp [h2, hlt]
    · rw [if_pos (by omega)]; simp [hlt]
  · rintro σ1 ⟨hf, h1, ok1, hok1, hd⟩ hcond
    have hN1 : σ1.v vN = n := by rw [hf.1 vN (by decide), hN]
    simp only [ne_eq, ev_band', ev_lt, ev_var, ev_inL', ev_tok, hc.tok, hN1, bv_mul_bv,
      bv_eq_zero, Bool.and_eq_false_iff, decide_eq_false_iff_not, not_or, not_not] at hcond
    obtain ⟨hlt, hdig⟩ := hcond
    refine hach_seq (hach_set (by bnd_tac <;> (try simp) <;> omega) (hach_set (by bnd_tac <;> (try simp) <;> omega)
      ⟨⟨(hf.set (by simp) _).set (by simp) _, by simp; omega,
        decide (tc ts (σ1.v vDP) = 1), by simp [hc.tok], ?_⟩, by simp; omega⟩))
    simp only [HSt.set_v, Function.update_self, ev_add, ev_var, ev_const]
    rw [Function.update_of_ne (by decide), hd, digitsOK_eq (p := σ1.v vDP), if_neg (by omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hdig
    rcases hdig with h0 | h0 <;> simp [h0]

/-- `CA := cmpScan (CP, CQ, CA)`. -/
def cmpP : Hs M :=
  .loop (Ex.bor (Ex.inL (.tok (.var vCP)) [0, 1]) (Ex.inL (.tok (.var vCQ)) [0, 1]))
    (.ite (Ex.inL (.tok (.var vCP)) [0, 1])
      (.ite (Ex.inL (.tok (.var vCQ)) [0, 1])
        (.ite (Ex.eq (Ex.eq (.tok (.var vCP)) (.const 1)) (Ex.eq (.tok (.var vCQ)) (.const 1)))
          .skip (.set vCA (Ex.eq (.tok (.var vCQ)) (.const 1))) ;;
          .set vCP (.var vCP + .const 1) ;; .set vCQ (.var vCQ + .const 1))
        (.ite (Ex.eq (.tok (.var vCP)) (.const 1)) (.set vCA (.const 0)) .skip ;;
          .set vCP (.var vCP + .const 1)))
      (.ite (Ex.eq (.tok (.var vCQ)) (.const 1)) (.set vCA (.const 1)) .skip ;;
        .set vCQ (.var vCQ + .const 1)))

lemma dig_eq (p : ℕ) : dig ts p =
    if tc ts p ∈ [0, 1] then some (decide (tc ts p = 1)) else none := by
  unfold dig
  by_cases h0 : tc ts p = 0
  · simp [h0]
  · by_cases h1 : tc ts p = 1 <;> simp [h0, h1]

lemma cmpScan_step (p q : ℕ) (acc : Bool) : cmpScan ts p q acc =
    if tc ts p ∈ [0, 1] then
      (if tc ts q ∈ [0, 1] then
        cmpScan ts (p + 1) (q + 1)
          (if decide (tc ts p = 1) = decide (tc ts q = 1) then acc else decide (tc ts q = 1))
      else cmpScan ts (p + 1) q (if decide (tc ts p = 1) then false else acc))
    else (if tc ts q ∈ [0, 1] then cmpScan ts p (q + 1) (if decide (tc ts q = 1) then true else acc)
      else acc) := by
  by_cases h1 : tc ts p ∈ [0, 1] <;> by_cases h2 : tc ts q ∈ [0, 1]
  · rw [if_pos h1, if_pos h2]
    exact cmpScan_ss (by rw [dig_eq, if_pos h1]) (by rw [dig_eq, if_pos h2])
  · rw [if_pos h1, if_neg h2]
    exact cmpScan_sn (by rw [dig_eq, if_pos h1]) (by rw [dig_eq, if_neg h2])
  · rw [if_neg h1, if_pos h2]
    exact cmpScan_ns (by rw [dig_eq, if_neg h1]) (by rw [dig_eq, if_pos h2])
  · rw [if_neg h1, if_neg h2]
    exact cmpScan_nn (by rw [dig_eq, if_neg h1]) (by rw [dig_eq, if_neg h2])

lemma lt_of_tc_mem {p : ℕ} (h : tc ts p ∈ [0, 1]) : p < ts.length := by
  apply lt_of_tc_ne; intro h'; rw [h'] at h; simp at h

theorem hach_cmpP (hc : Ctx ts w B) (σ : HSt M)
    (hp : σ.v vCP ≤ ts.length + 1) (hq : σ.v vCQ ≤ ts.length + 1) (acc : Bool)
    (hacc : σ.v vCA = bv acc) :
    HAch w B cmpP σ (fun σ' =>
      σ'.v vCA = bv (cmpScan ts (σ.v vCP) (σ.v vCQ) acc) ∧ Frame [vCP, vCQ, vCA] σ σ') := by
  have hB64 := hc.b64
  have hBn := hc.bn
  set n := ts.length
  let inv : HSt M → Prop := fun σ1 => Frame [vCP, vCQ, vCA] σ σ1 ∧ σ1.v vCP ≤ n + 1 ∧
    σ1.v vCQ ≤ n + 1 ∧ ∃ a, σ1.v vCA = bv a ∧
      cmpScan ts (σ.v vCP) (σ.v vCQ) acc = cmpScan ts (σ1.v vCP) (σ1.v vCQ) a
  refine hach_while inv (fun σ1 => 2 * n + 2 - σ1.v vCP - σ1.v vCQ) _ ?_ ?_ ?_ σ
    ⟨Frame.refl _ _, hp, hq, acc, hacc, rfl⟩
  · rintro σ1 ⟨-, h1, h2, -⟩
    bnd_tac <;> (try simp) <;> omega
  · rintro σ1 ⟨hf, h1, h2, a, ha, hd⟩ hcond
    simp only [ev_bor', ev_inL', ev_tok, ev_var, hc.tok, bv_eq_zero, decide_eq_false_iff_not,
      pos_bv_add_bv, Bool.or_eq_true, decide_eq_true_eq, not_or] at hcond
    refine ⟨?_, hf⟩
    rw [ha, hd, cmpScan_step, if_neg hcond.1, if_neg hcond.2]
  · rintro σ1 ⟨hf, h1, h2, a, ha, hd⟩ hcond
    have ha1 : σ1.v vCA ≤ 1 := by rw [ha]; exact bv_le _
    simp only [ne_eq, ev_bor', ev_inL', ev_tok, ev_var, hc.tok, bv_eq_zero, decide_eq_false_iff_not,
      pos_bv_add_bv, Bool.or_eq_true, decide_eq_true_eq, not_or, not_and_or, not_not] at hcond
    by_cases hP : tc ts (σ1.v vCP) ∈ [0, 1]
    · have hPl := lt_of_tc_mem hP
      refine hach_iteT (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, hP]) ?_
      by_cases hQ : tc ts (σ1.v vCQ) ∈ [0, 1]
      · have hQl := lt_of_tc_mem hQ
        refine hach_iteT (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, hQ]) ?_
        have hfin : ∀ σ2 : HSt M, Frame [vCA] σ1 σ2 → σ2.v vCA = bv
            (if decide (tc ts (σ1.v vCP) = 1) = decide (tc ts (σ1.v vCQ) = 1) then a
              else decide (tc ts (σ1.v vCQ) = 1)) →
            HAch w B (.set vCP (.var vCP + .const 1) ;; .set vCQ (.var vCQ + .const 1)) σ2
              (fun σ' => inv σ' ∧ 2 * n + 2 - σ'.v vCP - σ'.v vCQ <
                2 * n + 2 - σ1.v vCP - σ1.v vCQ) := by
          intro σ2 hf2 hv2
          have e1 : σ2.v vCP = σ1.v vCP := hf2.1 _ (by decide)
          have e2 : σ2.v vCQ = σ1.v vCQ := hf2.1 _ (by decide)
          refine hach_seq (hach_set (by bnd_tac <;> (try simp) <;> omega)
            (hach_set (by bnd_tac <;> (try simp) <;> omega) ?_))
          refine ⟨⟨((hf.trans (hf2.mono (by simp))).set (by simp) _).set (by simp) _, ?_, ?_, (if decide (tc ts (σ1.v vCP) = 1) = decide (tc ts (σ1.v vCQ) = 1) then a
              else decide (tc ts (σ1.v vCQ) = 1)),
            ?_, ?_⟩, ?_⟩ <;>
            simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const, Fin.reduceEq,
              if_true, if_false, e1, e2]
          · omega
          · omega
          · exact hv2
          · rw [hd, cmpScan_step, if_pos hP, if_pos hQ]
          · omega
        refine hach_seq (hach_ite (by bnd_tac <;> (try simp) <;> omega) ?_)
        split_ifs with h3
        · refine hach_skip (hfin σ1 (Frame.refl _ _) ?_)
          simp only [ne_eq, ev_eq, ev_tok, ev_var, ev_const, hc.tok, bv_eq_zero,
            decide_eq_false_iff_not, not_not, bv_inj] at h3
          rw [if_pos (by simpa using h3), ha]
        · refine hach_set (by bnd_tac <;> (try simp) <;> omega) (hfin _ ((Frame.refl _ _).set
            (by simp) _) ?_)
          simp only [ne_eq, ev_eq, ev_tok, ev_var, ev_const, hc.tok, bv_eq_zero,
            decide_eq_false_iff_not, not_not, bv_inj] at h3
          simp only [HSt.set_v, Function.update_self, ev_eq, ev_tok, ev_var, ev_const, hc.tok]
          rw [if_neg (by simpa using h3)]
      · refine hach_iteF (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, hQ]) ?_
        have hfin : ∀ σ2 : HSt M, Frame [vCA] σ1 σ2 → σ2.v vCA = bv
            (if decide (tc ts (σ1.v vCP) = 1) then false else a) →
            HAch w B (.set vCP (.var vCP + .const 1)) σ2
              (fun σ' => inv σ' ∧ 2 * n + 2 - σ'.v vCP - σ'.v vCQ <
                2 * n + 2 - σ1.v vCP - σ1.v vCQ) := by
          intro σ2 hf2 hv2
          have e1 : σ2.v vCP = σ1.v vCP := hf2.1 _ (by decide)
          have e2 : σ2.v vCQ = σ1.v vCQ := hf2.1 _ (by decide)
          refine hach_set (by bnd_tac <;> (try simp) <;> omega) ?_
          refine ⟨⟨(hf.trans (hf2.mono (by simp))).set (by simp) _, ?_, ?_, (if decide (tc ts (σ1.v vCP) = 1) then false else a),
            ?_, ?_⟩, ?_⟩ <;>
            simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const, Fin.reduceEq,
              if_true, if_false, e1, e2]
          · omega
          · omega
          · exact hv2
          · rw [hd, cmpScan_step, if_pos hP, if_neg hQ]
          · omega
        refine hach_seq (hach_ite (by bnd_tac <;> (try simp) <;> omega) ?_)
        split_ifs with h3
        · refine hach_set (by simp) (hfin _ ((Frame.refl _ _).set
            (by simp) _) ?_)
          simp only [ne_eq, ev_eq, ev_tok, ev_var, ev_const, hc.tok, bv_eq_zero,
            decide_eq_false_iff_not, not_not] at h3
          simp [h3]
        · refine hach_skip (hfin σ1 (Frame.refl _ _) ?_)
          simp only [ne_eq, ev_eq, ev_tok, ev_var, ev_const, hc.tok, bv_eq_zero,
            decide_eq_false_iff_not, not_not] at h3
          simp [h3, ha]
    · have hQ : tc ts (σ1.v vCQ) ∈ [0, 1] := by tauto
      have hQl := lt_of_tc_mem hQ
      refine hach_iteF (by bnd_tac <;> (try simp) <;> omega) (by simp [hc.tok, hP]) ?_
      have hfin : ∀ σ2 : HSt M, Frame [vCA] σ1 σ2 → σ2.v vCA = bv
          (if decide (tc ts (σ1.v vCQ) = 1) then true else a) →
          HAch w B (.set vCQ (.var vCQ + .const 1)) σ2
            (fun σ' => inv σ' ∧ 2 * n + 2 - σ'.v vCP - σ'.v vCQ <
              2 * n + 2 - σ1.v vCP - σ1.v vCQ) := by
        intro σ2 hf2 hv2
        have e1 : σ2.v vCP = σ1.v vCP := hf2.1 _ (by decide)
        have e2 : σ2.v vCQ = σ1.v vCQ := hf2.1 _ (by decide)
        refine hach_set (by bnd_tac <;> (try simp) <;> omega) ?_
        refine ⟨⟨(hf.trans (hf2.mono (by simp))).set (by simp) _, ?_, ?_, (if decide (tc ts (σ1.v vCQ) = 1) then true else a),
          ?_, ?_⟩, ?_⟩ <;>
          simp only [HSt.set_v, Function.update_apply, ev_add, ev_var, ev_const, Fin.reduceEq,
            if_true, if_false, e1, e2]
        · omega
        · omega
        · exact hv2
        · rw [hd, cmpScan_step, if_neg hP, if_pos hQ]
        · omega
      refine hach_seq (hach_ite (by bnd_tac <;> (try simp) <;> omega) ?_)
      split_ifs with h3
      · refine hach_set (by (try simp); omega) (hfin _ ((Frame.refl _ _).set
          (by simp) _) ?_)
        simp only [ne_eq, ev_eq, ev_tok, ev_var, ev_const, hc.tok, bv_eq_zero,
          decide_eq_false_iff_not, not_not] at h3
        simp [h3]
      · refine hach_skip (hfin σ1 (Frame.refl _ _) ?_)
        simp only [ne_eq, ev_eq, ev_tok, ev_var, ev_const, hc.tok, bv_eq_zero,
          decide_eq_false_iff_not, not_not] at h3
        simp [h3, ha]

end CTLP

end PathChecking
