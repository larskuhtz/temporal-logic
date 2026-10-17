module

public import RequestProject.Shallow.Prog.Pro

/-!
# The query function of the round algorithm

`qProg k` reads the packed input `pack w q a`, decodes `q = qIdx M u ℓ j` and emits the query
`QP`; `exists_QProg` shows that this gives a logspace function with the specification
`QSpecOK k`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- The prologue of the query program. -/
def proP (k : ℕ) : Pr V :=
  .seq lenP (.seq (.set vL (.bin .div (.v vN) (.c 5))) (.seq (.set vNq (.bin .add (.v vL) (.c 1)))
  (.seq (.set vM (.bin .add (.v vL) (.c 2))) (.seq qP
  (.seq (.set vJ (.bin .mod (.v vQ) (.v vNq)))
  (.seq (.set vLl (.bin .mod (.bin .div (.v vQ) (.v vNq)) (.v vNq)))
  (.seq (.set vU (.bin .div (.bin .div (.v vQ) (.v vNq)) (.v vNq)))
  (.seq (fendP (.c 1)) (.seq (.set vR0 (.bin .add (.v sR) (.c 1))) (.seq logP (powP k)))))))))))

/-- Frame of `proP`. -/
abbrev proW : List (Fin V) :=
  [vN, vDn, vI4, vL, vNq, vM, vA, vQ, vJ, vLl, vU, sR, sP, sC, sD, sI, vR0, vP, vLg, vD]

/-- Postcondition of the prologue. -/
structure ProPost (ts : List Tok) (q : ℕ) (a : List Bool) (C k : ℕ) (r : Fin V → ℕ) : Prop where
  env : Env ts q a C r
  hNq : r vNq = ts.length + 1
  hM : r vM = ts.length + 2
  hJ : r vJ = q % (ts.length + 1)
  hLl : r vLl = q / (ts.length + 1) % (ts.length + 1)
  hU : r vU = q / (ts.length + 1) / (ts.length + 1)
  hR0 : r vR0 = fend ts 1 + 1
  hD : r vD = (Nat.log 2 (5 * ts.length) + 1) ^ k

lemma sp_proP (k : ℕ) (hq : q ≤ a.length)
    (hC : 2 * (pack (encodeToks ts) q a).length + 40 ≤ C)
    (hCk : (Nat.log 2 (5 * ts.length) + 1) ^ k + k + 1 ≤ C) :
    Sp (pack (encodeToks ts) q a) C (proP k) ρ proW [] (ProPost ts q a C k) := by
  have hlen := pack_length (encodeToks ts) q a hq
  rw [encodeToks_length] at hlen
  have hL5 : 10 * ts.length + 40 ≤ C := by omega
  unfold proP
  -- |w|
  refine sp_seqE (o2 := []) ((sp_lenP (ρ := ρ) hq hC).frame.mono (by decide) (fun _ _ h => h))
    (fun ρ1 _ h1 => ?_) rfl
  have hN1 : ρ1 vN = 5 * ts.length := by rw [h1.1, encodeToks_length]
  -- number of tokens, N, m
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ1 vL
    ts.length) (by decide) (by simp [hN1, min_eq_left (show 5 ≤ C by omega)]))
    (fun ρ2 _ h2 => ?_) rfl
  subst h2
  set ρ2 := Function.update ρ1 vL ts.length
  have hE2 : Env ts q a C ρ2 := ⟨hq, hC, by simp (disch := decide) [ρ2, Function.update_of_ne, hN1],
    by simp [ρ2]⟩
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ2 vNq
    (ts.length + 1)) (by decide) (by
      congr 1
      simp only [eval_bin, ap_add, eval_v, eval_c, hE2.hL]
      simp (disch := omega) only [min_eq_left])) (fun ρ3 _ h3 => ?_) rfl
  subst h3
  set ρ3 := Function.update ρ2 vNq (ts.length + 1)
  have hE3 : Env ts q a C ρ3 := hE2.congr (Function.update_of_ne (by decide) _ _)
    (Function.update_of_ne (by decide) _ _)
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ3 vM
    (ts.length + 2)) (by decide) (by
      congr 1
      simp only [eval_bin, ap_add, eval_v, eval_c, hE3.hL]
      simp (disch := omega) only [min_eq_left])) (fun ρ4 _ h4 => ?_) rfl
  subst h4
  set ρ4 := Function.update ρ3 vM (ts.length + 2)
  have hE4 : Env ts q a C ρ4 := hE3.congr (Function.update_of_ne (by decide) _ _)
    (Function.update_of_ne (by decide) _ _)
  have hNq4 : ρ4 vNq = ts.length + 1 := by simp (disch := decide) [ρ4, ρ3, Function.update_of_ne]
  have hM4 : ρ4 vM = ts.length + 2 := by simp [ρ4]
  -- q
  refine sp_seqE (o2 := []) ((sp_qP (w := encodeToks ts) (ρ := ρ4) hq hC
    (by rw [hE4.hN, encodeToks_length])).frame.mono (by decide) (fun _ _ h => h))
    (fun ρ5 _ h5 => ?_) rfl
  have hE5 : Env ts q a C ρ5 := hE4.congr (h5.2 _ (by decide)) (h5.2 _ (by decide))
  have hNq5 : ρ5 vNq = ts.length + 1 := (h5.2 _ (by decide)).trans hNq4
  have hM5 : ρ5 vM = ts.length + 2 := (h5.2 _ (by decide)).trans hM4
  have hQ5 : ρ5 vQ = q := h5.1.1
  -- decoding
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ5 vJ
    (q % (ts.length + 1))) (by decide) (by simp [hQ5, hNq5])) (fun ρ6 _ h6 => ?_) rfl
  subst h6
  set ρ6 := Function.update ρ5 vJ (q % (ts.length + 1))
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ6 vLl
    (q / (ts.length + 1) % (ts.length + 1))) (by decide) (by
      simp (disch := decide) [ρ6, Function.update_of_ne, hQ5, hNq5])) (fun ρ7 _ h7 => ?_) rfl
  subst h7
  set ρ7 := Function.update ρ6 vLl (q / (ts.length + 1) % (ts.length + 1))
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ7 vU
    (q / (ts.length + 1) / (ts.length + 1))) (by decide) (by
      simp (disch := decide) [ρ7, ρ6, Function.update_of_ne, hQ5, hNq5]))
    (fun ρ8 _ h8 => ?_) rfl
  subst h8
  set ρ8 := Function.update ρ7 vU (q / (ts.length + 1) / (ts.length + 1))
  have g8 : ∀ v, v ≠ vJ → v ≠ vLl → v ≠ vU → ρ8 v = ρ5 v := fun v h1 h2 h3 => by
    simp only [ρ8, ρ7, ρ6, Function.update_of_ne h1, Function.update_of_ne h2,
      Function.update_of_ne h3]
  have hE8 : Env ts q a C ρ8 := hE5.congr (g8 _ (by decide) (by decide) (by decide))
    (g8 _ (by decide) (by decide) (by decide))
  -- root
  refine sp_seqE (o2 := []) ((sp_fendP hE8 (.c 1) (by simp only [eval_c]; omega)).frame.mono (by decide)
    (fun _ _ h => h)) (fun ρ9 _ h9 => ?_) rfl
  simp only [eval_c, min_eq_left (show 1 ≤ C by omega)] at h9
  have hfe : fend ts 1 ≤ ts.length + 1 := fend_le_succ ts (by omega)
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ9 vR0
    (fend ts 1 + 1)) (by decide) (by
      congr 1
      simp only [eval_bin, ap_add, eval_v, eval_c, h9.1]
      simp (disch := omega) only [min_eq_left])) (fun ρ10 _ h10 => ?_) rfl
  subst h10
  set ρ10 := Function.update ρ9 vR0 (fend ts 1 + 1)
  have g10 : ∀ v, v ∉ scanW → v ≠ vR0 → ρ10 v = ρ8 v := fun v h1 h2 => by
    simp only [ρ10, Function.update_of_ne h2]; exact h9.2 v h1
  have hE10 : Env ts q a C ρ10 := hE8.congr (g10 _ (by decide) (by decide))
    (g10 _ (by decide) (by decide))
  -- depth bound
  refine sp_seqE (o2 := []) ((sp_logP (x := pack (encodeToks ts) q a) (ρ := ρ10)
    (by rw [hE10.hN]; omega)).frame.mono (by decide) (fun _ _ h => h)) (fun ρ11 _ h11 => ?_) rfl
  rw [hE10.hN] at h11
  refine ((sp_powP (x := pack (encodeToks ts) q a) (ρ := ρ11) k (by rw [h11.1]; exact hCk)).frame.mono
    (by decide) (fun _ _ h => h)).mono (fun _ h => h) (fun r _ hr => ?_)
  have e : ∀ v, v ∉ [vD, vI4] → v ∉ [vP, vLg, vI4] → v ∉ scanW → v ≠ vR0 → r v = ρ10 v :=
    fun v h1 h2 h3 h4 => by rw [hr.2 v h1, h11.2 v h2]
  have e8 : ∀ v, v ∉ [vD, vI4] → v ∉ [vP, vLg, vI4] → v ∉ scanW → v ≠ vR0 → v ≠ vJ → v ≠ vLl →
      v ≠ vU → r v = ρ5 v := fun v h1 h2 h3 h4 h5 h6 h7 => by
    rw [e v h1 h2 h3 h4, g10 v h3 h4, g8 v h5 h6 h7]
  refine ⟨hE5.congr (e8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (e8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hNq5]
  · rw [e8 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hM5]
  · rw [e _ (by decide) (by decide) (by decide) (by decide), g10 _ (by decide) (by decide)]
    simp (disch := decide) [ρ8, ρ7, ρ6, Function.update_of_ne]
  · rw [e _ (by decide) (by decide) (by decide) (by decide), g10 _ (by decide) (by decide)]
    simp (disch := decide) [ρ8, ρ7, Function.update_of_ne]
  · rw [e _ (by decide) (by decide) (by decide) (by decide), g10 _ (by decide) (by decide)]
    simp (disch := decide) [ρ8, Function.update_of_ne]
  · rw [hr.2 _ (by decide), h11.2 _ (by decide)]
    simp [ρ10]
  · rw [hr.1, h11.1]

end SQ

end PathChecking

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

/-- The query program. -/
def qProg (k : ℕ) : Pr V := .seq (proP k) queryP

lemma qIdx_decode {M u ℓ j : ℕ} (hℓ : ℓ < M) (hj : j < M) :
    qIdx M u ℓ j % M = j ∧ qIdx M u ℓ j / M % M = ℓ ∧ qIdx M u ℓ j / M / M = u := by
  have hM : 0 < M := by omega
  have h1 : qIdx M u ℓ j / M = u * M + ℓ := by
    unfold qIdx
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hj, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · unfold qIdx; rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
  · rw [h1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hℓ]
  · rw [h1, Nat.add_comm, Nat.add_mul_div_right _ _ hM, Nat.div_eq_of_lt hℓ, zero_add]

lemma cap_big (n k : ℕ) (hn : 3 ≤ n) : 2 * n + 40 ≤ (n + 2) ^ (k + 4) + 3 := by
  have h1 : (n + 2) ^ 4 ≤ (n + 2) ^ (k + 4) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 5 * (n + 2) ≤ (n + 2) ^ 2 := by nlinarith
  have h3 : (n + 2) ^ 4 = ((n + 2) ^ 2) ^ 2 := by ring
  nlinarith

lemma cap_big' (n k b : ℕ) (hb : b ≤ n) :
    (b + 1) ^ k + k + 1 ≤ (n + 2) ^ (k + 4) + 3 := by
  have A : (b + 1) ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
  have B : k + 1 ≤ (n + 2) ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    have : 2 ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left (by omega) k
    omega
  have D : 2 ≤ (n + 2) ^ 4 := by
    have : 2 ^ 4 ≤ (n + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  have E : (n + 2) ^ (k + 4) = (n + 2) ^ k * (n + 2) ^ 4 := pow_add _ _ _
  nlinarith

theorem qProg_spec (k : ℕ) : QSpecOK k (fun x => (qProg k).output (k + 4) x) := by
  intro φ t a u ℓ j ha hu hℓ hj
  set ts := instToks φ t with hts
  set M := ts.length + 1 with hMdef
  have hw : (encodeToks ts).length = 5 * ts.length := encodeToks_length ts
  have hq3 := qIdx_lt hu hℓ hj
  have hMa : M ^ 3 ≤ a.length := by
    rw [ha, hw]; exact Nat.pow_le_pow_left (by omega) 3
  have hq : qIdx M u ℓ j ≤ a.length := by omega
  have hxlen := pack_length (encodeToks ts) (qIdx M u ℓ j) a hq
  set x := pack (encodeToks ts) (qIdx M u ℓ j) a with hx
  have ha1 : 1 ≤ a.length := by rw [ha]; exact Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hroot : fend ts 1 + 1 ≤ ts.length + 1 := by
    have : 1 ≤ ts.length := by simp [hts, instToks]
    have := fend_le' ts this
    omega
  have hC : 2 * x.length + 40 ≤ capOf (k + 4) x := cap_big _ _ (by omega)
  have hlog : Nat.log 2 (5 * ts.length) ≤ x.length := by
    have := Nat.log_le_self 2 (5 * ts.length); omega
  have hCk : (Nat.log 2 (5 * ts.length) + 1) ^ k + k + 1 ≤ capOf (k + 4) x :=
    cap_big' _ _ _ hlog
  obtain ⟨hdj, hdl, hdu⟩ := qIdx_decode (u := u) hℓ hj
  have hsp := sp_seqE (o2 := encodeToks (QP ts (fend ts 1 + 1)
      ((Nat.log 2 (5 * ts.length) + 1) ^ k) (ts.length + 2) (ts.length + 1) u ℓ j
      (ansF (ts.length + 1) a))) (o := encodeToks (QP ts (fend ts 1 + 1)
      ((Nat.log 2 (5 * ts.length) + 1) ^ k) (ts.length + 2) (ts.length + 1) u ℓ j
      (ansF (ts.length + 1) a))) (Q := fun _ => True)
    ((sp_proP (ρ := fun _ => 0) k hq hC hCk).mono (W' := proW ++ queryW) (by decide)
      (fun _ _ h => h))
    (fun ρ1 _ h1 => by
      have h := (sp_queryP h1.env h1.hNq hMa (by rw [h1.hU, hdu]; omega)
        (by rw [h1.hJ, hdj]; omega) (by rw [h1.hR0]; exact hroot)).mono
          (W' := proW ++ queryW) (by decide) (fun _ _ h => h)
      rwa [h1.hR0, h1.hD, h1.hM, h1.hU, h1.hLl, h1.hJ, hdj, hdl, hdu] at h) (by simp)
  obtain ⟨ρ', r, -, -⟩ := hsp
  show (Pr.run x (capOf (k + 4) x) (qProg k) (fun _ => 0)).2 = _
  rw [qProg, r, root, shallowBound, hw]

theorem exists_QProg (k : ℕ) :
    ∃ Q : Word → Word, LogspaceComputable Q ∧ QSpecOK k Q :=
  ⟨_, logspaceComputable_of_output (k + 4) (qProg k) _ (fun _ => rfl), qProg_spec k⟩

end SQ

end PathChecking
