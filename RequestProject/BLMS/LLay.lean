module

public import RequestProject.BLMS.LGate

/-!
# Layers in the loop language

`depP` computes `Conc.dep C i`, `lyrP` the layer `Conc.lyr C i` and `bdP` the layer boundary
`(toLC C).bd l`.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

namespace LP

open LL

/-- layer of the output gate -/
abbrev vTop : Var := 2
/-- number of input gates `N` -/
abbrev vN : Var := 3
/-- last layer `D` -/
abbrev vD : Var := 4
/-- input of `depP` -/
abbrev vDi : Var := 30
/-- output of `depP` -/
abbrev vDcnt : Var := 31
/-- current gate of `depP` -/
abbrev vDcur : Var := 32
/-- loop variable of `depP` -/
abbrev vDk : Var := 33
/-- input of `lyrP` -/
abbrev vLi : Var := 34
/-- output of `lyrP` -/
abbrev vLy : Var := 35
/-- input of `bdP` -/
abbrev vBl : Var := 36
/-- output of `bdP` -/
abbrev vBd : Var := 37
/-- bound of the search in `bdP` -/
abbrev vBnb : Var := 38
/-- loop variable of `bdP` -/
abbrev vBi : Var := 39

variable {C : Circuit} {w : Word} {K : ℕ}

lemma Env.nK (hE : Env C w K) : C.length + 2 ≤ K := by
  have := hE.n_le; have := hE.gts_le; have := hE.lenK; omega

/-! ## The chain of first arguments -/

/-- Body of `depP`. -/
def depBody : Pr V :=
  .seq (.set vGi (.v vDcur)) (.seq gateP (.ite (.bin .eq (.v vGC) (.c 0))
    (.seq (.set vDcur (.v vGL)) (.set vDcnt (.bin .add (.v vDcnt) (.c 1)))) .skip))

/-- `vDcnt := dep C vDi`. -/
def depP : Pr V :=
  .seq (.set vDcur (.v vDi)) (.seq (.set vDcnt (.c 0)) (.loop vDk (.v vNG) depBody))

lemma depP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ)
    (hNT : ρ vNT = (gts C).length) (hNG : ρ vNG = C.length) :
    st w K depP ρ vDcnt = Conc.dep C (ρ vDi) := by
  have hK := hE.nK
  unfold depP
  simp only [st_seq, st_set, eval_v, eval_c]
  set ρ1 := Function.update (Function.update ρ vDcur (ρ vDi)) vDcnt (min 0 K)
  have hb : (Ex.v vNG : Ex V).eval w K ρ1 = C.length := by
    simp (config := {decide := true}) [ρ1, hNG]
  have key := st_loopI (w := w) (K := K) vDk (.v vNG) depBody ρ1 (Conc.chStep C) (ρ vDi, 0)
    (fun k ρ' a => ρ' vDcur = a.1 ∧ ρ' vDcnt = a.2 ∧ a.2 ≤ k)
    ⟨by simp (config := {decide := true}) [ρ1], by simp [ρ1], le_rfl⟩ (by
      intro k hk ρ' a hfr ⟨h1, h2, h3⟩
      rw [hb] at hk
      have hNT' : ρ' vNT = (gts C).length := by
        rw [hfr vNT (by decide)]; simp (config := {decide := true}) [ρ1, hNT]
      have hNG' : ρ' vNG = C.length := by
        rw [hfr vNG (by decide)]; simp (config := {decide := true}) [ρ1, hNG]
      unfold depBody
      simp only [st_seq, st_set, eval_v]
      have e0 : Function.update ρ' vDk k vDcur = a.1 := by
        simp (config := {decide := true}) [h1]
      rw [e0]
      set ρ3 := Function.update (Function.update ρ' vDk k) vGi a.1
      have g := gateP_spec hE hC ρ3 (by simp (config := {decide := true}) [ρ3, hNT'])
        (by simp (config := {decide := true}) [ρ3, hNG'])
      have hgi : ρ3 vGi = a.1 := by simp [ρ3]
      rw [hgi] at g
      have hcnt : st w K gateP ρ3 vDcnt = a.2 := by
        rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true}) [ρ3, h2]
      rw [st_ite]
      simp only [eval_bin, ap_eq, eval_v, eval_c, min_eq_left (Nat.zero_le K), g.c]
      unfold Conc.chStep Conc.chG
      by_cases hc : Conc.isC C a.1 = true
      · rw [if_neg (by simp [hc]), if_pos hc]
        simp only [st_skip]
        refine ⟨?_, ?_, by omega⟩
        · rw [st_frame _ _ _ (by decide)]; simp (config := {decide := true}) [ρ3, h1]
        · exact hcnt
      · rw [if_pos (by simp at hc; simp [hc]), if_neg hc]
        simp only [st_seq, st_set, eval_bin, ap_add, eval_v, eval_c]
        refine ⟨?_, ?_, by simp; omega⟩
        · simp (config := {decide := true}) [g.l, toLC]
        · simp (config := {decide := true}) [hcnt, min_eq_left (show 1 ≤ K by omega)]
          omega)
  rw [hb] at key
  exact key.2.1

lemma dep_le (i : ℕ) : Conc.dep C i ≤ C.length := by
  unfold Conc.dep
  have : ∀ k (a : ℕ × ℕ), ((List.range k).foldl (Conc.chStep C) a).2 ≤ a.2 + k := by
    intro k
    induction k with
    | zero => intro a; simp
    | succ k ih =>
      intro a
      rw [foldl_range_succ]
      have := ih a
      have hs : ∀ p : ℕ × ℕ, (Conc.chStep C p k).2 ≤ p.2 + 1 := by
        intro p; unfold Conc.chStep Conc.chG; split_ifs <;> simp
      have := hs ((List.range k).foldl (Conc.chStep C) a)
      omega
  simpa using this C.length (i, 0)

/-! ## Layers -/

/-- `vLy := lyr C vLi`. -/
def lyrP : Pr V :=
  .ite (.bin .lt (.v vLi) (.v vNG)) (.seq (.set vDi (.v vLi)) (.seq depP (.set vLy (.v vDcnt))))
    (.set vLy (.bin .add (.v vTop) (.c 1)))

lemma lyrP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ)
    (hNT : ρ vNT = (gts C).length) (hNG : ρ vNG = C.length) (hTop : ρ vTop = Conc.top C) :
    st w K lyrP ρ vLy = Conc.lyr C (ρ vLi) := by
  have hK := hE.nK
  unfold lyrP
  rw [st_ite]
  simp only [eval_bin, ap_lt, eval_v, hNG]
  by_cases hi : ρ vLi < C.length
  · rw [if_pos (by simp [hi])]
    simp only [st_seq, st_set, eval_v, Function.update_self]
    rw [depP_spec hE hC _ (by simp (config := {decide := true}) [hNT])
      (by simp (config := {decide := true}) [hNG])]
    simp [Conc.lyr, hi]
  · rw [if_neg (by simp [hi])]
    have := dep_le (C := C) (C.length - 1)
    simp [Conc.lyr, hi, hTop, Conc.top, min_eq_left (show 1 ≤ K by omega)]
    omega

/-- `vBd := (toLC C).bd vBl`. -/
def bdP : Pr V :=
  .seq (.set vBnb (.bin .add (.v vNG) (.c 1)))
    (firstFP vBd vBi vBnb (.seq (.set vLi (.v vBi)) lyrP) (.bin .eq (.bin .lt (.v vLy) (.v vBl)) (.c 0)))

lemma bdP_spec (hE : Env C w K) (hC : StratMCVPInstance C) (ρ : Var → ℕ)
    (hNT : ρ vNT = (gts C).length) (hNG : ρ vNG = C.length) (hTop : ρ vTop = Conc.top C) :
    st w K bdP ρ vBd = (toLC C).bd (ρ vBl) := by
  have hK := hE.nK
  unfold bdP
  simp only [st_seq, st_set]
  set ρ1 := Function.update ρ vBnb ((Ex.bin .add (.v vNG) (.c 1) : Ex V).eval w K ρ)
  have h1 : ρ1 vBnb = C.length + 1 := by
    simp [ρ1, hNG, min_eq_left (show 1 ≤ K by omega)]; omega
  rw [firstFP_spec vBd vBi vBnb _ _ ρ1 (fun i => decide (ρ vBl ≤ Conc.lyr C i)) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega), h1]
  · rfl
  · intro p hp ρ' hfr
    have hf : ∀ z, z ∉ (Pr.seq (.set vLi (.v vBi)) lyrP).wr → z ≠ vBd → z ≠ vBi → z ≠ vBnb →
        ρ' z = ρ z := by
      intro z h1 h2 h3 h4
      rw [hfr z h1 h2 h3]
      simp only [ρ1]
      rw [Function.update_of_ne h4]
    simp only [st_seq, st_set, eval_v]
    simp only [eval_bin, ap_eq, ap_lt, eval_v, eval_c, min_eq_left (Nat.zero_le K)]
    rw [st_frame _ _ vBl (by decide)]
    rw [lyrP_spec hE hC _ (by simp (config := {decide := true}) [hf vNT (by decide) (by decide) (by decide) (by decide), hNT])
      (by simp (config := {decide := true}) [hf vNG (by decide) (by decide) (by decide) (by decide), hNG])
      (by simp (config := {decide := true}) [hf vTop (by decide) (by decide) (by decide) (by decide), hTop])]
    simp (config := {decide := true}) [hf vBl (by decide) (by decide) (by decide) (by decide)]

end LP

end BLMS

end PathChecking
