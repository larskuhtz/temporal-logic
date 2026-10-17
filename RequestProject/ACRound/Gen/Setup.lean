module

public import RequestProject.ACRound.Gen.Group
public import RequestProject.ACRound.Gen.Poly

/-!
# Computing the layout parameters

`GenP.paramsP G` reads the input length `n` from the generator input `1ⁿ 0 ⋯` and computes the
layout parameters `G.Nq n`, `G.R n`, `G.L n`, `G.S n` and the group size (`GenP.run_paramsP`).
-/

@[expose] public section

namespace PathChecking

namespace GCst

variable (G : GCst)

/-- Group size. -/
def W (n : ℕ) : ℕ := 2 * (G.L n + 1) + (G.L n + 1) * G.S n + 1

/-- A bound on all numbers handled by the generator (apart from input positions). -/
def Mb (n : ℕ) : ℕ :=
  (n + 2 + G.R n * G.Nq n * G.W n) + 2 * G.S n + 2 * G.L n + 2 * n + 10 + G.e + G.A + G.k +
    G.c + G.cB + G.Nq n + G.R n + (n + 1) ^ G.A + (Nat.log 2 n + 1) ^ G.k +
    (G.L n + 1) ^ G.cB + G.W n + G.R n * G.Nq n

lemma lay_W (CB : ℕ → Circuit) (n : ℕ) : (G.lay CB n).W = G.W n := rfl

lemma lay_F0 (CB : ℕ → Circuit) (n : ℕ) :
    (G.lay CB n).F0 = n + 2 + G.R n * G.Nq n * G.W n := rfl

lemma Mb_poly : PolyB G.Mb := by
  have hn1 : PolyB (fun n => n + 1) := PolyB.id'.add (PolyB.const 1)
  have hR : PolyB G.R := by
    refine (PolyB.const G.c |>.mul (hn1.pow G.k)).mono fun n => ?_
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (log_add_one_le n) _)
  have hlg : PolyB (fun n => (Nat.log 2 n + 1) ^ G.k) :=
    (hn1.pow G.k).mono fun n => Nat.pow_le_pow_left (log_add_one_le n) _
  have hL : PolyB G.L := PolyB.const _ |>.mul (hn1.pow _)
  have hL1 : PolyB (fun n => G.L n + 1) := hL.add (PolyB.const 1)
  have hS : PolyB G.S := (PolyB.const _ |>.mul (hL1.pow _)).add (PolyB.const 1)
  have hW : PolyB G.W := ((PolyB.const 2 |>.mul hL1).add (hL1.mul hS)).add (PolyB.const 1)
  have hNq : PolyB G.Nq := hn1.pow _
  unfold Mb
  refine ((((((((((((((((((PolyB.id'.add (PolyB.const 2)).add ((hR.mul hNq).mul hW)).add
    ((PolyB.const 2).mul hS)).add ((PolyB.const 2).mul hL)).add ((PolyB.const 2).mul PolyB.id')).add
    (PolyB.const 10)).add (PolyB.const _)).add (PolyB.const _)).add (PolyB.const _)).add
    (PolyB.const _)).add (PolyB.const _)).add hNq).add hR).add (hn1.pow _)).add hlg).add
    (hL1.pow _)).add hW).add (hR.mul hNq)).mono fun n => le_rfl

end GCst

namespace GenP

open LL GenC

variable {z : Word} {C : ℕ}

/-- temporary -/
abbrev t1 : Fin V := 28
/-- power loop counter -/
abbrev cnt : Fin V := 29
/-- logarithm -/
abbrev lg : Fin V := 30
/-- logarithm: power of two -/
abbrev p2 : Fin V := 31
/-- logarithm: loop counter -/
abbrev tj : Fin V := 32

lemma run_powP' (dst base cnt : Fin V) (k : ℕ) (hdb : dst ≠ base) (hcb : cnt ≠ base)
    (hdc : dst ≠ cnt) (ρ : Fin V → ℕ) (hk : k ≤ C) (hC : 1 ≤ C) (hb : ρ base ^ k ≤ C) :
    ∃ ρ', (powP dst base cnt k).run z C ρ = (ρ', []) ∧ ρ' dst = ρ base ^ k ∧
      ∀ v, v ≠ dst → v ≠ cnt → ρ' v = ρ v := by
  obtain ⟨h1, h2⟩ := run_powP (z := z) dst base cnt k hdb hcb hdc ρ hk hC hb
  exact ⟨_, Prod.ext rfl h2, h1, fun v a b => Pr.run_frame (powP dst base cnt k) ρ v
    (by simp [powP_wr, a, b])⟩

lemma run_logP' (lg p2 j nv : Fin V) (h1 : lg ≠ p2) (h2 : lg ≠ j) (h3 : lg ≠ nv) (h4 : p2 ≠ j)
    (h5 : p2 ≠ nv) (h6 : j ≠ nv) (ρ : Fin V → ℕ) (hC : 2 * ρ nv + 2 ≤ C) :
    ∃ ρ', (logP lg p2 j nv).run z C ρ = (ρ', []) ∧ ρ' lg = Nat.log 2 (ρ nv) ∧
      ∀ v, v ≠ lg → v ≠ p2 → v ≠ j → ρ' v = ρ v := by
  obtain ⟨k1, k2⟩ := run_logP (z := z) lg p2 j nv h1 h2 h3 h4 h5 h6 ρ hC
  exact ⟨_, Prod.ext rfl k2, k1, fun v a b c => Pr.run_frame (logP lg p2 j nv) ρ v
    (by simp [logP_wr, a, b, c])⟩

lemma run_set_eq (x : Fin V) (e : Ex V) (ρ : Fin V → ℕ) (a : ℕ) (h : e.eval z C ρ = a) :
    (Pr.set x e).run z C ρ = (Function.update ρ x a, []) := by
  simp [h]

/-- The parameter program. -/
def paramsP (G : GCst) : Pr V :=
  .seq (findP vn vfd vj .len (.inp (.bin .add (.v vj) (.c 1))))
  (.seq (.set t1 (.bin .add (.v vn) (.c 1)))
  (.seq (powP vNq t1 cnt G.e)
  (.seq (powP vL t1 cnt G.A)
  (.seq (.set vL (.bin .mul (.c G.A) (.v vL)))
  (.seq (logP lg p2 tj vn)
  (.seq (.set t1 (.bin .add (.v lg) (.c 1)))
  (.seq (powP vR t1 cnt G.k)
  (.seq (.set vR (.bin .mul (.c G.c) (.v vR)))
  (.seq (.set t1 (.bin .add (.v vL) (.c 1)))
  (.seq (powP vS t1 cnt G.cB)
  (.seq (.set vS (.bin .add (.bin .mul (.c G.cB) (.v vS)) (.c 1)))
  (.set vW (.bin .add (.bin .add (.bin .mul (.c 2) (.v t1)) (.bin .mul (.v t1) (.v vS)))
    (.c 1))))))))))))))

/-- **The parameters.** -/
lemma run_paramsP (G : GCst) (CB : ℕ → Circuit) (n : ℕ) (ρ : Fin V → ℕ)
    (hun : ∀ i < n, z[i]? = some true) (hsep : z[n]? = some false)
    (hC : G.Mb n ≤ C) (hz : 4 * z.length + 40 ≤ C) :
    ∃ ρ', (paramsP G).run z C ρ = (ρ', []) ∧ GenP.Env (G.lay CB n) ρ' := by
  have hzn : n < z.length := (List.getElem?_eq_some_iff.1 hsep).1
  unfold GCst.Mb at hC
  have hW1 : 1 ≤ G.W n := by unfold GCst.W; omega
  have hNq1 : 1 ≤ G.Nq n := Nat.one_le_pow _ _ (by omega)
  have hRN : G.R n * G.Nq n ≤ G.R n * G.Nq n * G.W n := Nat.le_mul_of_pos_right _ hW1
  -- step 1: find `n`
  obtain ⟨f1, f2, f3⟩ := run_findP (z := z) (C := C) vn vfd vj .len (.inp (.bin .add (.v vj) (.c 1)))
    (by decide) (by decide) (by decide) ρ (fun i => bitCode z[i]?) n (by omega)
    (fun _ _ => rfl)
    (fun i hi ρ' _ => by
      simp only [eval_len, min_eq_left (show z.length ≤ C by omega)] at hi
      simp only [eval_inp, eval_bin, ap_add, eval_v, eval_c, Function.update_self]
      rw [min_eq_left (show 1 ≤ C by omega),
        min_eq_left (show i + 1 ≤ C by omega), symNum_inputSym_succ])
    (by simp only [eval_len]; omega) (by simp [hsep, bitCode])
    (fun i hi => by simp [hun i hi, bitCode])
  set ρ1 := ((findP vn vfd vj .len (.inp (.bin .add (.v vj) (.c 1)))).run z C ρ).1
  have r1 : (findP vn vfd vj .len (.inp (.bin .add (.v vj) (.c 1)))).run z C ρ = (ρ1, []) :=
    Prod.ext rfl f2
  -- step 2: `t1 := n + 1`
  have r2 := run_set_eq (z := z) (C := C) t1 (.bin .add (.v vn) (.c 1)) ρ1 (n + 1)
    (by simp [f1, min_eq_left (show 1 ≤ C by omega)]; omega)
  set ρ2 := Function.update ρ1 t1 (n + 1)
  -- step 3: `vNq := (n + 1)^e`
  obtain ⟨ρ3, r3, a3, b3⟩ := run_powP' (z := z) (C := C) vNq t1 cnt G.e (by decide) (by decide)
    (by decide) ρ2 (by omega) (by omega) (by simp [ρ2]; unfold GCst.Nq at hC; omega)
  -- step 4: `vL := (n + 1)^A`
  obtain ⟨ρ4, r4, a4, b4⟩ := run_powP' (z := z) (C := C) vL t1 cnt G.A (by decide) (by decide)
    (by decide) ρ3 (by omega) (by omega) (by rw [b3 _ (by decide) (by decide)]; simp [ρ2]; omega)
  have a4' : ρ4 vL = (n + 1) ^ G.A := by rw [a4, b3 _ (by decide) (by decide)]; simp [ρ2]
  have r5 := run_set_eq (z := z) (C := C) vL (.bin .mul (.c G.A) (.v vL)) ρ4 (G.L n)
    (by simp [a4', min_eq_left (show G.A ≤ C by omega)]; unfold GCst.L at hC ⊢; omega)
  set ρ5 := Function.update ρ4 vL (G.L n)
  have hn5 : ρ5 vn = n := by
    simp only [ρ5]; rw [Function.update_of_ne (by decide), b4 _ (by decide) (by decide),
      b3 _ (by decide) (by decide)]; simp only [ρ2]
    rw [Function.update_of_ne (by decide), f1]
  -- step 6: logarithm
  obtain ⟨ρ6, r6, a6, b6⟩ := run_logP' (z := z) (C := C) lg p2 tj vn (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) ρ5 (by rw [hn5]; omega)
  rw [hn5] at a6
  have r7 := run_set_eq (z := z) (C := C) t1 (.bin .add (.v lg) (.c 1)) ρ6 (Nat.log 2 n + 1)
    (by
      have := log_add_one_le n
      simp [a6, min_eq_left (show 1 ≤ C by omega)]; omega)
  set ρ7 := Function.update ρ6 t1 (Nat.log 2 n + 1)
  obtain ⟨ρ8, r8, a8, b8⟩ := run_powP' (z := z) (C := C) vR t1 cnt G.k (by decide) (by decide)
    (by decide) ρ7 (by omega) (by omega) (by simp [ρ7]; omega)
  have a8' : ρ8 vR = (Nat.log 2 n + 1) ^ G.k := by rw [a8]; simp [ρ7]
  have r9 := run_set_eq (z := z) (C := C) vR (.bin .mul (.c G.c) (.v vR)) ρ8 (G.R n)
    (by simp [a8', min_eq_left (show G.c ≤ C by omega)]; unfold GCst.R at hC ⊢; omega)
  set ρ9 := Function.update ρ8 vR (G.R n)
  have hL9 : ρ9 vL = G.L n := by
    simp only [ρ9]; rw [Function.update_of_ne (by decide), b8 _ (by decide) (by decide)]
    simp only [ρ7]; rw [Function.update_of_ne (by decide), b6 _ (by decide) (by decide) (by decide)]
    simp [ρ5]
  have r10 := run_set_eq (z := z) (C := C) t1 (.bin .add (.v vL) (.c 1)) ρ9 (G.L n + 1)
    (by simp [hL9, min_eq_left (show 1 ≤ C by omega)]; omega)
  set ρ10 := Function.update ρ9 t1 (G.L n + 1)
  obtain ⟨ρ11, r11, a11, b11⟩ := run_powP' (z := z) (C := C) vS t1 cnt G.cB (by decide) (by decide)
    (by decide) ρ10 (by omega) (by omega) (by simp [ρ10]; omega)
  have a11' : ρ11 vS = (G.L n + 1) ^ G.cB := by rw [a11]; simp [ρ10]
  have r12 := run_set_eq (z := z) (C := C) vS (.bin .add (.bin .mul (.c G.cB) (.v vS)) (.c 1)) ρ11
    (G.S n)
    (by
      simp [a11', min_eq_left (show G.cB ≤ C by omega), min_eq_left (show 1 ≤ C by omega)]
      unfold GCst.S at hC ⊢; omega)
  set ρ12 := Function.update ρ11 vS (G.S n)
  have ht12 : ρ12 t1 = G.L n + 1 := by
    simp only [ρ12]; rw [Function.update_of_ne (by decide), b11 _ (by decide) (by decide)]
    simp [ρ10]
  have r13 := run_set_eq (z := z) (C := C) vW (.bin .add (.bin .add (.bin .mul (.c 2) (.v t1))
    (.bin .mul (.v t1) (.v vS))) (.c 1)) ρ12 (G.W n)
    (by
      have hS : ρ12 vS = G.S n := by simp [ρ12]
      unfold GCst.W at hC ⊢
      simp only [eval_bin, eval_v, eval_c, ap_add, ap_mul, ht12, hS]
      simp (disch := omega) only [min_eq_left])
  refine ⟨Function.update ρ12 vW (G.W n), ?_, ?_⟩
  · unfold paramsP
    rw [seq_eq r1 (seq_eq r2 (seq_eq r3 (seq_eq r4 (seq_eq r5 (seq_eq r6 (seq_eq r7 (seq_eq r8
      (seq_eq r9 (seq_eq r10 (seq_eq r11 (seq_eq r12 r13)))))))))))]
    rfl
  · have hb : ∀ v, v ≠ vW → v ≠ vS → v ≠ cnt → v ≠ t1 → v ≠ vR →
        Function.update ρ12 vW (G.W n) v = ρ6 v := fun v a b c d e => by
      rw [Function.update_of_ne a]; simp only [ρ12]
      rw [Function.update_of_ne b, b11 v b c]; simp only [ρ10]
      rw [Function.update_of_ne d]; simp only [ρ9]
      rw [Function.update_of_ne e, b8 v e c]; simp only [ρ7]
      rw [Function.update_of_ne d]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hb _ (by decide) (by decide) (by decide) (by decide) (by decide),
        b6 _ (by decide) (by decide) (by decide), hn5]; rfl
    · rw [hb _ (by decide) (by decide) (by decide) (by decide) (by decide),
        b6 _ (by decide) (by decide) (by decide)]
      simp only [ρ5]
      rw [Function.update_of_ne (by decide), b4 _ (by decide) (by decide), a3]
      simp only [ρ2, Function.update_self]; rfl
    · rw [Function.update_of_ne (by decide)]; simp only [ρ12]
      rw [Function.update_of_ne (by decide), b11 _ (by decide) (by decide)]; simp only [ρ10]
      rw [Function.update_of_ne (by decide)]; simp only [ρ9, Function.update_self]; rfl
    · rw [Function.update_of_ne (by decide)]
      simp only [ρ12]
      rw [Function.update_of_ne (by decide), b11 _ (by decide) (by decide)]
      simp only [ρ10]
      rw [Function.update_of_ne (by decide), hL9]; rfl
    · rw [Function.update_of_ne (by decide)]
      simp only [ρ12, Function.update_self]; rfl
    · simp only [Function.update_self]; rfl

end GenP

end PathChecking
