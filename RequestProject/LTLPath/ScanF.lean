module

public import RequestProject.LTLPath.Path
public import RequestProject.LTLPath.FEU

/-!
# Bracket scans by bounded search

A bracket scan started with counter `1` stops at the first position `q` where the number of
closing tokens in `[p, q]` exceeds the number of opening tokens; hence it can be computed by a
bounded search with counting (`scan_eq_scanF`).
-/

@[expose] public section

namespace PathChecking

open CTLP

namespace LTok

variable (ts : List Tok)

/-- Number of positions `j ∈ [a, b)` whose token code satisfies `P`. -/
def cntP (P : ℕ → Bool) (a b : ℕ) : ℕ := (List.range (b - a)).countP fun m => P (tc ts (a + m))

/-- The scan with counter `c`, by bounded search. -/
def scanF (up down : ℕ → Bool) (p c : ℕ) : ℕ :=
  if ffind (fun q => decide (c + cntP ts up p (q + 1) ≤ cntP ts down p (q + 1))) p ts.length <
      ts.length
  then ffind (fun q => decide (c + cntP ts up p (q + 1) ≤ cntP ts down p (q + 1))) p ts.length + 1
  else max p ts.length

variable {ts}

lemma cntP_succ_left (P : ℕ → Bool) {a b : ℕ} (h : a < b) :
    cntP ts P a b = (if P (tc ts a) then 1 else 0) + cntP ts P (a + 1) b := by
  unfold cntP
  rw [show b - a = (b - (a + 1)) + 1 by omega, List.range_succ_eq_map, List.countP_cons,
    List.countP_map]
  simp only [Nat.add_zero, Function.comp_def]
  rw [add_comm]
  congr 2
  funext m; congr 2; omega

lemma findF_shift {N : ℕ} {f : ℕ → ℕ} (h0 : f 0 = 0) :
    FE.findF (N + 1) f = FE.findF N (fun m => f (m + 1)) + 1 := by
  unfold FE.findF
  rw [List.range_succ_eq_map, List.find?_cons_of_neg (by simp [h0]), List.find?_map]
  change Option.getD (Option.map Nat.succ ((List.range N).find? (fun m => decide (f (m + 1) ≠ 0))))
    (N + 1) = _
  cases (List.range N).find? (fun m => decide (f (m + 1) ≠ 0)) <;> rfl

lemma ffind_succ {P : ℕ → Bool} {a n : ℕ} (ha : a < n) (hP : P a = false) :
    ffind P a n = ffind P (a + 1) n := by
  unfold ffind
  rw [show n - a = (n - (a + 1)) + 1 by omega, findF_shift (by simp [hP])]
  simp only [Nat.add_assoc, Nat.add_comm 1]

/-- **Scans by bounded search.** -/
theorem scan_eq_scanF {up down : ℕ → Bool} (hdis : ∀ k, ¬ (up k = true ∧ down k = true)) :
    ∀ m p c, ts.length - p = m → 1 ≤ c → scan ts up down p c = scanF ts up down p c := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro p c hm hc
    rw [scan_eq]
    by_cases hp : ts.length ≤ p
    · rw [if_pos hp]
      unfold scanF ffind
      rw [show ts.length - p = 0 by omega]
      have : FE.findF 0 = fun _ => 0 := by funext f; simp [FE.findF]
      rw [this, if_neg (by omega)]; omega
    rw [if_neg hp]
    have hd := hdis (tc ts p)
    have hplen : p < ts.length := by omega
    have cs : ∀ b, p ≤ b → cntP ts up p (b + 1) = (if up (tc ts p) then 1 else 0) +
        cntP ts up (p + 1) (b + 1) ∧ cntP ts down p (b + 1) = (if down (tc ts p) then 1 else 0) +
          cntP ts down (p + 1) (b + 1) := fun b hb =>
      ⟨cntP_succ_left _ (by omega), cntP_succ_left _ (by omega)⟩
    have c0 : ∀ P, cntP ts P (p + 1) (p + 1) = 0 := fun P => by simp [cntP]
    set P := fun q => decide (c + cntP ts up p (q + 1) ≤ cntP ts down p (q + 1))
    by_cases h0 : cstep up down (tc ts p) c = 0
    · rw [if_pos h0]
      have hu : up (tc ts p) = false := by
        by_contra hu; simp only [cstep, Bool.not_eq_false] at h0 hu; simp [hu] at h0
      have hdn : down (tc ts p) = true ∧ c = 1 := by
        unfold cstep at h0; rw [hu] at h0
        by_cases hdd : down (tc ts p) = true
        · simp [hdd] at h0; exact ⟨hdd, by omega⟩
        · simp [hdd] at h0; omega
      have hPp : P p = true := by
        simp only [P, decide_eq_true_eq]
        rw [(cs p le_rfl).1, (cs p le_rfl).2, c0, c0, hu, hdn.1, hdn.2]; simp
      have hf : ffind P p ts.length = p := ffind_eq le_rfl hplen hPp (fun j h1 h2 => by omega)
      unfold scanF
      rw [show (fun q => decide (c + cntP ts up p (q + 1) ≤ cntP ts down p (q + 1))) = P from rfl,
        hf, if_pos hplen]
    · rw [if_neg h0]
      set c' := cstep up down (tc ts p) c
      have hc'eq : c' = c + (if up (tc ts p) then 1 else 0) - (if down (tc ts p) then 1 else 0) ∧
          (if down (tc ts p) then 1 else 0) ≤ c + (if up (tc ts p) then 1 else 0) := by
        simp only [c', cstep] at h0 ⊢
        by_cases hu : up (tc ts p) = true
        · have : down (tc ts p) = false := by
            by_contra h'; exact hd ⟨hu, by simpa using h'⟩
          simp [hu, this]
        · by_cases hdd : down (tc ts p) = true
          · simp [hu, hdd] at h0 ⊢; omega
          · simp [hu, hdd]
      rw [ih _ (by omega) (p + 1) c' rfl (by omega)]
      have hPp : P p = false := by
        simp only [P, decide_eq_false_iff_not, not_le]
        rw [(cs p le_rfl).1, (cs p le_rfl).2, c0, c0]
        simp only [c', cstep] at h0
        by_cases hu : up (tc ts p) = true
        · simp [hu]; split_ifs <;> omega
        · by_cases hdd : down (tc ts p) = true
          · simp [hu, hdd] at h0 ⊢; omega
          · simp [hu, hdd] at h0 ⊢; omega
      have hf1 : ffind P p ts.length = ffind P (p + 1) ts.length := ffind_succ hplen hPp
      have hf2 : ffind P (p + 1) ts.length = ffind (fun q => decide (c' + cntP ts up (p + 1) (q + 1) ≤
          cntP ts down (p + 1) (q + 1))) (p + 1) ts.length := by
        unfold ffind
        congr 1
        refine FE.findF_congr fun m _ => ?_
        have e := cs (p + 1 + m) (by omega)
        have := hc'eq.2
        have key : (c + cntP ts up p (p + 1 + m + 1) ≤ cntP ts down p (p + 1 + m + 1)) ↔
            (c' + cntP ts up (p + 1) (p + 1 + m + 1) ≤ cntP ts down (p + 1) (p + 1 + m + 1)) := by
          rw [e.1, e.2, hc'eq.1]; omega
        simp only [P, key]
      have hge : p + 1 ≤ ffind P (p + 1) ts.length := by unfold ffind; omega
      unfold scanF
      rw [show (fun q => decide (c + cntP ts up p (q + 1) ≤ cntP ts down p (q + 1))) = P from rfl,
        hf1, ← hf2]
      split_ifs with hlt
      · rfl
      · omega

end LTok

end PathChecking
