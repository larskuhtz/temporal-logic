module

public import RequestProject.Shallow.Prog.DDec
public import RequestProject.Shallow.Prog.QMain

/-!
# The decision function of the round algorithm

`dProg k` reads the packed input `pack w 0 a`, checks that `w` encodes an instance whose tree
has branching depth `< (⌊log₂ |w|⌋ + 1)^k`, and that all answers of the last round for the root
are true; `exists_DProg` shows that this gives a logspace function with the specification
`DSpecOK k`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}

/-- the result of the answer check -/
abbrev vAns : Fin V := 50
/-- the result of the decision -/
abbrev vRes : Fin V := 46

/-! ## The answers for the root -/

/-- One step of the answer check. -/
def ansBody : Pr V := .ite (ansE (.v vR0) (.v aI) (.c 1)) .skip (.set vAns (.c 0))

/-- `vAns := 1` iff all answers `A (vR0) ℓ 1` are true. -/
def ansP : Pr V := .seq (.set vAns (.c 1)) (.loop aI (.v vNq) ansBody)

lemma sp_ansP (hE : Env ts q a C ρ) (hM : ρ vNq = ts.length + 1)
    (ha : (ts.length + 1) ^ 3 ≤ a.length) :
    Sp (pack (encodeToks ts) q a) C ansP ρ [vAns, aI] []
      (fun r => r vAns = if ∀ ℓ < ts.length + 1, ansF (ts.length + 1) a (ρ vR0) ℓ 1 = true
        then 1 else 0) := by
  have hC := hE.len_le
  unfold ansP
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vAns 1)
    (by decide) (by simp [min_eq_left (show 1 ≤ C by omega)])) (fun ρ1 _ h1 => ?_) rfl
  subst h1
  have := sp_loop_inv (x := pack (encodeToks ts) q a) (C := C) aI (.v vNq) ansBody
    (Function.update ρ vAns 1) [vAns, aI]
    (fun k r => r vAns = if ∀ ℓ < k, ansF (ts.length + 1) a (ρ vR0) ℓ 1 = true then 1 else 0)
    (by decide) (by simp) (fun k hk r fr hI => by
      simp only [eval_v, Function.update_of_ne (show vNq ≠ vAns by decide), hM] at hk
      have hE' : Env ts q a C (Function.update r aI k) := hE.congr
        (by rw [Function.update_of_ne (by decide), fr vN (by decide),
          Function.update_of_ne (by decide)])
        (by rw [Function.update_of_ne (by decide), fr vL (by decide),
          Function.update_of_ne (by decide)])
      have hM' : (Function.update r aI k) vNq = ts.length + 1 := by
        rw [Function.update_of_ne (by decide), fr vNq (by decide),
          Function.update_of_ne (by decide), hM]
      have hR0 : (Function.update r aI k) vR0 = ρ vR0 := by
        rw [Function.update_of_ne (by decide), fr vR0 (by decide),
          Function.update_of_ne (by decide)]
      have hev := eval_ansE hE' hM' ha (.v vR0) (.v aI) (.c 1)
      simp only [eval_v, eval_c, Function.update_self, hR0,
        min_eq_left (show 1 ≤ C by omega)] at hev
      unfold ansBody
      by_cases hk' : ansF (ts.length + 1) a (ρ vR0) k 1 = true
      · refine sp_ite_pos (by rw [hev, if_pos hk']; omega) (sp_skip ?_)
        beta_reduce
        rw [Function.update_of_ne (by decide), hI]
        congr 1
        apply propext
        constructor
        · intro h ℓ hℓ
          rcases Nat.lt_succ_iff_lt_or_eq.1 hℓ with hℓ | rfl
          · exact h ℓ hℓ
          · exact hk'
        · intro h ℓ hℓ; exact h ℓ (by omega)
      · refine sp_ite_neg (by rw [hev, if_neg hk']) (sp_set (by decide) ?_)
        beta_reduce
        rw [Function.update_self, if_neg (fun h => hk' (h k (by omega)))]
        simp)
  refine this.mono (fun _ h => h) (fun r _ h => ?_)
  rw [h]
  simp (disch := decide) [Function.update_of_ne, hM]

/-! ## The main part -/

lemma ite_mul_aux {C : ℕ} (r : Bool) (Q : Prop) [Decidable Q] (hC : 1 ≤ C) :
    min ((if r = true then 1 else 0) * (if Q then 1 else 0)) C =
      if (r && decide Q) = true then 1 else 0 := by
  cases r <;> by_cases hQ : Q <;> simp [hQ]; omega

/-- The checks after decoding. -/
def mainP (k : ℕ) : Pr V :=
  .seq logP (.seq (powP k) (.seq recP (.seq (.seq (.set vNq (.bin .add (.v vL) (.c 1)))
    (.set vR0 (.bin .add (.v vFE) (.c 1)))) (.seq ansP (.set vRes (.bin .mul (.v vRC) (.v vAns)))))))

/-- All variables. -/
abbrev allW : List (Fin V) := List.finRange V

lemma sp_mainP (k : ℕ) (hE : Env ts q a C ρ) (hL1 : 1 ≤ ts.length)
    (ha : (ts.length + 1) ^ 3 ≤ a.length)
    (hCk : (Nat.log 2 (5 * ts.length) + 1) ^ k + k + 1 ≤ C) :
    Sp (pack (encodeToks ts) q a) C (mainP k) ρ allW []
      (fun r => r vRes = if (recog ts ((Nat.log 2 (5 * ts.length) + 1) ^ k) &&
        decide (∀ ℓ < ts.length + 1, ansF (ts.length + 1) a (fend ts 1 + 1) ℓ 1 = true)) = true
        then 1 else 0) := by
  set x := pack (encodeToks ts) q a
  set b := (Nat.log 2 (5 * ts.length) + 1) ^ k
  have hC := hE.len_le
  unfold mainP
  refine sp_seqE (o1 := []) (o2 := []) ((sp_logP (x := x) (ρ := ρ) (C := C)
    (by rw [hE.hN]; omega)).frame.mono (W' := allW) (by decide) (fun _ _ h => h))
    (fun r1 _ h1 => ?_) rfl
  obtain ⟨h1G, h1f⟩ := h1
  have hE1 : Env ts q a C r1 := hE.of_frame h1f (by decide) (by decide)
  rw [hE.hN] at h1G
  refine sp_seqE (o1 := []) (o2 := []) ((sp_powP (x := x) (ρ := r1) (C := C) k
    (by rw [h1G]; exact hCk)).frame.mono (W' := allW) (by decide) (fun _ _ h => h))
    (fun r2 _ h2 => ?_) rfl
  obtain ⟨h2D, h2f⟩ := h2
  have hE2 : Env ts q a C r2 := hE1.of_frame h2f (by decide) (by decide)
  rw [h1G] at h2D
  have hb2 : r2 vD + 2 ≤ C := by
    rw [h2D]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp; omega
    · omega
  refine sp_seqE (o1 := []) (o2 := []) ((sp_recP hE2 hL1 hb2).frame.mono (W' := allW)
    (by decide) (fun _ _ h => h)) (fun r3 _ h3 => ?_) rfl
  obtain ⟨⟨h3R, h3F⟩, h3f⟩ := h3
  rw [h2D] at h3R
  have hE3 : Env ts q a C r3 := hE2.of_frame h3f (by decide) (by decide)
  have hfL : fend ts 1 ≤ ts.length := fend_le' ts hL1
  refine sp_seqE (o1 := []) (o2 := []) (sp_set2 (W := allW) (a := vNq) (b := vR0)
    (e1 := .bin .add (.v vL) (.c 1)) (e2 := .bin .add (.v vFE) (.c 1)) (ρ := r3) (x := x) (C := C)
    (Q := fun r => r = Function.update (Function.update r3 vNq (ts.length + 1)) vR0
      (fend ts 1 + 1)) (by decide) (by decide) (by
        simp (disch := first | decide | omega) [Function.update_of_ne, hE3.hL, h3F,
          ])) (fun r4 _ h4 => ?_) rfl
  subst h4
  set r4 := Function.update (Function.update r3 vNq (ts.length + 1)) vR0 (fend ts 1 + 1)
  have hE4 : Env ts q a C r4 := hE3.congr (by simp (disch := decide) [r4, Function.update_of_ne])
    (by simp (disch := decide) [r4, Function.update_of_ne])
  refine sp_seqE (o1 := []) (o2 := []) ((sp_ansP hE4 (by simp (disch := decide)
    [r4, Function.update_of_ne]) ha).frame.mono (W' := allW) (by decide) (fun _ _ h => h))
    (fun r5 _ h5 => ?_) rfl
  obtain ⟨h5A, h5f⟩ := h5
  have h5R : r5 vRC = if recog ts b then 1 else 0 := by
    rw [h5f vRC (by decide)]; simp (disch := decide) [r4, Function.update_of_ne, h3R, b]
  simp only [r4, Function.update_self] at h5A
  refine sp_set (by decide) ?_
  simp only [Function.update_self, eval_bin, ap_mul, eval_v, h5A, h5R]
  exact ite_mul_aux _ _ (by omega)

end SQ

end PathChecking
