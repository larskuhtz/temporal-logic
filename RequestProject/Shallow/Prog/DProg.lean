module

public import RequestProject.Shallow.Prog.DMain

/-!
# The decision program and its specification

`dProg k` decodes the input, runs `mainP k` on valid inputs and outputs the result bit;
`dProg_spec` proves the specification `DSpecOK k`, and `exists_DProg` the existence of a
logspace decision function.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

/-- Reading `|w|`, the number of tokens, and checking the token blocks. -/
def dPro : Pr V :=
  .seq lenP (.seq (.set vL (.bin .div (.v vN) (.c 5))) (.seq badP (.set vRes (.c 0))))

/-- The input is the encoding of a nonempty token list. -/
def okE : Ex V :=
  .bin .mul (.bin .mul (.bin .eq (.bin .mod (.v vN) (.c 5)) (.c 0)) (.bin .eq (.v vBad) (.c 0)))
    (.bin .lt (.c 0) (.v vL))

instance (w : Word) : Decidable (decOK w) := by unfold decOK; infer_instance

/-- The decision program. -/
def dProg (k : ℕ) : Pr V := .seq dPro (.seq (.ite okE (mainP k) .skip) (.out (.v vRes)))

lemma sp_dPro {w : Word} {a : List Bool} {C : ℕ} {ρ : Fin V → ℕ}
    (hC : 2 * (pack w 0 a).length + 40 ≤ C) :
    Sp (pack w 0 a) C dPro ρ allW [] (fun r => r vN = w.length ∧ r vL = w.length / 5 ∧
      r vBad = (if ∀ p < w.length / 5, chunk w p < 29 then 0 else 1) ∧ r vRes = 0) := by
  have hlen := pack_length w 0 a (Nat.zero_le _)
  unfold dPro
  refine sp_seqE (o1 := []) (o2 := []) ((sp_lenP (ρ := ρ) (Nat.zero_le _) hC).mono
    (W' := allW) (by decide) (fun _ _ h => h)) (fun r1 _ h1 => ?_) rfl
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update r1 vL
    (w.length / 5)) (by decide) (by simp [h1, min_eq_left (show 5 ≤ C by omega)]))
    (fun r2 _ h2 => ?_) rfl
  subst h2
  refine sp_seqE (o1 := []) (o2 := []) ((sp_badP (Nat.zero_le _) hC
    (by simp (disch := decide) [Function.update_of_ne, h1]) (by simp)).frame.mono
    (W' := allW) (by decide) (fun _ _ h => h)) (fun r3 _ h3 => ?_) rfl
  obtain ⟨h3B, h3f⟩ := h3
  refine sp_set (by decide) ⟨?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (by decide), h3f vN (by decide)]
    simp (disch := decide) [Function.update_of_ne, h1]
  · rw [Function.update_of_ne (by decide), h3f vL (by decide)]
    simp
  · rw [Function.update_of_ne (by decide), h3B]
  · simp

lemma eval_okE {x : Word} {C : ℕ} {r : Fin V → ℕ} {w : Word} (hC : 5 ≤ C)
    (hN : r vN = w.length) (hL : r vL = w.length / 5)
    (hB : r vBad = (if ∀ p < w.length / 5, chunk w p < 29 then 0 else 1)) :
    okE.eval x C r = if decOK w then 1 else 0 := by
  simp only [okE, eval_bin, ap_mul, ap_eq, ap_mod, ap_lt, eval_v, eval_c, hN, hL, hB,
    min_eq_left hC, decOK, Nat.zero_min]
  by_cases h3 : ∀ p < w.length / 5, chunk w p < 29
  · simp only [eq_true h3, if_true, and_true]
    by_cases h1 : w.length % 5 = 0 <;> by_cases h2 : 0 < w.length / 5 <;> simp [h1, h2] <;> omega
  · simp only [eq_false h3, if_false, and_false]
    simp

/-- **The decision program meets its specification.** -/
theorem dProg_spec (k : ℕ) : DSpecOK k (fun x => (dProg k).output (k + 4) x) := by
  intro w a ha
  have ha1 : 1 ≤ a.length := by rw [ha]; exact Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hxlen := pack_length w 0 a (Nat.zero_le _)
  set x := pack w 0 a with hx
  set C := capOf (k + 4) x with hCdef
  have hC : 2 * x.length + 40 ≤ C := cap_big _ _ (by omega)
  obtain ⟨r1, hr1, -, hN, hL, hB, hR⟩ := sp_dPro (ρ := fun _ => 0) hC
  have hok := eval_okE (x := x) (C := C) (by omega) hN hL hB
  show (Pr.run x C (dProg k) (fun _ => 0)).2 = [true] ↔ _
  rw [dProg, run_seq, hr1]
  simp only [run_seq, run_out, List.nil_append]
  by_cases hd : decOK w
  · rw [run_ite_pos (by rw [hok, if_pos hd]; omega)]
    obtain ⟨ts, hw, hne⟩ := decode_of_decOK hd
    have hL1 : 1 ≤ ts.length := List.length_pos_iff.2 hne
    have hwl : w.length = 5 * ts.length := by rw [hw, encodeToks_length]
    have hE : Env ts 0 a C r1 := ⟨Nat.zero_le _, by rw [← hw]; exact hC, by rw [hN, hwl],
      by rw [hL, hwl]; omega⟩
    have ha' : (ts.length + 1) ^ 3 ≤ a.length := by
      rw [ha]; exact Nat.pow_le_pow_left (by omega) 3
    have hlog : Nat.log 2 (5 * ts.length) ≤ x.length := by
      have := Nat.log_le_self 2 (5 * ts.length); omega
    have hCk : (Nat.log 2 (5 * ts.length) + 1) ^ k + k + 1 ≤ C := cap_big' _ _ _ hlog
    have hsp := sp_mainP k hE hL1 ha' hCk
    rw [show pack (encodeToks ts) 0 a = x by rw [hx, hw]] at hsp
    obtain ⟨r2, hr2, -, hres⟩ := hsp
    rw [hr2]
    simp only [List.nil_append, eval_v, hres, List.cons.injEq, and_true, decide_eq_true_eq]
    rw [show ((if (recog ts ((Nat.log 2 (5 * ts.length) + 1) ^ k) && decide (∀ ℓ < ts.length + 1,
        ansF (ts.length + 1) a (fend ts 1 + 1) ℓ 1 = true)) = true then 1 else 0) ≠ 0) ↔
        (recog ts ((Nat.log 2 (5 * ts.length) + 1) ^ k) = true ∧ ∀ ℓ < ts.length + 1,
          ansF (ts.length + 1) a (fend ts 1 + 1) ℓ 1 = true) by
      split_ifs with h <;> simp_all]
    rw [recog_iff]
    subst hw
    constructor
    · rintro ⟨⟨φ, t, hts, hsb⟩, hans⟩
      refine ⟨φ, t, by rw [hts]; rfl, ?_, ?_⟩
      · rw [shallowBound, encodeToks_length]; exact hsb
      · rw [← show ts = instToks φ t from hts]
        exact hans
    · rintro ⟨φ, t, hts, hsb, hans⟩
      have hts' : ts = instToks φ t := MCVPReduction.encodeToks_injective hts
      rw [shallowBound, encodeToks_length] at hsb
      refine ⟨⟨φ, t, hts', hsb⟩, ?_⟩
      rw [hts']
      exact hans
  · rw [run_ite_neg (by rw [hok, if_neg hd])]
    simp only [run_skip, List.nil_append, eval_v, hR]
    simp only [ne_eq, not_true_eq_false, decide_false, List.cons.injEq, Bool.false_eq_true,
      and_true, false_iff, not_exists, not_and]
    intro φ t hw
    exact absurd (hw ▸ decOK_encode (by simp [instToks])) hd

/-- The decision function of the round algorithm is logspace. -/
theorem exists_DProg (k : ℕ) :
    ∃ D : Word → Word, LogspaceComputable D ∧ DSpecOK k D :=
  ⟨_, logspaceComputable_of_output (k + 4) (dProg k) _ (fun _ => rfl), dProg_spec k⟩

end SQ

end PathChecking
