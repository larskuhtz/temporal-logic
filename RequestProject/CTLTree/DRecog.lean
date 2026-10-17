module

public import RequestProject.Shallow.Prog.DProg

/-!
# A logspace recognizer of CTL* instances without branching bound

`recProg` decodes its input `pack w 0 []` and outputs whether `w` encodes a nonempty token list
`ts` with `recog ts (|ts| + 1)`, i.e. (by `recog_iff`) an instance `( φ ) t` of CTL* tree
checking (the branching bound `|ts| + 1` is never restrictive).  It reuses the counter-based
recognizer of `RequestProject/Shallow/Prog/DRec.lean`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

/-- The checks after decoding: `recog ts (|ts| + 1)`. -/
def mainV : Pr V :=
  .seq (.set vD (.bin .add (.v vL) (.c 1))) (.seq recP (.set vRes (.v vRC)))

lemma sp_mainV {C : ℕ} {ts : List Tok} {q : ℕ} {a : List Bool} {ρ : Fin V → ℕ}
    (hE : Env ts q a C ρ) (hL1 : 1 ≤ ts.length) :
    Sp (pack (encodeToks ts) q a) C mainV ρ allW []
      (fun r => r vRes = if recog ts (ts.length + 1) then 1 else 0) := by
  set x := pack (encodeToks ts) q a
  have hC := hE.len_le
  unfold mainV
  refine sp_seqE (o1 := []) (o2 := []) (sp_set (Q := fun r => r = Function.update ρ vD
    (ts.length + 1)) (by decide) (by
      simp [hE.hL, min_eq_left (show ts.length + 1 ≤ C by omega),
        min_eq_left (show 1 ≤ C by omega)])) (fun r1 _ h1 => ?_) rfl
  subst h1
  have hE1 : Env ts q a C (Function.update ρ vD (ts.length + 1)) :=
    hE.congr (by simp (disch := decide) [Function.update_of_ne])
      (by simp (disch := decide) [Function.update_of_ne])
  refine sp_seqE (o1 := []) (o2 := []) ((sp_recP hE1 hL1 (by simp; omega)).frame.mono
    (W' := allW) (by decide) (fun _ _ h => h)) (fun r2 _ h2 => ?_) rfl
  obtain ⟨⟨h2R, -⟩, -⟩ := h2
  refine sp_set (by decide) ?_
  simp only [Function.update_self, eval_v, h2R, Function.update_self]

/-- The recognizer program. -/
def recProg : Pr V := .seq dPro (.seq (.ite okE mainV .skip) (.out (.v vRes)))

/-- **Specification of the recognizer.** -/
theorem recProg_spec (w : Word) : ∃ b : Bool, recProg.output 4 (pack w 0 []) = [b] ∧
    (b = true ↔ ∃ ts : List Tok, w = encodeToks ts ∧ ts ≠ [] ∧ recog ts (ts.length + 1) = true) := by
  have hxlen := pack_length w 0 [] (Nat.zero_le _)
  set x := pack w 0 [] with hx
  set C := capOf 4 x with hCdef
  have hC : 2 * x.length + 40 ≤ C := by
    rcases Nat.lt_or_ge x.length 3 with h | h
    · simp only [C, capOf]
      have : 3 ^ 4 ≤ (x.length + 2) ^ 4 := Nat.pow_le_pow_left (by omega) 4
      omega
    · exact cap_big _ 0 h
  obtain ⟨r1, hr1, -, hN, hL, hB, hR⟩ := sp_dPro (a := []) (ρ := fun _ => 0) hC
  have hok := eval_okE (x := x) (C := C) (by omega) hN hL hB
  show ∃ b, (Pr.run x C recProg (fun _ => 0)).2 = [b] ∧ _
  rw [recProg, run_seq, hr1]
  simp only [run_seq, run_out, List.nil_append]
  by_cases hd : decOK w
  · rw [run_ite_pos (by rw [hok, if_pos hd]; omega)]
    obtain ⟨ts, hw, hne⟩ := decode_of_decOK hd
    have hL1 : 1 ≤ ts.length := List.length_pos_iff.2 hne
    have hwl : w.length = 5 * ts.length := by rw [hw, encodeToks_length]
    have hE : Env ts 0 [] C r1 := ⟨Nat.zero_le _, by rw [← hw]; exact hC, by rw [hN, hwl],
      by rw [hL, hwl]; omega⟩
    have hsp := sp_mainV hE hL1
    rw [show pack (encodeToks ts) 0 [] = x by rw [hx, hw]] at hsp
    obtain ⟨r2, hr2, -, hres⟩ := hsp
    rw [hr2]
    simp only [List.nil_append, eval_v, hres]
    refine ⟨_, rfl, ?_⟩
    simp only [decide_eq_true_eq]
    constructor
    · intro h
      refine ⟨ts, hw, hne, ?_⟩
      by_contra hc; simp [hc] at h
    · rintro ⟨us, hus, -, hr⟩
      rw [hw] at hus
      rw [← MCVPReduction.encodeToks_injective hus] at hr
      simp [hr]
  · rw [run_ite_neg (by rw [hok, if_neg hd])]
    simp only [run_skip, List.nil_append, eval_v, hR]
    refine ⟨_, rfl, ?_⟩
    simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, false_iff, not_exists,
      not_and]
    intro ts hw hne
    exact absurd (hw ▸ decOK_encode hne) hd

/-- The recognizer is logspace computable. -/
theorem recProg_logspace : LogspaceComputable (fun x => recProg.output 4 x) :=
  logspaceComputable_of_output 4 recProg _ (fun _ => rfl)

end SQ

end PathChecking
