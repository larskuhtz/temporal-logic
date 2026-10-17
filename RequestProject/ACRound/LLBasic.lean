module

public import RequestProject.LogLang.Out
public import RequestProject.Logspace.Concat

/-!
# Simple logspace functions written in the loop language

* `x ↦ x.flatMap g ++ s` for a fixed `g : Bool → List Bool` and suffix `s`;
* `x ↦ x.tail`;
* `x ↦ [x ≠ [], head of x]`.
-/

@[expose] public section

namespace PathChecking

namespace LL

/-- The code of an optional input bit (as read by `Ex.inp`): `1`, `0`, or `3` past the end. -/
def bitCode : Option Bool → ℕ
  | some true => 1
  | some false => 0
  | none => 3

lemma symNum_inputSym_succ (z : Word) (k : ℕ) : symNum (inputSym z (k + 1)) = bitCode z[k]? := by
  unfold inputSym
  rw [if_neg (by omega), show k + 1 - 1 = k by omega]
  rcases z[k]? with _ | ⟨_ | _⟩ <;> rfl

lemma bitCode_eq_one (o : Option Bool) : bitCode o = 1 ↔ o = some true := by
  rcases o with _ | ⟨_ | _⟩ <;> simp [bitCode]

lemma bitCode_eq_zero (o : Option Bool) : bitCode o = 0 ↔ o = some false := by
  rcases o with _ | ⟨_ | _⟩ <;> simp [bitCode]

lemma len_lt_cap2 (w : Word) : 2 * w.length + 4 < capOf 2 w := by
  unfold capOf; nlinarith

lemma flatMap_range_getD {α β : Type*} (x : List α) (g : α → List β) (d : α) :
    (List.range x.length).flatMap (fun i => g (x[i]?.getD d)) = x.flatMap g := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.flatMap_cons, ← ih]
    simp [Function.comp_def]

/-! ## Bit maps -/

/-- `x ↦ x.flatMap g ++ s`. -/
def bitMapProg (g : Bool → List Bool) (s : List Bool) : Pr 1 :=
  .seq (.loop 0 .len (.ite (.bin .eq (.inp (.bin .add (.v 0) (.c 1))) (.c 1))
    (outW (g true)) (outW (g false)))) (outW s)

lemma bitMapProg_output (g : Bool → List Bool) (s : List Bool) (x : Word) :
    (bitMapProg g s).output 2 x = x.flatMap g ++ s := by
  have hC := len_lt_cap2 x
  unfold Pr.output bitMapProg
  simp only [run_seq, run_outW]
  set C := capOf 2 x
  have h := run_loop_spec (V := 1) (w := x) (C := C) 0 .len
    (.ite (.bin .eq (.inp (.bin .add (.v 0) (.c 1))) (.c 1)) (outW (g true)) (outW (g false)))
    (fun _ => 0) (fun _ _ => True) (fun i => g (x[i]?.getD false)) trivial (by
      intro i hi ρ' _
      refine ⟨trivial, ?_⟩
      simp only [eval_len] at hi
      have hi' : i < x.length := by omega
      rw [run_ite]
      simp only [eval_bin, ap_eq, eval_inp, ap_add, eval_v, Function.update_self, eval_c]
      rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (show i + 1 ≤ C by omega)]
      rw [symNum_inputSym_succ, List.getElem?_eq_getElem hi']
      cases x[i] <;> simp [bitCode])
  rw [h.2]
  simp only [eval_len]
  rw [min_eq_left (by omega)]
  congr 1
  exact flatMap_range_getD x g false

/-- The program for `x ↦ x.tail`. -/
def tailProg : Pr 1 :=
  .loop 0 .len (.ite (.bin .eq (.v 0) (.c 0)) .skip
    (.ite (.bin .eq (.inp (.bin .add (.v 0) (.c 1))) (.c 1)) (outW [true]) (outW [false])))

lemma tailProg_output (x : Word) : tailProg.output 2 x = x.tail := by
  have hC := len_lt_cap2 x
  unfold Pr.output tailProg
  set C := capOf 2 x
  have h := run_loop_spec (V := 1) (w := x) (C := C) 0 .len
    (.ite (.bin .eq (.v 0) (.c 0)) .skip
      (.ite (.bin .eq (.inp (.bin .add (.v 0) (.c 1))) (.c 1)) (outW [true]) (outW [false])))
    (fun _ => 0) (fun _ _ => True)
    (fun i => if i = 0 then [] else [x[i]?.getD false]) trivial (by
      intro i hi ρ' _
      refine ⟨trivial, ?_⟩
      simp only [eval_len] at hi
      have hi' : i < x.length := by omega
      rw [run_ite]
      simp only [eval_bin, ap_eq, eval_v, Function.update_self, eval_c]
      rw [min_eq_left (show 0 ≤ C by omega)]
      by_cases h0 : i = 0
      · simp [h0]
      · rw [if_neg (by simp [h0]), if_neg h0, run_ite]
        simp only [eval_bin, ap_eq, eval_inp, ap_add, eval_v, Function.update_self, eval_c]
        rw [min_eq_left (show 1 ≤ C by omega), min_eq_left (show i + 1 ≤ C by omega)]
        rw [symNum_inputSym_succ, List.getElem?_eq_getElem hi']
        cases x[i] <;> simp [bitCode])
  rw [h.2]
  simp only [eval_len]
  rw [min_eq_left (by omega)]
  rcases x with _ | ⟨a, x⟩
  · rfl
  · rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [if_true, List.nil_append, Function.comp_def, Nat.succ_ne_zero, if_false,
      List.getElem?_cons_succ, List.tail_cons]
    rw [flatMap_range_getD x (fun b => [b]) false, LS.flatMap_single]

/-- The program for `x ↦ [x ≠ [], head of x]`. -/
def head2Prog : Pr 1 :=
  .seq (.out (.bin .lt (.c 0) .len)) (.out (.bin .eq (.inp (.c 1)) (.c 1)))

/-- `[x ≠ [], head of x]` -/
def head2 (x : Word) : Word := [!x.isEmpty, x.headD false]

lemma head2Prog_output (x : Word) : head2Prog.output 2 x = head2 x := by
  have hC := len_lt_cap2 x
  unfold Pr.output head2Prog head2
  set C := capOf 2 x
  simp only [run_seq, run_out, eval_bin, ap_lt, eval_c, eval_len, ap_eq, eval_inp]
  have e0 : min 0 C = 0 := min_eq_left (by omega)
  have e1 : min x.length C = x.length := min_eq_left (by omega)
  have e2 : min 1 C = 1 := min_eq_left (by omega)
  simp only [e0, e1, e2]
  rcases x with _ | ⟨a, x⟩
  · simp [inputSym, symNum]
  · cases a <;> simp [inputSym, symNum]

end LL

open LL

theorem LogspaceComputable.bitMap (g : Bool → List Bool) (s : List Bool) :
    LogspaceComputable (fun x => x.flatMap g ++ s) :=
  logspaceComputable_of_output 2 (bitMapProg g s) _ (bitMapProg_output g s)

theorem LogspaceComputable.tail : LogspaceComputable List.tail :=
  logspaceComputable_of_output 2 tailProg _ tailProg_output

theorem LogspaceComputable.head2 : LogspaceComputable LL.head2 :=
  logspaceComputable_of_output 2 head2Prog _ head2Prog_output

end PathChecking
