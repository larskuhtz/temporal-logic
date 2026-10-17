module

public import RequestProject.ACRound.LangF
public import RequestProject.ACRound.TagMap

/-!
# The checker program for `LangF`, and `LangF f ∈ L`
-/

@[expose] public section

namespace PathChecking

open Classical

/-- The answer for `x = b :: 1^i 0 u` and `y = f u`. -/
def e3F (x y : Word) : Bool :=
  if false ∈ x.tail then
    (if x.headD false then decide (y.length = x.tail.idxOf false)
      else y.getD (x.tail.idxOf false) false)
  else false

lemma charWord_LangF (f : Word → Word) (x : Word) :
    charWord (LangF f) x = [e3F x (f (sfxF x))] := by
  unfold charWord e3F
  congr 1
  rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_LangF_iff]
  constructor
  · rintro ⟨b, t, rfl, ht, h⟩
    simp only [List.tail_cons, ht, if_true, List.headD_cons]
    cases b <;> simpa using h
  · intro h
    rcases x with _ | ⟨b, t⟩
    · simp at h
    · simp only [List.tail_cons, List.headD_cons] at h
      by_cases ht : false ∈ t
      · rw [if_pos ht] at h
        refine ⟨b, t, rfl, ht, ?_⟩
        cases b <;> simpa using h
      · rw [if_neg ht] at h; simp at h

namespace LL

/-- Body of the checker loop. Variables: `0` pair index `p`, `1` end of `x`, `2` position of
the first `0` of `x` after the head (plus one), `3` end seen. -/
def e3Body : Pr 4 :=
  .ite (.bin .eq (.v 3) (.c 0))
    (.ite (.bin .eq (rd (.bin .add (.v 0) (.v 0))) (.c 0))
      (.seq (.set 1 (.v 0)) (.set 3 (.c 1)))
      (.ite (.bin .lt (.c 0) (.v 0))
        (.ite (.bin .eq (.v 2) (.c 0))
          (.ite (.bin .eq (rd (.bin .add (.bin .add (.v 0) (.v 0)) (.c 1))) (.c 0))
            (.set 2 (.bin .add (.v 0) (.c 1))) .skip) .skip) .skip))
    .skip

/-- The checker program. -/
def e3Prog : Pr 4 :=
  .seq (.loop 0 .len e3Body)
    (.ite (.v 2)
      (.ite (.bin .eq (rd (.c 1)) (.c 1))
        (.out (.bin .eq (.bin .sub (.bin .sub .len (.bin .add (.v 1) (.v 1))) (.c 2))
          (.bin .sub (.v 2) (.c 2))))
        (.out (.bin .eq (rd (.bin .add (.bin .add (.bin .add (.v 1) (.v 1)) (.c 2))
          (.bin .sub (.v 2) (.c 2)))) (.c 1))))
      (.out (.c 0)))

lemma idxOf_eq_of_not_mem_take (l : List Bool) (k : ℕ) (hk : k < l.length)
    (h1 : false ∉ l.take k) (h2 : l[k] = false) : l.idxOf false = k := by
  induction l generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    rcases k with _ | k
    · simp at h2; subst h2; simp
    · have ha : a = true := by
        cases a
        · simp at h1
        · rfl
      subst ha
      simp only [List.take_succ_cons, List.mem_cons, Bool.false_eq_true, false_or] at h1
      rw [List.idxOf_cons_ne _ (by decide), ih k (by simpa using hk) h1 (by simpa using h2)]

/-- The value of variable `2` after reading the first `k` pairs. -/
def kkOf (x : Word) (k : ℕ) : ℕ :=
  if false ∈ (x.take k).tail then x.tail.idxOf false + 2 else 0

lemma e3Prog_output (x y : Word) :
    e3Prog.output 2 (x.flatMap dupB ++ [false, false] ++ y) = [e3F x y] := by
  set z := x.flatMap dupB ++ [false, false] ++ y with hz
  have hdl := dup_length x
  have hzl : z.length = 2 * x.length + 2 + y.length := by
    simp [hz, hdl]; omega
  have hC := len_lt_cap2 z
  unfold Pr.output e3Prog
  set C := capOf 2 z
  have zA : ∀ p < x.length, z[2 * p]? = some true := by
    intro p hp
    rw [hz, List.append_assoc, List.getElem?_append_left (by omega), dup_get_even, if_pos hp]
  have zB : ∀ p < x.length, z[2 * p + 1]? = x[p]? := by
    intro p hp
    rw [hz, List.append_assoc, List.getElem?_append_left (by omega), dup_get_odd]
  have zC : z[2 * x.length]? = some false := by
    rw [hz, List.append_assoc, List.getElem?_append_right (by omega), hdl]; simp
  have zD : ∀ j, z[2 * x.length + 2 + j]? = y[j]? := by
    intro j
    rw [hz, List.getElem?_append_right (by simp [hdl])]
    simp [hdl]
  rw [run_seq]
  have hloop := run_loop_spec (V := 4) (w := z) (C := C) 0 .len e3Body (fun _ => 0)
    (fun p ρ => ρ 3 = (if x.length < p then 1 else 0) ∧ ρ 2 = kkOf x (min p x.length) ∧
      (x.length < p → ρ 1 = x.length))
    (fun _ => []) (by simp [kkOf]) (by
      intro p hp ρ' ⟨h3, h2, h1⟩
      simp only [eval_len] at hp
      have hpz : p < z.length := by omega
      set ρ := Function.update ρ' 0 p with hρ
      have r0 : ρ 0 = p := by simp [hρ]
      have r1 : ρ 1 = ρ' 1 := by simp [hρ]
      have r2 : ρ 2 = ρ' 2 := by simp [hρ]
      have r3 : ρ 3 = ρ' 3 := by simp [hρ]
      have e0 : min 0 C = 0 := min_eq_left (by omega)
      have e1 : min 1 C = 1 := min_eq_left (by omega)
      have ev2p : (rd (.bin .add (.v 0) (.v 0)) : Ex 4).eval z C ρ = bitCode z[2 * p]? :=
        eval_rd z C ρ _ (2 * p) (by simp [r0]; omega) (by omega)
      have ev2p1 : (rd (.bin .add (.bin .add (.v 0) (.v 0)) (.c 1)) : Ex 4).eval z C ρ =
          bitCode z[2 * p + 1]? :=
        eval_rd z C ρ _ (2 * p + 1) (by simp [r0, e1]; omega) (by omega)
      unfold e3Body
      rw [run_ite]
      simp only [eval_bin, ap_eq, eval_v, r3, h3, eval_c, e0]
      rcases Nat.lt_trichotomy x.length p with hxp | hxp | hxp
      · -- past the end
        simp only [if_pos hxp, one_ne_zero, if_false, ne_eq, not_true_eq_false, run_skip]
        refine ⟨⟨by simp [hρ, h3, hxp]; omega, ?_, fun _ => by simp [hρ, h1 hxp]⟩, by simp⟩
        rw [r2, h2, min_eq_right (by omega), min_eq_right (by omega)]
      · -- the separator
        subst hxp
        simp only [lt_irrefl, if_false, if_true, ne_eq, one_ne_zero, not_false_eq_true]
        rw [run_ite_pos (by simp [ev2p, zC, bitCode])]
        simp only [run_seq, run_set, eval_v, eval_c, r0]
        refine ⟨⟨by simp [e1], ?_, fun _ => by simp⟩, by simp⟩
        simp only [Function.update_apply, show (2 : Fin 4) ≠ 3 by decide,
          show (2 : Fin 4) ≠ 1 by decide, if_false]
        rw [r2, h2, min_eq_right (by omega), min_eq_right (by omega)]
      · -- a data pair
        simp only [if_neg (show ¬ x.length < p by omega), if_true, ne_eq, one_ne_zero,
          not_false_eq_true]
        rw [run_ite_neg (by simp [ev2p, zA p hxp, bitCode])]
        rw [min_eq_left (show p ≤ x.length by omega)] at h2
        rw [min_eq_left (show p + 1 ≤ x.length by omega)]
        have hk3 : ∀ ρ'' : Fin 4 → ℕ, ρ'' 3 = ρ 3 → ρ'' 1 = ρ 1 →
            ρ'' 3 = (if x.length < p + 1 then 1 else 0) ∧
            (x.length < p + 1 → ρ'' 1 = x.length) := by
          intro ρ'' a b
          refine ⟨by rw [a, r3, h3, if_neg (by omega), if_neg (by omega)], fun h => by omega⟩
        rw [run_ite]
        simp only [eval_bin, ap_lt, eval_c, e0, eval_v, r0]
        by_cases hp0 : p = 0
        · subst hp0
          simp only [lt_irrefl, if_false, ne_eq, not_true_eq_false, run_skip]
          obtain ⟨a, b⟩ := hk3 ρ rfl rfl
          refine ⟨⟨a, ?_, b⟩, by simp⟩
          rw [r2, h2]
          rcases x with _ | ⟨c, x⟩ <;> simp [kkOf]
        · simp only [show 0 < p by omega, if_true, ne_eq, one_ne_zero, not_false_eq_true]
          rw [run_ite]
          simp only [eval_bin, ap_eq, eval_v, r2, eval_c, e0]
          have hmem := take_succ_tail_mem x p (by omega) hxp
          by_cases hk : ρ' 2 = 0
          · have hnot : false ∉ (x.take p).tail := by
              intro hh; rw [h2] at hk; simp [kkOf, hh] at hk
            simp only [hk, if_true, ne_eq, one_ne_zero, not_false_eq_true]
            rw [run_ite]
            simp only [eval_bin, ap_eq, ev2p1, zB p hxp, eval_c, e0,
              List.getElem?_eq_getElem hxp]
            cases hx : x[p]
            · simp only [bitCode, if_true, ne_eq, one_ne_zero, not_false_eq_true, run_set]
              obtain ⟨a, b⟩ := hk3 (Function.update ρ 2 _) (by simp) (by simp)
              refine ⟨⟨a, ?_, b⟩, by simp⟩
              simp only [Function.update_self, eval_bin, ap_add, eval_v, r0, eval_c, e1]
              rw [min_eq_left (by omega)]
              have hin : false ∈ (x.take (p + 1)).tail := hmem.2 (Or.inr hx)
              simp only [kkOf, if_pos hin]
              -- the index of the first zero of the tail is `p - 1`
              rcases x with _ | ⟨c, t⟩
              · simp at hxp
              · obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
                simp only [List.tail_cons]
                simp only [List.take_succ_cons, List.tail_cons] at hnot
                rw [idxOf_eq_of_not_mem_take t q (by simpa using hxp) hnot (by simpa using hx)]
            · rw [if_neg (by simp [bitCode])]
              obtain ⟨a, b⟩ := hk3 ρ rfl rfl
              refine ⟨⟨a, ?_, b⟩, by simp⟩
              simp only [run_skip]
              rw [r2, hk]
              have : false ∉ (x.take (p + 1)).tail := by
                rw [hmem]; simp [hnot, hx]
              simp [kkOf, this]
          · simp only [hk, if_false, ne_eq, not_true_eq_false, run_skip]
            obtain ⟨a, b⟩ := hk3 ρ rfl rfl
            refine ⟨⟨a, ?_, b⟩, by simp⟩
            have hin : false ∈ (x.take p).tail := by
              by_contra hh; rw [h2] at hk; simp [kkOf, hh] at hk
            rw [r2, h2]
            simp [kkOf, hin, hmem.2 (Or.inl hin)])
  have hlen : Ex.eval z C (fun _ => 0) (Ex.len : Ex 4) = z.length := by
    simp only [eval_len]; omega
  simp only [hlen] at hloop
  obtain ⟨⟨h3, h2, h1⟩, hout⟩ := hloop
  rw [hout]
  rw [show List.flatMap (fun _ => ([] : List Bool)) (List.range z.length) = [] by simp,
    List.nil_append]
  set ρ := (Pr.run z C (Pr.loop 0 Ex.len e3Body) fun _ => 0).1 with hρ
  have hm : ρ 1 = x.length := h1 (by omega)
  rw [min_eq_right (show x.length ≤ z.length by omega)] at h2
  have e0 : min 0 C = 0 := min_eq_left (by omega)
  have e1 : min 1 C = 1 := min_eq_left (by omega)
  have e2 : min 2 C = 2 := min_eq_left (by omega)
  unfold e3F
  by_cases hx : false ∈ x.tail
  · have hkk : ρ 2 = x.tail.idxOf false + 2 := by rw [h2]; simp [kkOf, hx, List.take_length]
    have hlt : x.tail.idxOf false < x.tail.length := List.idxOf_lt_length_iff.2 hx
    rw [run_ite_pos (by simp [hkk])]
    rcases x with _ | ⟨b, t⟩
    · simp at hx
    · simp only [List.tail_cons, List.length_cons] at hkk hlt hm hx ⊢
      simp only [hx, if_true, List.headD_cons]
      have hb : (rd (.c 1) : Ex 4).eval z C ρ = bitCode (some b) := by
        rw [eval_rd z C ρ _ 1 (by simp [e1]) (by omega)]
        have := zB 0 (by simp)
        simp only [Nat.mul_zero, Nat.zero_add] at this
        rw [this]; rfl
      have hbe : (Ex.bin .eq (rd (.c 1)) (.c 1) : Ex 4).eval z C ρ = if b then 1 else 0 := by
        simp only [eval_bin, ap_eq, hb, eval_c, e1]
        cases b <;> simp [bitCode]
      cases b
      · rw [run_ite_neg (by rw [hbe]; rfl)]
        have hr : (rd (.bin .add (.bin .add (.bin .add (.v 1) (.v 1)) (.c 2))
            (.bin .sub (.v 2) (.c 2))) : Ex 4).eval z C ρ =
            bitCode y[t.idxOf false]? := by
          have hzD := zD (t.idxOf false)
          simp only [List.length_cons] at hzD
          rw [eval_rd z C ρ _ (2 * (t.length + 1) + 2 + t.idxOf false) _ (by omega), hzD]
          simp only [eval_bin, ap_add, ap_sub, eval_v, hm, hkk, eval_c, e2]
          rw [min_eq_left (by omega), min_eq_left (by omega), min_eq_left (by omega)]
          omega
        rw [run_out]
        simp only [eval_bin, ap_eq, hr, eval_c, e1]
        rcases hy : y[t.idxOf false]? with _ | ⟨_ | _⟩ <;>
          simp [bitCode, List.getD_eq_getElem?_getD, hy]
      · rw [run_ite_pos (by rw [hbe]; decide), run_out]
        have hv : (Ex.bin .eq (.bin .sub (.bin .sub .len (.bin .add (.v 1) (.v 1))) (.c 2))
            (.bin .sub (.v 2) (.c 2)) : Ex 4).eval z C ρ =
            if y.length = t.idxOf false then 1 else 0 := by
          simp only [eval_bin, ap_eq, ap_sub, eval_len, ap_add, eval_v, hm, hkk, eval_c, e2]
          rw [min_eq_left (show z.length ≤ C by omega), min_eq_left (by omega), hzl]
          simp only [List.length_cons]
          congr 1
          apply propext; constructor <;> intro h <;> omega
        rw [hv]
        by_cases hy : y.length = t.idxOf false <;> simp [hy]
  · have hkk : ρ 2 = 0 := by rw [h2]; simp [kkOf, hx, List.take_length]
    rw [run_ite_neg (by simp [hkk])]
    simp [hx]

end LL

open LL

/-- **The bit/length language of a logspace function is in `L`.** -/
theorem LangF_mem_ClassL {f : Word → Word} (hf : LogspaceComputable f) : LangF f ∈ ClassL := by
  have hsfx : LogspaceComputable sfxF :=
    logspaceComputable_of_output 2 sfxProg _ sfxProg_output
  have hpre : LogspaceComputable (fun x => x.flatMap dupB ++ [false, false] ++ f (sfxF x)) :=
    (LogspaceComputable.bitMap dupB [false, false]).append (hsfx.comp hf)
  have he3 : LogspaceComputable (e3Prog.output 2) :=
    logspaceComputable_of_output 2 e3Prog _ (fun _ => rfl)
  have := hpre.comp he3
  show LogspaceComputable (charWord (LangF f))
  refine (funext fun x => ?_ : (e3Prog.output 2 ∘ fun x => x.flatMap dupB ++ [false, false] ++
    f (sfxF x)) = charWord (LangF f)) ▸ this
  rw [Function.comp_apply, e3Prog_output, charWord_LangF]

end PathChecking
