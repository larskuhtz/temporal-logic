module

public import RequestProject.LogLang.Out

/-!
# A functional front end for the loop language

Programs of the loop language (`LL.Pr`) manipulate variables imperatively.  For the query and
decision functions of the LTL path checking algorithm it is more convenient to write *pure*
expressions with bounded binders:

* `FE.E`: expressions with constants, variables (de Bruijn *levels*: a binder at depth `d` binds
  the variable `v d`), the input length, input symbols, the binary operations of the loop
  language, `ite`, bounded search `find n body` (least `i < n` with `body i ≠ 0`, or `n`), bounded
  counting `count n body` and `lett a body`;
* `FE.O`: output programs emitting tokens, bits and binary numbers, with `ite`, bounded loops
  and `lett`.

Both are compiled into the loop language (`FE.comp`, `FE.compO`), with a generic correctness
proof.  Hence the function computed by an output program is logspace computable
(`FE.logspaceComputable_of_out`).
-/

@[expose] public section

namespace PathChecking

namespace FE

open LL

/-- Expressions.  Binders (`find`, `count`, `lett`) at depth `d` bind the variable `v d`. -/
inductive E
  | c (k : ℕ)
  | v (x : ℕ)
  | len
  | inp (e : E)
  | bin (o : BOp) (a b : E)
  | ite (c a b : E)
  | find (n body : E)
  | count (n body : E)
  | lett (a body : E)

/-- Bounded search: the least `i < N` with `f i ≠ 0`, or `N`. -/
def findF (N : ℕ) (f : ℕ → ℕ) : ℕ := ((List.range N).find? (fun i => f i ≠ 0)).getD N

/-- Bounded counting with additions capped at `C`. -/
def countF (C N : ℕ) (f : ℕ → ℕ) : ℕ :=
  (List.range N).foldl (fun acc i => if f i ≠ 0 then min (acc + 1) C else acc) 0

/-- Semantics of expressions at binder depth `d` in the environment `ρ`. -/
def eval (w : Word) (C : ℕ) : ℕ → (ℕ → ℕ) → E → ℕ
  | _, _, .c k => min k C
  | _, ρ, .v x => ρ x
  | _, _, .len => min w.length C
  | d, ρ, .inp e => symNum (inputSym w (eval w C d ρ e))
  | d, ρ, .bin o a b => o.ap C (eval w C d ρ a) (eval w C d ρ b)
  | d, ρ, .ite cnd a b => if eval w C d ρ cnd ≠ 0 then eval w C d ρ a else eval w C d ρ b
  | d, ρ, .find n body => findF (eval w C d ρ n)
      (fun i => eval w C (d + 1) (Function.update ρ d i) body)
  | d, ρ, .count n body => countF C (eval w C d ρ n)
      (fun i => eval w C (d + 1) (Function.update ρ d i) body)
  | d, ρ, .lett a body => eval w C (d + 1) (Function.update ρ d (eval w C d ρ a)) body

/-- Well-scoped expressions: at depth `d`, only the variables `v x` with `x < d` occur. -/
def E.wf : ℕ → E → Bool
  | _, .c _ => true
  | d, .v x => decide (x < d)
  | _, .len => true
  | d, .inp e => e.wf d
  | d, .bin _ a b => a.wf d && b.wf d
  | d, .ite cnd a b => cnd.wf d && a.wf d && b.wf d
  | d, .find n body => n.wf d && body.wf (d + 1)
  | d, .count n body => n.wf d && body.wf (d + 1)
  | d, .lett a body => a.wf d && body.wf (d + 1)

/-- Binder depth. -/
def E.bd : E → ℕ
  | .c _ => 0
  | .v _ => 0
  | .len => 0
  | .inp e => e.bd
  | .bin _ a b => max a.bd b.bd
  | .ite cnd a b => max cnd.bd (max a.bd b.bd)
  | .find n body => max n.bd (body.bd + 1)
  | .count n body => max n.bd (body.bd + 1)
  | .lett a body => max a.bd (body.bd + 1)

/-- Scratch space needed by the compiled expression. -/
def E.sn : E → ℕ
  | .c _ => 0
  | .v _ => 0
  | .len => 0
  | .inp e => e.sn
  | .bin _ a b => max a.sn (b.sn + 1)
  | .ite cnd a b => max cnd.sn (max a.sn b.sn)
  | .find n body => max n.sn (body.sn + 2)
  | .count n body => max (n.sn + 1) (body.sn + 2)
  | .lett a body => max (a.sn + 1) body.sn

lemma eval_congr (w : Word) (C : ℕ) : ∀ (e : E) (d : ℕ) (ρ ρ' : ℕ → ℕ), e.wf d = true →
    (∀ x < d, ρ x = ρ' x) → eval w C d ρ e = eval w C d ρ' e := by
  intro e
  induction e with
  | c k => intros; rfl
  | v x => intro d ρ ρ' hw h; simp only [E.wf, decide_eq_true_eq] at hw; exact h x hw
  | len => intros; rfl
  | inp e ih => intro d ρ ρ' hw h; simp only [eval]; rw [ih d ρ ρ' hw h]
  | bin o a b iha ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [eval]; rw [iha d ρ ρ' hw.1 h, ihb d ρ ρ' hw.2 h]
  | ite c a b ihc iha ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [eval]; rw [ihc d ρ ρ' hw.1.1 h, iha d ρ ρ' hw.1.2 h, ihb d ρ ρ' hw.2 h]
  | find n body ihn ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [eval]
    rw [ihn d ρ ρ' hw.1 h]
    congr 1; funext i
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)
  | count n body ihn ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [eval]
    rw [ihn d ρ ρ' hw.1 h]
    congr 1; funext i
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)
  | lett a body iha ihb =>
    intro d ρ ρ' hw h
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [eval]
    rw [iha d ρ ρ' hw.1 h]
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)

/-! ## Compilation -/

variable {V : ℕ}

/-- Variable number `i` (clamped to `V`). -/
def fv (V i : ℕ) : Fin (V + 1) := ⟨min i V, by omega⟩

lemma fv_val {i : ℕ} (h : i ≤ V) : (fv V i).val = i := by simp [fv, h]

lemma fv_inj {i j : ℕ} (hi : i ≤ V) (hj : j ≤ V) : fv V i = fv V j ↔ i = j := by
  constructor
  · intro e; have := congrArg Fin.val e; rwa [fv_val hi, fv_val hj] at this
  · rintro rfl; rfl

lemma fv_ne {i j : ℕ} (hi : i ≤ V) (hj : j ≤ V) (h : i ≠ j) : fv V i ≠ fv V j :=
  fun e => h ((fv_inj hi hj).1 e)

/-- The environment seen by expressions. -/
def envOf (ρ : Fin (V + 1) → ℕ) : ℕ → ℕ := fun i => ρ (fv V i)

lemma envOf_update (ρ : Fin (V + 1) → ℕ) {d : ℕ} (hd : d ≤ V) (a : ℕ) (x : ℕ) (hx : x ≤ V) :
    envOf (Function.update ρ (fv V d) a) x = Function.update (envOf ρ) d a x := by
  simp only [envOf]
  by_cases h : x = d
  · subst h; simp
  · rw [Function.update_of_ne (fv_ne hx hd h), Function.update_of_ne h]; rfl

/-- Compilation of expressions: the value is stored in variable `t`, binders of depth `≥ d` use
the variables `d, d+1, …`, and scratch variables `≥ sp` are used. -/
def comp (V : ℕ) : E → ℕ → ℕ → ℕ → Pr (V + 1)
  | .c k, _, t, _ => .set (fv V t) (.c k)
  | .v x, _, t, _ => .set (fv V t) (.v (fv V x))
  | .len, _, t, _ => .set (fv V t) .len
  | .inp e, d, t, sp => .seq (comp V e d t sp) (.set (fv V t) (.inp (.v (fv V t))))
  | .bin o a b, d, t, sp => .seq (comp V a d t sp) (.seq (comp V b d sp (sp + 1))
      (.set (fv V t) (.bin o (.v (fv V t)) (.v (fv V sp)))))
  | .ite cnd a b, d, t, sp => .seq (comp V cnd d t sp)
      (.ite (.v (fv V t)) (comp V a d t sp) (comp V b d t sp))
  | .find n body, d, t, sp => .seq (comp V n d t sp) (.seq (.set (fv V sp) (.c 0))
      (.loop (fv V d) (.v (fv V t)) (.ite (.v (fv V sp)) .skip
        (.seq (comp V body (d + 1) (sp + 1) (sp + 2))
          (.ite (.v (fv V (sp + 1))) (.seq (.set (fv V t) (.v (fv V d))) (.set (fv V sp) (.c 1)))
            .skip)))))
  | .count n body, d, t, sp => .seq (comp V n d sp (sp + 1)) (.seq (.set (fv V t) (.c 0))
      (.loop (fv V d) (.v (fv V sp)) (.seq (comp V body (d + 1) (sp + 1) (sp + 2))
        (.ite (.v (fv V (sp + 1))) (.set (fv V t) (.bin .add (.v (fv V t)) (.c 1))) .skip))))
  | .lett a body, d, t, sp => .seq (comp V a d sp (sp + 1))
      (.seq (.set (fv V d) (.v (fv V sp))) (comp V body (d + 1) t sp))

lemma findF_succ (N : ℕ) (f : ℕ → ℕ) :
    findF (N + 1) f = if findF N f < N then findF N f else if f N ≠ 0 then N else N + 1 := by
  unfold findF
  rw [List.range_succ, List.find?_append]
  cases h : (List.range N).find? (fun i => f i ≠ 0) with
  | some i =>
    have := List.mem_of_find?_eq_some h
    simp only [List.mem_range] at this
    simp [this]
  | none =>
    simp only [Option.none_or, Option.getD_none, lt_irrefl, if_false]
    by_cases hN : f N ≠ 0
    · simp [List.find?, hN]
    · simp [List.find?, hN]

lemma countF_succ (C N : ℕ) (f : ℕ → ℕ) :
    countF C (N + 1) f = if f N ≠ 0 then min (countF C N f + 1) C else countF C N f := by
  unfold countF
  rw [List.range_succ, List.foldl_append]
  rfl

section Correct

variable {w : Word} {C : ℕ}

/-- **Correctness of the expression compiler.** -/
theorem run_comp (hC : 1 ≤ C) (SB : ℕ) : ∀ (e : E) (d t sp : ℕ) (ρ : Fin (V + 1) → ℕ),
    e.wf d = true → d + e.bd ≤ SB → SB ≤ t → t < sp → sp + e.sn ≤ V →
    ((comp V e d t sp).run w C ρ).2 = [] ∧
    ((comp V e d t sp).run w C ρ).1 (fv V t) = eval w C d (envOf ρ) e ∧
    ∀ z, z ≤ V → (z < d ∨ (SB ≤ z ∧ z < sp)) → z ≠ t →
      ((comp V e d t sp).run w C ρ).1 (fv V z) = ρ (fv V z) := by
  intro e
  induction e with
  | c k =>
    intro d t sp ρ _ _ hSt htp hsp
    refine ⟨rfl, by simp [comp, eval], fun z hz _ hzt => ?_⟩
    simp only [comp, run_set]
    rw [Function.update_of_ne (fv_ne hz (by omega) hzt)]
  | v x =>
    intro d t sp ρ _ _ hSt htp hsp
    refine ⟨rfl, by simp [comp, eval, envOf], fun z hz _ hzt => ?_⟩
    simp only [comp, run_set]
    rw [Function.update_of_ne (fv_ne hz (by omega) hzt)]
  | len =>
    intro d t sp ρ _ _ hSt htp hsp
    refine ⟨rfl, by simp [comp, eval], fun z hz _ hzt => ?_⟩
    simp only [comp, run_set]
    rw [Function.update_of_ne (fv_ne hz (by omega) hzt)]
  | inp e ih =>
    intro d t sp ρ hw hbd hSt htp hsp
    simp only [E.wf] at hw
    simp only [E.bd, E.sn] at hbd hsp
    obtain ⟨h1, h2, h3⟩ := ih d t sp ρ hw hbd hSt htp hsp
    simp only [comp, run_seq, run_set, h1, List.nil_append, Function.update_self, eval_inp,
      eval_v, h2]
    refine ⟨trivial, by simp [eval], fun z hz hzr hzt => ?_⟩
    rw [Function.update_of_ne (fv_ne hz (by omega) hzt), h3 z hz hzr hzt]
  | bin o a b iha ihb =>
    intro d t sp ρ hw hbd hSt htp hsp
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.bd, E.sn] at hbd hsp
    obtain ⟨a1, a2, a3⟩ := iha d t sp ρ hw.1 (by omega) hSt htp (by omega)
    set ρ1 := ((comp V a d t sp).run w C ρ).1 with hρ1
    obtain ⟨b1, b2, b3⟩ := ihb d sp (sp + 1) ρ1 hw.2 (by omega) (by omega) (by omega) (by omega)
    set ρ2 := ((comp V b d sp (sp + 1)).run w C ρ1).1 with hρ2
    have hb : eval w C d (envOf ρ1) b = eval w C d (envOf ρ) b :=
      eval_congr w C b d _ _ hw.2 (fun x hx => a3 x (by omega) (Or.inl hx) (by omega))
    have ht2 : ρ2 (fv V t) = ρ1 (fv V t) := b3 t (by omega) (Or.inr ⟨hSt, by omega⟩) (by omega)
    simp only [comp, run_seq, run_set]
    rw [← hρ1, ← hρ2]
    refine ⟨by simp [a1, b1], ?_, fun z hz hzr hzt => ?_⟩
    · simp only [Function.update_self, eval_bin, eval_v, eval]
      rw [ht2, a2, b2, hb]
    · rw [Function.update_of_ne (fv_ne hz (by omega) hzt)]
      rw [b3 z hz (by omega) (by omega), a3 z hz hzr hzt]
  | ite c a b ihc iha ihb =>
    intro d t sp ρ hw hbd hSt htp hsp
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.bd, E.sn] at hbd hsp
    obtain ⟨c1, c2, c3⟩ := ihc d t sp ρ hw.1.1 (by omega) hSt htp (by omega)
    set ρ1 := ((comp V c d t sp).run w C ρ).1 with hρ1
    have hcongr : ∀ e : E, e.wf d = true → eval w C d (envOf ρ1) e = eval w C d (envOf ρ) e :=
      fun e he => eval_congr w C e d _ _ he (fun x hx => c3 x (by omega) (Or.inl hx) (by omega))
    simp only [comp, run_seq]
    rw [← hρ1]
    by_cases hcv : eval w C d (envOf ρ) c ≠ 0
    · rw [run_ite_pos (by rw [eval_v, c2]; exact hcv)]
      obtain ⟨a1, a2, a3⟩ := iha d t sp ρ1 hw.1.2 (by omega) hSt htp (by omega)
      refine ⟨by simp [c1, a1], ?_, fun z hz hzr hzt => ?_⟩
      · rw [a2, hcongr a hw.1.2]; simp [eval, hcv]
      · rw [a3 z hz hzr hzt, c3 z hz hzr hzt]
    · rw [run_ite_neg (by rw [eval_v, c2]; exact not_not.1 hcv)]
      obtain ⟨b1, b2, b3⟩ := ihb d t sp ρ1 hw.2 (by omega) hSt htp (by omega)
      refine ⟨by simp [c1, b1], ?_, fun z hz hzr hzt => ?_⟩
      · rw [b2, hcongr b hw.2]; simp [eval, hcv]
      · rw [b3 z hz hzr hzt, c3 z hz hzr hzt]
  | find n body ihn ihb =>
    intro d t sp ρ hw hbd hSt htp hsp
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.bd, E.sn] at hbd hsp
    obtain ⟨n1, n2, n3⟩ := ihn d t sp ρ hw.1 (by omega) hSt htp (by omega)
    set ρ1 := ((comp V n d t sp).run w C ρ).1
    set N := eval w C d (envOf ρ) n
    set f := fun i => eval w C (d + 1) (Function.update (envOf ρ) d i) body
    set ρ2 := Function.update ρ1 (fv V sp) ((Ex.c 0 : Ex (V + 1)).eval w C ρ1)
    have hd : d < SB := by omega
    have hfr : ∀ z, z ≤ V → (z < d ∨ (SB ≤ z ∧ z < sp)) → z ≠ t → ρ2 (fv V z) = ρ (fv V z) := by
      intro z hz hzr hzt
      simp only [ρ2]
      rw [Function.update_of_ne (fv_ne hz (by omega) (by omega)), n3 z hz hzr hzt]
    set body' : Pr (V + 1) := (.ite (.v (fv V sp)) .skip
        (.seq (comp V body (d + 1) (sp + 1) (sp + 2))
          (.ite (.v (fv V (sp + 1))) (.seq (.set (fv V t) (.v (fv V d))) (.set (fv V sp) (.c 1)))
            .skip))) with hbody'
    have hloopb : (Ex.v (fv V t) : Ex (V + 1)).eval w C ρ2 = N := by
      simp only [eval_v, ρ2]
      rw [Function.update_of_ne (fv_ne (by omega) (by omega) (by omega)), n2]
    let I : ℕ → (Fin (V + 1) → ℕ) → Prop := fun i ρ' =>
      (∀ z, z ≤ V → (z < d ∨ (SB ≤ z ∧ z < sp)) → z ≠ t → ρ' (fv V z) = ρ (fv V z)) ∧
      ((ρ' (fv V sp) = 0 ∧ ρ' (fv V t) = N ∧ findF i f = i) ∨
        (ρ' (fv V sp) ≠ 0 ∧ ρ' (fv V t) = findF i f ∧ findF i f < i))
    have key := run_loop_spec (w := w) (C := C) (fv V d) (.v (fv V t)) body' ρ2 I
      (fun _ => []) ⟨hfr, Or.inl ⟨by simp [ρ2], by
        simp only [ρ2]; rw [Function.update_of_ne (fv_ne (by omega) (by omega) (by omega)), n2],
        by simp [findF]⟩⟩ (by
      intro i hi ρ' hI
      obtain ⟨hIf, hI⟩ := hI
      set ρ'' := Function.update ρ' (fv V d) i
      have e'' : ∀ z, z ≤ V → z ≠ d → ρ'' (fv V z) = ρ' (fv V z) :=
        fun z hz hzd => Function.update_of_ne (fv_ne hz (by omega) hzd) _ _
      rcases hI with ⟨hs, ht, hf⟩ | ⟨hs, ht, hf⟩
      · rw [hbody', run_ite_neg (by simp [e'' sp (by omega) (by omega), hs])]
        obtain ⟨b1, b2, b3⟩ := ihb (d + 1) (sp + 1) (sp + 2) ρ'' hw.2 (by omega) (by omega)
          (by omega) (by omega)
        have hfi : eval w C (d + 1) (envOf ρ'') body = f i := by
          refine eval_congr w C body (d + 1) _ _ hw.2 (fun x hx => ?_)
          rw [envOf_update ρ' (by omega) i x (by omega)]
          by_cases hxd : x = d
          · subst hxd; simp
          · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
            exact hIf x (by omega) (Or.inl (by omega)) (by omega)
        have hfs : findF (i + 1) f = if f i ≠ 0 then i else i + 1 := by
          rw [findF_succ, hf]; simp
        simp only [run_seq, b1, List.nil_append]
        by_cases hfi0 : f i ≠ 0
        · rw [run_ite_pos (by simp [b2, hfi, hfi0])]
          simp only [run_seq, run_set, List.append_nil]
          refine ⟨⟨fun z hz hzr hzt => ?_, Or.inr ⟨?_, ?_, ?_⟩⟩, by simp⟩
          · rw [Function.update_of_ne (fv_ne hz (by omega) (by omega)),
              Function.update_of_ne (fv_ne hz (by omega) hzt),
              b3 z hz (by omega) (by omega), e'' z hz (by omega)]
            exact hIf z hz hzr hzt
          · simp; omega
          · rw [Function.update_of_ne (fv_ne (by omega) (by omega) (by omega)),
              Function.update_self, eval_v, b3 d (by omega) (by omega) (by omega)]
            simp [ρ'', hfs, hfi0]
          · rw [hfs, if_pos hfi0]; omega
        · rw [run_ite_neg (by simp [b2, hfi]; omega)]
          simp only [run_skip]
          refine ⟨⟨fun z hz hzr hzt => ?_, Or.inl ⟨?_, ?_, ?_⟩⟩, by simp⟩
          · rw [b3 z hz (by omega) (by omega), e'' z hz (by omega)]
            exact hIf z hz hzr hzt
          · rw [b3 sp (by omega) (Or.inr ⟨by omega, by omega⟩) (by omega),
              e'' sp (by omega) (by omega), hs]
          · rw [b3 t (by omega) (Or.inr ⟨by omega, by omega⟩) (by omega),
              e'' t (by omega) (by omega), ht]
          · rw [hfs, if_neg hfi0]
      · rw [hbody', run_ite_pos (by simp [e'' sp (by omega) (by omega), hs])]
        simp only [run_skip]
        have hfs : findF (i + 1) f = findF i f := by rw [findF_succ, if_pos (by omega)]
        refine ⟨⟨fun z hz hzr hzt => ?_, Or.inr ⟨?_, ?_, ?_⟩⟩, trivial⟩
        · rw [e'' z hz (by omega)]; exact hIf z hz hzr hzt
        · rw [e'' sp (by omega) (by omega)]; exact hs
        · rw [e'' t (by omega) (by omega), ht, hfs]
        · omega)
    rw [hloopb] at key
    obtain ⟨⟨kf, kr⟩, ko⟩ := key
    simp only [comp, run_seq, run_set, n1, List.nil_append]
    refine ⟨by rw [ko]; simp, ?_, kf⟩
    show _ = findF N f
    rcases kr with ⟨-, h, h'⟩ | ⟨-, h, -⟩
    · rw [h, h']
    · exact h
  | count n body ihn ihb =>
    intro d t sp ρ hw hbd hSt htp hsp
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.bd, E.sn] at hbd hsp
    obtain ⟨n1, n2, n3⟩ := ihn d sp (sp + 1) ρ hw.1 (by omega) (by omega) (by omega) (by omega)
    set ρ1 := ((comp V n d sp (sp + 1)).run w C ρ).1
    set N := eval w C d (envOf ρ) n
    set f := fun i => eval w C (d + 1) (Function.update (envOf ρ) d i) body
    set ρ2 := Function.update ρ1 (fv V t) ((Ex.c 0 : Ex (V + 1)).eval w C ρ1)
    set body' : Pr (V + 1) := (.seq (comp V body (d + 1) (sp + 1) (sp + 2))
        (.ite (.v (fv V (sp + 1))) (.set (fv V t) (.bin .add (.v (fv V t)) (.c 1))) .skip))
      with hbody'
    have hloopb : (Ex.v (fv V sp) : Ex (V + 1)).eval w C ρ2 = N := by
      simp only [eval_v, ρ2]
      rw [Function.update_of_ne (fv_ne (by omega) (by omega) (by omega)), n2]
    let I : ℕ → (Fin (V + 1) → ℕ) → Prop := fun i ρ' =>
      (∀ z, z ≤ V → (z < d ∨ (SB ≤ z ∧ z < sp)) → z ≠ t → ρ' (fv V z) = ρ (fv V z)) ∧
      ρ' (fv V t) = countF C i f
    have key := run_loop_spec (w := w) (C := C) (fv V d) (.v (fv V sp)) body' ρ2 I
      (fun _ => []) ⟨fun z hz hzr hzt => by
        simp only [ρ2]
        rw [Function.update_of_ne (fv_ne hz (by omega) hzt),
          n3 z hz (by omega) (by omega)], by simp [ρ2, countF]⟩ (by
      intro i hi ρ' hI
      obtain ⟨hIf, hI⟩ := hI
      set ρ'' := Function.update ρ' (fv V d) i
      have e'' : ∀ z, z ≤ V → z ≠ d → ρ'' (fv V z) = ρ' (fv V z) :=
        fun z hz hzd => Function.update_of_ne (fv_ne hz (by omega) hzd) _ _
      obtain ⟨b1, b2, b3⟩ := ihb (d + 1) (sp + 1) (sp + 2) ρ'' hw.2 (by omega) (by omega)
        (by omega) (by omega)
      have hfi : eval w C (d + 1) (envOf ρ'') body = f i := by
        refine eval_congr w C body (d + 1) _ _ hw.2 (fun x hx => ?_)
        rw [envOf_update ρ' (by omega) i x (by omega)]
        by_cases hxd : x = d
        · subst hxd; simp
        · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
          exact hIf x (by omega) (Or.inl (by omega)) (by omega)
      have ht3 : ((comp V body (d + 1) (sp + 1) (sp + 2)).run w C ρ'').1 (fv V t) =
          countF C i f := by
        rw [b3 t (by omega) (Or.inr ⟨by omega, by omega⟩) (by omega), e'' t (by omega) (by omega),
          hI]
      rw [hbody']
      simp only [run_seq, b1, List.nil_append]
      by_cases hfi0 : f i ≠ 0
      · rw [run_ite_pos (by simp [b2, hfi, hfi0])]
        simp only [run_set]
        refine ⟨⟨fun z hz hzr hzt => ?_, ?_⟩, trivial⟩
        · rw [Function.update_of_ne (fv_ne hz (by omega) hzt), b3 z hz (by omega) (by omega),
            e'' z hz (by omega)]
          exact hIf z hz hzr hzt
        · simp only [Function.update_self, eval_bin, ap_add, eval_v, eval_c, ht3]
          rw [countF_succ, if_pos hfi0, min_eq_left hC]
      · rw [run_ite_neg (by simp [b2, hfi]; omega)]
        simp only [run_skip]
        refine ⟨⟨fun z hz hzr hzt => ?_, ?_⟩, trivial⟩
        · rw [b3 z hz (by omega) (by omega), e'' z hz (by omega)]
          exact hIf z hz hzr hzt
        · rw [ht3, countF_succ, if_neg hfi0])
    rw [hloopb] at key
    obtain ⟨⟨kf, kr⟩, ko⟩ := key
    simp only [comp, run_seq, run_set, n1, List.nil_append]
    exact ⟨by rw [ko]; simp, kr, kf⟩
  | lett a body iha ihb =>
    intro d t sp ρ hw hbd hSt htp hsp
    simp only [E.wf, Bool.and_eq_true] at hw
    simp only [E.bd, E.sn] at hbd hsp
    obtain ⟨a1, a2, a3⟩ := iha d sp (sp + 1) ρ hw.1 (by omega) (by omega) (by omega) (by omega)
    set ρ1 := ((comp V a d sp (sp + 1)).run w C ρ).1
    set ρ2 := Function.update ρ1 (fv V d) (ρ1 (fv V sp))
    obtain ⟨b1, b2, b3⟩ := ihb (d + 1) t sp ρ2 hw.2 (by omega) hSt htp (by omega)
    simp only [comp, run_seq, run_set, a1, List.nil_append, eval_v]
    refine ⟨b1, ?_, fun z hz hzr hzt => ?_⟩
    · rw [b2]
      refine eval_congr w C body (d + 1) _ _ hw.2 (fun x hx => ?_)
      rw [envOf_update ρ1 (by omega) _ x (by omega)]
      by_cases hxd : x = d
      · subst hxd; simp [a2]
      · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
        exact a3 x (by omega) (Or.inl (by omega)) (by omega)
    · rw [b3 z hz (by omega) hzt]
      simp only [ρ2]
      rw [Function.update_of_ne (fv_ne hz (by omega) (by omega)),
        a3 z hz (by omega) (by omega)]

end Correct

end FE

end PathChecking
