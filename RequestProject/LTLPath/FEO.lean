module

public import RequestProject.LTLPath.FEU
public import RequestProject.LogLang.Main

/-!
# Output programs for the functional front end

`FE.O`: output programs emitting bits and binary numbers (`natToks`), with sequencing,
conditionals, bounded loops (a loop at binder depth `d` binds `v d`) and `lett`.  The uncapped
semantics is `FE.evO`; output programs are compiled into the loop language (`FE.compO`), and
`FE.logspaceComputable_of_O` shows that the function computed by a closed output program is
logspace computable.
-/

@[expose] public section

namespace PathChecking

namespace FE

open LL

/-- Output programs. -/
inductive O
  | nil
  | bit (e : E)
  | nat (e : E)
  | seq (a b : O)
  | ite (c : E) (a b : O)
  | loop (n : E) (body : O)
  | lett (a : E) (body : O)

/-- Uncapped semantics of output programs. -/
def evO (w : Word) : ℕ → (ℕ → ℕ) → O → Word
  | _, _, .nil => []
  | d, ρ, .bit e => [decide (ev w d ρ e ≠ 0)]
  | d, ρ, .nat e => encodeToks (natToks (ev w d ρ e))
  | d, ρ, .seq a b => evO w d ρ a ++ evO w d ρ b
  | d, ρ, .ite c a b => if ev w d ρ c ≠ 0 then evO w d ρ a else evO w d ρ b
  | d, ρ, .loop n body => (List.range (ev w d ρ n)).flatMap
      (fun i => evO w (d + 1) (Function.update ρ d i) body)
  | d, ρ, .lett a body => evO w (d + 1) (Function.update ρ d (ev w d ρ a)) body

/-- Well-scoped output programs. -/
def O.wf : ℕ → O → Bool
  | _, .nil => true
  | d, .bit e => e.wf d
  | d, .nat e => e.wf d
  | d, .seq a b => a.wf d && b.wf d
  | d, .ite c a b => c.wf d && a.wf d && b.wf d
  | d, .loop n body => n.wf d && body.wf (d + 1)
  | d, .lett a body => a.wf d && body.wf (d + 1)

/-- Binder depth. -/
def O.bd : O → ℕ
  | .nil => 0
  | .bit e => e.bd
  | .nat e => e.bd
  | .seq a b => max a.bd b.bd
  | .ite c a b => max c.bd (max a.bd b.bd)
  | .loop n body => max n.bd (body.bd + 1)
  | .lett a body => max a.bd (body.bd + 1)

/-- Scratch space. -/
def O.sn : O → ℕ
  | .nil => 0
  | .bit e => e.sn + 1
  | .nat e => max (e.sn + 1) 3
  | .seq a b => max a.sn b.sn
  | .ite c a b => max (c.sn + 1) (max a.sn b.sn)
  | .loop n body => max (n.sn + 1) (body.sn + 1)
  | .lett a body => max (a.sn + 1) body.sn

/-- Degree. -/
def O.dg : ℕ → (ℕ → ℕ) → O → ℕ
  | _, _, .nil => 0
  | d, δ, .bit e => e.dg d δ
  | d, δ, .nat e => e.dg d δ
  | d, δ, .seq a b => max (a.dg d δ) (b.dg d δ)
  | d, δ, .ite c a b => max (c.dg d δ) (max (a.dg d δ) (b.dg d δ))
  | d, δ, .loop n body => max (n.dg d δ) (body.dg (d + 1) (Function.update δ d (n.dg d δ)))
  | d, δ, .lett a body => max (a.dg d δ) (body.dg (d + 1) (Function.update δ d (a.dg d δ)))

lemma evO_congr (w : Word) : ∀ (o : O) (d : ℕ) (ρ ρ' : ℕ → ℕ), o.wf d = true →
    (∀ x < d, ρ x = ρ' x) → evO w d ρ o = evO w d ρ' o := by
  intro o
  induction o with
  | nil => intros; rfl
  | bit e => intro d ρ ρ' hw h; simp only [O.wf] at hw; simp only [evO]; rw [ev_congr w e d ρ ρ' hw h]
  | nat e => intro d ρ ρ' hw h; simp only [O.wf] at hw; simp only [evO]; rw [ev_congr w e d ρ ρ' hw h]
  | seq a b iha ihb =>
    intro d ρ ρ' hw h
    simp only [O.wf, Bool.and_eq_true] at hw
    simp only [evO]; rw [iha d ρ ρ' hw.1 h, ihb d ρ ρ' hw.2 h]
  | ite c a b iha ihb =>
    intro d ρ ρ' hw h
    simp only [O.wf, Bool.and_eq_true] at hw
    simp only [evO]; rw [ev_congr w c d ρ ρ' hw.1.1 h, iha d ρ ρ' hw.1.2 h, ihb d ρ ρ' hw.2 h]
  | loop n body ihb =>
    intro d ρ ρ' hw h
    simp only [O.wf, Bool.and_eq_true] at hw
    simp only [evO]
    rw [ev_congr w n d ρ ρ' hw.1 h]
    congr 1; funext i
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)
  | lett a body ihb =>
    intro d ρ ρ' hw h
    simp only [O.wf, Bool.and_eq_true] at hw
    simp only [evO]
    rw [ev_congr w a d ρ ρ' hw.1 h]
    refine ihb (d + 1) _ _ hw.2 (fun x hx => ?_)
    by_cases hxd : x = d
    · subst hxd; simp
    · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]; exact h x (by omega)

variable {V : ℕ}

/-- Compilation of output programs. -/
def compO (V : ℕ) : O → ℕ → ℕ → Pr (V + 1)
  | .nil, _, _ => .skip
  | .bit e, d, sp => .seq (comp V e d sp (sp + 1)) (.out (.v (fv V sp)))
  | .nat e, d, sp => .seq (comp V e d sp (sp + 1)) (emitNat (fv V sp) (fv V (sp + 1)) (fv V (sp + 2)))
  | .seq a b, d, sp => .seq (compO V a d sp) (compO V b d sp)
  | .ite c a b, d, sp => .seq (comp V c d sp (sp + 1))
      (.ite (.v (fv V sp)) (compO V a d sp) (compO V b d sp))
  | .loop n body, d, sp => .seq (comp V n d sp (sp + 1))
      (.loop (fv V d) (.v (fv V sp)) (compO V body (d + 1) (sp + 1)))
  | .lett a body, d, sp => .seq (comp V a d sp (sp + 1))
      (.seq (.set (fv V d) (.v (fv V sp))) (compO V body (d + 1) sp))

section Correct

variable {w : Word} {C : ℕ}

lemma bound_env {ρ : Fin (V + 1) → ℕ} {ρ' : Fin (V + 1) → ℕ} {δ : ℕ → ℕ} {d : ℕ} (hdV : d ≤ V)
    (h : ∀ x < d, envOf ρ x ≤ (w.length + 2) ^ δ x) (hfr : ∀ z, z < d → ρ' (fv V z) = ρ (fv V z)) :
    ∀ x < d, envOf ρ' x ≤ (w.length + 2) ^ δ x := by
  intro x hx
  show ρ' (fv V x) ≤ _
  rw [hfr x hx]; exact h x hx

/-- **Correctness of the output compiler.** -/
theorem run_compO (hC : 2 ≤ C) (SB : ℕ) : ∀ (o : O) (d sp : ℕ) (ρ : Fin (V + 1) → ℕ) (δ : ℕ → ℕ),
    o.wf d = true → d + o.bd ≤ SB → SB ≤ sp → sp + o.sn ≤ V →
    (∀ x < d, envOf ρ x ≤ (w.length + 2) ^ δ x) → (w.length + 2) ^ o.dg d δ ≤ C →
    ((compO V o d sp).run w C ρ).2 = evO w d (envOf ρ) o ∧
    ∀ z, z ≤ V → (z < d ∨ (SB ≤ z ∧ z < sp)) →
      ((compO V o d sp).run w C ρ).1 (fv V z) = ρ (fv V z) := by
  have hX : 2 ≤ w.length + 2 := by omega
  intro o
  induction o with
  | nil => intro d sp ρ δ _ _ _ _ _ _; exact ⟨rfl, fun _ _ _ => rfl⟩
  | bit e =>
    intro d sp ρ δ hw hbd hSB hsp hρ hC'
    simp only [O.wf] at hw; simp only [O.bd] at hbd; simp only [O.sn] at hsp
    simp only [O.dg] at hC'
    obtain ⟨c1, c2, c3⟩ := run_comp (V := V) (w := w) (C := C) (by omega) SB e d sp (sp + 1) ρ hw
      (by omega) hSB (by omega) (by omega)
    have hev := (eval_eq_ev e d (envOf ρ) δ hw hρ hC').1
    simp only [compO, run_seq, run_out, eval_v, c1, c2, hev, List.nil_append, evO]
    exact ⟨trivial, fun z hz hzr => c3 z hz (by omega) (by omega)⟩
  | nat e =>
    intro d sp ρ δ hw hbd hSB hsp hρ hC'
    simp only [O.wf] at hw; simp only [O.bd] at hbd; simp only [O.sn] at hsp
    simp only [O.dg] at hC'
    obtain ⟨c1, c2, c3⟩ := run_comp (V := V) (w := w) (C := C) (by omega) SB e d sp (sp + 1) ρ hw
      (by omega) hSB (by omega) (by omega)
    have hev := (eval_eq_ev e d (envOf ρ) δ hw hρ hC').1
    obtain ⟨e1, e2⟩ := run_emitNat (w := w) (C := C) (fv V sp) (fv V (sp + 1)) (fv V (sp + 2))
      (fv_ne (by omega) (by omega) (by omega)) hC ((comp V e d sp (sp + 1)).run w C ρ).1
    simp only [compO, run_seq, c1, List.nil_append, evO]
    refine ⟨by rw [e1, c2, hev], fun z hz hzr => ?_⟩
    rw [e2 _ (fv_ne hz (by omega) (by omega)) (fv_ne hz (by omega) (by omega))]
    exact c3 z hz (by omega) (by omega)
  | seq a b iha ihb =>
    intro d sp ρ δ hw hbd hSB hsp hρ hC'
    simp only [O.wf, Bool.and_eq_true] at hw; simp only [O.bd] at hbd; simp only [O.sn] at hsp
    simp only [O.dg] at hC'
    obtain ⟨a1, a2⟩ := iha d sp ρ δ hw.1 (by omega) hSB (by omega) hρ
      ((pow_mono hX (le_max_left _ _)).trans hC')
    set ρ1 := ((compO V a d sp).run w C ρ).1
    have hρ1 : ∀ x < d, envOf ρ1 x ≤ (w.length + 2) ^ δ x :=
      bound_env (by omega) hρ (fun z hz => a2 z (by omega) (Or.inl hz))
    obtain ⟨b1, b2⟩ := ihb d sp ρ1 δ hw.2 (by omega) hSB (by omega) hρ1
      ((pow_mono hX (le_max_right _ _)).trans hC')
    simp only [compO, run_seq, evO]
    refine ⟨?_, fun z hz hzr => by rw [b2 z hz hzr, a2 z hz hzr]⟩
    rw [a1]
    change _ ++ (Pr.run w C (compO V b d sp) ρ1).2 = _
    rw [b1, evO_congr w b d (envOf ρ1) (envOf ρ) hw.2 (fun x hx => a2 x (by omega) (Or.inl hx))]
  | ite c a b iha ihb =>
    intro d sp ρ δ hw hbd hSB hsp hρ hC'
    simp only [O.wf, Bool.and_eq_true] at hw; simp only [O.bd] at hbd; simp only [O.sn] at hsp
    simp only [O.dg] at hC'
    obtain ⟨c1, c2, c3⟩ := run_comp (V := V) (w := w) (C := C) (by omega) SB c d sp (sp + 1) ρ
      hw.1.1 (by omega) hSB (by omega) (by omega)
    have hev := (eval_eq_ev c d (envOf ρ) δ hw.1.1 hρ
      ((pow_mono hX (le_max_left _ _)).trans hC')).1
    set ρ1 := ((comp V c d sp (sp + 1)).run w C ρ).1
    have hρ1 : ∀ x < d, envOf ρ1 x ≤ (w.length + 2) ^ δ x :=
      bound_env (by omega) hρ (fun z hz => c3 z (by omega) (Or.inl hz) (by omega))
    have key : ∀ x < d, envOf ρ1 x = envOf ρ x := fun x hx => c3 x (by omega) (Or.inl hx) (by omega)
    simp only [compO, run_seq, c1, List.nil_append, evO]
    rw [run_ite]
    simp only [eval_v]
    simp only [show (Pr.run w C (comp V c d sp (sp + 1)) ρ).1 (fv V sp) = ev w d (envOf ρ) c from c2.trans hev]
    split_ifs with hcnd
    · obtain ⟨a1, a2⟩ := iha d sp ρ1 δ hw.1.2 (by omega) hSB (by omega) hρ1
        ((pow_mono hX ((le_max_left _ _).trans (le_max_right _ _))).trans hC')
      refine ⟨by rw [a1, evO_congr w a d _ _ hw.1.2 key], fun z hz hzr => ?_⟩
      rw [a2 z hz hzr]; exact c3 z hz (by omega) (by omega)
    · obtain ⟨b1, b2⟩ := ihb d sp ρ1 δ hw.2 (by omega) hSB (by omega) hρ1
        ((pow_mono hX ((le_max_right _ _).trans (le_max_right _ _))).trans hC')
      refine ⟨by rw [b1, evO_congr w b d _ _ hw.2 key], fun z hz hzr => ?_⟩
      rw [b2 z hz hzr]; exact c3 z hz (by omega) (by omega)
  | loop n body ihb =>
    intro d sp ρ δ hw hbd hSB hsp hρ hC'
    simp only [O.wf, Bool.and_eq_true] at hw; simp only [O.bd] at hbd; simp only [O.sn] at hsp
    simp only [O.dg] at hC'
    obtain ⟨c1, c2, c3⟩ := run_comp (V := V) (w := w) (C := C) (by omega) SB n d sp (sp + 1) ρ
      hw.1 (by omega) hSB (by omega) (by omega)
    obtain ⟨hev, hevb⟩ := eval_eq_ev n d (envOf ρ) δ hw.1 hρ
      ((pow_mono hX (le_max_left _ _)).trans hC')
    set ρ1 := ((comp V n d sp (sp + 1)).run w C ρ).1
    have key : ∀ x < d, ρ1 (fv V x) = ρ (fv V x) := fun x hx => c3 x (by omega) (Or.inl hx) (by omega)
    simp only [compO, run_seq, c1, List.nil_append, evO]
    have hL := run_loop_spec (w := w) (C := C) (fv V d) (.v (fv V sp))
      (compO V body (d + 1) (sp + 1)) ρ1
      (fun _ ρ' => ∀ z, z ≤ V → (z < d ∨ (SB ≤ z ∧ z < sp + 1)) → ρ' (fv V z) = ρ1 (fv V z))
      (fun i => evO w (d + 1) (Function.update (envOf ρ) d i) body) (fun _ _ _ => rfl) ?_
    · have hb : (Ex.v (fv V sp) : Ex V.succ).eval w C ρ1 = ev w d (envOf ρ) n := by
        simp only [eval_v]; rw [c2, hev]
      rw [hb] at hL
      refine ⟨hL.2, fun z hz hzr => ?_⟩
      rw [hL.1 z hz (by omega)]; exact c3 z hz (by omega) (by omega)
    · intro i hi ρ' hρ'
      have hi' : i < ev w d (envOf ρ) n := by simp only [eval_v] at hi; rwa [c2, hev] at hi
      set ρ'' := Function.update ρ' (fv V d) i
      have hbnd : ∀ x < d + 1, envOf ρ'' x ≤
          (w.length + 2) ^ Function.update δ d (n.dg d δ) x := by
        intro x hx
        simp only [ρ'']
        rw [envOf_update ρ' (by omega) i x (by omega)]
        refine update_bound (ρ := envOf ρ') (fun y hy => ?_) (hi'.le.trans hevb) x hx
        show ρ' (fv V y) ≤ _
        rw [hρ' y (by omega) (Or.inl hy), key y hy]; exact hρ y hy
      obtain ⟨b1, b2⟩ := ihb (d + 1) (sp + 1) ρ'' _ hw.2 (by omega) (by omega) (by omega) hbnd
        ((pow_mono hX (le_max_right _ _)).trans hC')
      refine ⟨fun z hz hzr => ?_, ?_⟩
      · rw [b2 z hz (by omega)]
        simp only [ρ'']
        rw [Function.update_of_ne (fv_ne hz (by omega) (by omega))]
        exact hρ' z hz hzr
      · rw [b1]
        refine evO_congr w body (d + 1) _ _ hw.2 (fun x hx => ?_)
        simp only [ρ'']
        rw [envOf_update ρ' (by omega) i x (by omega)]
        by_cases hxd : x = d
        · subst hxd; simp
        · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
          show ρ' (fv V x) = ρ (fv V x)
          rw [hρ' x (by omega) (Or.inl (by omega)), key x (by omega)]
  | lett a body ihb =>
    intro d sp ρ δ hw hbd hSB hsp hρ hC'
    simp only [O.wf, Bool.and_eq_true] at hw; simp only [O.bd] at hbd; simp only [O.sn] at hsp
    simp only [O.dg] at hC'
    obtain ⟨c1, c2, c3⟩ := run_comp (V := V) (w := w) (C := C) (by omega) SB a d sp (sp + 1) ρ
      hw.1 (by omega) hSB (by omega) (by omega)
    obtain ⟨hev, hevb⟩ := eval_eq_ev a d (envOf ρ) δ hw.1 hρ
      ((pow_mono hX (le_max_left _ _)).trans hC')
    set ρ1 := ((comp V a d sp (sp + 1)).run w C ρ).1
    have key : ∀ x < d, ρ1 (fv V x) = ρ (fv V x) := fun x hx => c3 x (by omega) (Or.inl hx) (by omega)
    set ρ2 := Function.update ρ1 (fv V d) (ρ1 (fv V sp))
    have hbnd : ∀ x < d + 1, envOf ρ2 x ≤
        (w.length + 2) ^ Function.update δ d (a.dg d δ) x := by
      intro x hx
      simp only [ρ2]
      rw [envOf_update ρ1 (by omega) _ x (by omega)]
      refine update_bound (ρ := envOf ρ1) (fun y hy => ?_) (by rw [c2, hev]; exact hevb) x hx
      show ρ1 (fv V y) ≤ _
      rw [key y hy]; exact hρ y hy
    obtain ⟨b1, b2⟩ := ihb (d + 1) sp ρ2 _ hw.2 (by omega) hSB (by omega) hbnd
      ((pow_mono hX (le_max_right _ _)).trans hC')
    simp only [compO, run_seq, run_set, eval_v, c1, List.nil_append, evO]
    refine ⟨?_, fun z hz hzr => ?_⟩
    · rw [b1]
      refine evO_congr w body (d + 1) _ _ hw.2 (fun x hx => ?_)
      simp only [ρ2]
      rw [envOf_update ρ1 (by omega) _ x (by omega)]
      by_cases hxd : x = d
      · subst hxd; simp [c2, hev]
      · rw [Function.update_of_ne hxd, Function.update_of_ne hxd]
        exact key x (by omega)
    · rw [b2 z hz (by omega)]
      simp only [ρ2]
      rw [Function.update_of_ne (fv_ne hz (by omega) (by omega))]
      exact c3 z hz (by omega) (by omega)

end Correct

/-- **Closed output programs compute logspace functions.** -/
theorem logspaceComputable_of_O (o : O) (ho : o.wf 0 = true) (f : Word → Word)
    (hf : ∀ w, evO w 0 (fun _ => 0) o = f w) : LogspaceComputable f := by
  refine logspaceComputable_of_output (o.dg 0 (fun _ => 0)) (compO (o.bd + o.sn) o 0 o.bd) f
    (fun w => ?_)
  unfold Pr.output
  have hC : 2 ≤ capOf (o.dg 0 (fun _ => 0)) w := by unfold capOf; omega
  have := (run_compO (V := o.bd + o.sn) (w := w) hC o.bd o 0 o.bd (fun _ => 0) (fun _ => 0) ho
    (by omega) le_rfl le_rfl (fun x hx => absurd hx (by omega))
    (by unfold capOf; omega)).1
  rw [this, ← hf w]
  rfl

end FE

end PathChecking
