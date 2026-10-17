module

public import RequestProject.Shallow.Prog.Tail

/-!
# A small specification calculus for the loop-language programs

`Sp x C P ρ W o Q`: running `P` from `ρ` emits `o`, changes only variables in `W` and ends in
a state satisfying `Q`.
-/

@[expose] public section

namespace PathChecking

namespace SQ

open LL CTLP ShallowP

variable {x : Word} {C : ℕ}

/-- Specification of a run. -/
def Sp (x : Word) (C : ℕ) (P : Pr V) (ρ : Fin V → ℕ) (W : List (Fin V)) (o : List Bool)
    (Q : (Fin V → ℕ) → Prop) : Prop :=
  ∃ ρ', P.run x C ρ = (ρ', o) ∧ (∀ v, v ∉ W → ρ' v = ρ v) ∧ Q ρ'

lemma Sp.mono {P : Pr V} {ρ : Fin V → ℕ} {W W' : List (Fin V)} {o : List Bool}
    {Q Q' : (Fin V → ℕ) → Prop} (h : Sp x C P ρ W o Q) (hW : ∀ z ∈ W, z ∈ W')
    (hQ : ∀ ρ', (∀ v, v ∉ W → ρ' v = ρ v) → Q ρ' → Q' ρ') : Sp x C P ρ W' o Q' := by
  obtain ⟨ρ', h1, h2, h3⟩ := h
  exact ⟨ρ', h1, fun v hv => h2 v (fun h => hv (hW v h)), hQ ρ' h2 h3⟩

lemma Sp.out_eq {P : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {o o' : List Bool}
    {Q : (Fin V → ℕ) → Prop} (h : Sp x C P ρ W o Q) (e : o = o') : Sp x C P ρ W o' Q := e ▸ h

lemma sp_seq {s t : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {o1 o2 : List Bool}
    {Q1 Q : (Fin V → ℕ) → Prop} (h1 : Sp x C s ρ W o1 Q1)
    (h2 : ∀ ρ1, (∀ v, v ∉ W → ρ1 v = ρ v) → Q1 ρ1 → Sp x C t ρ1 W o2 Q) :
    Sp x C (.seq s t) ρ W (o1 ++ o2) Q := by
  obtain ⟨ρ1, r1, f1, q1⟩ := h1
  obtain ⟨ρ2, r2, f2, q2⟩ := h2 ρ1 f1 q1
  refine ⟨ρ2, ?_, fun v hv => (f2 v hv).trans (f1 v hv), q2⟩
  simp [run_seq, r1, r2]

lemma sp_skip {ρ : Fin V → ℕ} {W : List (Fin V)} {Q : (Fin V → ℕ) → Prop} (h : Q ρ) :
    Sp x C .skip ρ W [] Q := ⟨ρ, rfl, fun _ _ => rfl, h⟩

lemma sp_set {y : Fin V} {e : Ex V} {ρ : Fin V → ℕ} {W : List (Fin V)}
    {Q : (Fin V → ℕ) → Prop} (hy : y ∈ W) (h : Q (Function.update ρ y (e.eval x C ρ))) :
    Sp x C (.set y e) ρ W [] Q :=
  ⟨_, rfl, fun _ hv => Function.update_of_ne (ne_of_nmem hv hy) _ _, h⟩

lemma sp_outToks {ts : List Tok} {ρ : Fin V → ℕ} {W : List (Fin V)} {Q : (Fin V → ℕ) → Prop}
    (h : Q ρ) : Sp x C (outToks ts) ρ W (encodeToks ts) Q :=
  ⟨ρ, run_outToks _ _, fun _ _ => rfl, h⟩

lemma sp_ite_pos {e : Ex V} {s t : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {o : List Bool}
    {Q : (Fin V → ℕ) → Prop} (he : e.eval x C ρ ≠ 0) (h : Sp x C s ρ W o Q) :
    Sp x C (.ite e s t) ρ W o Q := by
  obtain ⟨ρ', r, f, q⟩ := h
  exact ⟨ρ', by rw [run_ite_pos he, r], f, q⟩

lemma sp_ite_neg {e : Ex V} {s t : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {o : List Bool}
    {Q : (Fin V → ℕ) → Prop} (he : e.eval x C ρ = 0) (h : Sp x C t ρ W o Q) :
    Sp x C (.ite e s t) ρ W o Q := by
  obtain ⟨ρ', r, f, q⟩ := h
  exact ⟨ρ', by rw [run_ite_neg he, r], f, q⟩

/-- Loop rule: every iteration emits `out k` and preserves the frame `W` (relative to the
start state); the loop counter must belong to `W`. -/
lemma sp_loop (y : Fin V) (e : Ex V) (body : Pr V) (ρ : Fin V → ℕ) (W : List (Fin V))
    (out : ℕ → List Bool) (hy : y ∈ W)
    (hbody : ∀ k < e.eval x C ρ, ∀ ρ', (∀ v, v ∉ W → ρ' v = ρ v) →
      Sp x C body (Function.update ρ' y k) W (out k) (fun _ => True)) :
    Sp x C (.loop y e body) ρ W ((List.range (e.eval x C ρ)).flatMap out) (fun _ => True) := by
  obtain ⟨ρ', h1, h2⟩ := run_loop_emit y e body ρ W out (fun k hk ρ' hρ' => by
    obtain ⟨ρ'', r, f, -⟩ := hbody k hk ρ' hρ'
    refine ⟨ρ'', r, fun v hv => ?_⟩
    rw [f v hv, Function.update_of_ne (ne_of_nmem hv hy), hρ' v hv])
  exact ⟨ρ', h1, h2, trivial⟩

/-- Loop rule over a position range. -/
lemma sp_rng (y : Fin V) (e : Ex V) (body : Pr V) (ρ : Fin V → ℕ) (W : List (Fin V))
    (A : ℕ) (f : ℕ → List Tok) (hy : y ∈ W)
    (hbody : ∀ k < e.eval x C ρ, ∀ ρ', (∀ v, v ∉ W → ρ' v = ρ v) →
      Sp x C body (Function.update ρ' y k) W (encodeToks (f (A + k))) (fun _ => True)) :
    Sp x C (.loop y e body) ρ W (encodeToks (rng A (e.eval x C ρ) f)) (fun _ => True) := by
  have := sp_loop y e body ρ W (fun k => encodeToks (f (A + k))) hy hbody
  rwa [rng, encodeToks_flatMap]

/-- Silent programs with a known frame. -/
lemma sp_of_silent {P : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {Q : (Fin V → ℕ) → Prop}
    (hs : (P.run x C ρ).2 = []) (hW : ∀ z ∈ P.wr, z ∈ W) (hQ : Q (P.run x C ρ).1) :
    Sp x C P ρ W [] Q :=
  ⟨(P.run x C ρ).1, Prod.ext rfl hs, fun v hv => frame_of_sub hW ρ v hv, hQ⟩

lemma Sp.frame {P : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {o : List Bool}
    {Q : (Fin V → ℕ) → Prop} (h : Sp x C P ρ W o Q) :
    Sp x C P ρ W o (fun ρ' => Q ρ' ∧ ∀ v, v ∉ W → ρ' v = ρ v) := by
  obtain ⟨ρ', r, f, q⟩ := h
  exact ⟨ρ', r, f, q, f⟩

/-- Silent loop rule with an invariant. -/
lemma sp_loop_inv (y : Fin V) (e : Ex V) (body : Pr V) (ρ : Fin V → ℕ) (W : List (Fin V))
    (I : ℕ → (Fin V → ℕ) → Prop) (hy : y ∈ W) (h0 : I 0 ρ)
    (hbody : ∀ k < e.eval x C ρ, ∀ ρ', (∀ v, v ∉ W → ρ' v = ρ v) → I k ρ' →
      Sp x C body (Function.update ρ' y k) W [] (I (k + 1))) :
    Sp x C (.loop y e body) ρ W [] (I (e.eval x C ρ)) := by
  have h := run_loop_spec (w := x) (C := C) y e body ρ
    (fun i ρ' => (∀ v, v ∉ W → ρ' v = ρ v) ∧ I i ρ') (fun _ => [])
    ⟨fun _ _ => rfl, h0⟩ (fun k hk ρ' ⟨f, hI⟩ => by
      obtain ⟨ρ'', r, f', q⟩ := hbody k hk ρ' f hI
      rw [r]
      refine ⟨⟨fun v hv => ?_, q⟩, rfl⟩
      show ρ'' v = ρ v
      rw [f' v hv, Function.update_of_ne (ne_of_nmem hv hy), f v hv])
  exact ⟨_, Prod.ext rfl (by rw [h.2]; simp), h.1.1, h.1.2⟩

lemma sp_seq_assoc {a b c : Pr V} {ρ : Fin V → ℕ} {W : List (Fin V)} {o : List Bool}
    {Q : (Fin V → ℕ) → Prop} (h : Sp x C (.seq (.seq a b) c) ρ W o Q) :
    Sp x C (.seq a (.seq b c)) ρ W o Q := by
  obtain ⟨ρ', r, f, hq⟩ := h
  refine ⟨ρ', ?_, f, hq⟩
  rw [← r]
  simp [run_seq, List.append_assoc]

end SQ

end PathChecking
