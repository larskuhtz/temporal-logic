module

public import RequestProject.LogLang.Main

/-!
# A library for reasoning about programs of the loop language

* expression notation and evaluation lemmas;
* the variables written by a program (`Pr.wr`) and the frame lemma `Pr.run_frame`;
* the loop rule `run_loop_spec` (invariant plus per-iteration output);
* output of fixed bit strings, tokens and binary numbers.
-/

@[expose] public section

namespace PathChecking

namespace LL

variable {V : ℕ}

/-! ## Expression notation -/

namespace Ex
/-- `a + b` (capped) -/
abbrev add' (a b : Ex V) : Ex V := .bin .add a b
/-- `a - b` -/
abbrev sub' (a b : Ex V) : Ex V := .bin .sub a b
/-- `a * b` (capped) -/
abbrev mul' (a b : Ex V) : Ex V := .bin .mul a b
/-- `a / b` -/
abbrev div' (a b : Ex V) : Ex V := .bin .div a b
/-- `a % b` -/
abbrev mod' (a b : Ex V) : Ex V := .bin .mod a b
/-- `[a < b]` -/
abbrev lt' (a b : Ex V) : Ex V := .bin .lt a b
/-- `[a = b]` -/
abbrev eq' (a b : Ex V) : Ex V := .bin .eq a b
/-- `[a ≠ 0 ∧ b ≠ 0]` -/
abbrev and' (a b : Ex V) : Ex V := .bin .lt (.c 0) (.bin .mul a b)
/-- `[a = 0]` -/
abbrev not' (a : Ex V) : Ex V := .bin .eq a (.c 0)
/-- `[a ≠ 0 ∨ b ≠ 0]` -/
abbrev or' (a b : Ex V) : Ex V := .bin .lt (.c 0) (.bin .add a b)
end Ex

section Eval
variable {w : Word} {C : ℕ} {ρ : Fin V → ℕ}

@[simp] lemma eval_c (k : ℕ) : (Ex.c k : Ex V).eval w C ρ = min k C := rfl
@[simp] lemma eval_v (x : Fin V) : (Ex.v x).eval w C ρ = ρ x := rfl
@[simp] lemma eval_len : (Ex.len : Ex V).eval w C ρ = min w.length C := rfl
@[simp] lemma eval_inp (e : Ex V) : (Ex.inp e).eval w C ρ = symNum (inputSym w (e.eval w C ρ)) :=
  rfl
@[simp] lemma eval_bin (o : BOp) (a b : Ex V) :
    (Ex.bin o a b).eval w C ρ = o.ap C (a.eval w C ρ) (b.eval w C ρ) := rfl

@[simp] lemma ap_add (a b : ℕ) : BOp.add.ap C a b = min (a + b) C := rfl
@[simp] lemma ap_sub (a b : ℕ) : BOp.sub.ap C a b = a - b := rfl
@[simp] lemma ap_mul (a b : ℕ) : BOp.mul.ap C a b = min (a * b) C := rfl
@[simp] lemma ap_div (a b : ℕ) : BOp.div.ap C a b = a / b := rfl
@[simp] lemma ap_mod (a b : ℕ) : BOp.mod.ap C a b = a % b := rfl
@[simp] lemma ap_lt (a b : ℕ) : BOp.lt.ap C a b = if a < b then 1 else 0 := rfl
@[simp] lemma ap_eq (a b : ℕ) : BOp.eq.ap C a b = if a = b then 1 else 0 := rfl

end Eval

/-! ## Running programs -/

section Run
variable {w : Word} {C : ℕ}

@[simp] lemma run_skip (ρ : Fin V → ℕ) : (Pr.skip : Pr V).run w C ρ = (ρ, []) := rfl
@[simp] lemma run_set (x : Fin V) (e : Ex V) (ρ : Fin V → ℕ) :
    (Pr.set x e).run w C ρ = (Function.update ρ x (e.eval w C ρ), []) := rfl
@[simp] lemma run_out (e : Ex V) (ρ : Fin V → ℕ) :
    (Pr.out e).run w C ρ = (ρ, [decide (e.eval w C ρ ≠ 0)]) := rfl
@[simp] lemma run_seq (s t : Pr V) (ρ : Fin V → ℕ) :
    (Pr.seq s t).run w C ρ = ((t.run w C (s.run w C ρ).1).1,
      (s.run w C ρ).2 ++ (t.run w C (s.run w C ρ).1).2) := rfl
lemma run_ite (e : Ex V) (s t : Pr V) (ρ : Fin V → ℕ) :
    (Pr.ite e s t).run w C ρ = if e.eval w C ρ ≠ 0 then s.run w C ρ else t.run w C ρ := rfl

lemma run_ite_pos {e : Ex V} {s t : Pr V} {ρ : Fin V → ℕ} (h : e.eval w C ρ ≠ 0) :
    (Pr.ite e s t).run w C ρ = s.run w C ρ := if_pos h
lemma run_ite_neg {e : Ex V} {s t : Pr V} {ρ : Fin V → ℕ} (h : e.eval w C ρ = 0) :
    (Pr.ite e s t).run w C ρ = t.run w C ρ := if_neg (by simpa using h)

/-- **Loop rule.**  If the invariant `I i` is preserved by every iteration `i < L` and
iteration `i` outputs `O i`, then after the loop `I L` holds and the output is the
concatenation of the `O i`. -/
lemma run_loop_spec (x : Fin V) (e : Ex V) (s : Pr V) (ρ : Fin V → ℕ)
    (I : ℕ → (Fin V → ℕ) → Prop) (O : ℕ → List Bool) (h0 : I 0 ρ)
    (hstep : ∀ i < e.eval w C ρ, ∀ ρ', I i ρ' →
      I (i + 1) (s.run w C (Function.update ρ' x i)).1 ∧
        (s.run w C (Function.update ρ' x i)).2 = O i) :
    I (e.eval w C ρ) ((Pr.loop x e s).run w C ρ).1 ∧
      ((Pr.loop x e s).run w C ρ).2 = (List.range (e.eval w C ρ)).flatMap O := by
  rw [run_loop]
  have key : ∀ j, j ≤ e.eval w C ρ →
      I j ((List.range j).foldl (loopF w C x s) (ρ, [])).1 ∧
        ((List.range j).foldl (loopF w C x s) (ρ, [])).2 = (List.range j).flatMap O := by
    intro j
    induction j with
    | zero => intro _; exact ⟨h0, rfl⟩
    | succ j ih =>
      intro hj
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨h3, h4⟩ := hstep j (by omega) _ h1
      rw [foldl_range_succ, List.range_succ, List.flatMap_append]
      refine ⟨h3, ?_⟩
      simp only [loopF, h2, h4, List.flatMap_singleton]
  exact key _ le_rfl

/-- Loop rule for invariants only. -/
lemma run_loop_inv (x : Fin V) (e : Ex V) (s : Pr V) (ρ : Fin V → ℕ)
    (I : ℕ → (Fin V → ℕ) → Prop) (h0 : I 0 ρ)
    (hstep : ∀ i < e.eval w C ρ, ∀ ρ', I i ρ' → I (i + 1) (s.run w C (Function.update ρ' x i)).1) :
    I (e.eval w C ρ) ((Pr.loop x e s).run w C ρ).1 := by
  rw [run_loop]
  have key : ∀ j, j ≤ e.eval w C ρ →
      I j ((List.range j).foldl (loopF w C x s) (ρ, [])).1 := by
    intro j
    induction j with
    | zero => intro _; exact h0
    | succ j ih =>
      intro hj
      rw [foldl_range_succ]
      exact hstep j (by omega) _ (ih (by omega))
  exact key _ le_rfl

/-- Variables (possibly) written by a program. -/
def Pr.wr : Pr V → List (Fin V)
  | .skip => []
  | .set x _ => [x]
  | .out _ => []
  | .seq s t => s.wr ++ t.wr
  | .ite _ s t => s.wr ++ t.wr
  | .loop x _ s => x :: s.wr

/-- **Frame lemma**: variables that are not written keep their values. -/
lemma Pr.run_frame (s : Pr V) : ∀ (ρ : Fin V → ℕ) (z : Fin V), z ∉ s.wr →
    (s.run w C ρ).1 z = ρ z := by
  induction s with
  | skip => intro ρ z _; rfl
  | set x e =>
    intro ρ z hz
    simp only [Pr.wr, List.mem_singleton] at hz
    simp [Function.update_of_ne hz]
  | out e => intro ρ z _; rfl
  | seq s t ihs iht =>
    intro ρ z hz
    simp only [Pr.wr, List.mem_append, not_or] at hz
    simp only [run_seq]
    rw [iht _ z hz.2, ihs _ z hz.1]
  | ite e s t ihs iht =>
    intro ρ z hz
    simp only [Pr.wr, List.mem_append, not_or] at hz
    rw [run_ite]
    split_ifs
    · exact ihs _ z hz.1
    · exact iht _ z hz.2
  | loop x e s ih =>
    intro ρ z hz
    simp only [Pr.wr, List.mem_cons, not_or] at hz
    exact run_loop_inv x e s ρ (fun _ ρ' => ρ' z = ρ z) rfl (fun i _ ρ' hρ' => by
      show _ = _; rw [ih _ z hz.2, Function.update_of_ne hz.1]; exact hρ')

/-- Programs without output statements. -/
def Pr.silent : Pr V → Bool
  | .skip => true
  | .set _ _ => true
  | .out _ => false
  | .seq s t => s.silent && t.silent
  | .ite _ s t => s.silent && t.silent
  | .loop _ _ s => s.silent

/-- Silent programs produce no output. -/
lemma Pr.run_silent (s : Pr V) (hs : s.silent = true) : ∀ ρ, (s.run w C ρ).2 = [] := by
  induction s with
  | skip => intro ρ; rfl
  | set x e => intro ρ; rfl
  | out e => simp [Pr.silent] at hs
  | seq s t ihs iht =>
    simp only [Pr.silent, Bool.and_eq_true] at hs
    intro ρ; simp [ihs hs.1, iht hs.2]
  | ite e s t ihs iht =>
    simp only [Pr.silent, Bool.and_eq_true] at hs
    intro ρ; rw [run_ite]; split_ifs
    · exact ihs hs.1 ρ
    · exact iht hs.2 ρ
  | loop x e s ih =>
    simp only [Pr.silent] at hs
    intro ρ
    have := (run_loop_spec (w := w) (C := C) x e s ρ (fun _ _ => True) (fun _ => []) trivial
      (fun i _ ρ' _ => ⟨trivial, ih hs _⟩)).2
    rw [this]; simp

end Run

end LL

end PathChecking
