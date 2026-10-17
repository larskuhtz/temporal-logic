module

public import RequestProject.PTime.RTok

/-!
# A structured language with variables, expressions and a monotone memory

Programs over `m` natural-number variables, with expressions built from constants, `+`,
truncated `-`, `*`, comparison, random access to the input tokens (`rtok`) and to a monotone bit
memory.  The big-step semantics `HEval w B` requires that all values computed by expressions are
at most `B`.  In `PTime/HLComp.lean` programs are compiled into the register language of
`PTime/Prog.lean`.
-/

@[expose] public section

namespace PathChecking

namespace HL

open PT

/-- Expressions. -/
inductive Ex (m : ℕ)
  | var (i : Fin m)
  | const (k : ℕ)
  | add (a b : Ex m)
  | sub (a b : Ex m)
  | mul (a b : Ex m)
  /-- `1` if `a < b`, else `0` -/
  | lt (a b : Ex m)
  /-- the code of the input token number `a` -/
  | tok (a : Ex m)
  /-- `1` if memory bit `a` is set, else `0` -/
  | mem (a : Ex m)

/-- States: variables, memory, output. -/
structure HSt (m : ℕ) where
  v : Fin m → ℕ
  mem : Finset ℕ
  out : List Bool

/-- Values of expressions. -/
noncomputable def Ex.ev {m : ℕ} (w : Word) (σ : HSt m) : Ex m → ℕ
  | .var i => σ.v i
  | .const k => k
  | .add a b => a.ev w σ + b.ev w σ
  | .sub a b => a.ev w σ - b.ev w σ
  | .mul a b => a.ev w σ * b.ev w σ
  | .lt a b => if a.ev w σ < b.ev w σ then 1 else 0
  | .tok a => rtok w (a.ev w σ)
  | .mem a => if a.ev w σ ∈ σ.mem then 1 else 0

/-- All values computed while evaluating the expression are at most `B`. -/
def Ex.Bnd {m : ℕ} (w : Word) (B : ℕ) (σ : HSt m) : Ex m → Prop
  | .var i => σ.v i ≤ B
  | .const k => k ≤ B
  | .add a b => a.Bnd w B σ ∧ b.Bnd w B σ ∧ a.ev w σ + b.ev w σ ≤ B
  | .sub a b => a.Bnd w B σ ∧ b.Bnd w B σ
  | .mul a b => a.Bnd w B σ ∧ b.Bnd w B σ ∧ a.ev w σ * b.ev w σ ≤ B
  | .lt a b => a.Bnd w B σ ∧ b.Bnd w B σ
  | .tok a => a.Bnd w B σ
  | .mem a => a.Bnd w B σ

/-- Statements. -/
inductive Hs (m : ℕ)
  | skip
  | set (i : Fin m) (e : Ex m)
  | mset (e : Ex m)
  | out (b : Bool)
  | seq (s t : Hs m)
  /-- branch on `e ≠ 0` -/
  | ite (e : Ex m) (s t : Hs m)
  /-- `while e ≠ 0 do s` -/
  | loop (e : Ex m) (s : Hs m)

/-- Sequential composition. -/
scoped infixr:30 " ;; " => Hs.seq

/-- Update a variable. -/
def HSt.set {m : ℕ} (σ : HSt m) (i : Fin m) (x : ℕ) : HSt m :=
  { σ with v := Function.update σ.v i x }

/-- Big-step semantics. -/
inductive HEval {m : ℕ} (w : Word) (B : ℕ) : Hs m → HSt m → HSt m → Prop
  | skip (σ : HSt m) : HEval w B .skip σ σ
  | set (σ : HSt m) (i : Fin m) (e : Ex m) : e.Bnd w B σ →
      HEval w B (.set i e) σ (σ.set i (e.ev w σ))
  | mset (σ : HSt m) (e : Ex m) : e.Bnd w B σ →
      HEval w B (.mset e) σ { σ with mem := insert (e.ev w σ) σ.mem }
  | out (σ : HSt m) (b : Bool) : HEval w B (.out b) σ { σ with out := σ.out ++ [b] }
  | seq {s t : Hs m} {σ₁ σ₂ σ₃ : HSt m} :
      HEval w B s σ₁ σ₂ → HEval w B t σ₂ σ₃ → HEval w B (.seq s t) σ₁ σ₃
  | iteT {e : Ex m} {s t : Hs m} {σ σ' : HSt m} : e.Bnd w B σ → e.ev w σ ≠ 0 →
      HEval w B s σ σ' → HEval w B (.ite e s t) σ σ'
  | iteF {e : Ex m} {s t : Hs m} {σ σ' : HSt m} : e.Bnd w B σ → e.ev w σ = 0 →
      HEval w B t σ σ' → HEval w B (.ite e s t) σ σ'
  | loopT {e : Ex m} {s : Hs m} {σ₁ σ₂ σ₃ : HSt m} : e.Bnd w B σ₁ → e.ev w σ₁ ≠ 0 →
      HEval w B s σ₁ σ₂ → HEval w B (.loop e s) σ₂ σ₃ → HEval w B (.loop e s) σ₁ σ₃
  | loopF {e : Ex m} {s : Hs m} {σ : HSt m} : e.Bnd w B σ → e.ev w σ = 0 →
      HEval w B (.loop e s) σ σ

/-! ## Weakest-precondition reasoning -/

variable {m : ℕ} {w : Word} {B : ℕ}

/-- `s` started in `σ` terminates in a state satisfying `Q`. -/
def HAch (w : Word) (B : ℕ) (s : Hs m) (σ : HSt m) (Q : HSt m → Prop) : Prop :=
  ∃ σ', HEval w B s σ σ' ∧ Q σ'

lemma HAch.mono {s : Hs m} {σ : HSt m} {Q Q' : HSt m → Prop} (h : HAch w B s σ Q)
    (hQ : ∀ σ', Q σ' → Q' σ') : HAch w B s σ Q' := by
  obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', h1, hQ _ h2⟩

lemma hach_skip {σ : HSt m} {Q : HSt m → Prop} (h : Q σ) : HAch w B .skip σ Q :=
  ⟨σ, HEval.skip σ, h⟩

lemma hach_set {σ : HSt m} {i : Fin m} {e : Ex m} {Q : HSt m → Prop} (hb : e.Bnd w B σ)
    (h : Q (σ.set i (e.ev w σ))) : HAch w B (.set i e) σ Q :=
  ⟨_, HEval.set σ i e hb, h⟩

lemma hach_mset {σ : HSt m} {e : Ex m} {Q : HSt m → Prop} (hb : e.Bnd w B σ)
    (h : Q { σ with mem := insert (e.ev w σ) σ.mem }) : HAch w B (.mset e) σ Q :=
  ⟨_, HEval.mset σ e hb, h⟩

lemma hach_out {σ : HSt m} {b : Bool} {Q : HSt m → Prop}
    (h : Q { σ with out := σ.out ++ [b] }) : HAch w B (.out b) σ Q :=
  ⟨_, HEval.out σ b, h⟩

lemma hach_seq {s t : Hs m} {σ : HSt m} {Q : HSt m → Prop}
    (h : HAch w B s σ (fun σ₁ => HAch w B t σ₁ Q)) : HAch w B (.seq s t) σ Q := by
  obtain ⟨σ₁, h1, σ₂, h2, hQ⟩ := h; exact ⟨σ₂, HEval.seq h1 h2, hQ⟩

lemma hach_ite {e : Ex m} {s t : Hs m} {σ : HSt m} {Q : HSt m → Prop} (hb : e.Bnd w B σ)
    (h : if e.ev w σ ≠ 0 then HAch w B s σ Q else HAch w B t σ Q) : HAch w B (.ite e s t) σ Q := by
  by_cases hc : e.ev w σ ≠ 0
  · rw [if_pos hc] at h; obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', HEval.iteT hb hc h1, h2⟩
  · rw [if_neg hc] at h; obtain ⟨σ', h1, h2⟩ := h
    exact ⟨σ', HEval.iteF hb (by simpa using hc) h1, h2⟩

lemma hach_iteT {e : Ex m} {s t : Hs m} {σ : HSt m} {Q : HSt m → Prop} (hb : e.Bnd w B σ)
    (hc : e.ev w σ ≠ 0) (h : HAch w B s σ Q) : HAch w B (.ite e s t) σ Q :=
  hach_ite hb (by rw [if_pos hc]; exact h)

lemma hach_iteF {e : Ex m} {s t : Hs m} {σ : HSt m} {Q : HSt m → Prop} (hb : e.Bnd w B σ)
    (hc : e.ev w σ = 0) (h : HAch w B t σ Q) : HAch w B (.ite e s t) σ Q :=
  hach_ite hb (by rw [if_neg (by simpa using hc)]; exact h)

/-- The loop rule, with a measure-indexed invariant. -/
lemma hach_loop {e : Ex m} {s : Hs m} (I : ℕ → HSt m → Prop) (Q : HSt m → Prop)
    (h : ∀ n σ, I n σ → e.Bnd w B σ ∧ ((e.ev w σ = 0 ∧ Q σ) ∨
      (e.ev w σ ≠ 0 ∧ HAch w B s σ (fun σ' => ∃ k < n, I k σ')))) :
    ∀ n σ, I n σ → HAch w B (.loop e s) σ Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hI
    obtain ⟨hb, h'⟩ := h n σ hI
    rcases h' with ⟨hc, hQ⟩ | ⟨hc, σ₁, h1, k, hk, hI'⟩
    · exact ⟨σ, HEval.loopF hb hc, hQ⟩
    · obtain ⟨σ₂, h2, hQ⟩ := ih k hk σ₁ hI'
      exact ⟨σ₂, HEval.loopT hb hc h1 h2, hQ⟩

@[simp] lemma HSt.set_v (σ : HSt m) (i : Fin m) (x : ℕ) :
    (σ.set i x).v = Function.update σ.v i x := rfl
@[simp] lemma HSt.set_mem (σ : HSt m) (i : Fin m) (x : ℕ) : (σ.set i x).mem = σ.mem := rfl
@[simp] lemma HSt.set_out (σ : HSt m) (i : Fin m) (x : ℕ) : (σ.set i x).out = σ.out := rfl

end HL

end PathChecking
