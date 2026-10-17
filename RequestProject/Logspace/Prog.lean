module

public import RequestProject.Complexity

/-!
# A structured programming language for logspace computations

Programs have a finite number of natural-number registers (`Fin K`), a read-only two-way
input head (the same end-marked input tape as the Turing machines of `Complexity.lean`)
and a write-only output.  The only arithmetic operations are increment, decrement and
zero tests; control flow is structured (`seq`, `ite`, `loop`).

The big-step semantics `Eval w B s σ σ'` carries a bound `B` on the register values:
an increment is only allowed if the result is `≤ B`.  In `Logspace/Machine.lean` every
program is compiled into a Turing machine whose work tape stores the registers in binary,
so that a program whose registers stay below `B` runs in space `O(log B)`.

Here we also define an unstructured "goto" language and prove that the compilation of
structured programs into goto programs is correct.
-/

@[expose] public section

namespace PathChecking

deriving instance DecidableEq for InSym

namespace LS

/-- Program states: input head position, register file, output produced so far. -/
structure St (K : ℕ) where
  pos : ℕ
  reg : Fin K → ℕ
  out : List Bool

/-- Update a register. -/
def St.setReg {K : ℕ} (σ : St K) (r : Fin K) (v : ℕ) : St K :=
  { σ with reg := Function.update σ.reg r v }

@[simp] lemma St.setReg_pos {K : ℕ} (σ : St K) (r : Fin K) (v : ℕ) :
    (σ.setReg r v).pos = σ.pos := rfl
@[simp] lemma St.setReg_out {K : ℕ} (σ : St K) (r : Fin K) (v : ℕ) :
    (σ.setReg r v).out = σ.out := rfl
@[simp] lemma St.setReg_reg {K : ℕ} (σ : St K) (r : Fin K) (v : ℕ) :
    (σ.setReg r v).reg = Function.update σ.reg r v := rfl

/-- Initial state. -/
def St.init (K : ℕ) : St K := ⟨0, fun _ => 0, []⟩

/-- Conditions. -/
inductive Cond (K : ℕ)
  | zero (r : Fin K)
  | sym (s : InSym)
  | not (c : Cond K)

/-- Evaluation of a condition. -/
def Cond.eval {K : ℕ} (w : Word) (σ : St K) : Cond K → Bool
  | .zero r => decide (σ.reg r = 0)
  | .sym s => decide (inputSym w σ.pos = s)
  | .not c => !(c.eval w σ)

/-- Structured programs. -/
inductive Stmt (K : ℕ)
  | skip
  | inc (r : Fin K)
  | dec (r : Fin K)
  | left
  | right
  | out (b : Bool)
  | seq (s t : Stmt K)
  | ite (c : Cond K) (s t : Stmt K)
  | loop (c : Cond K) (s : Stmt K)

/-- Big-step semantics with register bound `B`. -/
inductive Eval {K : ℕ} (w : Word) (B : ℕ) : Stmt K → St K → St K → Prop
  | skip (σ : St K) : Eval w B .skip σ σ
  | inc (σ : St K) (r : Fin K) : σ.reg r < B → Eval w B (.inc r) σ (σ.setReg r (σ.reg r + 1))
  | dec (σ : St K) (r : Fin K) : Eval w B (.dec r) σ (σ.setReg r (σ.reg r - 1))
  | left (σ : St K) : Eval w B .left σ { σ with pos := σ.pos - 1 }
  | right (σ : St K) : Eval w B .right σ { σ with pos := min (σ.pos + 1) (w.length + 1) }
  | out (σ : St K) (b : Bool) : Eval w B (.out b) σ { σ with out := σ.out ++ [b] }
  | seq {s t : Stmt K} {σ₁ σ₂ σ₃ : St K} :
      Eval w B s σ₁ σ₂ → Eval w B t σ₂ σ₃ → Eval w B (.seq s t) σ₁ σ₃
  | iteT {c : Cond K} {s t : Stmt K} {σ σ' : St K} :
      c.eval w σ = true → Eval w B s σ σ' → Eval w B (.ite c s t) σ σ'
  | iteF {c : Cond K} {s t : Stmt K} {σ σ' : St K} :
      c.eval w σ = false → Eval w B t σ σ' → Eval w B (.ite c s t) σ σ'
  | loopT {c : Cond K} {s : Stmt K} {σ₁ σ₂ σ₃ : St K} :
      c.eval w σ₁ = true → Eval w B s σ₁ σ₂ → Eval w B (.loop c s) σ₂ σ₃ →
        Eval w B (.loop c s) σ₁ σ₃
  | loopF {c : Cond K} {s : Stmt K} {σ : St K} :
      c.eval w σ = false → Eval w B (.loop c s) σ σ

/-- Good states: the input head is on the tape and all registers are `≤ B`. -/
def Good {K : ℕ} (w : Word) (B : ℕ) (σ : St K) : Prop :=
  σ.pos ≤ w.length + 1 ∧ ∀ r, σ.reg r ≤ B

lemma Eval.good {K : ℕ} {w : Word} {B : ℕ} {s : Stmt K} {σ σ' : St K}
    (h : Eval w B s σ σ') (hσ : Good w B σ) : Good w B σ' := by
  induction h with
  | skip => exact hσ
  | inc σ r hr =>
    refine ⟨hσ.1, fun r' => ?_⟩
    by_cases hr' : r' = r
    · subst hr'; simp; omega
    · simp [Function.update_of_ne hr']; exact hσ.2 r'
  | dec σ r =>
    refine ⟨hσ.1, fun r' => ?_⟩
    by_cases hr' : r' = r
    · subst hr'; simp; have := hσ.2 r'; omega
    · simp [Function.update_of_ne hr']; exact hσ.2 r'
  | left σ => exact ⟨by simp; have := hσ.1; omega, hσ.2⟩
  | right σ => exact ⟨by simp, hσ.2⟩
  | out σ b => exact hσ
  | seq _ _ ih1 ih2 => exact ih2 (ih1 hσ)
  | iteT _ _ ih => exact ih hσ
  | iteF _ _ ih => exact ih hσ
  | loopT _ _ _ ih1 ih2 => exact ih2 (ih1 hσ)
  | loopF _ => exact hσ

/-! ## Goto programs -/

/-- Instructions of goto programs. -/
inductive GI (K : ℕ)
  | inc (r : Fin K)
  | dec (r : Fin K)
  | jz (r : Fin K) (t : ℕ)
  | jsym (s : InSym) (t : ℕ)
  | left
  | right
  | out (b : Bool)
  | jmp (t : ℕ)
  | halt

/-- Execution of a single goto instruction. -/
def gexec {K : ℕ} (ins : GI K) (w : Word) (a : ℕ × St K) : ℕ × St K :=
  match ins with
  | .inc r => (a.1 + 1, a.2.setReg r (a.2.reg r + 1))
  | .dec r => (a.1 + 1, a.2.setReg r (a.2.reg r - 1))
  | .jz r t => (if a.2.reg r = 0 then t else a.1 + 1, a.2)
  | .jsym s t => (if inputSym w a.2.pos = s then t else a.1 + 1, a.2)
  | .left => (a.1 + 1, { a.2 with pos := a.2.pos - 1 })
  | .right => (a.1 + 1, { a.2 with pos := min (a.2.pos + 1) (w.length + 1) })
  | .out b => (a.1 + 1, { a.2 with out := a.2.out ++ [b] })
  | .jmp t => (t, a.2)
  | .halt => a

/-- One step of a goto program (`halt` and positions outside the code are fixed points). -/
def gstep {K : ℕ} (code : List (GI K)) (w : Word) (a : ℕ × St K) : ℕ × St K :=
  gexec (code.getD a.1 .halt) w a

/-- Multi-step execution of a goto program through good states. -/
def GSteps {K : ℕ} (code : List (GI K)) (w : Word) (B : ℕ) : ℕ × St K → ℕ × St K → Prop :=
  Relation.ReflTransGen (fun a b => gstep code w a = b ∧ Good w B b.2)

/-- Code for a condition: jump to `t` if it holds, to `f` otherwise. -/
def condJ {K : ℕ} : Cond K → ℕ → ℕ → List (GI K)
  | .zero r, t, f => [.jz r t, .jmp f]
  | .sym s, t, f => [.jsym s t, .jmp f]
  | .not c, t, f => condJ c f t

lemma condJ_length {K : ℕ} (c : Cond K) (t f : ℕ) : (condJ c t f).length = 2 := by
  induction c generalizing t f <;> simp [condJ, *]

/-- Length of compiled code. -/
def clen {K : ℕ} : Stmt K → ℕ
  | .skip => 0
  | .inc _ => 1
  | .dec _ => 1
  | .left => 1
  | .right => 1
  | .out _ => 1
  | .seq s t => clen s + clen t
  | .ite _ s t => clen s + clen t + 3
  | .loop _ s => clen s + 3

/-- Compilation of a structured program placed at address `b`. -/
def comp {K : ℕ} : Stmt K → ℕ → List (GI K)
  | .skip, _ => []
  | .inc r, _ => [.inc r]
  | .dec r, _ => [.dec r]
  | .left, _ => [.left]
  | .right, _ => [.right]
  | .out x, _ => [.out x]
  | .seq s t, b => comp s b ++ comp t (b + clen s)
  | .ite c s t, b => condJ c (b + 2) (b + clen s + 3) ++ comp s (b + 2) ++
      [.jmp (b + clen s + clen t + 3)] ++ comp t (b + clen s + 3)
  | .loop c s, b => condJ c (b + 2) (b + clen s + 3) ++ comp s (b + 2) ++ [.jmp b]

lemma comp_length {K : ℕ} (s : Stmt K) (b : ℕ) : (comp s b).length = clen s := by
  induction s generalizing b <;> simp [comp, clen, condJ_length, *] <;> omega

/-- The goto program of a structured program, followed by `halt`. -/
def Stmt.code {K : ℕ} (s : Stmt K) : List (GI K) := comp s 0 ++ [.halt]

section Sim

variable {K : ℕ} {code : List (GI K)} {w : Word} {B : ℕ}

lemma getD_mid (pre c post : List (GI K)) (i : ℕ) (hi : i < c.length) :
    (pre ++ c ++ post).getD (pre.length + i) .halt = c.getD i .halt := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
  simp

lemma gsteps_single {a b : ℕ × St K} (h : gstep code w a = b) (hb : Good w B b.2) :
    GSteps code w B a b :=
  Relation.ReflTransGen.single ⟨h, hb⟩

lemma gstep_at (pre c post : List (GI K)) (i : ℕ) (hi : i < c.length) (σ : St K) :
    gstep (pre ++ c ++ post) w (pre.length + i, σ) = gexec (c.getD i .halt) w (pre.length + i, σ) := by
  rw [gstep, getD_mid pre c post i hi]

lemma condJ_sim (c : Cond K) (t f : ℕ) (pre post : List (GI K)) (σ : St K) (hσ : Good w B σ) :
    GSteps (pre ++ condJ c t f ++ post) w B (pre.length, σ)
      (if c.eval w σ then t else f, σ) := by
  induction c generalizing t f with
  | zero r =>
    have e0 := gstep_at (w := w) pre (condJ (.zero r) t f) post 0 (by simp [condJ]) σ
    have e1 := gstep_at (w := w) pre (condJ (.zero r) t f) post 1 (by simp [condJ]) σ
    simp only [add_zero] at e0
    by_cases hr : σ.reg r = 0
    · apply gsteps_single _ hσ
      rw [e0]; simp [condJ, gexec, hr, Cond.eval]
    · refine Relation.ReflTransGen.head (b := (pre.length + 1, σ)) ⟨?_, hσ⟩ ?_
      · rw [e0]; simp [condJ, gexec, hr]
      · apply gsteps_single _ hσ
        rw [e1]; simp [condJ, gexec, hr, Cond.eval]
  | sym s =>
    have e0 := gstep_at (w := w) pre (condJ (.sym s) t f) post 0 (by simp [condJ]) σ
    have e1 := gstep_at (w := w) pre (condJ (.sym s) t f) post 1 (by simp [condJ]) σ
    simp only [add_zero] at e0
    by_cases hr : inputSym w σ.pos = s
    · apply gsteps_single _ hσ
      rw [e0]; simp [condJ, gexec, hr, Cond.eval]
    · refine Relation.ReflTransGen.head (b := (pre.length + 1, σ)) ⟨?_, hσ⟩ ?_
      · rw [e0]; simp [condJ, gexec, hr]
      · apply gsteps_single _ hσ
        rw [e1]; simp [condJ, gexec, hr, Cond.eval]
  | not c ih =>
    have := ih f t
    simp only [condJ, Cond.eval]
    by_cases h : Cond.eval w σ c = true
    · simp only [h, if_true] at this; simpa [h] using this
    · simp only [h] at this; simpa [h] using this

/-- Correctness of the compilation into goto programs. -/
theorem comp_sim {s : Stmt K} {σ σ' : St K} (h : Eval w B s σ σ') (hσ : Good w B σ)
    (pre post : List (GI K)) :
    GSteps (pre ++ comp s pre.length ++ post) w B (pre.length, σ)
      (pre.length + clen s, σ') := by
  induction h generalizing pre post with
  | skip σ => simp [clen]; exact Relation.ReflTransGen.refl
  | inc σ r hr =>
    apply gsteps_single _ ((Eval.inc (w := w) σ r hr).good hσ)
    have := gstep_at (w := w) pre (comp (.inc r) pre.length) post 0 (by simp [comp]) σ
    rw [add_zero] at this; rw [this]; simp [comp, gexec, clen]
  | dec σ r =>
    apply gsteps_single _ ((Eval.dec (w := w) (B := B) σ r).good hσ)
    have := gstep_at (w := w) pre (comp (.dec r) pre.length) post 0 (by simp [comp]) σ
    rw [add_zero] at this; rw [this]; simp [comp, gexec, clen]
  | left σ =>
    apply gsteps_single _ ((Eval.left (w := w) (B := B) σ).good hσ)
    have := gstep_at (w := w) pre (comp (K := K) .left pre.length) post 0 (by simp [comp]) σ
    rw [add_zero] at this; rw [this]; simp [comp, gexec, clen]
  | right σ =>
    apply gsteps_single _ ((Eval.right (w := w) (B := B) σ).good hσ)
    have := gstep_at (w := w) pre (comp (K := K) .right pre.length) post 0 (by simp [comp]) σ
    rw [add_zero] at this; rw [this]; simp [comp, gexec, clen]
  | out σ b =>
    apply gsteps_single _ hσ
    have := gstep_at (w := w) pre (comp (K := K) (.out b) pre.length) post 0 (by simp [comp]) σ
    rw [add_zero] at this; rw [this]; simp [comp, gexec, clen]
  | @seq s t σ₁ σ₂ σ₃ h1 h2 ih1 ih2 =>
    have a1 := ih1 hσ pre (comp t (pre.length + clen s) ++ post)
    have a2 := ih2 (h1.good hσ) (pre ++ comp s pre.length) post
    simp only [List.length_append, comp_length] at a2
    have e1 : pre ++ comp (.seq s t) pre.length ++ post =
        pre ++ comp s pre.length ++ (comp t (pre.length + clen s) ++ post) := by
      simp [comp]
    have e2 : pre ++ comp (.seq s t) pre.length ++ post =
        pre ++ comp s pre.length ++ comp t (pre.length + clen s) ++ post := by
      simp [comp]
    have e3 : pre.length + clen (.seq s t) = pre.length + clen s + clen t := by
      simp [clen]; omega
    rw [e3]
    exact (e1 ▸ a1).trans (e2 ▸ a2)
  | @iteT c s t σ σ' hc h ih =>
    have a0 := condJ_sim c (pre.length + 2) (pre.length + clen s + 3) pre
      (comp s (pre.length + 2) ++ [.jmp (pre.length + clen s + clen t + 3)] ++ comp t (pre.length + clen s + 3) ++ post) σ hσ
    simp only [hc, if_true] at a0
    have a1 := ih hσ (pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3))
      ([.jmp (pre.length + clen s + clen t + 3)] ++ comp t (pre.length + clen s + 3) ++ post)
    simp only [List.length_append, condJ_length] at a1
    have a2 := gstep_at (w := w) (pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++ comp s (pre.length + 2))
      [.jmp (pre.length + clen s + clen t + 3)] (comp t (pre.length + clen s + 3) ++ post) 0 (by simp) σ'
    simp only [List.length_append, condJ_length, comp_length, add_zero] at a2
    have e0 : pre ++ comp (.ite c s t) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        (comp s (pre.length + 2) ++ [.jmp (pre.length + clen s + clen t + 3)] ++ comp t (pre.length + clen s + 3) ++ post) := by
      simp [comp]
    have e1 : pre ++ comp (.ite c s t) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        comp s (pre.length + 2) ++ ([.jmp (pre.length + clen s + clen t + 3)] ++ comp t (pre.length + clen s + 3) ++ post) := by
      simp [comp]
    have e2 : pre ++ comp (.ite c s t) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        comp s (pre.length + 2) ++ [.jmp (pre.length + clen s + clen t + 3)] ++ (comp t (pre.length + clen s + 3) ++ post) := by
      simp [comp]
    refine (e0 ▸ a0).trans ((e1 ▸ a1).trans (gsteps_single ?_ (h.good hσ)))
    rw [e2, a2]; simp [gexec, clen]; omega
  | @iteF c s t σ σ' hc h ih =>
    have a0 := condJ_sim c (pre.length + 2) (pre.length + clen s + 3) pre
      (comp s (pre.length + 2) ++ [.jmp (pre.length + clen s + clen t + 3)] ++ comp t (pre.length + clen s + 3) ++ post) σ hσ
    simp only [hc, Bool.false_eq_true, if_false] at a0
    have a1 := ih hσ (pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
      comp s (pre.length + 2) ++ [.jmp (pre.length + clen s + clen t + 3)]) post
    simp only [List.length_append, condJ_length, comp_length, List.length_singleton] at a1
    rw [show pre.length + 2 + clen s + 1 = pre.length + clen s + 3 by omega] at a1
    have e0 : pre ++ comp (.ite c s t) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        (comp s (pre.length + 2) ++ [.jmp (pre.length + clen s + clen t + 3)] ++ comp t (pre.length + clen s + 3) ++ post) := by
      simp [comp]
    have e1 : pre ++ comp (.ite c s t) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        comp s (pre.length + 2) ++ [.jmp (pre.length + clen s + clen t + 3)] ++ comp t (pre.length + clen s + 3) ++ post := by
      simp [comp]
    have e3 : pre.length + clen (.ite c s t) = pre.length + clen s + 3 + clen t := by simp [clen]; omega
    rw [e3]
    exact (e0 ▸ a0).trans (e1 ▸ a1)
  | @loopT c s σ₁ σ₂ σ₃ hc h hl ih ihl =>
    have a0 := condJ_sim c (pre.length + 2) (pre.length + clen s + 3) pre
      (comp s (pre.length + 2) ++ [.jmp pre.length] ++ post) σ₁ hσ
    simp only [hc, if_true] at a0
    have a1 := ih hσ (pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3)) ([.jmp pre.length] ++ post)
    simp only [List.length_append, condJ_length] at a1
    have a2 := gstep_at (w := w) (pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++ comp s (pre.length + 2))
      [.jmp pre.length] post 0 (by simp) σ₂
    simp only [List.length_append, condJ_length, comp_length, add_zero] at a2
    have e0 : pre ++ comp (.loop c s) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        (comp s (pre.length + 2) ++ [.jmp pre.length] ++ post) := by
      simp [comp]
    have e1 : pre ++ comp (.loop c s) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        comp s (pre.length + 2) ++ ([.jmp pre.length] ++ post) := by
      simp [comp]
    have e2 : pre ++ comp (.loop c s) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        comp s (pre.length + 2) ++ [.jmp pre.length] ++ post := by
      simp [comp]
    refine (e0 ▸ a0).trans ((e1 ▸ a1).trans ((gsteps_single ?_ (h.good hσ)).trans
      (ihl (h.good hσ) pre post)))
    rw [e2, a2]; simp [gexec]
  | @loopF c s σ hc =>
    have a0 := condJ_sim c (pre.length + 2) (pre.length + clen s + 3) pre
      (comp s (pre.length + 2) ++ [.jmp pre.length] ++ post) σ hσ
    simp only [hc] at a0
    have e0 : pre ++ comp (.loop c s) pre.length ++ post = pre ++ condJ c (pre.length + 2) (pre.length + clen s + 3) ++
        (comp s (pre.length + 2) ++ [.jmp pre.length] ++ post) := by
      simp [comp]
    have e3 : pre.length + clen (.loop c s) = pre.length + clen s + 3 := by simp [clen]; omega
    rw [e3]; exact e0 ▸ a0


/-- Correctness of `Stmt.code`: a terminating run of `s` is simulated by a run of its goto
program ending at the final `halt` instruction. -/
theorem code_sim {s : Stmt K} {σ σ' : St K} (h : Eval w B s σ σ') (hσ : Good w B σ) :
    GSteps s.code w B (0, σ) (clen s, σ') := by
  have := comp_sim h hσ [] [.halt]
  simpa [Stmt.code] using this

lemma code_halt (s : Stmt K) : s.code.getD (clen s) .halt = .halt := by
  simp [Stmt.code, List.getD_eq_getElem?_getD, comp_length]

end Sim

/-! ## Jump targets of compiled code -/

/-- All jump targets of an instruction are `≤ L`. -/
def GI.TgtLe {K : ℕ} (L : ℕ) : GI K → Prop
  | .jz _ t => t ≤ L
  | .jsym _ t => t ≤ L
  | .jmp t => t ≤ L
  | _ => True

lemma condJ_tgt {K : ℕ} (c : Cond K) (t f L : ℕ) (ht : t ≤ L) (hf : f ≤ L) :
    ∀ i ∈ condJ c t f, i.TgtLe L := by
  induction c generalizing t f with
  | zero r => simp [condJ, GI.TgtLe, ht, hf]
  | sym s => simp [condJ, GI.TgtLe, ht, hf]
  | not c ih => exact ih f t hf ht

lemma comp_tgt {K : ℕ} (s : Stmt K) (b L : ℕ) (hL : b + clen s ≤ L) :
    ∀ i ∈ comp s b, i.TgtLe L := by
  induction s generalizing b with
  | skip => simp [comp]
  | inc r => simp [comp, GI.TgtLe]
  | dec r => simp [comp, GI.TgtLe]
  | left => simp [comp, GI.TgtLe]
  | right => simp [comp, GI.TgtLe]
  | out x => simp [comp, GI.TgtLe]
  | seq s t ihs iht =>
    simp only [clen] at hL
    intro i hi
    simp only [comp, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ihs b (by omega) i hi
    · exact iht _ (by omega) i hi
  | ite c s t ihs iht =>
    simp only [clen] at hL
    intro i hi
    simp only [comp, List.mem_append, List.mem_singleton] at hi
    rcases hi with ((hi | hi) | rfl) | hi
    · exact condJ_tgt c _ _ L (by omega) (by omega) i hi
    · exact ihs _ (by omega) i hi
    · simp [GI.TgtLe]; omega
    · exact iht _ (by omega) i hi
  | loop c s ihs =>
    simp only [clen] at hL
    intro i hi
    simp only [comp, List.mem_append, List.mem_singleton] at hi
    rcases hi with ((hi | hi) | rfl)
    · exact condJ_tgt c _ _ L (by omega) (by omega) i hi
    · exact ihs _ (by omega) i hi
    · simp [GI.TgtLe]; omega

/-- The program counter of a compiled program never exceeds the address of its final
`halt` instruction. -/
lemma gstep_pc_le {K : ℕ} (s : Stmt K) (w : Word) (a : ℕ × St K) (ha : a.1 ≤ clen s) :
    (gstep s.code w a).1 ≤ clen s := by
  rcases Nat.lt_or_ge a.1 (clen s) with h | h
  · have hi : s.code.getD a.1 .halt = (comp s 0)[a.1]'(by rw [comp_length]; exact h) := by
      rw [Stmt.code, List.getD_eq_getElem _ _ (by simp [comp_length]; omega),
        List.getElem_append_left]
    have ht := comp_tgt s 0 (clen s) (by omega) _ (List.getElem_mem (by rw [comp_length]; exact h))
    rw [← hi] at ht
    unfold gstep
    revert ht
    cases s.code.getD a.1 .halt <;> simp [gexec, GI.TgtLe] <;> (try split_ifs) <;> omega
  · have : a.1 = clen s := by omega
    rw [gstep, this, code_halt]; simp [gexec, this]


end LS

end PathChecking
