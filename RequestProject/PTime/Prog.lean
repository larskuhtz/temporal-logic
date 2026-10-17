module

public import RequestProject.Logspace.Lib

/-!
# Register programs with a monotone bit memory

This extends the register language of `Logspace/Prog.lean` by a *memory*: an infinite array
of bits, all initially `false`, accessed through a *cursor*.  The new instructions move the
cursor (`cl`, `cr`), set the bit under the cursor to `true` (`mset`) and test it (condition
`mem`).  Bits can only be set, never cleared, so the memory grows monotonically.

As before, the big-step semantics carries a bound `B`: registers and the cursor stay `≤ B`.
Every program of `Logspace/Prog.lean` embeds into this language (`LS.Stmt.lift`).

In `PTime/Machine.lean` programs are compiled into Turing machines; a terminating program whose
registers and cursor are polynomially bounded runs in polynomial time
(`PTime/Main.lean`), because between two changes of the (monotone) memory no state can repeat.
-/

@[expose] public section

namespace PathChecking

namespace PT

open LS

/-- Program states: the register state of `Logspace/Prog.lean`, a cursor and the set of
positions of memory bits that are `true`. -/
structure PSt (K : ℕ) where
  base : St K
  cur : ℕ
  mem : Finset ℕ

/-- Initial state. -/
def PSt.init (K : ℕ) : PSt K := ⟨St.init K, 0, ∅⟩

/-- Conditions. -/
inductive PCond (K : ℕ)
  | zero (r : Fin K)
  | sym (s : InSym)
  | mem
  | not (c : PCond K)

/-- Evaluation of a condition. -/
def PCond.eval {K : ℕ} (w : Word) (σ : PSt K) : PCond K → Bool
  | .zero r => decide (σ.base.reg r = 0)
  | .sym s => decide (inputSym w σ.base.pos = s)
  | .mem => decide (σ.cur ∈ σ.mem)
  | .not c => !(c.eval w σ)

/-- Structured programs. -/
inductive PStmt (K : ℕ)
  | skip
  | inc (r : Fin K)
  | dec (r : Fin K)
  | left
  | right
  | out (b : Bool)
  | cl
  | cr
  | mset
  | seq (s t : PStmt K)
  | ite (c : PCond K) (s t : PStmt K)
  | loop (c : PCond K) (s : PStmt K)

/-- Big-step semantics with bound `B` on the registers and the cursor. -/
inductive PEval {K : ℕ} (w : Word) (B : ℕ) : PStmt K → PSt K → PSt K → Prop
  | skip (σ : PSt K) : PEval w B .skip σ σ
  | inc (σ : PSt K) (r : Fin K) : σ.base.reg r < B →
      PEval w B (.inc r) σ { σ with base := σ.base.setReg r (σ.base.reg r + 1) }
  | dec (σ : PSt K) (r : Fin K) :
      PEval w B (.dec r) σ { σ with base := σ.base.setReg r (σ.base.reg r - 1) }
  | left (σ : PSt K) : PEval w B .left σ { σ with base := { σ.base with pos := σ.base.pos - 1 } }
  | right (σ : PSt K) : PEval w B .right σ
      { σ with base := { σ.base with pos := min (σ.base.pos + 1) (w.length + 1) } }
  | out (σ : PSt K) (b : Bool) :
      PEval w B (.out b) σ { σ with base := { σ.base with out := σ.base.out ++ [b] } }
  | cl (σ : PSt K) : PEval w B .cl σ { σ with cur := σ.cur - 1 }
  | cr (σ : PSt K) : σ.cur < B → PEval w B .cr σ { σ with cur := σ.cur + 1 }
  | mset (σ : PSt K) : PEval w B .mset σ { σ with mem := insert σ.cur σ.mem }
  | seq {s t : PStmt K} {σ₁ σ₂ σ₃ : PSt K} :
      PEval w B s σ₁ σ₂ → PEval w B t σ₂ σ₃ → PEval w B (.seq s t) σ₁ σ₃
  | iteT {c : PCond K} {s t : PStmt K} {σ σ' : PSt K} :
      c.eval w σ = true → PEval w B s σ σ' → PEval w B (.ite c s t) σ σ'
  | iteF {c : PCond K} {s t : PStmt K} {σ σ' : PSt K} :
      c.eval w σ = false → PEval w B t σ σ' → PEval w B (.ite c s t) σ σ'
  | loopT {c : PCond K} {s : PStmt K} {σ₁ σ₂ σ₃ : PSt K} :
      c.eval w σ₁ = true → PEval w B s σ₁ σ₂ → PEval w B (.loop c s) σ₂ σ₃ →
        PEval w B (.loop c s) σ₁ σ₃
  | loopF {c : PCond K} {s : PStmt K} {σ : PSt K} :
      c.eval w σ = false → PEval w B (.loop c s) σ σ

/-- Good states: input head on the tape, registers and cursor `≤ B`, memory below `B`. -/
def PGood {K : ℕ} (w : Word) (B : ℕ) (σ : PSt K) : Prop :=
  σ.base.pos ≤ w.length + 1 ∧ (∀ r, σ.base.reg r ≤ B) ∧ σ.cur ≤ B ∧ ∀ i ∈ σ.mem, i ≤ B

/-! ## Embedding the logspace language -/

/-- Conditions of `Logspace/Prog.lean` as conditions of the extended language. -/
def _root_.PathChecking.LS.Cond.lift {K : ℕ} : Cond K → PCond K
  | .zero r => .zero r
  | .sym s => .sym s
  | .not c => .not c.lift

/-- Programs of `Logspace/Prog.lean` as programs of the extended language. -/
def _root_.PathChecking.LS.Stmt.lift {K : ℕ} : Stmt K → PStmt K
  | .skip => .skip
  | .inc r => .inc r
  | .dec r => .dec r
  | .left => .left
  | .right => .right
  | .out b => .out b
  | .seq s t => .seq s.lift t.lift
  | .ite c s t => .ite c.lift s.lift t.lift
  | .loop c s => .loop c.lift s.lift

lemma cond_lift_eval {K : ℕ} (w : Word) (c : Cond K) (σ : PSt K) :
    c.lift.eval w σ = c.eval w σ.base := by
  induction c with
  | zero r => rfl
  | sym s => rfl
  | not c ih => simp [Cond.lift, PCond.eval, Cond.eval, ih]

/-- Runs of embedded programs. -/
lemma peval_lift {K : ℕ} {w : Word} {B : ℕ} {s : Stmt K} {σ σ' : St K} (h : Eval w B s σ σ')
    (c : ℕ) (m : Finset ℕ) : PEval w B s.lift ⟨σ, c, m⟩ ⟨σ', c, m⟩ := by
  induction h with
  | skip σ => exact PEval.skip _
  | inc σ r hr => exact PEval.inc ⟨σ, c, m⟩ r hr
  | dec σ r => exact PEval.dec ⟨σ, c, m⟩ r
  | left σ => exact PEval.left ⟨σ, c, m⟩
  | right σ => exact PEval.right ⟨σ, c, m⟩
  | out σ b => exact PEval.out ⟨σ, c, m⟩ b
  | seq _ _ ih1 ih2 => exact PEval.seq ih1 ih2
  | iteT hc _ ih => exact PEval.iteT (by rw [cond_lift_eval]; exact hc) ih
  | iteF hc _ ih => exact PEval.iteF (by rw [cond_lift_eval]; exact hc) ih
  | loopT hc _ _ ih1 ih2 => exact PEval.loopT (by rw [cond_lift_eval]; exact hc) ih1 ih2
  | loopF hc => exact PEval.loopF (by rw [cond_lift_eval]; exact hc)

/-! ## Goto programs -/

/-- Instructions of goto programs. -/
inductive PGI (K : ℕ)
  | inc (r : Fin K)
  | dec (r : Fin K)
  | jz (r : Fin K) (t : ℕ)
  | jsym (s : InSym) (t : ℕ)
  | jm (t : ℕ)
  | left
  | right
  | out (b : Bool)
  | cl
  | cr
  | mset
  | jmp (t : ℕ)
  | halt

/-- Execution of a single goto instruction. -/
def pexec {K : ℕ} (ins : PGI K) (w : Word) (a : ℕ × PSt K) : ℕ × PSt K :=
  match ins with
  | .inc r => (a.1 + 1, { a.2 with base := a.2.base.setReg r (a.2.base.reg r + 1) })
  | .dec r => (a.1 + 1, { a.2 with base := a.2.base.setReg r (a.2.base.reg r - 1) })
  | .jz r t => (if a.2.base.reg r = 0 then t else a.1 + 1, a.2)
  | .jsym s t => (if inputSym w a.2.base.pos = s then t else a.1 + 1, a.2)
  | .jm t => (if a.2.cur ∈ a.2.mem then t else a.1 + 1, a.2)
  | .left => (a.1 + 1, { a.2 with base := { a.2.base with pos := a.2.base.pos - 1 } })
  | .right => (a.1 + 1,
      { a.2 with base := { a.2.base with pos := min (a.2.base.pos + 1) (w.length + 1) } })
  | .out b => (a.1 + 1, { a.2 with base := { a.2.base with out := a.2.base.out ++ [b] } })
  | .cl => (a.1 + 1, { a.2 with cur := a.2.cur - 1 })
  | .cr => (a.1 + 1, { a.2 with cur := a.2.cur + 1 })
  | .mset => (a.1 + 1, { a.2 with mem := insert a.2.cur a.2.mem })
  | .jmp t => (t, a.2)
  | .halt => a

/-- One step of a goto program. -/
def pstep {K : ℕ} (code : List (PGI K)) (w : Word) (a : ℕ × PSt K) : ℕ × PSt K :=
  pexec (code.getD a.1 .halt) w a

/-- Multi-step execution through good states. -/
def PSteps {K : ℕ} (code : List (PGI K)) (w : Word) (B : ℕ) : ℕ × PSt K → ℕ × PSt K → Prop :=
  Relation.ReflTransGen (fun a b => pstep code w a = b ∧ PGood w B b.2)

/-- Code for a condition. -/
def pcondJ {K : ℕ} : PCond K → ℕ → ℕ → List (PGI K)
  | .zero r, t, f => [.jz r t, .jmp f]
  | .sym s, t, f => [.jsym s t, .jmp f]
  | .mem, t, f => [.jm t, .jmp f]
  | .not c, t, f => pcondJ c f t

lemma pcondJ_length {K : ℕ} (c : PCond K) (t f : ℕ) : (pcondJ c t f).length = 2 := by
  induction c generalizing t f <;> simp [pcondJ, *]

/-- Length of compiled code. -/
def pclen {K : ℕ} : PStmt K → ℕ
  | .skip => 0
  | .inc _ => 1
  | .dec _ => 1
  | .left => 1
  | .right => 1
  | .out _ => 1
  | .cl => 1
  | .cr => 1
  | .mset => 1
  | .seq s t => pclen s + pclen t
  | .ite _ s t => pclen s + pclen t + 3
  | .loop _ s => pclen s + 3

/-- Compilation of a structured program placed at address `b`. -/
def pcomp {K : ℕ} : PStmt K → ℕ → List (PGI K)
  | .skip, _ => []
  | .inc r, _ => [.inc r]
  | .dec r, _ => [.dec r]
  | .left, _ => [.left]
  | .right, _ => [.right]
  | .out x, _ => [.out x]
  | .cl, _ => [.cl]
  | .cr, _ => [.cr]
  | .mset, _ => [.mset]
  | .seq s t, b => pcomp s b ++ pcomp t (b + pclen s)
  | .ite c s t, b => pcondJ c (b + 2) (b + pclen s + 3) ++ pcomp s (b + 2) ++
      [.jmp (b + pclen s + pclen t + 3)] ++ pcomp t (b + pclen s + 3)
  | .loop c s, b => pcondJ c (b + 2) (b + pclen s + 3) ++ pcomp s (b + 2) ++ [.jmp b]

lemma pcomp_length {K : ℕ} (s : PStmt K) (b : ℕ) : (pcomp s b).length = pclen s := by
  induction s generalizing b <;> simp [pcomp, pclen, pcondJ_length, *] <;> omega

/-- The goto program of a structured program, followed by `halt`. -/
def PStmt.code {K : ℕ} (s : PStmt K) : List (PGI K) := pcomp s 0 ++ [.halt]

lemma PEval.good {K : ℕ} {w : Word} {B : ℕ} {s : PStmt K} {σ σ' : PSt K}
    (h : PEval w B s σ σ') (hσ : PGood w B σ) : PGood w B σ' := by
  induction h with
  | skip => exact hσ
  | inc σ r hr =>
    refine ⟨hσ.1, fun r' => ?_, hσ.2.2⟩
    by_cases hr' : r' = r
    · subst hr'; simp; omega
    · simp [Function.update_of_ne hr']; exact hσ.2.1 r'
  | dec σ r =>
    refine ⟨hσ.1, fun r' => ?_, hσ.2.2⟩
    by_cases hr' : r' = r
    · subst hr'; simp; have := hσ.2.1 r'; omega
    · simp [Function.update_of_ne hr']; exact hσ.2.1 r'
  | left σ => exact ⟨by simp; have := hσ.1; omega, hσ.2⟩
  | right σ => exact ⟨by simp, hσ.2⟩
  | out σ b => exact hσ
  | cl σ => exact ⟨hσ.1, hσ.2.1, by simp; have := hσ.2.2.1; omega, hσ.2.2.2⟩
  | cr σ h => exact ⟨hσ.1, hσ.2.1, by simp; omega, hσ.2.2.2⟩
  | mset σ =>
    refine ⟨hσ.1, hσ.2.1, hσ.2.2.1, fun i hi => ?_⟩
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · exact hσ.2.2.1
    · exact hσ.2.2.2 i hi
  | seq _ _ ih1 ih2 => exact ih2 (ih1 hσ)
  | iteT _ _ ih => exact ih hσ
  | iteF _ _ ih => exact ih hσ
  | loopT _ _ _ ih1 ih2 => exact ih2 (ih1 hσ)
  | loopF _ => exact hσ

section Sim

variable {K : ℕ} {code : List (PGI K)} {w : Word} {B : ℕ}

lemma pgetD_mid (pre c post : List (PGI K)) (i : ℕ) (hi : i < c.length) :
    (pre ++ c ++ post).getD (pre.length + i) .halt = c.getD i .halt := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hi]
  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp)]
  simp

lemma psteps_single {a b : ℕ × PSt K} (h : pstep code w a = b) (hb : PGood w B b.2) :
    PSteps code w B a b :=
  Relation.ReflTransGen.single ⟨h, hb⟩

lemma pstep_at (pre c post : List (PGI K)) (i : ℕ) (hi : i < c.length) (σ : PSt K) :
    pstep (pre ++ c ++ post) w (pre.length + i, σ) =
      pexec (c.getD i .halt) w (pre.length + i, σ) := by
  rw [pstep, pgetD_mid pre c post i hi]

lemma pcondJ_sim (c : PCond K) (t f : ℕ) (pre post : List (PGI K)) (σ : PSt K)
    (hσ : PGood w B σ) :
    PSteps (pre ++ pcondJ c t f ++ post) w B (pre.length, σ)
      (if c.eval w σ then t else f, σ) := by
  induction c generalizing t f with
  | zero r =>
    have e0 := pstep_at (w := w) pre (pcondJ (.zero r) t f) post 0 (by simp [pcondJ]) σ
    have e1 := pstep_at (w := w) pre (pcondJ (.zero r) t f) post 1 (by simp [pcondJ]) σ
    simp only [add_zero] at e0
    by_cases hr : σ.base.reg r = 0
    · apply psteps_single _ hσ
      rw [e0]; simp [pcondJ, pexec, hr, PCond.eval]
    · refine Relation.ReflTransGen.head (b := (pre.length + 1, σ)) ⟨?_, hσ⟩ ?_
      · rw [e0]; simp [pcondJ, pexec, hr]
      · apply psteps_single _ hσ
        rw [e1]; simp [pcondJ, pexec, hr, PCond.eval]
  | sym s =>
    have e0 := pstep_at (w := w) pre (pcondJ (.sym s) t f) post 0 (by simp [pcondJ]) σ
    have e1 := pstep_at (w := w) pre (pcondJ (.sym s) t f) post 1 (by simp [pcondJ]) σ
    simp only [add_zero] at e0
    by_cases hr : inputSym w σ.base.pos = s
    · apply psteps_single _ hσ
      rw [e0]; simp [pcondJ, pexec, hr, PCond.eval]
    · refine Relation.ReflTransGen.head (b := (pre.length + 1, σ)) ⟨?_, hσ⟩ ?_
      · rw [e0]; simp [pcondJ, pexec, hr]
      · apply psteps_single _ hσ
        rw [e1]; simp [pcondJ, pexec, hr, PCond.eval]
  | mem =>
    have e0 := pstep_at (w := w) pre (pcondJ (K := K) .mem t f) post 0 (by simp [pcondJ]) σ
    have e1 := pstep_at (w := w) pre (pcondJ (K := K) .mem t f) post 1 (by simp [pcondJ]) σ
    simp only [add_zero] at e0
    by_cases hr : σ.cur ∈ σ.mem
    · apply psteps_single _ hσ
      rw [e0]; simp [pcondJ, pexec, hr, PCond.eval]
    · refine Relation.ReflTransGen.head (b := (pre.length + 1, σ)) ⟨?_, hσ⟩ ?_
      · rw [e0]; simp [pcondJ, pexec, hr]
      · apply psteps_single _ hσ
        rw [e1]; simp [pcondJ, pexec, hr, PCond.eval]
  | not c ih =>
    have := ih f t
    simp only [pcondJ, PCond.eval]
    by_cases h : PCond.eval w σ c = true
    · simp only [h, if_true] at this; simpa [h] using this
    · simp only [h] at this; simpa [h] using this

lemma psim_single (ins : PGI K) (pre post : List (PGI K)) (σ σ' : PSt K)
    (he : pexec ins w (pre.length, σ) = (pre.length + 1, σ')) (hσ' : PGood w B σ') :
    PSteps (pre ++ [ins] ++ post) w B (pre.length, σ) (pre.length + 1, σ') := by
  apply psteps_single _ hσ'
  have := pstep_at (w := w) pre [ins] post 0 (by simp) σ
  rw [add_zero] at this; rw [this]; simpa using he

/-- Correctness of the compilation into goto programs. -/
theorem pcomp_sim {s : PStmt K} {σ σ' : PSt K} (h : PEval w B s σ σ') (hσ : PGood w B σ)
    (pre post : List (PGI K)) :
    PSteps (pre ++ pcomp s pre.length ++ post) w B (pre.length, σ)
      (pre.length + pclen s, σ') := by
  induction h generalizing pre post with
  | skip σ => simp [pclen]; exact Relation.ReflTransGen.refl
  | inc σ r hr =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.inc (w := w) σ r hr).good hσ)
  | dec σ r =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.dec (w := w) (B := B) σ r).good hσ)
  | left σ =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.left (w := w) (B := B) σ).good hσ)
  | right σ =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.right (w := w) (B := B) σ).good hσ)
  | out σ b =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.out (w := w) (B := B) σ b).good hσ)
  | cl σ =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.cl (w := w) (B := B) σ).good hσ)
  | cr σ hc =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.cr (w := w) σ hc).good hσ)
  | mset σ =>
    exact psim_single _ pre post _ _ (by simp [pexec]) ((PEval.mset (w := w) (B := B) σ).good hσ)
  | @seq s t σ₁ σ₂ σ₃ h1 h2 ih1 ih2 =>
    have a1 := ih1 hσ pre (pcomp t (pre.length + pclen s) ++ post)
    have a2 := ih2 (h1.good hσ) (pre ++ pcomp s pre.length) post
    simp only [List.length_append, pcomp_length] at a2
    have e1 : pre ++ pcomp (.seq s t) pre.length ++ post =
        pre ++ pcomp s pre.length ++ (pcomp t (pre.length + pclen s) ++ post) := by
      simp [pcomp]
    have e2 : pre ++ pcomp (.seq s t) pre.length ++ post =
        pre ++ pcomp s pre.length ++ pcomp t (pre.length + pclen s) ++ post := by
      simp [pcomp]
    have e3 : pre.length + pclen (.seq s t) = pre.length + pclen s + pclen t := by
      simp [pclen]; omega
    rw [e3]
    exact (e1 ▸ a1).trans (e2 ▸ a2)
  | @iteT c s t σ σ' hc h ih =>
    have a0 := pcondJ_sim c (pre.length + 2) (pre.length + pclen s + 3) pre
      (pcomp s (pre.length + 2) ++ [.jmp (pre.length + pclen s + pclen t + 3)] ++
        pcomp t (pre.length + pclen s + 3) ++ post) σ hσ
    simp only [hc, if_true] at a0
    have a1 := ih hσ (pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3))
      ([.jmp (pre.length + pclen s + pclen t + 3)] ++ pcomp t (pre.length + pclen s + 3) ++ post)
    simp only [List.length_append, pcondJ_length] at a1
    have a2 := pstep_at (w := w) (pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
      pcomp s (pre.length + 2))
      [.jmp (pre.length + pclen s + pclen t + 3)] (pcomp t (pre.length + pclen s + 3) ++ post) 0
      (by simp) σ'
    simp only [List.length_append, pcondJ_length, pcomp_length, add_zero] at a2
    have e0 : pre ++ pcomp (.ite c s t) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        (pcomp s (pre.length + 2) ++ [.jmp (pre.length + pclen s + pclen t + 3)] ++
          pcomp t (pre.length + pclen s + 3) ++ post) := by
      simp [pcomp]
    have e1 : pre ++ pcomp (.ite c s t) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        pcomp s (pre.length + 2) ++ ([.jmp (pre.length + pclen s + pclen t + 3)] ++
          pcomp t (pre.length + pclen s + 3) ++ post) := by
      simp [pcomp]
    have e2 : pre ++ pcomp (.ite c s t) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        pcomp s (pre.length + 2) ++ [.jmp (pre.length + pclen s + pclen t + 3)] ++
          (pcomp t (pre.length + pclen s + 3) ++ post) := by
      simp [pcomp]
    refine (e0 ▸ a0).trans ((e1 ▸ a1).trans (psteps_single ?_ (h.good hσ)))
    rw [e2, a2]; simp [pexec, pclen]; omega
  | @iteF c s t σ σ' hc h ih =>
    have a0 := pcondJ_sim c (pre.length + 2) (pre.length + pclen s + 3) pre
      (pcomp s (pre.length + 2) ++ [.jmp (pre.length + pclen s + pclen t + 3)] ++
        pcomp t (pre.length + pclen s + 3) ++ post) σ hσ
    simp only [hc, Bool.false_eq_true, if_false] at a0
    have a1 := ih hσ (pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
      pcomp s (pre.length + 2) ++ [.jmp (pre.length + pclen s + pclen t + 3)]) post
    simp only [List.length_append, pcondJ_length, pcomp_length, List.length_singleton] at a1
    rw [show pre.length + 2 + pclen s + 1 = pre.length + pclen s + 3 by omega] at a1
    have e0 : pre ++ pcomp (.ite c s t) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        (pcomp s (pre.length + 2) ++ [.jmp (pre.length + pclen s + pclen t + 3)] ++
          pcomp t (pre.length + pclen s + 3) ++ post) := by
      simp [pcomp]
    have e1 : pre ++ pcomp (.ite c s t) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        pcomp s (pre.length + 2) ++ [.jmp (pre.length + pclen s + pclen t + 3)] ++
          pcomp t (pre.length + pclen s + 3) ++ post := by
      simp [pcomp]
    have e3 : pre.length + pclen (.ite c s t) = pre.length + pclen s + 3 + pclen t := by
      simp [pclen]; omega
    rw [e3]
    exact (e0 ▸ a0).trans (e1 ▸ a1)
  | @loopT c s σ₁ σ₂ σ₃ hc h hl ih ihl =>
    have a0 := pcondJ_sim c (pre.length + 2) (pre.length + pclen s + 3) pre
      (pcomp s (pre.length + 2) ++ [.jmp pre.length] ++ post) σ₁ hσ
    simp only [hc, if_true] at a0
    have a1 := ih hσ (pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3))
      ([.jmp pre.length] ++ post)
    simp only [List.length_append, pcondJ_length] at a1
    have a2 := pstep_at (w := w) (pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
      pcomp s (pre.length + 2)) [.jmp pre.length] post 0 (by simp) σ₂
    simp only [List.length_append, pcondJ_length, pcomp_length, add_zero] at a2
    have e0 : pre ++ pcomp (.loop c s) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        (pcomp s (pre.length + 2) ++ [.jmp pre.length] ++ post) := by
      simp [pcomp]
    have e1 : pre ++ pcomp (.loop c s) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        pcomp s (pre.length + 2) ++ ([.jmp pre.length] ++ post) := by
      simp [pcomp]
    have e2 : pre ++ pcomp (.loop c s) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        pcomp s (pre.length + 2) ++ [.jmp pre.length] ++ post := by
      simp [pcomp]
    refine (e0 ▸ a0).trans ((e1 ▸ a1).trans ((psteps_single ?_ (h.good hσ)).trans
      (ihl (h.good hσ) pre post)))
    rw [e2, a2]; simp [pexec]
  | @loopF c s σ hc =>
    have a0 := pcondJ_sim c (pre.length + 2) (pre.length + pclen s + 3) pre
      (pcomp s (pre.length + 2) ++ [.jmp pre.length] ++ post) σ hσ
    simp only [hc] at a0
    have e0 : pre ++ pcomp (.loop c s) pre.length ++ post =
        pre ++ pcondJ c (pre.length + 2) (pre.length + pclen s + 3) ++
        (pcomp s (pre.length + 2) ++ [.jmp pre.length] ++ post) := by
      simp [pcomp]
    have e3 : pre.length + pclen (.loop c s) = pre.length + pclen s + 3 := by
      simp [pclen]; omega
    rw [e3]; exact e0 ▸ a0

/-- Correctness of `PStmt.code`. -/
theorem pcode_sim {s : PStmt K} {σ σ' : PSt K} (h : PEval w B s σ σ') (hσ : PGood w B σ) :
    PSteps s.code w B (0, σ) (pclen s, σ') := by
  have := pcomp_sim h hσ [] [.halt]
  simpa [PStmt.code] using this

lemma pcode_halt (s : PStmt K) : s.code.getD (pclen s) .halt = .halt := by
  simp [PStmt.code, List.getD_eq_getElem?_getD, pcomp_length]

end Sim

/-! ## Jump targets -/

/-- All jump targets of an instruction are `≤ L`. -/
def PGI.TgtLe {K : ℕ} (L : ℕ) : PGI K → Prop
  | .jz _ t => t ≤ L
  | .jsym _ t => t ≤ L
  | .jm t => t ≤ L
  | .jmp t => t ≤ L
  | _ => True

lemma pcondJ_tgt {K : ℕ} (c : PCond K) (t f L : ℕ) (ht : t ≤ L) (hf : f ≤ L) :
    ∀ i ∈ pcondJ c t f, i.TgtLe L := by
  induction c generalizing t f with
  | zero r => simp [pcondJ, PGI.TgtLe, ht, hf]
  | sym s => simp [pcondJ, PGI.TgtLe, ht, hf]
  | mem => simp [pcondJ, PGI.TgtLe, ht, hf]
  | not c ih => exact ih f t hf ht

lemma pcomp_tgt {K : ℕ} (s : PStmt K) (b L : ℕ) (hL : b + pclen s ≤ L) :
    ∀ i ∈ pcomp s b, i.TgtLe L := by
  induction s generalizing b with
  | seq s t ihs iht =>
    simp only [pclen] at hL
    intro i hi
    simp only [pcomp, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ihs b (by omega) i hi
    · exact iht _ (by omega) i hi
  | ite c s t ihs iht =>
    simp only [pclen] at hL
    intro i hi
    simp only [pcomp, List.mem_append, List.mem_singleton] at hi
    rcases hi with ((hi | hi) | rfl) | hi
    · exact pcondJ_tgt c _ _ L (by omega) (by omega) i hi
    · exact ihs _ (by omega) i hi
    · simp [PGI.TgtLe]; omega
    · exact iht _ (by omega) i hi
  | loop c s ihs =>
    simp only [pclen] at hL
    intro i hi
    simp only [pcomp, List.mem_append, List.mem_singleton] at hi
    rcases hi with ((hi | hi) | rfl)
    · exact pcondJ_tgt c _ _ L (by omega) (by omega) i hi
    · exact ihs _ (by omega) i hi
    · simp [PGI.TgtLe]; omega
  | _ => simp [pcomp, PGI.TgtLe]

/-- The program counter never exceeds the address of the final `halt`. -/
lemma pstep_pc_le {K : ℕ} (s : PStmt K) (w : Word) (a : ℕ × PSt K) (ha : a.1 ≤ pclen s) :
    (pstep s.code w a).1 ≤ pclen s := by
  rcases Nat.lt_or_ge a.1 (pclen s) with h | h
  · have hi : s.code.getD a.1 .halt = (pcomp s 0)[a.1]'(by rw [pcomp_length]; exact h) := by
      rw [PStmt.code, List.getD_eq_getElem _ _ (by simp [pcomp_length]; omega),
        List.getElem_append_left]
    have ht := pcomp_tgt s 0 (pclen s) (by omega) _
      (List.getElem_mem (by rw [pcomp_length]; exact h))
    rw [← hi] at ht
    unfold pstep
    revert ht
    cases s.code.getD a.1 .halt <;> simp [pexec, PGI.TgtLe] <;> (try split_ifs) <;> omega
  · have : a.1 = pclen s := by omega
    rw [pstep, this, pcode_halt]; simp [pexec, this]

end PT

end PathChecking
