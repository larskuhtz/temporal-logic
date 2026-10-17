module

public import RequestProject.Encoding

/-!
# Complexity classes

We define, from scratch, the machine models and complexity classes needed to state the
results:

* deterministic Turing machines with a read-only two-way input tape, one work tape and a
  write-only output tape; logspace and polynomial-time computable functions, logspace
  many-one reductions, the classes `L` and `P`, and `P`-hardness;
* deterministic pushdown automata, the class `DCFL` and the class
  `LogDCFL` (languages logspace many-one reducible to a deterministic context-free language);
* Boolean circuits with unbounded fan-in `AND`/`OR` gates, `NOT` gates and oracle gates,
  logspace uniformity, the classes `AC^k[𝒞]` (`ACOracle k 𝒞`), `NC^k` and `NC`.

## References

Full entries are in `REFERENCES.md`.

* Logspace many-one reductions: N. D. Jones, *Space-Bounded Reducibility among Combinatorial
  Problems*, J. Comput. System Sci. 11(1), 1975 [Jon75]; textbooks: Ch. H. Papadimitriou,
  *Computational Complexity*, 1994 [Pap94]; S. Arora, B. Barak, *Computational Complexity: A
  Modern Approach*, 2009 [AB09].
* `LogDCFL`: I. H. Sudborough, *On the Tape Complexity of Deterministic Context-Free Languages*,
  J. ACM 25(3), 1978 [Sud78].
* Uniform circuits, `NC^k`, `AC^k` and oracle gates: W. L. Ruzzo, *On Uniform Circuit Complexity*,
  J. Comput. System Sci. 22(3), 1981 [Ruz81]; S. A. Cook, *A Taxonomy of Problems with Fast
  Parallel Algorithms*, Information and Control 64, 1985 [Coo85]; textbook: H. Vollmer,
  *Introduction to Circuit Complexity*, 1999 [Vol99].
* The classes as used by Kuhtz–Finkbeiner: [KF12, Section 2] refers to D. S. Johnson,
  *A catalog of complexity classes*, 1990 [Joh90] and to [Vol99].

The definitions here are this project's own, written from scratch. We have not checked that they
agree in every detail (machine model, uniformity condition, the depth cost of oracle gates)
with those of the cited works.
-/

@[expose] public section

namespace PathChecking

open Classical

/-! ## Turing machines -/

/-- Head movements. -/
inductive Dir
  | left
  | stay
  | right
  deriving DecidableEq

/-- Move a head position (positions are natural numbers; moving left from `0` stays at `0`). -/
def Dir.move : Dir → ℕ → ℕ
  | .left, p => p - 1
  | .stay, p => p
  | .right, p => p + 1

/-- Symbols seen by the input head: the input `w` is written between two end markers,
position `0` is the left end marker, positions `1 … |w|` hold the input bits and position
`|w| + 1` is the right end marker. -/
inductive InSym
  | lend
  | rend
  | bit (b : Bool)

/-- The symbol at position `p` of the (end-marked) input tape. -/
def inputSym (w : Word) (p : ℕ) : InSym :=
  if p = 0 then .lend else
    match w[p - 1]? with
    | some b => .bit b
    | none => .rend

/-- A deterministic Turing machine (transducer) with a read-only two-way input tape, one
read/write work tape (infinite to the right) and a write-only, one-way output tape over
`Bool`.  In each step it reads the input symbol and the work symbol under the heads,
changes state, writes a work symbol, moves both heads, and possibly appends one bit to the
output. -/
structure TM where
  /-- states -/
  Q : Type
  [finQ : Fintype Q]
  /-- work tape alphabet -/
  Γ : Type
  [finΓ : Fintype Γ]
  /-- blank work tape symbol -/
  blank : Γ
  /-- initial state -/
  start : Q
  /-- halting states -/
  halt : Q → Bool
  /-- transition function: new state, written work symbol, work head move, input head
  move, optional output bit -/
  δ : Q → InSym → Γ → Q × Γ × Dir × Dir × Option Bool

/-- Configurations of a Turing machine. -/
structure TM.Cfg (M : TM) where
  state : M.Q
  inPos : ℕ
  tape : ℕ → M.Γ
  workPos : ℕ
  output : List Bool

/-- Initial configuration. -/
def TM.init (M : TM) : M.Cfg :=
  ⟨M.start, 0, fun _ => M.blank, 0, []⟩

/-- One computation step on input `w` (halting configurations are fixed points). -/
def TM.step (M : TM) (w : Word) (c : M.Cfg) : M.Cfg :=
  if M.halt c.state then c else
    match M.δ c.state (inputSym w c.inPos) (c.tape c.workPos) with
    | (q', g, dw, di, o) =>
      { state := q'
        inPos := min (di.move c.inPos) (w.length + 1)
        tape := Function.update c.tape c.workPos g
        workPos := dw.move c.workPos
        output := c.output ++ o.toList }

/-- The configuration reached after `t` steps on input `w`. -/
def TM.run (M : TM) (w : Word) (t : ℕ) : M.Cfg :=
  (M.step w)^[t] M.init

/-- After `t` steps on input `w`, the machine has halted with output `o`. -/
def TM.HaltsWith (M : TM) (w : Word) (t : ℕ) (o : Word) : Prop :=
  M.halt (M.run w t).state = true ∧ (M.run w t).output = o

/-- `M` computes the (total) function `f`. -/
def TM.Computes (M : TM) (f : Word → Word) : Prop :=
  ∀ w, ∃ t, M.HaltsWith w t (f w)

/-- A function is computable in logarithmic space: some machine computes it, and on inputs
of length `n` the work head never leaves the first `c · (⌊log₂ n⌋ + 1)` cells. -/
def LogspaceComputable (f : Word → Word) : Prop :=
  ∃ (M : TM) (c : ℕ), M.Computes f ∧
    ∀ w t, (M.run w t).workPos ≤ c * (Nat.log 2 w.length + 1)

/-- A function is computable in polynomial time. -/
def PolytimeComputable (f : Word → Word) : Prop :=
  ∃ (M : TM) (c : ℕ), ∀ w, ∃ t ≤ c * (w.length + 1) ^ c, M.HaltsWith w t (f w)

/-- The characteristic function of a language, as a one-bit output. -/
noncomputable def charWord (A : Language) (w : Word) : Word :=
  [decide (w ∈ A)]

/-- Unfolding `charWord`.  (Stating it here also fixes the module that owns the automatically
generated equation lemmas of `charWord`, so that files using them can be imported together.) -/
theorem charWord_eq (A : Language) (w : Word) : charWord A w = [decide (w ∈ A)] :=
  charWord.eq_1 A w

theorem charWord_apply (A : Language) (w : Word) : charWord A w = [decide (w ∈ A)] :=
  charWord.eq_def A w

/-- The class `L` (deterministic logarithmic space). -/
def ClassL : Set Language :=
  {A | LogspaceComputable (charWord A)}

/-- The class `P` (deterministic polynomial time). -/
def ClassP : Set Language :=
  {A | PolytimeComputable (charWord A)}

/-- Logspace many-one reducibility `A ≤ₗ B`. -/
def LogspaceReducible (A B : Language) : Prop :=
  ∃ f : Word → Word, LogspaceComputable f ∧ ∀ w, w ∈ A ↔ f w ∈ B

/-- `A` is `P`-hard (under logspace many-one reductions). -/
def PHard (A : Language) : Prop :=
  ∀ B ∈ ClassP, LogspaceReducible B A

/-! ## Deterministic pushdown automata, `DCFL` and `LogDCFL` -/

/-- A deterministic pushdown automaton over the binary input alphabet, accepting by final
state.  `δ q (some a) Z` is the move reading input bit `a` with top of stack `Z`;
`δ q none Z` is an ε-move.  A move replaces the top stack symbol by a word of stack
symbols.  Determinism: if an ε-move is possible, no reading move is possible. -/
structure DPDA where
  /-- states -/
  Q : Type
  [finQ : Fintype Q]
  /-- stack alphabet -/
  S : Type
  [finS : Fintype S]
  /-- initial state -/
  start : Q
  /-- initial stack symbol -/
  bottom : S
  /-- accepting states -/
  accept : Set Q
  /-- (partial) transition function -/
  δ : Q → Option Bool → S → Option (Q × List S)
  /-- determinism -/
  deterministic : ∀ q Z, (δ q none Z).isSome → ∀ a, δ q (some a) Z = none

/-- Configurations of a DPDA: state, remaining input, stack (top first). -/
structure DPDA.Cfg (M : DPDA) where
  state : M.Q
  input : Word
  stack : List M.S

/-- One move of a DPDA. -/
inductive DPDA.Step (M : DPDA) : M.Cfg → M.Cfg → Prop
  | read {q : M.Q} {a : Bool} {w : Word} {Z : M.S} {γ : List M.S} {q' : M.Q} {α : List M.S} :
      M.δ q (some a) Z = some (q', α) → M.Step ⟨q, a :: w, Z :: γ⟩ ⟨q', w, α ++ γ⟩
  | eps {q : M.Q} {w : Word} {Z : M.S} {γ : List M.S} {q' : M.Q} {α : List M.S} :
      M.δ q none Z = some (q', α) → M.Step ⟨q, w, Z :: γ⟩ ⟨q', w, α ++ γ⟩

/-- A DPDA accepts `w` if, starting from the initial configuration, it can consume all of
`w` and reach an accepting state. -/
def DPDA.Accepts (M : DPDA) (w : Word) : Prop :=
  ∃ (q : M.Q) (γ : List M.S), q ∈ M.accept ∧
    Relation.ReflTransGen M.Step ⟨M.start, w, [M.bottom]⟩ ⟨q, [], γ⟩

/-- Deterministic context-free languages. -/
def DCFL : Set Language :=
  {A | ∃ M : DPDA, ∀ w, w ∈ A ↔ M.Accepts w}

/-- `LogDCFL`: languages that are logspace many-one reducible to a deterministic
context-free language. -/
def LogDCFL : Set Language :=
  {A | ∃ B ∈ DCFL, LogspaceReducible A B}

/-! ## Boolean circuits -/

/-- Gate types. `input i` reads the `i`-th input bit; `oracle` gates output whether the
word formed by their (ordered) inputs belongs to the oracle language. -/
inductive GateKind
  | input (i : ℕ)
  | const (b : Bool)
  | not
  | and
  | or
  | oracle

/-- A gate: its type and the (ordered) list of indices of the gates feeding into it. -/
structure Gate where
  kind : GateKind
  args : List ℕ

/-- A circuit is a list of gates in topological order; the last gate is the output gate. -/
abbrev Circuit := List Gate

/-- Value of a gate, given the input `x`, the oracle language `B` and the values of all
previous gates. -/
noncomputable def Gate.eval (B : Language) (x : Word) (vals : List Bool) (g : Gate) : Bool :=
  let a := g.args.map fun j => vals.getD j false
  match g.kind with
  | .input i => x.getD i false
  | .const b => b
  | .not => !(a.headD false)
  | .and => a.all id
  | .or => a.any id
  | .oracle => decide (a ∈ B)

/-- Values of all gates of a circuit on input `x` with oracle `B`. -/
noncomputable def Circuit.values (B : Language) (x : Word) (C : Circuit) : List Bool :=
  C.foldl (fun vals g => vals ++ [g.eval B x vals]) []

/-- Output of a circuit (the value of its last gate) on input `x` with oracle `B`. -/
noncomputable def Circuit.eval (B : Language) (x : Word) (C : Circuit) : Bool :=
  (C.values B x).getLastD false

/-- Depth of each gate: inputs and constants have depth `0`, every other gate has depth one
more than the maximal depth of its arguments. -/
def Circuit.depths (C : Circuit) : List ℕ :=
  C.foldl (fun ds g => ds ++ [match g.kind with
    | .input _ => 0
    | .const _ => 0
    | _ => 1 + (g.args.map fun j => ds.getD j 0).foldl max 0]) []

/-- Depth of a circuit. -/
def Circuit.depth (C : Circuit) : ℕ :=
  C.depths.foldl max 0

/-- Size of a circuit (number of gates). -/
def Circuit.size (C : Circuit) : ℕ :=
  C.length

/-- Well-formedness of a circuit with `n` inputs: there is at least one gate, every gate
only reads earlier gates, input gates read existing input bits and have no arguments,
constants have no arguments, and `NOT` gates have exactly one argument. -/
def Circuit.WellFormed (n : ℕ) (C : Circuit) : Prop :=
  C ≠ [] ∧
  ∀ (i : ℕ) (h : i < C.length),
    (∀ j ∈ C[i].args, j < i) ∧
    match C[i].kind with
    | .input k => k < n ∧ C[i].args = []
    | .const _ => C[i].args = []
    | .not => C[i].args.length = 1
    | _ => True

/-- Token encoding of a gate. -/
def Gate.toks (g : Gate) : List Tok :=
  (match g.kind with
    | .input i => Tok.tag 0 :: natToks i
    | .const false => [Tok.tag 1]
    | .const true => [Tok.tag 2]
    | .not => [Tok.tag 3]
    | .and => [Tok.tag 4]
    | .or => [Tok.tag 5]
    | .oracle => [Tok.tag 6]) ++
  (Tok.lpar :: (g.args.flatMap natToks ++ [Tok.rpar]))

/-- Binary encoding of a circuit. -/
def Circuit.encode (C : Circuit) : Word :=
  encodeToks (C.flatMap Gate.toks)

/-- A circuit family `(C n)_n` is logspace uniform if the map `1ⁿ ↦ ⟨C n⟩` is computable in
logarithmic space. -/
def LogspaceUniform (C : ℕ → Circuit) : Prop :=
  ∃ f : Word → Word, LogspaceComputable f ∧
    ∀ n, f (List.replicate n true) = (C n).encode

/-- `AC^k[𝒞]`: languages decided by logspace-uniform families of circuits of polynomial
size and depth `O(log^k n)`, built from unbounded fan-in `AND`/`OR` gates, `NOT` gates and
oracle gates for a single oracle language `B ∈ 𝒞` (each oracle gate counts as one level of
depth). -/
def ACOracle (k : ℕ) (𝒞 : Set Language) : Set Language :=
  {A | ∃ B ∈ 𝒞, ∃ (C : ℕ → Circuit) (c : ℕ), LogspaceUniform C ∧
    (∀ n, (C n).WellFormed n ∧ (C n).size ≤ c * (n + 1) ^ c ∧
      (C n).depth ≤ c * (Nat.log 2 n + 1) ^ k) ∧
    ∀ w, (C w.length).eval B w = true ↔ w ∈ A}

/-- `NC^k`: languages decided by logspace-uniform families of circuits of polynomial size
and depth `O(log^k n)` built from `AND`/`OR` gates of fan-in at most two and `NOT` gates
(no oracle gates). -/
def NCk (k : ℕ) : Set Language :=
  {A | ∃ (C : ℕ → Circuit) (c : ℕ), LogspaceUniform C ∧
    (∀ n, (C n).WellFormed n ∧ (C n).size ≤ c * (n + 1) ^ c ∧
      (C n).depth ≤ c * (Nat.log 2 n + 1) ^ k ∧
      ∀ g ∈ C n, g.kind ≠ GateKind.oracle ∧ g.args.length ≤ 2) ∧
    ∀ w, (C w.length).eval ∅ w = true ↔ w ∈ A}

/-- `NC = ⋃ₖ NC^k`, the class of efficiently parallelizable problems. -/
def NC : Set Language :=
  ⋃ k, NCk k

end PathChecking
