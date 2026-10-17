module

public import RequestProject.LTLPath.Grid

/-!
# Drawing layered circuits as grids

A *layered system* (`LG.LSys`) is a gate system `g` together with a set of *live* gates, a *row*
`Y h ≥ 1` and a *column* `X h` for every live gate.  The hypotheses `LSys.OK` say that the live
gates are `AND`/`OR` gates whose arguments are

* (`R`) the live gate in the same row and the next column `X h + 1`, or
* (`V`) live gates in the row below with column in `[X h - 1, X h + 3]`, or
* (`F`) non-live gates (constants), if `h` is in row `1`;

that live gates are determined by their row and column, that wires between two rows do not
cross, and that in a row the indices decrease with the columns.  These are the properties of the
query circuits of the LTL path checking algorithm (`RequestProject/LTLPath/QueryStrat.lean`).

`LSys.circ` draws the system as a grid (`RequestProject/LTLPath/Grid.lean`), which is a
stratified monotone planar circuit.  With `k = 10`, the live gate `h` is placed at column
`col h = 2 (X h + M - Y h)` and time `tim h = k · Y h + Cmax - col h`: a node `(c, t)` lies in
*band* `b` with *phase* `φ` if `t + c - Cmax = k b + φ`, and the live gates of row `b` are the
nodes of phase `0` and even column of band `b`.

* An `R`-argument of `h` is the node diagonally below the node diagonally below `h`; the node in
  between (phase `0`, odd column) copies it.
* A `V`-argument `x` of `h` (the *wire* `(h, x)`) is routed through the band of its row: from
  `x` at column `A = col x` the wire alternates straight and diagonal steps (phases `1, …, e`,
  `e = A - T`), and then goes straight up the column `T` (the *slot* of the wire: `col h` for the
  first non-`R` argument, `col h + 1` for the second one) until it reaches `h`.  Since all wire
  sources have even columns, and since wires do not cross, different wires never meet.
* `F`-arguments of gates of row `1` are constants in layer `0`, copied straight up to the slot.

`LSys.circ_strat`: the drawing is a stratified monotone planar circuit; `LSys.circ_eval`: its
value is the value of the output gate `h0`.
-/

@[expose] public section

namespace PathChecking

namespace LG

open Grid Classical

/-- The value of a constant gate. -/
def cval (gt : Gate) : Bool :=
  match gt.kind with
  | .const b => b
  | _ => false

/-- A layered system: gates, live gates, rows and columns. -/
structure LSys where
  g : ℕ → Gate
  live : ℕ → Bool
  X : ℕ → ℕ
  Y : ℕ → ℕ

namespace LSys

variable (L : LSys)

/-- Hypotheses on a layered system. -/
structure OK : Prop where
  ord : GS.Ordered L.g
  kind : ∀ h, L.live h = true → (L.g h).kind = .and ∨ (L.g h).kind = .or
  ne : ∀ h, L.live h = true → (L.g h).args ≠ []
  len : ∀ h, L.live h = true → (L.g h).args.length ≤ 2
  cst : ∀ h, L.live h = false → ∃ b, L.g h = ⟨.const b, []⟩
  ypos : ∀ h, L.live h = true → 1 ≤ L.Y h
  arg : ∀ h, L.live h = true → ∀ x ∈ (L.g h).args,
    (L.live x = true ∧ L.Y x = L.Y h ∧ L.X x = L.X h + 1) ∨
    (L.live x = true ∧ L.Y x + 1 = L.Y h ∧ L.X h ≤ L.X x + 1 ∧ L.X x ≤ L.X h + 3) ∨
    (L.live x = false ∧ L.Y h = 1)
  inj : ∀ a b, L.live a = true → L.live b = true → L.Y a = L.Y b → L.X a = L.X b → a = b
  cross : ∀ a a' b b', L.live a = true → L.live b = true → a' ∈ (L.g a).args →
    b' ∈ (L.g b).args → L.live a' = true → L.live b' = true → L.Y a' + 1 = L.Y a →
    L.Y b' + 1 = L.Y b → L.Y a = L.Y b → L.X a < L.X b → L.X a' ≤ L.X b'
  roword : ∀ a b, L.live a = true → L.live b = true → L.Y a = L.Y b → L.X a < L.X b → b < a

/-- Is `x` an argument of `h` in the same row? -/
def isR (h x : ℕ) : Bool := L.live x && L.Y x == L.Y h

/-- The arguments of `h` that are not in the same row. -/
def nonR (h : ℕ) : List ℕ := (L.g h).args.filter fun x => !L.isR h x

/-- Does `h` have an argument in the same row? -/
def hasR (h : ℕ) : Bool := (L.g h).args.any (L.isR h)

/-- The first non-`R` argument: the larger index. -/
def sArg (h : ℕ) : Option ℕ :=
  match L.nonR h with
  | [] => none
  | [a] => some a
  | a :: b :: _ => some (max a b)

/-- The second non-`R` argument, if there are two different ones: the smaller index. -/
def dArg (h : ℕ) : Option ℕ :=
  match L.nonR h with
  | a :: b :: _ => if a = b then none else some (min a b)
  | _ => none

variable (M Cmax : ℕ)

/-- Column of a live gate. -/
def col (h : ℕ) : ℕ := 2 * (L.X h + M - L.Y h)

/-- Time of a live gate. -/
def tim (h : ℕ) : ℕ := 10 * L.Y h + Cmax - L.col M h

/-- The slot of the wire `(h, x)`. -/
def slot (h x : ℕ) : ℕ := if L.sArg h = some x then L.col M h else L.col M h + 1

/-- `h` is the live gate of row `b` at column `c`. -/
def GateAt (b c h : ℕ) : Prop := L.live h = true ∧ L.Y h = b ∧ L.col M h = c

/-- The node of band `b`, phase `φ` and column `c` is a diagonal step of a wire. -/
def DDes (b φ c : ℕ) : Prop :=
  ∃ h x, L.live h = true ∧ x ∈ (L.g h).args ∧ L.live x = true ∧ L.Y x = b ∧ L.Y x + 1 = L.Y h ∧
    L.col M x = c + φ ∧ L.slot M h x + φ ≤ L.col M x

/-- The constant in layer `0` of column `c`. -/
noncomputable def colConst (c : ℕ) : Bool :=
  decide ((∃ h x, L.GateAt M 1 c h ∧ L.sArg h = some x ∧ L.live x = false ∧ cval (L.g x) = true) ∨
    (∃ h x, L.GateAt M 1 (c - 1) h ∧ c % 2 = 1 ∧ L.dArg h = some x ∧ L.live x = false ∧
      cval (L.g x) = true))

/-- Straight copy. -/
def nS : GN := .gt .and true false

/-- Diagonal copy. -/
def nD : GN := .gt .and false true

/-- The node at column `c` and time `t`. -/
noncomputable def node (c t : ℕ) : GN :=
  if t = 0 then .cst (L.colConst M c)
  else if t + c < Cmax then nS
  else if (t + c - Cmax) % 10 = 0 then
    if c % 2 = 0 then
      if hg : ∃ h, L.GateAt M ((t + c - Cmax) / 10) c h then
        .gt (L.g (Nat.find hg)).kind (L.sArg (Nat.find hg)).isSome
          (L.hasR (Nat.find hg) || (L.dArg (Nat.find hg)).isSome)
      else nS
    else if ∃ h, L.GateAt M ((t + c - Cmax) / 10) (c - 1) h ∧ L.hasR h = true then nD else nS
  else if L.DDes M ((t + c - Cmax) / 10) ((t + c - Cmax) % 10) c then nD else nS

/-- The grid drawing of the system with output gate `h0` (a constant if `h0` is not live). -/
noncomputable def circ (h0 : ℕ) : Circuit :=
  if L.live h0 = true then
    Grid.circ (fun t j => L.node M Cmax (L.col M h0 + j) t) (Cmax + 1 - L.col M h0) (L.tim M Cmax h0)
  else [⟨.const (cval (L.g h0)), []⟩]

/-- Bounds on the rows and columns. -/
def Bd : Prop := ∀ h, L.live h = true → L.Y h ≤ M ∧ L.col M h + 2 ≤ Cmax

end LSys

end LG

end PathChecking
