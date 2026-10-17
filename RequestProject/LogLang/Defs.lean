module

public import RequestProject.Complexity

/-!
# A denotational loop language for logspace computations

Programs of this language manipulate finitely many natural-number variables, read the input
at computed positions and emit output bits.  All arithmetic is *clamped* at a cap
`C = (|w| + 2)^E + 3` that depends polynomially on the input length, and the only loops are
`for`-loops over a range given by an expression.  The semantics `Pr.run` is a pure total
function.  In `LogLang/Compile.lean` every program is compiled into a register program, which
shows that the function it computes is logspace computable (`LL.logspaceComputable_of_run`).
-/

@[expose] public section

namespace PathChecking

namespace LL

/-- Binary operations. -/
inductive BOp
  | add
  | sub
  | mul
  | div
  | mod
  /-- `1` if `a < b`, else `0` -/
  | lt
  /-- `1` if `a = b`, else `0` -/
  | eq

/-- Value of a binary operation (with cap `C` for `add` and `mul`). -/
def BOp.ap (C : ℕ) : BOp → ℕ → ℕ → ℕ
  | .add, a, b => min (a + b) C
  | .sub, a, b => a - b
  | .mul, a, b => min (a * b) C
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0

/-- Expressions over variables `Fin V`. -/
inductive Ex (V : ℕ)
  /-- constant -/
  | c (k : ℕ)
  /-- variable -/
  | v (x : Fin V)
  /-- length of the input -/
  | len
  /-- input symbol at a position (`0`/`1` for bits, `2` left end marker, `3` right end marker) -/
  | inp (e : Ex V)
  /-- binary operation -/
  | bin (o : BOp) (a b : Ex V)

/-- Numeric code of an input symbol. -/
def symNum : InSym → ℕ
  | .bit false => 0
  | .bit true => 1
  | .lend => 2
  | .rend => 3

/-- Value of an expression (with cap `C`). -/
def Ex.eval {V : ℕ} (w : Word) (C : ℕ) (ρ : Fin V → ℕ) : Ex V → ℕ
  | .c k => min k C
  | .v x => ρ x
  | .len => min w.length C
  | .inp e => symNum (inputSym w (e.eval w C ρ))
  | .bin o a b => o.ap C (a.eval w C ρ) (b.eval w C ρ)

/-- Programs. -/
inductive Pr (V : ℕ)
  | skip
  /-- assignment `x := e` -/
  | set (x : Fin V) (e : Ex V)
  /-- emit the bit `e ≠ 0` -/
  | out (e : Ex V)
  | seq (s t : Pr V)
  /-- `if e ≠ 0 then s else t` -/
  | ite (e : Ex V) (s t : Pr V)
  /-- `for x in [0, e) do s` (the bound is evaluated once) -/
  | loop (x : Fin V) (e : Ex V) (s : Pr V)

/-- Semantics: final variable values and the emitted bits. -/
def Pr.run {V : ℕ} (w : Word) (C : ℕ) : Pr V → (Fin V → ℕ) → (Fin V → ℕ) × List Bool
  | .skip, ρ => (ρ, [])
  | .set x e, ρ => (Function.update ρ x (e.eval w C ρ), [])
  | .out e, ρ => (ρ, [decide (e.eval w C ρ ≠ 0)])
  | .seq s t, ρ =>
    let r₁ := s.run w C ρ
    let r₂ := t.run w C r₁.1
    (r₂.1, r₁.2 ++ r₂.2)
  | .ite e s t, ρ => if e.eval w C ρ ≠ 0 then s.run w C ρ else t.run w C ρ
  | .loop x e s, ρ =>
    (List.range (e.eval w C ρ)).foldl
      (fun (acc : (Fin V → ℕ) × List Bool) i =>
        let r := s.run w C (Function.update acc.1 x i)
        (r.1, acc.2 ++ r.2)) (ρ, [])

/-- The cap used for inputs `w`: `(|w| + 2)^E + 3`. -/
def capOf (E : ℕ) (w : Word) : ℕ := (w.length + 2) ^ E + 3

/-- Output of a program with cap exponent `E` on input `w` (all variables start at `0`). -/
def Pr.output {V : ℕ} (E : ℕ) (P : Pr V) (w : Word) : Word :=
  (P.run w (capOf E w) (fun _ => 0)).2

end LL

end PathChecking
