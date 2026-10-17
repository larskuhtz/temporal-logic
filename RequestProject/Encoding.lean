module

public import Mathlib

/-!
# Binary encodings of problem instances

All decision problems in this development are languages over the binary alphabet
(`List Bool`).  Structured objects (numbers, sets of atomic propositions, formulas, paths,
trees, circuits) are first written as lists of *tokens* over a small fixed alphabet `Tok`,
and every token is then written as a fixed-width block of 5 bits.  This is a standard
"reasonable" encoding: it is computable and decodable in logarithmic space, so the
complexity classes considered here do not depend on the details of this choice.
-/

@[expose] public section

namespace PathChecking

/-- Binary words. -/
abbrev Word := List Bool

/-- Languages (decision problems) over the binary alphabet. -/
abbrev Language := Set Word

/-- Tokens of the intermediate encoding alphabet. -/
inductive Tok
  /-- binary digit `0` -/
  | zero
  /-- binary digit `1` -/
  | one
  /-- end of a binary number -/
  | sep
  /-- opening bracket -/
  | lpar
  /-- closing bracket -/
  | rpar
  /-- constructor tags (operators of formulas, gate types, ...) -/
  | tag (k : Fin 24)
  deriving DecidableEq

/-- Numeric code of a token; all codes are `< 32`. -/
def Tok.code : Tok → ℕ
  | .zero => 0
  | .one => 1
  | .sep => 2
  | .lpar => 3
  | .rpar => 4
  | .tag k => 5 + k.val

/-- Fixed-width (5 bit) binary block of a token. -/
def Tok.bits (t : Tok) : Word :=
  (List.range 5).map fun i => t.code.testBit i

/-- Binary encoding of a list of tokens. -/
def encodeToks (ts : List Tok) : Word :=
  ts.flatMap Tok.bits

/-- Token encoding of a natural number: its binary digits (least significant first),
terminated by `sep`. -/
def natToks (n : ℕ) : List Tok :=
  (Nat.bits n).map (fun b => if b then Tok.one else Tok.zero) ++ [Tok.sep]

/-- Token encoding of a finite set of atomic propositions (a letter of a path / label of a
tree node): the elements in increasing order, enclosed in brackets. -/
def finsetToks (s : Finset ℕ) : List Tok :=
  Tok.lpar :: ((s.sort (· ≤ ·)).flatMap natToks ++ [Tok.rpar])

end PathChecking
