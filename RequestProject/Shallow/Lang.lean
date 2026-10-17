module

public import RequestProject.Complexity
public import RequestProject.Shallow.Oracle

/-!
# CTL* tree checking on trees with shallow branching

`CTLStarShallowTreeChecking k` is CTL* tree checking restricted to instances `(φ, t)` of
(binary) size `n` whose tree has all branching nodes at depth `< (⌊log₂ n⌋ + 1)^k`
(`ShallowBranching`).
-/

@[expose] public section

namespace PathChecking

open Shallow

/-- The branching-depth bound used for inputs of length `n`: `(⌊log₂ n⌋ + 1)^k`. -/
def shallowBound (k n : ℕ) : ℕ := (Nat.log 2 n + 1) ^ k

/-- **CTL* tree checking on trees with polylogarithmically shallow branching**: encodings `x` of
pairs `(φ, t)` such that every node of `t` with two or more children lies at depth
`< (⌊log₂ |x|⌋ + 1)^k`, and `t ⊨ φ`. -/
def CTLStarShallowTreeChecking (k : ℕ) : Language :=
  {x | ∃ (φ : CTLStar) (t : LTree),
    x = encodeToks (Tok.lpar :: (φ.toks ++ (Tok.rpar :: t.toks))) ∧
    ShallowBranching (shallowBound k x.length) t ∧ CTLStar.TreeSat t φ}

end PathChecking
