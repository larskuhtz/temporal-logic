module

public import RequestProject.Complexity
public import RequestProject.Shallow.Lang
public import RequestProject.Shallow.Glue
public import RequestProject.ACRound.Main
public import RequestProject.Shallow.Prog.DProg

/-!
# Complexity of CTL* tree checking on trees with shallow branching

`CTLStarShallowTreeChecking k` is CTL* tree checking restricted to instances `(φ, t)` of
(binary) size `n` whose tree has all branching nodes at depth `< (⌊log₂ n⌋ + 1)^k`
(`ShallowBranching`).  The reduction of `RequestProject/Shallow/Reduction.lean` decides such an
instance with `(⌊log₂ n⌋ + 1)^k + 1` rounds of parallel LTL path-checking queries.

This file provides the logspace query function (`ShallowP.exists_QProg`) and decision function
(`ShallowP.exists_DProg`) of that round algorithm.  They are assembled into Theorem 5
(`CTLStarShallowTreeChecking_roundDecidable`, `CTLStarShallowTreeChecking_mem_AC_LogDCFL`) in
`RequestProject/Statements.lean`.  See `docs/SHALLOW_BRANCHING.md`.
-/

@[expose] public section

namespace PathChecking

/-- The query function of the round algorithm: a logspace function producing the queries
`QP` of the positional reduction from the packed input. -/
theorem ShallowP.exists_QProg (k : ℕ) :
    ∃ Q : Word → Word, LogspaceComputable Q ∧ ShallowP.QSpecOK k Q :=
  SQ.exists_QProg k

/-- The decision function of the round algorithm: a logspace function checking that the input
is an instance with shallow branching and that the answers for the root are all true. -/
theorem ShallowP.exists_DProg (k : ℕ) :
    ∃ D : Word → Word, LogspaceComputable D ∧ ShallowP.DSpecOK k D :=
  SQ.exists_DProg k

end PathChecking
