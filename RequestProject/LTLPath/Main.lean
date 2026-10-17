module

public import RequestProject.LTLPath.OIF
public import RequestProject.ACRound.Main
public import RequestProject.LTLPath.FDD

/-!
# LTL path checking as a round algorithm

`ltl_roundDecidable`: LTL path checking is decided by a logspace algorithm with `O(log n)` rounds
of polynomially many parallel queries to any language that agrees with the circuit value problem
on one-input-face monotone planar circuits.

Together with `RoundDecidable.mem_ACOracle_of_LogDCFL` this gives Theorem 1a,
`LTLPathChecking_mem_AC1_LogDCFL_of_OIF` in `RequestProject/Statements.lean`.  The design of the
algorithm is described in `docs/LTL_PATH_CHECKING.md`.
-/

@[expose] public section

namespace PathChecking

/-- **LTL path checking with rounds of one-input-face circuit queries.** -/
theorem ltl_roundDecidable (B : Language)
    (hB : ∀ C : Circuit, OIFMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true)) :
    RoundDecidable LTLPathChecking B 1 :=
  roundDecidable_of_specs B hB qFun dFun qFun_logspace dFun_logspace qFun_spec dFun_spec

end PathChecking
