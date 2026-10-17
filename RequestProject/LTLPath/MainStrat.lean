module

public import RequestProject.LTLPath.Strat
public import RequestProject.LTLPath.Main
public import RequestProject.LTLPath.FDQS

/-!
# LTL path checking with rounds of stratified circuit queries

`ltl_roundDecidable_strat`: LTL path checking is decided by a logspace algorithm with
`O(log n)` rounds of polynomially many parallel queries to any language that agrees with the
circuit value problem on stratified monotone planar circuits.
-/

@[expose] public section

namespace PathChecking

/-- **LTL path checking with rounds of stratified circuit queries.** -/
theorem ltl_roundDecidable_strat (B : Language)
    (hB : ∀ C : Circuit, StratMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true)) :
    RoundDecidable LTLPathChecking B 1 :=
  roundDecidable_of_specsS B hB qFunS dFun qFunS_logspace dFun_logspace qFunS_spec dFun_spec

end PathChecking
