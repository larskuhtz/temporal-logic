module

public import RequestProject.BLMS.Word
public import RequestProject.BLMS.Prog
public import RequestProject.LogLang.Main

/-!
# The stratified monotone planar circuit value problem is in `LogDCFL`

[BLMS, Theorem 2].  The reduction maps (the encoding of) a circuit `C` to the word
`circWord C`: the initial configuration of the pushdown algorithm of [BLMS, Section 5] followed
by enough copies of the table of its moves.  This map is computed by a program of the loop
language (`circProg_output`), hence is logspace computable, and the fixed deterministic pushdown
automaton `PD.pda` accepts `circWord C` iff `C` evaluates to `true` (`circWord_accepts`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

/-- **Barrington–Lu–Miltersen–Skyum theorem** [BLMS, Theorem 2]. -/
theorem stratMCVP_in_LogDCFL : StratMCVP_in_LogDCFL := by
  obtain ⟨V, E, P, hP⟩ := circProg_output
  refine ⟨{w | PD.pda.Accepts (P.output E w)}, ⟨{w | PD.pda.Accepts w}, ⟨PD.pda, fun _ => Iff.rfl⟩,
    P.output E, LL.logspaceComputable_of_output E P _ (fun _ => rfl), fun _ => Iff.rfl⟩, ?_⟩
  intro C hC
  show PD.pda.Accepts (P.output E C.encode) ↔ _
  rw [hP C hC]
  exact circWord_accepts hC

end BLMS

end PathChecking
