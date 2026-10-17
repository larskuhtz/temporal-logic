module

public import RequestProject.CTLTree.DProg

/-!
# CTL tree checking with `O(log n)` rounds of LTL path checking queries

Following [Kuh10], CTL tree checking is decided by a logspace algorithm asking `⌊log₂ n⌋ + 1`
rounds of polynomially many parallel queries to LTL path checking.

In every round, for every node `u` and every subformula, one LTL query is asked on the *chain*
of `u`: the path from `u` through the kids of size at least half the size of `u`.  The
subformulas `EX`, `EU`, `AU` are translated so that their values through the other (small) kids
are read from the answers of the previous round (`RequestProject/CTLTree/Chain.lean`,
`RequestProject/CTLTree/QCorrect.lean`).  Since small kids have less than half the size, after
`r` rounds the answers are correct for all nodes of size `< 2^r`
(`RequestProject/CTLTree/Glue.lean`).  The query and decision functions are logspace
(`RequestProject/CTLTree/FQ3.lean`, `RequestProject/CTLTree/DProg.lean`).
-/

@[expose] public section

namespace PathChecking

/-- **CTL tree checking by rounds of LTL path checking queries.** -/
theorem CTLT.roundDecidable : RoundDecidable CTLTreeChecking LTLPathChecking 1 :=
  CTLT.roundDecidable_of_specs qFunC dFunC qFunC_logspace dFunC_logspace qFunC_spec dFunC_spec

end PathChecking
