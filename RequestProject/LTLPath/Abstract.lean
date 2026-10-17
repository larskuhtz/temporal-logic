module

public import RequestProject.LTLPath.Sem
public import RequestProject.LTLPath.Sequence

/-!
# Correctness of the abstract algorithm

For a formula tree with a semantics (`Sem`) and root polarity `false`, after `4R + 1` rounds
with `L ≤ 2^R` of queries answered by an oracle that is correct on one-input-face instances,
the status of the root gate `(1, 0, main)` is the truth value of the formula at position `0`.
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

/-- **Correctness of the abstract algorithm.** -/
theorem oseq_root {B : Language} (hB : OIFCorrect B) {sat : ℕ → ℕ → Bool} (hS : T.Sem sat)
    (hpol : T.pol 1 = false) {R t : ℕ} (hR : T.L ≤ 2 ^ R) (ht : 4 * R + 1 ≤ t) :
    T.oseq B t (T.idx 1 0 1) = some (sat 1 0) := by
  have h1N : 1 < T.N := nd_lt_N T.nd_one
  have hpos : T.pos (T.idx 1 0 1) = 1 := (decode_idx h1N Wm_pos le_rfl).1
  rw [oseq_eq hB, seq_root hR ht hpos, gate_sem hS 1 T.nd_one 0 (by unfold W; nlinarith [T.hℓ]),
    hpol, Bool.xor_false]

end FT

end PathChecking
