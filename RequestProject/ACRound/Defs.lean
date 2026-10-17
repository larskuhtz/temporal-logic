module

public import RequestProject.Complexity

/-!
# Logspace algorithms with rounds of parallel oracle queries

`RoundDecidable A B k` says that `A` is decided by a logspace algorithm that asks
`O(log^k n)` *rounds* of polynomially many parallel queries to the oracle `B`:

* the queries of a round are computed by a logspace function `Q` from the input `w`, the
  index `q` of the query and the answers `a` of the previous round, packed into one word
  `pack w q a`;
* after the last round, a logspace function `D` decides from `w` and the last answers.

The main result about these algorithms, `RoundDecidable.mem_ACOracle_add` in
`RequestProject/ACRound/Main.lean`, says: if moreover `B ∈ AC^j[LogDCFL]`, then
`A ∈ AC^{k+j}[LogDCFL]`.
-/

@[expose] public section

namespace PathChecking

/-- The input of the query function and of the decision function: the input `w` (preceded by
its length in unary, so that it can be located), the answers `a` of the previous round, and the
index `q ≤ |a|` of the query, written in unary at the end (`|a| - q` zeros followed by `q` ones).
The length `2 |w| + 1 + 2 |a|` does not depend on `q` or on the bits of `a`. -/
def pack (w : Word) (q : ℕ) (a : List Bool) : Word :=
  List.replicate w.length true ++ [false] ++ w ++ a ++
    List.replicate (a.length - q) false ++ List.replicate q true

/-- Length of a packed input. -/
lemma pack_length (w : Word) (q : ℕ) (a : List Bool) (hq : q ≤ a.length) :
    (pack w q a).length = 2 * w.length + 1 + 2 * a.length := by
  simp [pack]; omega

/-- Answers of the rounds of an oracle algorithm with query function `Q`, `Nq` queries per
round and oracle `B`: round `0` is all `false`; in round `r + 1`, query `q < Nq` is the word
`Q (pack w q a)`, where `a` are the answers of round `r`. -/
noncomputable def roundAns (B : Language) (Q : Word → Word) (Nq : ℕ) (w : Word) :
    ℕ → List Bool
  | 0 => List.replicate Nq false
  | r + 1 => (List.range Nq).map fun q =>
      @decide (Q (pack w q (roundAns B Q Nq w r)) ∈ B) (Classical.dec _)

/-- `A` is decidable by a logspace algorithm with `c · (⌊log₂ n⌋ + 1)^k` rounds of
`(n + 1)^e` parallel queries to `B` (on inputs of length `n`). -/
def RoundDecidable (A B : Language) (k : ℕ) : Prop :=
  ∃ (e c : ℕ) (Q D : Word → Word), LogspaceComputable Q ∧ LogspaceComputable D ∧
    ∀ w : Word, w ∈ A ↔
      D (pack w 0 (roundAns B Q ((w.length + 1) ^ e) w (c * (Nat.log 2 w.length + 1) ^ k))) =
        [true]

end PathChecking
