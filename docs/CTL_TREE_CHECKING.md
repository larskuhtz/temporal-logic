# Theorem 1b: CTL tree checking in `AC²[LogDCFL]`

Lean statements (in `RequestProject/Statements.lean`):

* `CTLTreeChecking_roundDecidable : RoundDecidable CTLTreeChecking LTLPathChecking 1`.
  CTL tree checking is decided by a logspace algorithm that asks `⌊log₂ n⌋ + 1` rounds of
  polynomially many parallel queries to LTL path checking.
* `CTLTreeChecking_mem_AC2_LogDCFL_of_OIF (h : OIFMCVP_in_LogDCFL) :
  CTLTreeChecking ∈ ACOracle 2 LogDCFL`. This is the round algorithm combined with Theorem 1a
  (`LTLPathChecking_mem_AC1_LogDCFL_of_OIF`) through `RoundDecidable.mem_ACOracle_LogDCFL`.
* `CTLTreeChecking_mem_AC2_LogDCFL`: the unconditional form. It combines the round algorithm
  with the unconditional Theorem 1a (`LTLPathChecking_mem_AC1_LogDCFL`), which rests on the
  Barrington–Lu–Miltersen–Skyum theorem [BLMS99, Theorem 2], proved in `RequestProject/BLMS/`.

All three statements are proved without `sorry`. They use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Relation to Kuhtz's proof

[Kuh10, Theorem 10] proves the bound as follows (Section 5.2 of the thesis):

1. The CTL expansion laws unroll the formula over the tree. The result is a circuit whose graph
   is a subgraph of the product of the formula tree and the computation tree.
2. The computation tree is contracted in `O(log n)` parallel stages. This is an `AC¹`
   reduction to circuits that are subgraphs of the product of a *path* and the formula tree.
3. The formula tree is then contracted as in LTL path checking. This is an `AC¹` reduction to
   one-input-face circuits, which are evaluated in `LogDCFL` ([Kuh10, Corollary 1], based on
   [CD06]).

Before these steps, a logspace reduction makes the tree binary ([Kuh10, Lemma 12]).

The formal proof is organised differently:

* **Contraction.** The computation tree is not contracted by rake/compress operations. It is
  split into *chains* by halving sizes. A chain is a heavy-path style decomposition, described
  below. Each of the `⌊log₂ n⌋ + 1` rounds handles all chains in parallel.
* **The path case is a black box.** Each round asks LTL path checking queries, which are
  instances of the problem of Theorem 1a. The `AC¹[LogDCFL]` bound of Theorem 1a is then
  used as is. The generic simulation of round algorithms by circuits
  (`RequestProject/ACRound/`) gives the `AC²` bound.
* **No binarisation.** The reduction to binary trees ([Kuh10, Lemma 12]) is not needed. Chains
  read the values through all non-chain children from the previous round, so arbitrary degrees
  are handled directly.

## The round algorithm

Instances are token lists `( φ ) t`. Positions of node encodings are recognised locally. The
size `sz u` of the node at position `u` is the length of its encoding.

**Chains** (`RequestProject/CTLTree/Pos.lean`). The chain of `u` is the list of node positions
`q` inside `u` with `sz u ≤ 2 · sz q`. Such nodes form a path from `u` downwards
(`chain_struct`). Every node has at most one *big* kid (`2 · sz c ≥ sz u`), and the chain
follows it. All other kids of chain nodes are *small*: `2 · sz c < sz u`.

**The query** (`RequestProject/CTLTree/Query.lean`). In every round, for every node position
`u` and every formula position `j`, the query `CQ` is an LTL path checking instance. Its lasso
word is

    N₀ X₀ N₁ X₁ ⋯ N_m X_m ⋯

with one *node letter* `N_i` and one *exit letter* `X_i` for each chain node `v_i`.

* The node letter is the label of `v_i`, renamed by `a ↦ a · 2^m + 2^m − 1`.
* The exit letter contains:
  * the proposition `0`, which marks exit positions;
  * the proposition `1`, at the last chain node if that node is not a leaf;
  * a proposition `k + 2` for every `EX`, `EU` or `AU` subformula at position `k`. Its value is
    the value of that subformula through the small kids of `v_i`, read from the answers of the
    previous round.
* After `X_m` the word is periodic: `(N_m X_m)^ω` if `v_m` is a leaf, and `X_m^ω` otherwise.

The formula of the query is the translation `trC` (`RequestProject/CTLTree/Chain.lean`). It is
the identity on Boolean structure, and maps

* `EX ψ ↦ X (k+2 ∨ X (¬0 ∧ ψ'))`,
* `ψ EU χ ↦ (0 ∨ ψ') U (if 0 then k+2 else χ')`,
* `ψ AU χ ↦ (if 0 then k+2 else ψ') U (if 0 then (k+2 ∧ 1) else χ')`.

`trC_correct` states: if the exit letters satisfy the sandwich conditions of `WordOK`, then
at every node position `2i` the translation holds iff the CTL subformula holds at `v_i`. The
proof is a backward induction along the chain, using the expansion laws of
`RequestProject/CTLTree/Sem.lean`. `CQ_correct` (`RequestProject/CTLTree/QCorrect.lean`)
checks these conditions for the word of the query. Here it uses that the answers of the
previous round are correct for all nodes of size `< sz u / 2`.

**Stabilisation** (`RequestProject/CTLTree/Glue.lean`). By induction on `r`, after `r` rounds
the answers are correct for all nodes of size `< 2^r` (`stab`). Since `2^(⌊log₂ n⌋ + 1) > n`,
the answer for the root and the main formula is correct after `⌊log₂ n⌋ + 1` rounds.
`roundDecidable_of_specs` assembles the round algorithm from the specifications of the query
and decision functions.

## Logspace implementations

* **Query function** (`RequestProject/CTLTree/FQ1.lean` – `FQ3.lean`). The query function is
  written in the denotational calculus of `RequestProject/LTLPath/FED.lean`, which compiles to
  logspace transducers. `qFunC_spec` proves that it outputs `CQ`, and `qFunC_logspace` that it
  is logspace computable.
* **Decision function** (`RequestProject/CTLTree/DProg.lean`). The decision function must also
  recognise encodings of CTL instances. The token map `hL` replaces the binary CTL tag `AU`
  (tag `6`) by the CTL* tags `E ∧` (tags `6 3`). Then `ts` is a CTL instance iff `hL ts` is a
  CTL* instance (`recog_hL_iff`, `RequestProject/CTLTree/Embed.lean`). CTL* instances are
  recognised by the counter-based recogniser of `RequestProject/Shallow/`, with a branching
  bound that never restricts (`RequestProject/CTLTree/DRecog.lean`). The decision function is
  the conjunction of this test and the answer bit of the root. It is assembled from logspace
  functions with `LogspaceComputable.append` and `LogspaceComputable.comp`.
