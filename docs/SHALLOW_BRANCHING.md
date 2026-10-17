# CTL* on trees with shallow branching: reduction to LTL path checking

Lean: `RequestProject/Shallow/Reduction.lean` (the reduction, §3) and `RequestProject/Shallow/`
(the logspace implementation, §4). The complexity results are Theorem 5 in
`RequestProject/Statements.lean`.

All statements below marked *(Lean)* are proved without `sorry`. `#print axioms` lists only
`propext`, `Classical.choice` and `Quot.sound`. The complexity consequence for polylogarithmic
branching depth is also proved in Lean, as Theorem 5 in `RequestProject/Statements.lean`
(§4.1). §4.2 lists the remarks of §4 that are informal only.

The semantics is the project's own: a finite tree becomes a Kripke structure by letting every
leaf loop to itself.

## 1. The tree class

`ShallowBranching d t` means: every node of `t` with two or more children lies at depth `< d`.
Equivalently, every subtree rooted at depth `d` is a simple path (`Linear`). Examples:

* a spider that branches only at the root: `d = 1`;
* a balanced binary tree with `N` nodes: `d ≈ log₂ N`;
* the single-fork trees of Theorem 4 (P-hard): `d` = length of the handle, i.e. linear.

## 2. Why the naive enumeration is not enough

A first idea is to enumerate all pairs (path, subformula) and evaluate them by LTL path
checking, innermost `E` first. This is correct, but the number of rounds of queries equals the
`E`-nesting depth of the formula. That depth can be linear: the P-hardness formulas have linear
nesting depth. So this order gives no parallel speed-up.

The reduction below enumerates the same pairs (path, subformula). The difference is that its
rounds follow **tree depth**, not formula depth. Within one round, nested `E`s of any depth are
handled by a single LTL formula.

## 3. The reduction

Let `φ` be the input formula. `pieces φ` lists the subformulas whose value *one step later* is
needed: the arguments of `X`, and the `U`-subformulas themselves.

### Tail round (depth `d`): `erase`, `tailLasso`

Below depth `d` every node `u` has exactly one path, so `E ψ ≡ ψ` there. Delete all path
quantifiers (`erase`) and check the resulting LTL formula on the lasso
`stem · leaf^ω` of the unique path (`tailLasso u`).

* `holds_iff_erase` *(Lean)*: on a path that starts at a linear node,
  `χ` holds iff `erase χ` holds on the sequence of labels.
* `tailLasso_letter` *(Lean)*: the letters of `tailLasso u` are exactly these labels.

### Branching round at a node `v`: `tr`, `roundLasso`

Let `p₀, …, p_{k-1}` be the paths from `v`, one per leaf below `v` (`treePaths v`;
`mem_treePaths` *(Lean)* shows these are exactly the tree paths from `v`). Assume that the
previous round has computed, for every piece `ψ` and every `j`, whether `ψ` holds on the tail
`pⱼ[1..]`. That tail is a path from a child of `v`.

* **Word.** Build the *cyclic* lasso `(L₀ L₁ ⋯ L_{k-1})^ω`, with one letter per path through
  `v`. Letter `Lⱼ` contains `2a` for every proposition `a` of `v`. It also contains the fresh
  proposition `nm φ ψ = 2·(index of ψ in pieces φ) + 1` for every piece `ψ` that holds on
  `pⱼ[1..]`. For the query about path `j`, the cycle is rotated so that it starts at `Lⱼ`.
* **Formula.** `tr` is the identity on Boolean structure, plus:
  * `X ψ ↦ nm φ ψ`;
  * `ψ₁ U ψ₂ ↦ tr ψ₂ ∨ (tr ψ₁ ∧ nm φ (ψ₁ U ψ₂))`, the expansion law;
  * `E ψ ↦ F (tr ψ)`.

  Because the word is cyclic, `F` reaches every path through `v`, from any starting position.
  Nested `E`s become nested `F`s in the same formula, so they cost no extra rounds.
* **Correctness.** `round_correct` *(Lean)*: for every subformula `χ` of `φ` and every `j < k`,
  `χ` holds on `pⱼ` iff `tr φ χ` holds at position 0 of the cycle rotated to `j`.

### The procedure: `vals`

`vals O φ n v` takes any oracle `O : LTL → LassoPath → Bool` and returns one truth table per
path from `v`. If `v` is linear, or if `n = 0`, it asks the tail queries. Otherwise it first
computes the tables of the children with budget `n - 1`, then builds the cyclic words and asks
one round of queries at `v`.

**Main theorem** (`Shallow.treeSat_iff_vals`) *(Lean)*: suppose `O ψ p = true ↔ p ⊨ ψ`, i.e.
`O` is an LTL path-checking oracle, and `ShallowBranching d t` holds. Then
`t ⊨ φ` iff every table in `vals O φ d t` reports `φ` true. The recursion has depth at most `d`,
so the procedure uses **at most `d + 1` rounds of queries**.
`treeSat_iff_ltlChecks` *(Lean)* is the same theorem with the semantic oracle plugged in.

**Size of the queries** *(Lean)*:
* `lsize_tr_le`: `|tr φ χ| ≤ 6·|χ|`.
* `lsize_erase_le`: `|erase χ| ≤ |χ|`.
* `nm_le`: every fresh proposition is a number `≤ 2|φ| + 1`.
* `roundLasso_loop_length`: the cyclic word at `v` has one letter per path from `v`, so its
  length is at most the number of leaves.

The fresh propositions are numbered by their position in `pieces φ` on purpose. A
pairing-function numbering of formulas would produce numbers with exponentially many bits.

## 4. Consequences for complexity

### 4.1 Formalised: Theorem 5 *(Lean)*

`RequestProject/Statements.lean` (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`):

* `CTLStarShallowTreeChecking k` (`RequestProject/Shallow/Lang.lean`): binary encodings `x` of
  pairs `(φ, t)` with all branching nodes of `t` at depth `< (⌊log₂ |x|⌋ + 1)^k` and `t ⊨ φ`.
* **5a** `CTLStarShallowTreeChecking_roundDecidable`: this language is decided by a logspace
  algorithm with `O(log^k n)` rounds of polynomially many parallel queries to the language
  `LTLPathChecking` (`RoundDecidable`, `RequestProject/ACRound/Defs.lean`). This is where the
  "simple bookkeeping" between rounds is proved to be logspace: both the function computing the
  queries of a round from the input and the previous answers, and the final decision function,
  are shown to be logspace computable.
* **5b** `CTLStarShallowTreeChecking_mem_AC_LogDCFL`: if the one-input-face monotone planar
  circuit value problem is in `LogDCFL` (`OIFMCVP_in_LogDCFL`, the Chakraborty–Datta theorem
  [CD06, Theorem 1], taken as a hypothesis), then `CTLStarShallowTreeChecking k ∈ AC^{k+1}[LogDCFL]`. The proof
  combines 5a with Theorem 1a (conditional form) by the generic step
  `RoundDecidable.mem_ACOracle_LogDCFL` (`RequestProject/ACRound/Main.lean`):
  `O(log^k n)` rounds of logspace work and queries to an `AC¹[LogDCFL]` language give
  `AC^{k+1}[LogDCFL]`.

How the formal algorithm relates to §3:

* **Oracle.** `vals` takes an abstract oracle `O`. Theorem 5 uses membership in the binary
  language `LTLPathChecking` instead: `ltlQuery_mem_iff` shows that this is an LTL path-checking
  oracle, and `treeSat_iff_vals_LTLPathChecking` is the main theorem of §3 with this oracle
  (`RequestProject/Shallow/Oracle.lean`).
* **Positional variant.** The logspace algorithm uses a variant of the branching round
  (`RequestProject/Shallow/PosRound.lean`, correctness `roundP_cyclic`). Fresh propositions are
  named by the token position of the subformula occurrence in the input, not by its index in
  `pieces φ`, and the original propositions are renamed so that they cannot clash with the fresh
  ones. The translation is adapted so that it can be written out token by token.
* **Counts.** For an input of length `n`, each round asks `(n + 1)^3` queries and the algorithm
  runs `2 (⌊log₂ n⌋ + 1)^k ≥ d + 1` rounds, where `d = (⌊log₂ n⌋ + 1)^k`
  (`RequestProject/Shallow/Glue.lean`).

Special cases:

* `k = 0` (all branching nodes at depth `< 1`, i.e. at most the root branches, e.g. spiders):
  5b gives `AC¹[LogDCFL]`, the bound of LTL path checking ([KF12, Theorem 1],
  [Kuh10, Corollary 4]).
* `k = 1` (branching depth `≤ ⌊log₂ n⌋`, e.g. balanced binary trees): 5b gives
  `AC²[LogDCFL]`, the same bound as for CTL tree checking (Theorem 1b, [Kuh10, Theorem 10]).

So the claim "branching nodes at polylogarithmic depth ⇒ NC" is proved in Lean, under the
hypothesis that the Chakraborty–Datta theorem holds.

### 4.2 Informal remarks (not formalised)

* **General depth `d`.** The argument of Theorem 5 suggests more generally that CTL* tree
  checking on trees with `ShallowBranching d` is decided by polynomial-size circuits of depth
  `O(d · log N)` with `d + 1` layers of oracle gates for LTL path checking. Lean only covers
  `d = (⌊log₂ n⌋ + 1)^k`.
* **Consistency with the hardness results.**
  * For the P-hard single-fork trees (Theorem 4) the branching node sits at linear depth, so the
    reduction needs linearly many rounds and gives no parallel speed-up. This is as expected.
  * The single-fork trees have just one branching node. So the number of rounds cannot be
    bounded by the number of branching nodes on a path: the *depth* of the branching is what
    matters.
  * With the padding variant mentioned in `CTLSTAR_PHARDNESS.md` §8 (branching at depth `N^ε`),
    the reduction needs `N^ε` rounds, which again fits.

## 5. What is not formalised

* The Chakraborty–Datta theorem [CD06, Theorem 1], which Theorem 5b takes as a hypothesis.
* The informal remarks of §4.2: the circuit bound for arbitrary `d`, and the comparison with
  the hardness results.
