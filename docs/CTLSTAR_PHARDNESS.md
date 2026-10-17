# CTL* tree checking is P-hard and P-complete (Theorems 2–4)

**Short version.** `PHard CTLStarTreeChecking` (Theorem 2 in `RequestProject/Statements.lean`,
`CTLStarTreeChecking_PHard`) is proved in Lean, with no `sorry` and only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The proof composes two logspace reductions:

1. every language in `P` reduces to the monotone circuit value problem MCVP
   (`PHardness.MCVP_PHard`, `RequestProject/PHard/`, section 6), via the tableau circuit of a
   polynomial-time machine;
2. MCVP reduces to CTL* tree checking (`MCVPReduction.MCVP_logspaceReducible_CTLStar`,
   sections 2–4). The tree is a *caterpillar* (a path with one extra leaf hanging off some of
   its nodes). The formula has nesting depth linear in the circuit and size polynomial in it.

Composition of logspace reductions is `LogspaceReducible.trans` (section 5). CTL* tree checking
is also in P (Theorem 3, section 7), so it is P-complete (`CTLStarTreeChecking_PComplete`).
The statement "CTL* tree checking is in NC" is therefore equivalent to `P ⊆ NC` (informally,
using that NC is closed under logspace reductions). Since NC is widely believed to be a proper
subset of P, it is not stated as a conjecture in this project. Theorem 4 (section 8) shows
that P-hardness already holds on single-fork trees.

The mathematical core of the CTL* reduction is in `RequestProject/MCVP/Construction.lean`:

* `reductionFormula_correct`: for every well-formed monotone circuit `C`,
  `CTLStar.TreeSat (reductionTree C) (reductionFormula C) ↔ eval C = true`;
* `reductionFormula_toks_length`: the formula has at most `100 (n+1)²` tokens
  (`n` = number of gates). The tree has `3n` nodes.

---

## 1. Why the obvious approaches fail, and what the obstacle really is

* CTL* formulas are *trees*, not DAGs. If the level-`k` formula `Φ_k` used the level-`(k-1)`
  formula twice, the size would blow up exponentially. So every level must use the previous one
  **exactly once**.
* Information only flows *upwards* in the tree: a state formula at node `u` only depends on
  the subtree of `u`.
* After pushing negations inward (E/A, U/R duality), the evaluation circuit is **monotone**. So
  Goldschlager-style crossovers built from negation (planar CVP with NOT is P-complete,
  Goldschlager [Gol77]) are not
  available. Non-planarity has to come from the E/A quantifiers.
* Nesting depth and tree height both have to be large, because:
  * for bounded or polylogarithmic E-nesting depth, the problem is in NC: each nesting level is
    one round of LTL path checking plus a big OR;
  * for trees of polylogarithmic height, it is also in NC: one round per tree level, and inside
    a node a tree contraction over the formula with Boolean values.

  (These two NC claims are informal observations, not formalised.)

So we need one state formula `Φ_k` per gate-time `k`, used once in `Φ_{k+1}`, with the truth
values of `Φ_k` at the tree nodes acting as a **register file**. The difficulty is making a
single-use formula *copy* every register except one, while that one register reads two
arbitrary deeper registers.

## 2. The construction

Circuit: gates `g_0, …, g_{n-1}`. Each gate is a constant or `g_k = g_a ∘ g_b` with
`∘ ∈ {∧, ∨}` and `a, b < k`. The output is `g_{n-1}`.

**Tree (caterpillar).** The spine, from the root down, is

    R_{n-1}, D_{n-1}, R_{n-2}, D_{n-2}, …, R_0, D_0

Each *register* `R_g` has one extra leaf child `side`. Labels:

| node  | atoms |
|-------|-------|
| `R_g` | `act_g`; `in_k` for each gate `k` that reads `g`; `init` if `g_g` is the constant `true` |
| `D_g` | `dum_g` |
| side leaf | `side` |

**Formula.** Let `Φ_0 = init`. For each gate `k`:

* if `g_k` is a constant: `Φ_{k+1} = Φ_k`;
* if `g_k` is an `∨` gate: `Φ_{k+1} = E θ_k(Φ_k)`;
* if `g_k` is an `∧` gate: `Φ_{k+1} = ¬E θ_k(¬Φ_k)`;

where

    θ_k(p) = act_k U ( β₁ ∧ ( γ₂ U ( β₂ ∧ p ) ) )
    β₁ = (X side ∧ ¬act_k) ∨ dum_k
    γ₂ = ¬X X side ∧ ¬side
    β₂ = (X side ∨ in_k) ∧ ¬side ∧ ¬dum_k

The previous level `p` occurs exactly once. In prefix notation it is even the *last* subterm,
so the formula is just the concatenation of `n` short prefixes followed by `init`. That makes
the reduction easy to compute in logspace.

**Invariant.** `Φ_k` holds at `R_g` iff gate `g` evaluates to true, for every `g < k` and every
constant gate. Define `Read_k(v)` as the set of nodes at which `p` is evaluated along some path
from `v` that satisfies `θ_k(p)`. Then `E θ_k(p)` at `v` is the OR of `p` over `Read_k(v)`, and
`¬E θ_k(¬p)` is the AND. The key facts (Lean: `copy_read`, `active_read`) are:

* **Copy:** for `g ≠ k`, `Read_k(R_g) = {R_g}`. The only successful path steps into `R_g`'s side
  leaf, and the read happens at offset 0, using the side leaf as `X side`.
* **Compute:** `Read_k(R_k) = {R_a, R_b}`. First phase: `act_k` holds only at `R_k`, so the first
  `U` must end exactly one step later. That node must be `D_k`, which is where `dum_k` holds.
  Second phase: walk down the spine. `¬X X side` stops the walk from ending at a register via
  its side leaf. So the read position must carry `in_k`, i.e. it is `R_a` or `R_b`.

The dummy node `D_k` is the trick that makes copying and reading compatible. Without it, a
register *between* `R_k` and its inputs sees exactly the same path suffix as the active path
passing through it, and also reads `R_a`/`R_b`. With the two-phase until, such a register would
need `β₁` on the spine branch, which only holds at `D_k`.

## 3. Semantic correctness (verified)

Verified in Lean (no `sorry`; only the standard axioms `propext`, `Classical.choice`,
`Quot.sound`):

1. Correctness of the reduction for the semantics of `Logics.lean` (finite trees, leaves loop to
   themselves, CTL* with `X`, `U`, `E`): `reductionFormula_correct`.
2. Polynomial formula size: `reductionFormula_toks_length`.

Before the Lean proof, a random-testing script was run on 3000 random circuits with an
independent CTL* evaluator. It found no mismatches, while a deliberately broken variant of the
construction gave 402 mismatches. This was exploratory and is superseded by the Lean proof.

## 4. Step (b): the reduction map is logspace computable (verified)

This step is now machine-checked, end to end, for the actual binary encodings used in the
project. Main results (all in `RequestProject/MCVP/`, no `sorry`, only the standard axioms):

* `Defs.lean`: `MCVP` is the language of encodings `encodeCircuit C` of non-empty well-formed
  monotone circuits whose last gate evaluates to true. Gates are encoded as a tag token followed
  by the two argument indices in binary (`natToks`), with the same 5-bit token blocks as the CTL*
  instances. `redFun` is the reduction map on binary words: a valid circuit code goes to the
  encoding of `(reductionFormula C, reductionTree C)`, and anything else goes to the empty word
  (never an instance). `redFun_correct : w ∈ MCVP ↔ redFun w ∈ CTLStarTreeChecking`. Its proof
  includes unique decodability of circuits, formulas and trees.
* `Main.lean`:
  * `redFun_logspaceComputable : LogspaceComputable redFun`. This is about the Turing machines
    of `Complexity.lean` (read-only input, one work tape whose head must stay within
    `c · (⌊log₂ n⌋ + 1)` cells, write-only output).
  * `MCVP_logspaceReducible_CTLStar : LogspaceReducible MCVP CTLStarTreeChecking`.
  * `CTLStarTreeChecking_PHard_of_MCVP`: if `MCVP` is P-hard (a), then
    `PHard CTLStarTreeChecking` (using (c), `LogspaceReducible.trans`, section 5).

How the logspace bound is obtained:

1. `Logspace/Prog.lean`, `Logspace/Machine.lean`: a small structured language with natural-number
   registers, a two-way read-only input head and a write-only output. The operations are
   increment, decrement, zero test, input-symbol test, head moves, output a bit, sequencing,
   if-then-else and while. Its big-step semantics carries a bound `B` on the registers.
   `logspaceComputable_of_prog` compiles any program whose registers stay below
   `B(w) < 2^(d (⌊log₂ |w|⌋ + 1))` into a Turing machine of the project's model. The registers
   are stored in binary on separate tracks of the work tape. The theorem proves that this
   machine computes the same function within the space bound.
2. `MCVP/*.lean`: the reduction program `redProg` uses 20 registers, all bounded by
   `4|w| + 4`. It works in two phases.
   * **Validation** (`validate`): parse the input gate by gate. Gate indices are compared with
     the gate counter least-significant-bit first (`cmpNum`), which also checks that numbers are
     canonical (no trailing zero). The specification works for arbitrary inputs: the program
     accepts exactly the words with `ValidCode w`, and then holds the number of gates.
   * **Output** (`outputProg`): stream `( Φ_n ) t`.
     * The formula is a concatenation of fixed prefix blocks, one per gate `k = n-1, …, 0`,
       followed by `init`. Each block is fixed tokens plus the numbers `4k+1, 4k+2, 4k+3`,
       written in binary.
     * The tree is a concatenation of blocks, one per gate `g = n-1, …, 0`, followed by `2n`
       closing brackets. The label of `R_g` (the non-linear part, `regLabel`) is produced in
       the sorted order required by `finsetToks`: first `act_g`/`init`, then `in_k` for
       `k = 0, …, n-1` in increasing order. For each `k` the program re-locates gate `k` on the
       input and compares its two arguments with `g`. `regLabel_sort` proves that this list is
       exactly `(regLabel C g).sort (· ≤ ·)`. This uses well-formedness: every gate reading `g`
       has index `> g`.
   * Only positions (head moves), counters `≤ n` and numbers `≤ 4n+3` are kept. Gates and
     numbers are re-read from the input whenever they are needed.

`ach_redProg` proves that `redProg`, started in the initial state, terminates with output
exactly `redFun w`, for **every** word `w` (valid or not).

## 5. Step (c): logspace reductions compose (verified)

That logspace computable functions compose is classical [Jon75]; see also [Pap94] and [AB09].
`RequestProject/Logspace/Compose.lean` proves it for the Turing machines of `Complexity.lean`:

* `LogspaceComputable.comp : LogspaceComputable f → LogspaceComputable g →
  LogspaceComputable (g ∘ f)`;
* `LogspaceReducible.trans : LogspaceReducible A B → LogspaceReducible B C →
  LogspaceReducible A C`.

How it is proved:

1. `Logspace/OutBound.lean`: a halting machine whose work head stays within `S` cells cannot
   repeat a configuration (ignoring the output) before halting. Counting configurations gives
   a halting time of at most `|Q| · (n+2) · (S+1) · |Γ|^(S+1)`. So a logspace computable `f`
   has `|f w| + 2 ≤ 2^(e (⌊log₂ |w|⌋ + 1))` for a constant `e`
   (`LogspaceComputable.exists_bound`).
2. `Logspace/Arith.lean`: verified register-program gadgets with constant parameters:
   case distinction on a register value, `r := G·r + d`, and division with remainder by `G`.
3. `Logspace/SimTM.lean`: one step of an arbitrary machine `M` as a register program
   (`simStep`, `ach_simStep`). The state index, the work head position, and the work tape are
   held in registers. The tape is split at the head into two numbers in base `|Γ|`, with the
   blank as digit `0`. Input head moves and output are parameters of the step, so the same
   code simulates a machine on the real input or on a virtual one.
4. `Logspace/Compose.lean`: the program `compProg` simulates `M₂` on the virtual input `f w`.
   Whenever `M₂` needs the symbol at virtual position `i`, the subroutine `sub` rewinds the
   input and re-runs `M₁` on `w` from its initial configuration. It counts output bits down
   from `i - 1` and records the bit when the counter reaches `0`; if `M₁` halts first, the
   symbol is the right end marker. All registers are bounded by a polynomial in `|w|`
   (`register_bound`), so `logspaceComputable_of_prog` yields a logspace machine for `g ∘ f`.

## 6. Step (a): MCVP is P-hard (verified)

Ladner [Lad75] showed that CVP is P-complete, using a tableau construction, and Goldschlager
[Gol77] showed the same for MCVP; see also [GHR95]. `RequestProject/PHard/Main.lean` proves `MCVP_PHard : PHard MCVP` for
the Turing machines of `Complexity.lean` and the encoding `encodeCircuit`.

* `PHard/Tableau.lean`: for a machine `M` deciding a language in time `T = c (n+1)^c`, the
  *tableau circuit* `tabCircuit M c w`. A configuration is represented by boolean *entries*
  `(p, j, z)`: either "input head at `p`, work head at `j`, state `z / 4`, abstracted output
  `z % 4`" (the output is abstracted to `[]`, `[false]`, `[true]` or "other"), or "work cell `j`
  holds symbol `z - 4|Q|`". Every entry of the next configuration is an OR, over all pairs of
  entries `(a, b)`, of `a ∧ b ∧ K(a, b)`, where the selector `K` only depends on the indices and
  on the input. The OR is computed by a chain of binary gates, and gate number `g` is given by a
  closed formula `gateFn M c w g`. `tabCircuit_eval` proves that the circuit evaluates to true
  iff `M` has halted after `T` steps with output `[true]`; `tabCircuit_wellFormed` proves that
  every gate only reads earlier gates.
* `PHard/Ops.lean`, `Expr.lean`, `Lib.lean`: verified register-program gadgets: arithmetic
  expressions (`+`, truncated `-`, `·`, `/`, `%`) compiled into register code, boolean tests,
  output of gates, input-head positioning, assignments and counting loops.
* `PHard/Prog.lean`, `Body.lean`, `Step.lean`, `Gate.lean`: the loop body `body M` decodes the
  gate index `g` into the entry indices and their components, decides the selector (by case
  distinction on the finitely many state/symbol codes and on the input symbol under the
  relevant head position), and outputs `gateFn M c w g` (`ach_body`).
* `PHard/Run.lean`: the program `tabProg M c` computes the parameters and then outputs all
  gates in order (`ach_tabProg`). All registers stay below the number of gates `Nb`, and
  `Nb_lt_pow` bounds it by `2^(d (⌊log₂ n⌋ + 1))`. So `logspaceComputable_of_prog` gives
  `tabRed_logspaceComputable`.

## 7. Membership in P, hence P-completeness (verified)

Theorem 3, `CTLStarTreeChecking_mem_P : CTLStarTreeChecking ∈ ClassP` in
`RequestProject/Statements.lean`, is proved for the Turing machines of `Complexity.lean` from
the program in `RequestProject/CTLStarP/`. Together with Theorem 2 this gives
`CTLStarTreeChecking_PComplete`.

* `PTime/`: a structured language with natural-number variables, arithmetic expressions, random
  access to the input tokens and a monotone bit memory (bits can be set but never cleared).
  `polytimeComputable_of_hl` compiles a terminating program whose values stay below a polynomial
  bound into a polynomial-time Turing machine. The time bound comes from counting: between two
  changes of the memory, no state of the goto program can repeat.
* `CTLStarP/Scan.lean`, `Valid*.lean`, `TreePos.lean`, `Eval*.lean`: a pure decision procedure
  `decideCTL` on token lists, with `decideCTL_iff`. A path from node `u` is described by a target
  position `ℓ` (it moves towards the leaf at `ℓ`), so the truth value of a path subformula at
  position `j` is a table entry `val j u ℓ` with polynomially many entries; `E ψ` at `u` is the
  disjunction of `val (j+1) u ℓ` over all `ℓ`.
* `CTLStarP/Prog/`: the procedure as a structured program. The first phase (`Tab.lean`) tabulates
  well-formed subformulas and lists of subtrees and checks the input format. The second phase
  (`Val.lean`, `Phase2.lean`) stores `val j u ℓ` in memory bit `2n + (j n + u) n + ℓ`, for
  decreasing `j`, decreasing `u` and increasing `ℓ`, so that each entry only reads entries already
  computed. `finalP` checks `val 1 root ℓ` for all `ℓ`.
* `CTLStarP/Main.lean`: the program first counts the input tokens and rejects inputs that are not
  token sequences; `main_correct` shows that it outputs `[decide (w ∈ CTLStarTreeChecking)]`,
  with all values below `16 (|w| + 2)^3 + 64`.

## 8. Restricted topologies: one single side leaf is enough (verified)

**Result.** `CTLStarSingleForkTreeChecking_PHard : PHard CTLStarSingleForkTreeChecking`
(`RequestProject/Statements.lean`, Theorem 4; no `sorry`, only the standard axioms). The language
`CTLStarSingleForkTreeChecking` (`RequestProject/Fork/Construction.lean`) is CTL* tree checking
restricted to *single-fork trees* (`LTree.IsSingleFork`): a path whose last node has exactly
two children, both of them leaves. Put differently, it is a path with exactly one extra side
leaf, attached to its last inner node. Such a tree has exactly two leaves and out-degree at most
2. It has a single branching node, and that node is the deepest inner node.

So neither unbounded branching nor many side leaves is needed: **two leaves suffice**. This
also covers "constant branching". The caterpillar of section 2 already had out-degree ≤ 2, and
the single-fork tree is the smallest kind of tree that is not a path.

**Construction** (`forkTree`, `forkFormula`). The tree is the spine `R_{n-1}, …, R_0` of
registers, and `R_0` has two leaf children `self` and `walk`. There are no dummy nodes. Register
labels are as in section 2. Every register therefore has exactly two paths: the *self path*
(down the spine into `self`) and the *walk path* (down the spine into `walk`). The path formulas
`F self` and `F walk` tell them apart at **every** position. That is what the per-register side
leaves and the dummy nodes did before. Level `k` uses

    θ_k(p) = (act_k ∨ F self) ∧ (F walk U ((in_k ∨ (¬act_k ∧ F self)) ∧ p))

with `Φ_{k+1} = E θ_k(Φ_k)` (∨ gates), `¬E θ_k(¬Φ_k)` (∧ gates), and `Φ_{k+1} = Φ_k` (constant
gates). Again `p` occurs exactly once, as the last subterm in prefix notation.

* **Copy** (`fork_copy_read`): for `g ≠ k`, the register `R_g` has no `act_k`, so it must use its
  self path. Along the self path `F walk` is false everywhere, so the until has to end at offset
  0, and the formula reads `p` at `R_g` itself.
* **Compute** (`fork_active_read`): at offset 0, `R_k` cannot read, because it has `act_k` and no
  `in_k`. So the until has to move, which needs `F walk`, i.e. the walk path. Along the walk path
  `F self` is false, so the reading positions are exactly the nodes labelled `in_k`, the two
  input registers.

A non-active register `R_g` lying between `R_k` and its inputs sees the same walk-path suffix as
`R_k`. It cannot exploit this, because entering that suffix requires `act_k ∨ F self` at the
start, which fails for `R_g` on the walk path.

**Verified pieces.**

* `forkFormula_correct`: `TreeSat (forkTree C) (forkFormula C) ↔ eval C = true` for every
  well-formed circuit.
* `forkTree_isSingleFork`: the tree has the required shape.
* `forkRedFun_correct`, `forkRedFun_logspaceComputable` (`RequestProject/Fork/`): the program
  `forkProg` uses the same validation phase and the same streaming routines as `redProg`
  (section 4). Only the formula blocks, the tree blocks and the final brackets differ.
* Composition with `PHardness.MCVP_PHard`.

Membership of the restricted problem in P is not formalised separately. Informally it follows
from section 7 together with a logspace check of the tree shape. So the restricted problem is
P-complete as well, but that claim is not machine-checked.

**What the topology has to provide (informal discussion, not formalised).**

* *A path* gives LTL path checking: on a path, `E ψ ≡ ψ` at every node. Its best known upper
  bound is `AC^1[LogDCFL] ⊆ NC` ([KF09, Theorem 2], [KF12, Theorem 1] for finite paths,
  [Kuh10, Corollary 4] for lasso paths; Theorem 1a, proved in this project).
* *Where the side leaf hangs is what matters, not how many leaves there are.* Suppose the single
  side leaf hangs at the root, or more generally at constant depth `d`. Every node below the
  branching node has only one path, so all state subformulas there are evaluated by LTL path
  checking. At the `d` nodes above the branching node, the values of all subformulas for both
  paths form a Boolean circuit of depth `O(|φ|)` built from formula-shaped pieces. I expect that
  this case stays within the LTL bounds plus `NC^1` formula evaluation, but I have not checked
  the details. The reduction needs the branching node *below* a path of `n` registers, because
  all `n` registers need two distinguishable continuations.
* *Padding.* Make the walk leaf the end of a long extra path of length `n^{1/ε}` with empty
  labels (keeping `F walk` on its last node). This gives P-hardness on single-fork trees whose
  branching node has depth only `N^ε`, where `N` is the size of the tree. This variant is not
  formalised.
* *General topologies.* The construction appears to tolerate extra subtrees with empty labels
  hanging off the spine: along them `F self` and `F walk` are both false, so they never satisfy
  `θ_k`. It also tolerates extra unlabelled spine nodes between registers. That suggests the
  following (unverified) picture: CTL* tree checking is P-hard on every tree family that
  contains, in a logspace-constructible way, trees with a branching node at depth `n^{Ω(1)}`.
  These include caterpillars, brooms (a long handle with several leaves at its end) and full
  binary trees of polynomial height. In contrast, families whose branching nodes all lie
  at polylogarithmic depth, such as balanced binary trees and spiders branching only at the root,
  seem to stay "LTL-like". For branching depth `(log n)^k` this is Theorem 5 (see
  `docs/SHALLOW_BRANCHING.md`): such instances are in `AC^{k+1}[LogDCFL]`, assuming the
  Chakraborty–Datta theorem [CD06, Theorem 1].

**Caveat.** I have not checked the literature for this result. The construction and proof are
for the semantics formalised in this project. Please check that they match the intended
setting, e.g. whether trees with finite maximal paths should be used instead of self-looping
leaves.
