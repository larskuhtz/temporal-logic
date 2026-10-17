This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Parallel complexity of path and tree checking for temporal logics, in Lean 4

This project formalises, in Lean 4 with Mathlib, results on the complexity of **path checking**
and **tree checking**. The question is whether a single lasso path or a single finite tree
satisfies a formula of LTL, BLTL+Past, CTL or CTL*. Lean is used both to state results from
the literature and to prove results about CTL* tree checking.

The machine models and complexity classes are defined from scratch in the project. They are
Turing machines with a read-only input tape, logspace and polynomial-time computability,
logspace reductions, `P`-hardness, deterministic pushdown automata and `LogDCFL`, and
logspace-uniform circuit families with oracle gates (`AC^k[𝒞]`, `NC`).

## Main results

All top-level statements are in [`RequestProject/Statements.lean`](RequestProject/Statements.lean).

| | Statement | Lean name | Status |
| --- | --- | --- | --- |
| CD | One-input-face monotone planar circuit value is in `LogDCFL` (Chakraborty–Datta) | `OIFMCVP_mem_LogDCFL` | stated, not proved |
| BLMS | Stratified monotone planar circuit value is in `LogDCFL` (Barrington–Lu–Miltersen–Skyum) | `StratMCVP_mem_LogDCFL` | **proved** |
| 1a | LTL path checking is in `AC¹[LogDCFL]`, assuming CD | `LTLPathChecking_mem_AC1_LogDCFL_of_OIF` | **proved** |
| 1a | LTL path checking is in `AC¹[LogDCFL]`, assuming BLMS | `LTLPathChecking_mem_AC1_LogDCFL_of_strat` | **proved** |
| 1a | LTL path checking is in `AC¹[LogDCFL]` | `LTLPathChecking_mem_AC1_LogDCFL` | **proved** (from row BLMS and the row above) |
| 1b | CTL tree checking is decided by a logspace algorithm with `⌊log₂ n⌋ + 1` rounds of parallel queries to LTL path checking | `CTLTreeChecking_roundDecidable` | **proved** |
| 1b | CTL tree checking is in `AC²[LogDCFL]`, assuming CD | `CTLTreeChecking_mem_AC2_LogDCFL_of_OIF` | **proved** |
| 1b | CTL tree checking is in `AC²[LogDCFL]` | `CTLTreeChecking_mem_AC2_LogDCFL` | **proved** (from the round algorithm and the unconditional 1a) |
| 1c | BLTL+Past path checking is in `NC` | `BLTLPastPathChecking_mem_NC` | stated, not proved |
| 2 | CTL* tree checking is `P`-hard | `CTLStarTreeChecking_PHard` | **proved** |
| 3 | CTL* tree checking is in `P`, hence `P`-complete | `CTLStarTreeChecking_mem_P`, `CTLStarTreeChecking_PComplete` | **proved** |
| 4 | CTL* tree checking is `P`-hard already on single-fork trees (a path plus one extra leaf at its end) | `CTLStarSingleForkTreeChecking_PHard` | **proved** |
| 5a | CTL* tree checking on trees whose branching nodes lie at depth `< (⌊log₂ n⌋ + 1)^k` is decided by a logspace algorithm with `O(log^k n)` rounds of parallel queries to LTL path checking | `CTLStarShallowTreeChecking_roundDecidable` | **proved** |
| 5b | The same restricted problem is in `AC^{k+1}[LogDCFL]`, assuming CD | `CTLStarShallowTreeChecking_mem_AC_LogDCFL` | **proved** |

Rows 1a–1c are results of Kuhtz and Finkbeiner and of Kuhtz's PhD thesis: 1a is
[KF09, Theorem 2] and [KF12, Theorem 1] for finite paths and [Kuh10, Corollary 4] for lasso
paths, 1b is [Kuh10, Theorem 10], and 1c follows from [KF12, Theorem 3] and [Kuh10, Theorem 13].
Row CD is [CD06, Theorem 1], and row BLMS is [BLMS99, Theorem 2]. The project proves BLMS
following [BLMS99, Section 5] (`RequestProject/BLMS/`): a logspace map sends a circuit to
the initial configuration of their pushdown algorithm followed by copies of its move table, and a
fixed deterministic pushdown automaton accepts the result iff the circuit evaluates to `true`.
Hence 1a and 1b are proved unconditionally; the `_of_OIF` forms keep CD as an explicit hypothesis. The BLMS form of 1a
builds the query circuits directly as stratified circuits, so it does not need the reduction from
one-input-face circuits to stratified circuits of Chakraborty and Datta [CD06]. 1b is reduced to 1a by a round
algorithm of this project's own; [Kuh10, Theorem 10] instead contracts the computation tree
directly (see [`docs/CTL_TREE_CHECKING.md`](docs/CTL_TREE_CHECKING.md)). 1c is stated
without proof.

Rows 2–5 are about CTL* tree checking. They are proved in Lean, and we know of no published
source for them. Kuhtz's thesis [Kuh10, Chapter 7] lists the complexity of CTL* tree checking as an
open question. By Theorems 2 and 3, CTL* tree checking is in `NC` exactly when `P ⊆ NC`. Since `NC` is
widely believed to be a proper subset of `P`, and the question whether `P ⊆ NC` is out of
scope for this project, no `NC` conjecture for CTL* tree checking is stated.

"Proved" means proved without `sorry`, using only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The only `sorry`s in the project are the two statements marked "stated, not
proved" above.

## Modelling choices

* Paths are lasso paths `u · v^ω`. A finite tree becomes a Kripke structure by letting every
  leaf loop to itself. A CTL* formula holds on a tree if it holds on every path from the root.
* Instances are encoded as binary words, using a 5-bit token encoding.
* In `AC^k[𝒞]` an oracle gate counts as one level of depth. Circuit families are logspace
  uniform.
* The Chakraborty–Datta theorem is stated as a promise problem. Some language in `LogDCFL`
  agrees with the circuit value on all encodings of one-input-face monotone planar circuits.
  The Barrington–Lu–Miltersen–Skyum theorem is stated in the same way for stratified monotone
  planar circuits in the standard layered form of [BLMS99, Section 2].

[KF09] and [KF12] treat finite paths. The project uses lasso paths, the setting of
[Kuh10, Corollary 4]. See [`docs/DESIGN_NOTES.md`](docs/DESIGN_NOTES.md) for all known
modelling differences from the cited works.

## Layout

```
RequestProject/
  Statements.lean   main results (start here)
  Encoding.lean     tokens and binary encodings of instances
  Complexity.lean   machine models and complexity classes
  Logics.lean       LTL, BLTL+Past, CTL, CTL* and their checking problems
  BLMS/             stratified monotone planar circuit value is in LogDCFL (pushdown algorithm of [BLMS99, Section 5])
  LTLPath/          Theorem 1a: LTL path checking as a round algorithm with one-input-face or stratified circuit queries
  ACRound/          round algorithms (logspace work + rounds of parallel oracle queries) and their simulation by AC circuits
  PHard/            MCVP is P-hard (tableau construction)
  MCVP/             MCVP logspace-reduces to CTL* tree checking (Theorem 2)
  CTLStarP/         decision procedure for CTL* tree checking (Theorem 3)
  Fork/             reduction to single-fork trees (Theorem 4)
  CTLTree/          Theorem 1b: CTL tree checking as a round algorithm with LTL path checking queries
  Shallow/          shallow branching: reduction to LTL path checking and its logspace implementation (Theorem 5)
  Logspace/         logspace transducers, register programs, composition of logspace functions
  LogLang/          a loop language compiled to logspace transducers
  PTime/            structured programs compiled to polynomial-time Turing machines
docs/
  LTL_PATH_CHECKING.md   design of the proof of Theorem 1a
  CTL_TREE_CHECKING.md   design of the proof of Theorem 1b
  CTLSTAR_PHARDNESS.md   Theorems 2–4: constructions and proofs
  SHALLOW_BRANCHING.md   Theorem 5: the reduction and its complexity
  DESIGN_NOTES.md        why the foundations are project-local, and modelling conventions
papers/                  the papers cited for Theorems 1a–1c and for the Chakraborty–Datta theorem
REFERENCES.md            bibliography (citation keys such as [KF12] used throughout the project)
```

## Building

```
lake exe cache get
lake build
```

The project uses Lean 4.28.0 and Mathlib `v4.28.0`, as pinned in `lean-toolchain` and
`lake-manifest.json`.

## References

Citations such as [KF12, Theorem 1] refer to the bibliography in [`REFERENCES.md`](REFERENCES.md),
a single alphabetical list.

---

This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```
