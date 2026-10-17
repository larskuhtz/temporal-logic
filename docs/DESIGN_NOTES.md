# Design notes: CSLib vs. project-local foundations

## Decision

The project keeps its own self-contained foundations (`RequestProject/Encoding.lean`,
`RequestProject/Complexity.lean`, `RequestProject/Logics.lean`) on top of Mathlib only.
It does **not** depend on CSLib for now.

## Reasons

1. **Not checked against CSLib's current sources.** CSLib could not be fetched from the
   environment this project was built in, so its current contents and its Lean/Mathlib
   pin could not be inspected. This project is pinned to Lean 4.28.0 and Mathlib
   `v4.28.0`. Adding CSLib means picking a CSLib revision built for exactly the same
   toolchain and Mathlib, and that compatibility could not be confirmed here.

2. **The statements need models that are specific to this project.** To state the theorems
   and conjectures, `Complexity.lean` needs:
   - *logspace* transducers: Turing machines with a read-only two-way input tape, a
     space-bounded work tape and a write-only output tape. Logspace many-one reductions
     and `P`-hardness are defined from these;
   - deterministic pushdown automata, `DCFL` and `LogDCFL`;
   - Boolean circuits with unbounded fan-in and oracle gates, depth and size measures, and
     logspace uniformity, which give `AC^k[𝒞]`, `NC^k` and `NC`.

   As far as the author knows, CSLib's computability library is aimed at automata on
   finite and infinite words, transition systems and (single-tape) Turing machines with
   polynomial-time notions. That is not enough to express logspace with a read-only input
   tape, uniform circuit classes with oracles, or DPDAs. **This was not checked against
   current CSLib.** If CSLib now has these notions, see the migration path below.

3. **Fit with the proofs.** The proofs build logspace-uniform circuit families with oracle
   gates (`RequestProject/ACRound/`), logspace transducers (`RequestProject/Logspace/`,
   `RequestProject/LogLang/`) and polynomial-time machines (`RequestProject/PTime/`). They
   work directly with the concrete gate-list representation `Circuit := List Gate` and its
   `eval`/`depth`/`size`, and with the project's Turing machine model. A general-purpose
   library model would add a layer of translation without helping with these steps.

## Migration path (if CSLib is adopted later)

The definitions that a library could replace all sit in one file,
`RequestProject/Complexity.lean` (`TM`, `LogspaceComputable`, `PolytimeComputable`,
`ClassL`, `ClassP`, `LogspaceReducible`, `PHard`, `DPDA`, `DCFL`, `LogDCFL`, `Circuit`,
`ACOracle`, `NCk`, `NC`). The logics and problem languages (`Logics.lean`) and the
statements (`RequestProject/Statements.lean`) only use these names. To switch to CSLib:

1. add CSLib as a `[[require]]` in `lakefile.toml`, at a revision that matches the project's
   Lean/Mathlib versions;
2. for each concept CSLib provides, prove that it is equivalent to the local definition,
   e.g. `PolytimeComputable f ↔ Cslib…PolyTimeComputable f`, adjusting the alphabet if
   needed;
3. then either restate `RequestProject/Statements.lean` with CSLib's notions, or keep the local ones and
   export the equivalences.

That way any proofs already written against the local definitions remain valid.

## Modelling conventions to keep in mind for the proofs

The modelling conventions are:
- languages are over `Bool`; instances use a fixed 5-bit token encoding;
- in `AC^k[𝒞]`, an oracle gate counts as one level of depth;
- circuit families are logspace-uniform;
- paths are ultimately periodic (`stem · loop^ω`);
- trees are finite, and every leaf loops to itself;
- a CTL* formula holds on a tree if it holds on every path from the root.

## Differences from the cited works

The formal statements use this project's own definitions: binary encodings, the Turing machine
model, logspace-uniform circuits, finite trees whose leaves loop to themselves, and lasso
paths. They have not been compared with the cited works in every detail. Known differences
(citation keys refer to `REFERENCES.md`):

* [KF09], [KF12] and [Kuh10, Theorem 6] treat **finite** paths. The project's
  `LTLPathChecking` uses **ultimately periodic** (lasso) paths, matching [Kuh10, Corollary 4].
  `BLTLPastPathChecking` also uses lasso paths, while [KF12, Theorem 3] and
  [Kuh10, Theorem 13] are stated for finite paths.
* Theorem 1c is stated with the weaker bound `NC`, as in the original task. The cited works
  give `AC¹(logDCFL) ⊆ NC`.
* Theorem 1b is proved by a round algorithm that reduces CTL tree checking to LTL path
  checking. [Kuh10, Theorem 10] obtains the same bound by contracting the computation tree
  directly (see `docs/CTL_TREE_CHECKING.md`).
