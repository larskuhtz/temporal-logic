# References

This file lists the literature cited in the Lean sources and in the documentation. Citations in
the code use the keys below, e.g. `[KF12, Theorem 3]`.

## How the entries were checked

The four papers in `papers/` were used as the primary source:

| File | Work |
| --- | --- |
| `papers/2009-ltl-path-checking-is-efficiently-parallelizable.pdf` | [KF09] |
| `papers/1210.0574.pdf` | [KF12] |
| `papers/kuhtz-thesis.pdf` | [Kuh10] |
| `papers/TR06-130.pdf` | [CD06] (ECCC report version) |

Every entry has a **Checked** line saying which of these papers confirms its bibliographic
data. For example, "[KF12] ref. 6" means entry 6 of the reference list of [KF12]. Theorem
numbers attributed to [KF09], [KF12], [Kuh10] and [CD06] were looked up in the papers
themselves. Entries marked **not checked** do not appear in the reference lists of the
provided papers. Their data is given from memory and should be verified before reuse.

## Path checking and tree checking (Theorems 1a–1c)

* **[KF09]** L. Kuhtz and B. Finkbeiner. *LTL Path Checking Is Efficiently Parallelizable.* In
  Proc. ICALP 2009, volume 5556 of LNCS, pages 235–246. Springer, 2009.
  Theorem 1: LTL path checking (finite paths) is in `AC¹(logDCFL)`.
  Checked: title page of the paper; [KF12] ref. 22; [Kuh10] ref. 58.
* **[KF12]** L. Kuhtz and B. Finkbeiner. *Efficient Parallel Path Checking for Linear-Time
  Temporal Logic With Past and Bounds.* Logical Methods in Computer Science 8(4:10), 2012,
  pages 1–24. DOI `10.2168/LMCS-8(4:10)2012`.
  Journal version of [KF09]. Theorem 1: LTL, Theorem 2: LTL+Past, Theorem 3: BLTL+Past path
  checking are in `AC¹(logDCFL)` (finite paths). Theorem 3.1 states the Chakraborty–Datta
  result [CD06], and Corollary 3.2 extends it to circuits with variable gates.
  Checked: title page of the paper.
* **[Kuh10]** L. Kuhtz. *Model Checking Finite Paths and Trees.* PhD thesis, Universität des
  Saarlandes, Saarbrücken, 2010.
  Theorem 6: `MC[LTL, path]`, i.e. finite paths, is in `AC¹(logDCFL)`. Corollary 4:
  `MC[LTL, ultimately periodic path]` is in `AC¹(logDCFL)`. Theorem 10: `MC[CTL, T]` for finite
  trees `T` is in `AC²(logDCFL)`. Theorem 11: LTL+Past. Theorem 13: `MC[BLTL+Past, paths]` is in
  `AC¹(logDCFL)`. Chapter 7 asks for the complexity of CTL* tree checking as an open question.
  Checked: title page of the thesis; [KF12] ref. 21.
* **[CD06]** T. Chakraborty and S. Datta. *One-input-face MPCVP is hard for L, but in
  LogDCFL.* In Proc. FSTTCS 2006, volume 4337 of LNCS, pages 57–68. Springer, 2006. Also
  Electronic Colloquium on Computational Complexity (ECCC), Report No. 130, 2006.
  Theorem 1: one-input-face monotone planar circuit value is in `LogDCFL`. This is used by
  [KF09], [KF12] and [Kuh10], and in this project it is the assumption `OIFMCVP_in_LogDCFL`.
  Checked: [KF12] ref. 6; [Kuh10] ref. 17; [KF09] ref. 5; the ECCC report itself.
* **[BLMS]** D. A. Mix Barrington, C.-J. Lu, P. B. Miltersen and S. Skyum. *On Monotone Planar
  Circuits.* Provided by the user as `papers/on-monotone-planar-circuits.pdf`.
  Theorem 2: the circuit value problem for stratified monotone planar circuits is in `LogDCFL`;
  the algorithm is in Section 5, and the standard layered form of the circuits in Section 2. In
  this project it is the assumption `StratMCVP_in_LogDCFL`.
  Checked: the provided PDF (title, authors, Theorem 2). Venue and year **not checked**.
* **[MS03]** N. Markey and Ph. Schnoebelen. *Model checking a path (preliminary report).* In
  Proc. CONCUR 2003, volume 2761 of LNCS, pages 251–265. Springer, 2003.
  Introduces path checking for LTL and its extensions.
  Checked: [KF12] ref. 26; [Kuh10] ref. 71.
* **[DS02]** S. Demri and Ph. Schnoebelen. *The complexity of propositional linear temporal
  logics in simple cases.* Information and Computation 174(1):84–103, 2002.
  [KF09], [KF12] and [Kuh10] cite it for the `NC¹` lower bound for LTL path checking.
  Checked: [KF12] ref. 9; [Kuh10] ref. 23.
* **[Bus87]** S. Buss. *The Boolean formula value problem is in ALOGTIME.* In Proc. STOC 1987,
  pages 123–131. ACM, 1987.
  Boolean formula evaluation is in (and complete for) `NC¹`.
  Checked: [Kuh10] ref. 16.
* **[ADKP89]** K. Abrahamson, N. Dadoun, D. G. Kirkpatrick and T. Przytycka. *A simple parallel
  tree contraction algorithm.* J. Algorithms 10(2):287–302, 1989.
  The tree contraction schedule followed by the LTL path checking algorithm
  (`docs/LTL_PATH_CHECKING.md`).
  Checked: [KF12] ref. 1; [Kuh10] ref. 1.

## The temporal logics

* **[Pnu77]** A. Pnueli. *The temporal logic of programs.* In Proc. 18th Annual IEEE Symposium
  on Foundations of Computer Science (FOCS 1977), pages 46–57, 1977. LTL.
  Checked: [Kuh10] ref. 78.
* **[LPZ85]** O. Lichtenstein, A. Pnueli and L. Zuck. *The glory of the past.* In Proc.
  Conference on Logic of Programs, pages 196–218. Springer, 1985. Past-time operators.
  Checked: [KF12] ref. 24; [Kuh10] ref. 66; [KF09] ref. 16.
* **[EC82]** E. A. Emerson and E. M. Clarke. *Using branching time temporal logic to synthesize
  synchronization skeletons.* Science of Computer Programming 2(3):241–266, 1982. CTL.
  Checked: [Kuh10] ref. 25.
* **[CES86]** E. M. Clarke, E. A. Emerson and A. P. Sistla. *Automatic verification of
  finite-state concurrent systems using temporal logic specifications.* ACM TOPLAS
  8(2):244–263, 1986. CTL model checking.
  Checked: [Kuh10] ref. 18.
* **[EH86]** E. A. Emerson and J. Y. Halpern. *"Sometimes" and "not never" revisited: on
  branching versus linear time temporal logic.* Journal of the ACM 33(1), 1986. CTL*.
  **Not checked.**

## Complexity classes and machine models

* **[Joh90]** D. S. Johnson. *A catalog of complexity classes.* In Handbook of Theoretical
  Computer Science, Volume A, pages 67–161. MIT Press, 1990. [KF12] cites it for the complexity
  classes, `logDCFL` among them.
  Checked: [KF12] ref. 17; [Kuh10] ref. 49.
* **[Vol99]** H. Vollmer. *Introduction to Circuit Complexity: A Uniform Approach.* Springer,
  1999. Uniform circuit classes `NC^k`, `AC^k`, and `AC¹` reductions with oracle gates.
  Checked: [KF12] ref. 29; [Kuh10] ref. 87.
* **[Pap94]** C. H. Papadimitriou. *Computational Complexity.* Addison-Wesley, 1994. Logspace
  reductions and their composition, and P-completeness of the circuit value problem.
  Checked: [Kuh10] ref. 75.
* **[Jon75]** N. D. Jones. *Space-bounded reducibility among combinatorial problems.* Journal
  of Computer and System Sciences 11(1), 1975. Logspace reductions compose.
  **Not checked.**
* **[Sud78]** I. H. Sudborough. *On the tape complexity of deterministic context-free
  languages.* Journal of the ACM 25(3), 1978. The class `LogDCFL`. **Not checked.**
* **[Ruz81]** W. L. Ruzzo. *On uniform circuit complexity.* Journal of Computer and System
  Sciences 22(3), 1981. Uniform circuit families. **Not checked.**
* **[Coo85]** S. A. Cook. *A taxonomy of problems with fast parallel algorithms.* Information
  and Control 64, 1985. `NC`, `AC^k`, circuits with oracle gates. **Not checked.**
* **[AB09]** S. Arora and B. Barak. *Computational Complexity: A Modern Approach.* Cambridge
  University Press, 2009. Space complexity, configuration counting (Chapter 4).
  **Not checked.**

## P-completeness of the (monotone) circuit value problem

* **[Lad75]** R. E. Ladner. *The circuit value problem is log space complete for P.* SIGACT
  News 7(1):18–20, 1975. CVP is P-complete, via the tableau circuit of a polynomial-time
  machine. This is the construction used in `RequestProject/PHard/`.
  Checked: [Kuh10] ref. 61; [CD06] ref. 12.
* **[Gol77]** L. M. Goldschlager. *The monotone and planar circuit value problems are log space
  complete for P.* SIGACT News 9(2):25–29, 1977. MCVP is P-complete.
  Checked: [Kuh10] ref. 34; [CD06] ref. 9.
* **[GHR95]** R. Greenlaw, H. J. Hoover and W. L. Ruzzo. *Limits to Parallel Computation:
  P-Completeness Theory.* Oxford University Press, 1995.
  Checked: [Kuh10] ref. 39.

## Where each result is cited

| Result | Lean name | Reference |
| --- | --- | --- |
| Chakraborty–Datta theorem (stated, not proved) | `OIFMCVP_mem_LogDCFL` | [CD06, Theorem 1]; [KF12, Theorem 3.1] |
| Theorem 1a, conditional on [CD06] (proved) | `LTLPathChecking_mem_AC1_LogDCFL_of_OIF` | [KF09, Theorem 1], [KF12, Theorem 1]; [Kuh10, Corollary 4] |
| Theorem 1a (follows from the two rows above) | `LTLPathChecking_mem_AC1_LogDCFL` | as above |
| Theorem 1b, conditional on [CD06] (proved) | `CTLTreeChecking_mem_AC2_LogDCFL_of_OIF` | [Kuh10, Theorem 10] |
| Theorem 1b (follows from the CD row and the row above) | `CTLTreeChecking_mem_AC2_LogDCFL` | as above |
| Theorem 1c (stated, not proved) | `BLTLPastPathChecking_mem_NC` | [KF12, Theorem 3]; [Kuh10, Theorem 13] |
| MCVP is P-hard (proved) | `PHardness.MCVP_PHard` | [Lad75], [Gol77], [GHR95] |
| Logspace reductions compose (proved) | `LogspaceComputable.comp`, `LogspaceReducible.trans` | [Jon75], [Pap94], [AB09] |
| Theorems 2–5 on CTL* tree checking (proved) | see `RequestProject/Statements.lean` | no published source known to us; [Kuh10, Chapter 7] poses the question |

## Modelling differences

The formal statements use this project's own definitions: binary encodings, the Turing machine
model, logspace-uniform circuits, finite trees whose leaves loop to themselves, and lasso
paths. They have not been compared with the cited works in every detail. Known differences:

* [KF09], [KF12] and [Kuh10, Theorem 6] treat **finite** paths. The project's
  `LTLPathChecking` uses **ultimately periodic** (lasso) paths, matching [Kuh10, Corollary 4].
  `BLTLPastPathChecking` also uses lasso paths, while [KF12, Theorem 3] and
  [Kuh10, Theorem 13] are stated for finite paths.
* Theorem 1c is stated with the weaker bound `NC`, as in the original task. The cited works
  give `AC¹(logDCFL) ⊆ NC`.
