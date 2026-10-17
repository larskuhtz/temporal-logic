# References

This is the bibliography of the project, as a single list sorted alphabetically by citation
key. The Lean sources, the documentation in `docs/` and `README.md` cite these works by key at
the place where a result is used, e.g. `[KF12, Theorem 3]`. Each entry ends with the places
where it is cited.

**How the entries were checked.** The papers in `papers/` were used as the primary source:
`papers/2009-ltl-path-checking-is-efficiently-parallelizable.pdf` is [KF09],
`papers/1210.0574.pdf` is [KF12], `papers/kuhtz-thesis.pdf` is [Kuh10], `papers/TR06-130.pdf`
is the ECCC report version of [CD06], and `papers/on-monotone-planar-circuits.pdf` is [BLMS99].
Theorem, section and chapter numbers attributed to these five works were looked up in the
papers themselves. The **Checked** line of each entry says where its bibliographic data was
confirmed; for example "[KF12] ref. 6" means entry 6 of the reference list of [KF12]. Entries
marked **not checked** do not appear in the reference lists of the provided papers; their data
is given from memory and should be verified before reuse.

* **[AB09]** S. Arora and B. Barak. *Computational Complexity: A Modern Approach.* Cambridge
  University Press, 2009.
  Space complexity, logspace reductions and configuration counting are in Chapter 4.
  Cited in: `RequestProject/Complexity.lean`, `RequestProject/Logspace/Compose.lean`,
  `RequestProject/Logspace/OutBound.lean`, `docs/CTLSTAR_PHARDNESS.md`.
  **Not checked.**

* **[ADKP89]** K. Abrahamson, N. Dadoun, D. G. Kirkpatrick and T. Przytycka. *A simple parallel
  tree contraction algorithm.* Journal of Algorithms 10(2):287–302, 1989.
  The parallel tree contraction that [KF12, Section 2.3] follows.
  Cited in: `RequestProject/Statements.lean`, `docs/LTL_PATH_CHECKING.md`.
  Checked: [KF12] ref. 1; [Kuh10] ref. 1.

* **[BLMS99]** D. A. Mix Barrington, C.-J. Lu, P. B. Miltersen and S. Skyum. *On monotone planar
  circuits.* In Proc. 14th Annual IEEE Conference on Computational Complexity (COCO 1999),
  pages 24–31. IEEE Computer Society, 1999.
  Theorem 2: the circuit value problem for stratified monotone planar circuits is in `LogDCFL`.
  The standard layered form of the circuits is in Section 2, Propositions 8 and 9 in Section 3,
  and the pushdown algorithm in Section 5. [Kuh10, Theorem 1] restates Theorem 2. In this
  project Theorem 2 is the statement `StratMCVP_in_LogDCFL`, proved as `StratMCVP_mem_LogDCFL`.
  Cited in: `README.md`, `RequestProject/Statements.lean`, `RequestProject/LTLPath/Strat.lean`,
  `RequestProject/BLMS/`, `docs/LTL_PATH_CHECKING.md`, `docs/CTL_TREE_CHECKING.md`.
  Checked: the provided PDF (title, authors, Theorem 2, sections, propositions); [KF12] ref. 4;
  [Kuh10] ref. 8; [KF09] ref. 3.

* **[Bus87]** S. Buss. *The Boolean formula value problem is in ALOGTIME.* In Proc. 19th Annual
  ACM Symposium on Theory of Computing (STOC 1987), pages 123–131. ACM, 1987.
  Boolean formula evaluation is in (and complete for) `NC¹`.
  Cited in: `RequestProject/Logics.lean`.
  Checked: [Kuh10] ref. 16.

* **[CD06]** T. Chakraborty and S. Datta. *One-input-face MPCVP is hard for L, but in
  LogDCFL.* In Proc. FSTTCS 2006, volume 4337 of LNCS, pages 57–68. Springer, 2006. Also
  Electronic Colloquium on Computational Complexity (ECCC), Report No. 130, 2006.
  Theorem 1 of the ECCC report: the one-input-face monotone planar circuit value problem is in
  `LogDCFL`. It is restated as [KF09, Theorem 1], [KF12, Theorem 3.1] and [Kuh10, Theorem 2]. In
  this project it is the statement `OIFMCVP_in_LogDCFL`, which is stated but not proved
  (`OIFMCVP_mem_LogDCFL`).
  Cited in: `README.md`, `RequestProject/Statements.lean`, `RequestProject/LTLPath/OIF.lean`,
  `docs/LTL_PATH_CHECKING.md`, `docs/CTL_TREE_CHECKING.md`, `docs/SHALLOW_BRANCHING.md`,
  `docs/CTLSTAR_PHARDNESS.md`.
  Checked: [KF12] ref. 6; [Kuh10] ref. 17; [KF09] ref. 5; the ECCC report itself.

* **[CES86]** E. M. Clarke, E. A. Emerson and A. P. Sistla. *Automatic verification of
  finite-state concurrent systems using temporal logic specifications.* ACM Transactions on
  Programming Languages and Systems 8(2):244–263, 1986.
  CTL model checking.
  Cited in: `RequestProject/Logics.lean`.
  Checked: [Kuh10] ref. 18.

* **[Coo85]** S. A. Cook. *A taxonomy of problems with fast parallel algorithms.* Information
  and Control 64(1–3):2–22, 1985.
  `NC`, `AC^k` and circuits with oracle gates.
  Cited in: `RequestProject/Complexity.lean`.
  **Not checked.**

* **[DS02]** S. Demri and Ph. Schnoebelen. *The complexity of propositional linear temporal
  logics in simple cases.* Information and Computation 174(1):84–103, 2002.
  [KF09], [KF12] and [Kuh10] cite it for the `NC¹` lower bound for LTL path checking.
  Cited in: `RequestProject/Logics.lean`.
  Checked: [KF12] ref. 9; [Kuh10] ref. 23.

* **[EC82]** E. A. Emerson and E. M. Clarke. *Using branching time temporal logic to synthesize
  synchronization skeletons.* Science of Computer Programming 2(3):241–266, 1982.
  CTL.
  Cited in: `RequestProject/Logics.lean`.
  Checked: [Kuh10] ref. 25.

* **[EH86]** E. A. Emerson and J. Y. Halpern. *"Sometimes" and "not never" revisited: on
  branching versus linear time temporal logic.* Journal of the ACM 33(1):151–178, 1986.
  CTL*.
  Cited in: `RequestProject/Statements.lean`, `RequestProject/Logics.lean`,
  `RequestProject/MCVP/Construction.lean`, `RequestProject/Fork/Construction.lean`.
  **Not checked.**

* **[GHR95]** R. Greenlaw, H. J. Hoover and W. L. Ruzzo. *Limits to Parallel Computation:
  P-Completeness Theory.* Oxford University Press, 1995.
  P-completeness, in particular of the (monotone) circuit value problem.
  Cited in: `RequestProject/Statements.lean`, `RequestProject/PHard/Main.lean`,
  `RequestProject/PHard/Tableau.lean`, `docs/CTLSTAR_PHARDNESS.md`.
  Checked: [Kuh10] ref. 39.

* **[Gol77]** L. M. Goldschlager. *The monotone and planar circuit value problems are log space
  complete for P.* SIGACT News 9(2):25–29, 1977.
  The monotone circuit value problem (MCVP) and the planar circuit value problem are
  P-complete.
  Cited in: `RequestProject/Statements.lean`, `RequestProject/PHard/`, `RequestProject/MCVP/`,
  `RequestProject/Fork/Construction.lean`, `docs/CTLSTAR_PHARDNESS.md`.
  Checked: [Kuh10] ref. 34; [CD06] ref. 9.

* **[Joh90]** D. S. Johnson. *A catalog of complexity classes.* In Handbook of Theoretical
  Computer Science, Volume A, pages 67–161. MIT Press, 1990.
  [KF12, Section 2] cites it for the complexity classes, `logDCFL` among them.
  Cited in: `RequestProject/Complexity.lean`.
  Checked: [KF12] ref. 17; [Kuh10] ref. 49.

* **[Jon75]** N. D. Jones. *Space-bounded reducibility among combinatorial problems.* Journal
  of Computer and System Sciences 11(1):68–85, 1975.
  Logspace reductions, and that logspace computable functions compose.
  Cited in: `RequestProject/Complexity.lean`, `RequestProject/Logspace/Compose.lean`,
  `RequestProject/MCVP/Main.lean`, `docs/CTLSTAR_PHARDNESS.md`.
  **Not checked.**

* **[KF09]** L. Kuhtz and B. Finkbeiner. *LTL path checking is efficiently parallelizable.* In
  Proc. ICALP 2009, volume 5556 of LNCS, pages 235–246. Springer, 2009.
  Theorem 2: LTL path checking (finite paths) is in `AC¹(logDCFL)`. Theorem 1 restates [CD06].
  Cited in: `README.md`, `RequestProject/Statements.lean`, `RequestProject/Logics.lean`,
  `RequestProject/LTLPath/OIF.lean`, `RequestProject/Shallow/Reduction.lean`,
  `docs/LTL_PATH_CHECKING.md`, `docs/CTLSTAR_PHARDNESS.md`, `docs/DESIGN_NOTES.md`.
  Checked: title page of the paper; [KF12] ref. 22; [Kuh10] ref. 58.

* **[KF12]** L. Kuhtz and B. Finkbeiner. *Efficient parallel path checking for linear-time
  temporal logic with past and bounds.* Logical Methods in Computer Science 8(4:10):1–24, 2012.
  DOI `10.2168/LMCS-8(4:10)2012`.
  Journal version of [KF09]. Theorem 1: LTL, Theorem 2: LTL+Past, Theorem 3: BLTL+Past path
  checking are in `AC¹(logDCFL)` (finite paths). Section 2 fixes the complexity classes,
  Section 2.3 the parallel tree contraction, and Sections 3–5 contain the algorithm. Theorem 3.1
  restates [CD06], and Corollary 3.2 extends it to circuits with variable gates.
  Cited in: `README.md`, `RequestProject/Statements.lean`, `RequestProject/Complexity.lean`,
  `RequestProject/Logics.lean`, `RequestProject/LTLPath/OIF.lean`,
  `RequestProject/Shallow/Reduction.lean`, `docs/LTL_PATH_CHECKING.md`,
  `docs/SHALLOW_BRANCHING.md`, `docs/CTLSTAR_PHARDNESS.md`, `docs/DESIGN_NOTES.md`.
  Checked: title page of the paper.

* **[Kuh10]** L. Kuhtz. *Model Checking Finite Paths and Trees.* PhD thesis, Universität des
  Saarlandes, Saarbrücken, 2010.
  Theorem 1 restates [BLMS99, Theorem 2], Theorem 2 restates [CD06], and Corollary 1 extends it
  to circuits with variable gates. Theorem 6: `MC[LTL, path]` (finite paths) is in
  `AC¹(logDCFL)`. Corollary 4: `MC[LTL, ultimately periodic path]` is in `AC¹(logDCFL)`.
  Theorem 10 (Section 5.2): `MC[CTL, T]` for finite trees `T` is in `AC²(logDCFL)`; Lemma 12 is
  the reduction to binary trees used in its proof. Theorem 11: LTL+Past. Theorem 13:
  `MC[BLTL+Past, paths]` is in `AC¹(logDCFL)`. Chapter 7 asks for the complexity of CTL* tree
  checking as an open question.
  Cited in: `README.md`, `RequestProject/Statements.lean`, `RequestProject/Logics.lean`,
  `RequestProject/LTLPath/OIF.lean`, `RequestProject/LTLPath/Strat.lean`,
  `RequestProject/CTLTree/Main.lean`, `RequestProject/Shallow/Reduction.lean`,
  `docs/CTL_TREE_CHECKING.md`, `docs/SHALLOW_BRANCHING.md`, `docs/CTLSTAR_PHARDNESS.md`,
  `docs/DESIGN_NOTES.md`.
  Checked: title page of the thesis; [KF12] ref. 21.

* **[Lad75]** R. E. Ladner. *The circuit value problem is log space complete for P.* SIGACT
  News 7(1):18–20, 1975.
  The circuit value problem is P-complete, via the tableau circuit of a polynomial-time
  machine. This is the construction used in `RequestProject/PHard/`.
  Cited in: `RequestProject/Statements.lean`, `RequestProject/PHard/`, `RequestProject/MCVP/`,
  `RequestProject/Fork/Construction.lean`, `docs/CTLSTAR_PHARDNESS.md`.
  Checked: [Kuh10] ref. 61; [CD06] ref. 12.

* **[LPZ85]** O. Lichtenstein, A. Pnueli and L. Zuck. *The glory of the past.* In Proc.
  Conference on Logic of Programs, pages 196–218. Springer, 1985.
  Past-time operators.
  Cited in: `RequestProject/Logics.lean`.
  Checked: [KF12] ref. 24; [Kuh10] ref. 66; [KF09] ref. 16.

* **[MS03]** N. Markey and Ph. Schnoebelen. *Model checking a path (preliminary report).* In
  Proc. CONCUR 2003, volume 2761 of LNCS, pages 251–265. Springer, 2003.
  Introduces path checking for LTL and its extensions.
  Cited in: `RequestProject/Logics.lean`.
  Checked: [KF12] ref. 26; [Kuh10] ref. 71.

* **[Pap94]** C. H. Papadimitriou. *Computational Complexity.* Addison-Wesley, 1994.
  Logspace reductions and their composition, and P-completeness of the circuit value problem
  (Chapter 8).
  Cited in: `RequestProject/Complexity.lean`, `RequestProject/Logspace/Compose.lean`,
  `docs/CTLSTAR_PHARDNESS.md`.
  Checked: [Kuh10] ref. 75.

* **[Pnu77]** A. Pnueli. *The temporal logic of programs.* In Proc. 18th Annual IEEE Symposium
  on Foundations of Computer Science (FOCS 1977), pages 46–57, 1977.
  LTL.
  Cited in: `RequestProject/Logics.lean`.
  Checked: [Kuh10] ref. 78.

* **[Ruz81]** W. L. Ruzzo. *On uniform circuit complexity.* Journal of Computer and System
  Sciences 22(3):365–383, 1981.
  Uniform circuit families.
  Cited in: `RequestProject/Complexity.lean`.
  **Not checked.**

* **[Sud78]** I. H. Sudborough. *On the tape complexity of deterministic context-free
  languages.* Journal of the ACM 25(3):405–414, 1978.
  The class `LogDCFL`.
  Cited in: `RequestProject/Complexity.lean`.
  **Not checked.**

* **[Vol99]** H. Vollmer. *Introduction to Circuit Complexity: A Uniform Approach.* Springer,
  1999.
  Uniform circuit classes `NC^k`, `AC^k`, and `AC¹` reductions with oracle gates.
  Cited in: `RequestProject/Complexity.lean`.
  Checked: [KF12] ref. 29; [Kuh10] ref. 87.
