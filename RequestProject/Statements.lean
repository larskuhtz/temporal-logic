module

public import RequestProject.Complexity
public import RequestProject.Logics
public import RequestProject.LTLPath.Main
public import RequestProject.LTLPath.MainStrat
public import RequestProject.PHard.Main
public import RequestProject.MCVP.Main
public import RequestProject.CTLStarP.Main
public import RequestProject.Fork.Main
public import RequestProject.Shallow.Main
public import RequestProject.CTLTree.Main
public import RequestProject.BLMS.Main

/-!
# Main results

This file collects the top-level results of the project. The problems are defined in
`RequestProject/Logics.lean`, the complexity classes in `RequestProject/Complexity.lean`, and
the encodings of instances as binary words in `RequestProject/Encoding.lean`. Each statement
below is a short wrapper around the theorem that proves it, and the docstring says where that
theorem lives.

## Part 1: path and tree checking in `NC`

* `OIFMCVP_mem_LogDCFL`: the one-input-face monotone planar circuit value problem is in `LogDCFL`
  (Chakraborty–Datta). **Stated, not proved.**
* `StratMCVP_mem_LogDCFL`: the stratified monotone planar circuit value problem is in `LogDCFL`
  (Barrington–Lu–Miltersen–Skyum). **Proved** (`RequestProject/BLMS/`).
* **Theorem 1a** `LTLPathChecking_mem_AC1_LogDCFL_of_OIF`: if the Chakraborty–Datta theorem holds,
  then LTL path checking is in `AC¹[LogDCFL]`. **Proved.** This is the result of [KF09].
  `LTLPathChecking_mem_AC1_LogDCFL_of_strat`: if the Barrington–Lu–Miltersen–Skyum theorem
  holds, then LTL path checking is in `AC¹[LogDCFL]`; the query circuits are built directly as
  stratified circuits. **Proved.**
  `LTLPathChecking_mem_AC1_LogDCFL` is the unconditional form. It is derived from
  `LTLPathChecking_mem_AC1_LogDCFL_of_strat` and `StratMCVP_mem_LogDCFL`. **Proved.**
* **Theorem 1b** `CTLTreeChecking_mem_AC2_LogDCFL_of_OIF`: if the Chakraborty–Datta theorem
  holds, then CTL tree checking is in `AC²[LogDCFL]`. **Proved**, via the round algorithm
  `CTLTreeChecking_roundDecidable` (`⌊log₂ n⌋ + 1` rounds of parallel LTL path checking queries).
  `CTLTreeChecking_mem_AC2_LogDCFL` is the unconditional form; it is derived from the round
  algorithm and the unconditional Theorem 1a. **Proved.**
* **Theorem 1c** `BLTLPastPathChecking_mem_NC`: BLTL+Past path checking is in `NC`.
  **Stated, not proved.**

## Part 2: CTL* tree checking

* **Theorem 2** `CTLStarTreeChecking_PHard`: CTL* tree checking is `P`-hard. **Proved.**
  This was conjecture 2b of the original task.
* **Theorem 3** `CTLStarTreeChecking_mem_P`, `CTLStarTreeChecking_PComplete`: CTL* tree checking
  is in `P`, and hence `P`-complete. **Proved.**
* **Theorem 4** `CTLStarSingleForkTreeChecking_PHard`: CTL* tree checking stays `P`-hard on
  *single-fork trees*, i.e. paths with one extra leaf at the end. **Proved.**
* **Theorem 5** covers trees whose branching nodes all lie at depth `< (⌊log₂ n⌋ + 1)^k`
  (`CTLStarShallowTreeChecking k`). **Proved.**
  * 5a `CTLStarShallowTreeChecking_roundDecidable`: this restricted problem is decided by a
    logspace algorithm with `O(log^k n)` rounds of parallel queries to LTL path checking.
  * 5b `CTLStarShallowTreeChecking_mem_AC_LogDCFL`: if the Chakraborty–Datta theorem holds, the
    restricted problem is in `AC^{k+1}[LogDCFL]`.

## How the proofs are organised

* Theorem 1a: `RequestProject/LTLPath/`, using the generic results on round algorithms in
  `RequestProject/ACRound/`.
* Theorem 1b: `RequestProject/CTLTree/`, reducing to Theorem 1a.
* Theorem 2: `RequestProject/PHard/` proves that MCVP is `P`-hard.
  `RequestProject/MCVP/` gives a logspace reduction from MCVP to CTL* tree checking.
* Theorem 3: `RequestProject/CTLStarP/`, compiled to Turing machines by `RequestProject/PTime/`.
* Theorem 4: `RequestProject/Fork/`.
* Theorem 5: `RequestProject/Shallow/`. The underlying reduction to LTL path checking is
  `Shallow.treeSat_iff_vals` in `RequestProject/Shallow/Reduction.lean`.
* Shared machinery: logspace transducers and their composition (`RequestProject/Logspace/`), a
  loop language that compiles to logspace transducers (`RequestProject/LogLang/`), and
  polynomial-time programs (`RequestProject/PTime/`).

## References

The keys refer to `REFERENCES.md`.

* Theorem 1a: Kuhtz–Finkbeiner [KF09, Theorem 1] and [KF12, Theorem 1] prove this for finite
  paths. [Kuh10, Corollary 4] proves it for ultimately periodic paths, which is the setting
  used here. The `LogDCFL` bound for one-input-face circuits is [CD06, Theorem 1], used as
  [KF12, Theorem 3.1]. The `LogDCFL` bound for stratified circuits is [BLMS, Theorem 2].
* Theorem 1b: [Kuh10, Theorem 10].
* Theorem 1c: [KF12, Theorem 3] and [Kuh10, Theorem 13] (BLTL+Past path checking is in
  `AC¹(logDCFL) ⊆ NC`, for finite paths).
* P-hardness of MCVP, used for Theorems 2 and 4: [Lad75], [Gol77]; see also [GHR95].
* Theorems 2–5: we know of no published source for these and have not searched the
  literature for one. [Kuh10, Chapter 7] lists the complexity of CTL* tree checking as an open
  question.

The statements use this project's own definitions: binary encodings, the Turing machine
model, logspace uniformity, finite trees whose leaves loop to themselves, and lasso paths. We
have not checked that these agree in every detail with the cited works. In particular, [KF12]
works with finite paths, while `LTLPathChecking` and `BLTLPastPathChecking` use ultimately
periodic (lasso) paths.
-/

@[expose] public section

namespace PathChecking

/-! ## Part 1: path and tree checking in `NC` -/

/-- **Chakraborty–Datta theorem** [CD06, Theorem 1]: the one-input-face monotone planar circuit
value problem is in `LogDCFL`. It is stated as a promise problem in `OIFMCVP_in_LogDCFL`
(`RequestProject/LTLPath/OIF.lean`).

Stated, not proved. It is used only by the conditional forms `..._of_OIF`, which represent the
original result of Kuhtz–Finkbeiner [KF09]; the unconditional Theorem 1a uses the
Barrington–Lu–Miltersen–Skyum theorem `StratMCVP_mem_LogDCFL` instead. -/
theorem OIFMCVP_mem_LogDCFL : OIFMCVP_in_LogDCFL := by
  sorry

/-- **Theorem 1a (conditional form).** If the one-input-face monotone planar circuit value
problem is in `LogDCFL` (Chakraborty–Datta), then LTL path checking over ultimately periodic
paths is in `AC¹[LogDCFL]`.

Proof: `ltl_roundDecidable` (`RequestProject/LTLPath/Main.lean`) shows that LTL path checking
is decided by a logspace algorithm with `O(log n)` rounds of parallel queries to one-input-face
circuit instances. `RoundDecidable.mem_ACOracle_of_LogDCFL` (`RequestProject/ACRound/Main.lean`)
turns this into an `AC¹[LogDCFL]` circuit family.

Reference: [KF09, Theorem 1], [KF12, Theorem 1] for finite paths; [Kuh10, Corollary 4] for
ultimately periodic paths. -/
theorem LTLPathChecking_mem_AC1_LogDCFL_of_OIF (h : OIFMCVP_in_LogDCFL) :
    LTLPathChecking ∈ ACOracle 1 LogDCFL := by
  obtain ⟨B, hB, hBC⟩ := h
  exact (ltl_roundDecidable B hBC).mem_ACOracle_of_LogDCFL hB

/-- **Barrington–Lu–Miltersen–Skyum theorem** [BLMS, Theorem 2]: the stratified monotone planar
circuit value problem is in `LogDCFL`. The algorithm is described in [BLMS, Section 5]. It is
stated as a promise problem in `StratMCVP_in_LogDCFL` (`RequestProject/LTLPath/Strat.lean`).

Proof: `BLMS.stratMCVP_in_LogDCFL` (`RequestProject/BLMS/Main.lean`). A logspace computable map
sends the encoding of a circuit to the initial configuration of the pushdown algorithm of
[BLMS, Section 5] followed by enough copies of the table of its moves, and a fixed
deterministic pushdown automaton accepts this word iff the circuit evaluates to `true`. -/
theorem StratMCVP_mem_LogDCFL : StratMCVP_in_LogDCFL :=
  BLMS.stratMCVP_in_LogDCFL

/-- **Theorem 1a (conditional form, stratified circuits).** If the stratified monotone planar
circuit value problem is in `LogDCFL` (Barrington–Lu–Miltersen–Skyum), then LTL path checking
over ultimately periodic paths is in `AC¹[LogDCFL]`.

Proof: `ltl_roundDecidable_strat` (`RequestProject/LTLPath/MainStrat.lean`) shows that LTL path
checking is decided by a logspace algorithm with `O(log n)` rounds of parallel queries to
stratified monotone planar circuit instances. The algorithm is the one of
`LTLPathChecking_mem_AC1_LogDCFL_of_OIF`, except that every query circuit is drawn directly as a
stratified circuit. `RoundDecidable.mem_ACOracle_of_LogDCFL` turns this into an
`AC¹[LogDCFL]` circuit family. -/
theorem LTLPathChecking_mem_AC1_LogDCFL_of_strat (h : StratMCVP_in_LogDCFL) :
    LTLPathChecking ∈ ACOracle 1 LogDCFL := by
  obtain ⟨B, hB, hBC⟩ := h
  exact (ltl_roundDecidable_strat B hBC).mem_ACOracle_of_LogDCFL hB

/-- **Theorem 1a.** The path checking problem for LTL over ultimately periodic paths is in
`AC¹[LogDCFL]`.

This follows from the conditional form `LTLPathChecking_mem_AC1_LogDCFL_of_strat` and the
Barrington–Lu–Miltersen–Skyum theorem `StratMCVP_mem_LogDCFL`. -/
theorem LTLPathChecking_mem_AC1_LogDCFL : LTLPathChecking ∈ ACOracle 1 LogDCFL :=
  LTLPathChecking_mem_AC1_LogDCFL_of_strat StratMCVP_mem_LogDCFL

/-- **Theorem 1b (round algorithm).** CTL tree checking over finite trees is decided by a
logspace algorithm with `⌊log₂ n⌋ + 1` rounds of polynomially many parallel queries to LTL path
checking.

Proof: `RequestProject/CTLTree/`. In every round one LTL query is asked for every node `u` and
every subformula, on the *chain* of `u` (the path through the kids of at least half the size of
`u`); the values of `EX`, `EU` and `AU` subformulas through the other kids are read from the
answers of the previous round, so after `r` rounds the answers are correct for all nodes of
size `< 2^r`. -/
theorem CTLTreeChecking_roundDecidable : RoundDecidable CTLTreeChecking LTLPathChecking 1 :=
  CTLT.roundDecidable

/-- **Theorem 1b (conditional form).** If the one-input-face monotone planar circuit value
problem is in `LogDCFL` (Chakraborty–Datta), then the tree checking problem for CTL over finite
trees is in `AC²[LogDCFL]`.

Proof: combine the round algorithm `CTLTreeChecking_roundDecidable` with Theorem 1a
(conditional form) using `RoundDecidable.mem_ACOracle_LogDCFL`.
Reference: [Kuh10, Theorem 10]. -/
theorem CTLTreeChecking_mem_AC2_LogDCFL_of_OIF (h : OIFMCVP_in_LogDCFL) :
    CTLTreeChecking ∈ ACOracle 2 LogDCFL :=
  CTLTreeChecking_roundDecidable.mem_ACOracle_LogDCFL (LTLPathChecking_mem_AC1_LogDCFL_of_OIF h)

/-- **Theorem 1b.** The tree checking problem for CTL over finite trees is in `AC²[LogDCFL]`.

This follows from the round algorithm `CTLTreeChecking_roundDecidable` and Theorem 1a
(`LTLPathChecking_mem_AC1_LogDCFL`, which rests on the Barrington–Lu–Miltersen–Skyum theorem
`StratMCVP_mem_LogDCFL`). Reference: [Kuh10, Theorem 10]. -/
theorem CTLTreeChecking_mem_AC2_LogDCFL : CTLTreeChecking ∈ ACOracle 2 LogDCFL :=
  CTLTreeChecking_roundDecidable.mem_ACOracle_LogDCFL LTLPathChecking_mem_AC1_LogDCFL

/-- **Theorem 1c.** The path checking problem for BLTL+Past over ultimately periodic paths is in
`NC`. BLTL+Past is LTL with past operators and bounded operators with binary bounds.

Stated, not proved. Reference: [KF12, Theorem 3] and [Kuh10, Theorem 13] prove the stronger
bound `AC¹(logDCFL)` for finite paths. -/
theorem BLTLPastPathChecking_mem_NC : BLTLPastPathChecking ∈ NC := by
  sorry

/-! ## Part 2: CTL* tree checking -/

/-- **Theorem 2.** The tree checking problem for CTL* is `P`-hard under logspace many-one
reductions.

Proof: MCVP is `P`-hard (`PHardness.MCVP_PHard`, `RequestProject/PHard/`; [Lad75], [Gol77]).
MCVP logspace-reduces to CTL* tree checking (`MCVPReduction.MCVP_logspaceReducible_CTLStar`,
`RequestProject/MCVP/`). We know of no published source for this theorem. -/
theorem CTLStarTreeChecking_PHard : PHard CTLStarTreeChecking :=
  MCVPReduction.CTLStarTreeChecking_PHard_of_MCVP PHardness.MCVP_PHard

/-- **Theorem 3.** The tree checking problem for CTL* is in `P`.

Proof: `RequestProject/CTLStarP/` gives a structured program with polynomially bounded values,
and `RequestProject/PTime/` compiles it into a polynomial-time Turing machine. Correctness of the program is `CTLP.main_correct`. -/
theorem CTLStarTreeChecking_mem_P : CTLStarTreeChecking ∈ ClassP := by
  show PolytimeComputable (charWord CTLStarTreeChecking)
  refine HL.polytimeComputable_of_hl CTLP.mainP _ CTLP.bound 192 (fun w => ?_)
    (fun w => by unfold CTLP.bound; omega) (fun w => ?_)
  · unfold CTLP.bound
    have h1 : (w.length + 2) ^ 3 ≤ 8 * (w.length + 1) ^ 3 := by
      have : w.length + 2 ≤ 2 * (w.length + 1) := by omega
      calc (w.length + 2) ^ 3 ≤ (2 * (w.length + 1)) ^ 3 := Nat.pow_le_pow_left this 3
        _ = 8 * (w.length + 1) ^ 3 := by ring
    have h2 : (w.length + 1) ^ 3 ≤ (w.length + 1) ^ 192 :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : 1 ≤ (w.length + 1) ^ 192 := Nat.one_le_pow _ _ (by omega)
    omega
  · obtain ⟨τ, hev, hout⟩ := CTLP.main_correct w
    exact ⟨τ, hev, by rw [hout]; rfl⟩

/-- **Theorem 3 (P-completeness).** The tree checking problem for CTL* is `P`-complete: it is in
`P` (Theorem 3) and `P`-hard (Theorem 2). -/
theorem CTLStarTreeChecking_PComplete :
    CTLStarTreeChecking ∈ ClassP ∧ PHard CTLStarTreeChecking :=
  ⟨CTLStarTreeChecking_mem_P, CTLStarTreeChecking_PHard⟩

/-- **Theorem 4.** CTL* tree checking is already `P`-hard when the input tree is a
*single-fork tree*. Such a tree is a path whose last node has exactly two children, both
leaves. It has exactly two leaves, out-degree at most `2`, and a single branching node.

Proof: `RequestProject/Fork/`. -/
theorem CTLStarSingleForkTreeChecking_PHard : PHard CTLStarSingleForkTreeChecking :=
  fun A hA => (PHardness.MCVP_PHard A hA).trans MCVPReduction.MCVP_logspaceReducible_singleFork

/-- **Theorem 5a.** CTL* tree checking on instances of size `n` whose branching nodes all lie at
depth `< (⌊log₂ n⌋ + 1)^k` is decided by a logspace algorithm with `O(log^k n)` rounds of
polynomially many parallel queries to LTL path checking.

Proof: `RequestProject/Shallow/`. The reduction behind it is `Shallow.treeSat_iff_vals`
(`RequestProject/Shallow/Reduction.lean`): on a tree whose branching nodes lie at depth `< d`,
CTL* tree checking is answered by `d + 1` rounds of LTL path-checking queries. -/
theorem CTLStarShallowTreeChecking_roundDecidable (k : ℕ) :
    RoundDecidable (CTLStarShallowTreeChecking k) LTLPathChecking k := by
  obtain ⟨Q, hQ, hQs⟩ := ShallowP.exists_QProg k
  obtain ⟨D, hD, hDs⟩ := ShallowP.exists_DProg k
  exact ShallowP.roundDecidable_of_specs k Q D hQ hD hQs hDs

/-- **Theorem 5b.** If the one-input-face monotone planar circuit value problem is in `LogDCFL`
(Chakraborty–Datta), then CTL* tree checking on instances of size `n` whose branching nodes all
lie at depth `< (⌊log₂ n⌋ + 1)^k` is in `AC^{k+1}[LogDCFL]`.

Proof: combine Theorem 5a with Theorem 1a (conditional form) using
`RoundDecidable.mem_ACOracle_LogDCFL`. -/
theorem CTLStarShallowTreeChecking_mem_AC_LogDCFL (k : ℕ) (h : OIFMCVP_in_LogDCFL) :
    CTLStarShallowTreeChecking k ∈ ACOracle (k + 1) LogDCFL :=
  (CTLStarShallowTreeChecking_roundDecidable k).mem_ACOracle_LogDCFL
    (LTLPathChecking_mem_AC1_LogDCFL_of_OIF h)

end PathChecking


-- Formalization of LTL/CTL/BLTL+Past/CTL* checking complexity statements.
