module

public import RequestProject.LTLPath.OIF

/-!
# Stratified monotone planar circuits

We define the stratified monotone planar circuits of Barrington, Lu, Miltersen and Skyum
[BLMS, Section 2] and state their theorem that the circuit value problem for these circuits is
in `LogDCFL` [BLMS, Theorem 2, Section 5] as the assumption `StratMCVP_in_LogDCFL`.

In [BLMS] a monotone planar circuit in standard (layered) form has nodes `g_i^l` at layers
`l = 0, …, L`, numbered `1 ≤ i ≤ w_l` inside each layer.  A node is an input node, an `AND`/`OR`
gate of fan-in two taking inputs `g_a^{l-1}, g_b^{l-1}` with `a < b` from the previous layer, or a
`COPY` gate taking one input from the previous layer.  Planarity is the condition that wires
between two consecutive layers do not cross: if `j < i` are two nodes of layer `l`, then every
input of `g_j^l` is at most every input of `g_i^l`.  All nodes of layer `0` are input nodes, and
the circuit is *stratified* if all input nodes are in layer `0`.  The output gate is in the last
layer.

A circuit of this project (`Circuit`, a list of gates in topological order whose last gate is the
output) is such a circuit if its gates are listed layer by layer and, inside each layer, in the
order of the layer (`Circuit.StratLayering`).  A `COPY` gate is an `AND` gate with one argument
(`Circuit.MonotoneFanin2`).  Since the gates are listed in the order of the layers, the
numbering inside a layer of [BLMS] is the order of the indices in the list, and the last gate
of the list lies in the last layer.

The assumption is stated as a *promise problem*, exactly as for the one-input-face problem in
`RequestProject/LTLPath/OIF.lean`: some language in `LogDCFL` agrees with the value of the
circuit on all encodings of stratified monotone planar circuits.

## References

* [BLMS] D. A. M. Barrington, C.-J. Lu, P. B. Miltersen, S. Skyum, *On monotone planar
  circuits* (`papers/on-monotone-planar-circuits.pdf`), Theorem 2; the algorithm is in Section 5.
-/

@[expose] public section

namespace PathChecking

/-- `lay` is a layering of the circuit `C` as a stratified monotone planar circuit in standard
form [BLMS, Section 2]:

* the gates are listed layer by layer (`lay` is monotone along the list);
* the input gates are exactly the gates of layer `0`;
* every argument of a gate lies in the previous layer;
* the arguments of a gate are listed in increasing order and are pairwise different (`a < b`);
* wires between two consecutive layers do not cross: if gate `i` comes before gate `i'` in the
  same layer, every argument of `i` is at most every argument of `i'`. -/
structure Circuit.StratLayering (C : Circuit) (lay : ℕ → ℕ) : Prop where
  mono : ∀ i j, i ≤ j → j < C.length → lay i ≤ lay j
  input_iff : ∀ i (h : i < C.length), C[i].IsInput ↔ lay i = 0
  args_prev : ∀ i (h : i < C.length), ∀ j ∈ C[i].args, lay j + 1 = lay i
  args_sorted : ∀ i (h : i < C.length), C[i].args.Pairwise (· < ·)
  planar : ∀ i i' (h : i < C.length) (h' : i' < C.length), i < i' → lay i = lay i' →
    ∀ a ∈ C[i].args, ∀ b ∈ C[i'].args, a ≤ b

/-- A circuit is *stratified planar* if it has a layering as in [BLMS, Section 2]. -/
def Circuit.Stratified (C : Circuit) : Prop := ∃ lay, C.StratLayering lay

/-- Instances of the stratified monotone planar circuit value problem: well-formed circuits
without input bits, monotone of fan-in at most two (`COPY` gates are `AND` gates with one
argument), and stratified planar. -/
def StratMCVPInstance (C : Circuit) : Prop :=
  C.WellFormed 0 ∧ C.MonotoneFanin2 ∧ C.Stratified

/-- **Assumption** (Barrington–Lu–Miltersen–Skyum [BLMS, Theorem 2]): the circuit value
problem for stratified monotone planar circuits is in `LogDCFL`.  Stated as a promise problem:
some language in `LogDCFL` contains the encoding of a stratified monotone planar circuit iff the
circuit evaluates to `true`. -/
def StratMCVP_in_LogDCFL : Prop :=
  ∃ B ∈ LogDCFL, ∀ C : Circuit, StratMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true)

end PathChecking
