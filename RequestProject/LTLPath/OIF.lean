module

public import RequestProject.Complexity

/-!
# One-input-face monotone planar circuits

We define

* straight-line planar drawings of graphs (`StraightLineDrawing`);
* the graph of a circuit with one extra *apex* vertex adjacent to every input gate
  (`Circuit.apexAdj`), and one-input-face planarity (`Circuit.OneInputFacePlanar`): the circuit
  graph together with the apex has a straight-line planar drawing;
* monotone circuits of fan-in at most two (`Circuit.MonotoneFanin2`) and the instances of the
  one-input-face monotone planar circuit value problem (`OIFMCVPInstance`);
* the assumption `OIFMCVP_in_LogDCFL`, the result of Chakraborty and Datta [CD06] that the
  one-input-face monotone planar circuit value problem is in `LogDCFL`.

By Fáry's theorem, a finite simple graph is planar iff it has a straight-line planar drawing.
A planar graph has an embedding in which a given set `I` of vertices lies on the outer face iff
the graph obtained by adding a new vertex adjacent to all vertices of `I` is planar.  Hence
`Circuit.OneInputFacePlanar` is the usual notion: the (undirected) graph of the circuit has a
planar embedding with all input gates on one face.

The assumption is stated as a *promise problem*: some language in `LogDCFL` agrees with the value
of the circuit on all encodings of one-input-face monotone planar circuits (nothing is required
of other words).  This is the weakest form of the statement.

## References

* [CD06] T. Chakraborty, S. Datta, *One-input-face MPCVP is hard for L, but in LogDCFL*,
  FSTTCS 2006, LNCS 4337, pp. 57–68 (also ECCC TR06-130), Theorem 1 of the ECCC report.
  It is restated as [KF09, Theorem 1], [KF12, Theorem 3.1] and [Kuh10, Theorem 2];
  in [KF12, Theorem 3.1] and [Kuh10, Theorem 2] it is stated for circuits without variable gates,
  which is the form used here (`C.WellFormed 0`). Full entries are in `REFERENCES.md`.
-/

@[expose] public section

namespace PathChecking

/-- A straight-line planar drawing of a graph with adjacency relation `adj`: vertices are mapped
injectively to points of the plane, edges are drawn as straight segments, no vertex lies on an
edge other than at its endpoints, and two different edges meet at most in a common endpoint. -/
structure StraightLineDrawing {V : Type*} (adj : V → V → Prop) where
  /-- position of a vertex -/
  pos : V → ℝ × ℝ
  /-- different vertices are drawn at different points -/
  inj : Function.Injective pos
  /-- no vertex lies on an edge other than its endpoints -/
  vertex_off_edge : ∀ u v w, adj u v → w ≠ u → w ≠ v → pos w ∉ segment ℝ (pos u) (pos v)
  /-- different edges meet only in common endpoints -/
  edges_meet : ∀ u v u' v', adj u v → adj u' v' → ¬ (u = u' ∧ v = v') → ¬ (u = v' ∧ v = u') →
    ∀ z ∈ segment ℝ (pos u) (pos v), z ∈ segment ℝ (pos u') (pos v') →
      ∃ c, (c = u ∨ c = v) ∧ (c = u' ∨ c = v') ∧ z = pos c

/-- Input gates: constants and input bits. -/
def Gate.IsInput (g : Gate) : Prop :=
  match g.kind with
  | .const _ => True
  | .input _ => True
  | _ => False

/-- The undirected graph of a circuit, extended by an apex vertex (`none`) adjacent to all input
gates.  Gate `i` is the vertex `some i`; two gates are adjacent if one is an argument of the
other. -/
def Circuit.apexAdj (C : Circuit) : Option (Fin C.length) → Option (Fin C.length) → Prop
  | some i, some j => j.val ∈ C[i].args ∨ i.val ∈ C[j].args
  | some i, none => C[i].IsInput
  | none, some j => C[j].IsInput
  | none, none => False

/-- **One-input-face planarity**: the graph of the circuit, together with an apex vertex adjacent
to all input gates, has a straight-line planar drawing.  Equivalently (Fáry's theorem), the graph
of the circuit has a planar embedding with all input gates on the outer face. -/
def Circuit.OneInputFacePlanar (C : Circuit) : Prop :=
  Nonempty (StraightLineDrawing C.apexAdj)

/-- Monotone circuits of fan-in at most two: every gate is a constant (without arguments), or an
`AND`/`OR` gate with one or two arguments. -/
def Circuit.MonotoneFanin2 (C : Circuit) : Prop :=
  ∀ g ∈ C, (∃ b, g.kind = .const b ∧ g.args = []) ∨
    ((g.kind = .and ∨ g.kind = .or) ∧ 1 ≤ g.args.length ∧ g.args.length ≤ 2)

/-- Instances of the one-input-face monotone planar circuit value problem: well-formed circuits
without input bits, monotone of fan-in at most two, and one-input-face planar. -/
def OIFMCVPInstance (C : Circuit) : Prop :=
  C.WellFormed 0 ∧ C.MonotoneFanin2 ∧ C.OneInputFacePlanar

/-- **Assumption** (Chakraborty–Datta [CD06, Theorem 1]): the one-input-face monotone planar
circuit value problem is in `LogDCFL`.  Stated as a promise problem: some language in `LogDCFL` contains the
encoding of a one-input-face monotone planar circuit iff the circuit evaluates to `true`. -/
def OIFMCVP_in_LogDCFL : Prop :=
  ∃ B ∈ LogDCFL, ∀ C : Circuit, OIFMCVPInstance C → (C.encode ∈ B ↔ C.eval ∅ [] = true)

end PathChecking
