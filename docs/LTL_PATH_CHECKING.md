# Theorem 1a: LTL path checking is in AC¹[LogDCFL] (design of the proof)

There are two conditional forms in `RequestProject/Statements.lean`, both proved without
`sorry` and using only the axioms `propext`, `Classical.choice` and `Quot.sound`:

* `LTLPathChecking_mem_AC1_LogDCFL_of_OIF` assumes the Chakraborty–Datta theorem
  `OIFMCVP_in_LogDCFL` [CD06, Theorem 1]. This is the original result of [KF09].
* `LTLPathChecking_mem_AC1_LogDCFL_of_strat` assumes the Barrington–Lu–Miltersen–Skyum theorem
  `StratMCVP_in_LogDCFL` [BLMS, Theorem 2]. The query circuits are drawn directly as stratified
  monotone planar circuits, so the reduction from one-input-face circuits to stratified circuits
  in [CD06] is not needed (see the last section).

The unconditional `LTLPathChecking_mem_AC1_LogDCFL` is derived from the second form and the
Barrington–Lu–Miltersen–Skyum theorem `StratMCVP_mem_LogDCFL`, which is proved in
`RequestProject/BLMS/` following [BLMS, Section 5]. The algorithm follows Kuhtz–Finkbeiner
[KF12, Sections 3–5] (monotone circuits, construction of the circuit, parallel tree
contraction [ADKP89]), adapted to lasso paths. File names below refer to
`RequestProject/LTLPath/` unless stated otherwise.

## Structure of the proof

* **From rounds to circuits.** `RoundDecidable.mem_ACOracle_of_LogDCFL`
  (`RequestProject/ACRound/Main.lean`) turns a logspace algorithm with `O(log^k n)` rounds of
  queries to a language in `LogDCFL` into an `AC^k[LogDCFL]` circuit family.
* **The oracle.** `OIF.lean` defines one-input-face monotone planar circuits
  (`OIFMCVPInstance`) and states the Chakraborty–Datta theorem as a promise problem
  (`OIFMCVP_in_LogDCFL`).
* **The round algorithm.** `ltl_roundDecidable` (`Main.lean`) proves
  `RoundDecidable LTLPathChecking B 1` for every `B` that agrees with the circuit value on
  one-input-face instances. It is assembled by `roundDecidable_of_specs` (`Assembly.lean`) from
  the query function `qFun` (`FDQ.lean`, `qFun_spec`, `qFun_logspace`) and the decision
  function `dFun` (`FDD.lean`, `dFun_spec`, `dFun_logspace`).
* **Correctness of the abstract algorithm.** `FT.oseq_root` (`Abstract.lean`) works on a
  formula tree with path data (`FT`). With any oracle that is correct on one-input-face
  instances, after `4R + 1` rounds (`L ≤ 2^R`) the status of the root gate is the truth value.
  Ingredients:
  * `Round.lean`: one round (correctness, closure, full closure, leaf regions);
  * `Phase.lean`: the invariant across phases and stages;
  * `Run.lean`: round 0 and the final round;
  * `Sequence.lean`: the round schedule `rS`/`rQ` and the oracle statuses (`oseq = seq`);
  * `QueryOIF.lean` (`query_oif`): every query circuit is a one-input-face monotone planar
    instance, shown with a layered drawing (uses `Depth.lean`, `QArgs.lean`);
  * `Sem.lean` (`gate_sem`): given `Sem`, the global circuit computes the semantics.
* **Instantiation from the input.** `Tree.lean`, `Path.lean`, `TokTree.lean`, `TokFT.lean`,
  `TokSem.lean` build `FT` and `Sem` from the tokens of a valid input: the positional tree
  from `fend`, the letters of the lasso, and the polarity as the parity of the number of `neg`
  ancestors. They also relate `sat 1 0` to `LTL.Sat`.
* **Logspace implementation.** `FE*.lean` and `FD*.lean` write `qFun` and `dFun` as functional
  expressions compiled to the loop language. `ValidPath.lean`, `ValidComp.lean` and
  `ValidI.lean` (`validI_iff`) recognise encodings of instances by local conditions, each
  inspecting only positions found by bounded search. `FDValid.lean` computes these conditions
  in logspace.

## Building blocks
* `Layered.lean`: a layered drawing (levels `Y : V → ℤ`, abscissae `X`, edges between equal or
  adjacent levels, no vertex inside a horizontal edge, edges between two adjacent levels are
  non-crossing) is a straight-line planar drawing.
* `FE.lean`: functional expressions (bounded `find`, `count`, `lett`) compiled to the loop
  language, with correctness (`run_comp`).
* `GSys.lean`: gate systems `g : ℕ → Gate`, values `GS.val`, prefix circuits (`GS.eval_prefix`);
  query systems `GS.qsys g st live keep β` (live gates keep kind and kept args, other gates are
  constants `(st h).getD β`); `GS.sandwich` (if statuses are correct and dropped args are known
  neutral, then `qv false ≤ val ≤ qv true`), `GS.dec_correct`, `live_eq_of_args`,
  `live_eq_of_absorb` (used for closure preservation).

## The algorithm

### Formula tree and the global circuit
* Instance tokens `ts = ( φ ) lasso`; formula positions `[1, F)` with `F = fend 1`; a *node* is a
  position in `[1,F)` holding a tag token; children of node `p`: `p+1` (unary/binary) and
  `fend (p+1)` (binary). Leaves: `ap`, `tt`. Leaf index `lix p` = number of leaves in `[1,p)`;
  leaf range of `p`: `[lix p, lix (fend p))`.
* Lasso stem length `s`, loop length `ℓ ≥ 1`; window `W p = s + (p+2) ℓ`, `Wm = s + (N+2) ℓ`
  (`N` = number of tokens). Polarity `pol p` = parity of the number of `neg` ancestors.
* Gates `(p, i, t)`, `i < Wm`, `t ∈ {aux, main}`; index `2((N-1-p) Wm + (Wm-1-i)) + [t = main]`.
  For `i < W p` (single-rail negation normal form, `∧/∨` swapped when `pol p = 1`):
  - `ap a`: main = const (`a ∈ letter i` xor pol); `tt`: const (`!pol`);
  - `neg`: main = AND[(p+1,i)]; `X`: main = AND[(p+1,i+1)];
  - `and`: main = (pol ? OR : AND)[(c1,i),(c2,i)];
  - `U`: main_i = (pol ? AND : OR)[(c2,i), aux_i] for `i < W-1`, main_{W-1} = AND[(c2,W-1)],
    aux_i = (pol ? OR : AND)[(c1,i), main_{i+1}];
  - everything else (aux of non-`U`, `i ≥ W p`, non-nodes): const false.
  Values are correct (= `Sat` xor pol) for `i < W p - ℓ` (minimal witness on a lasso is
  `< max(i,s) + ℓ`; children have windows `≥ W p + ℓ`).

### Statuses and answers
* Answer slots: ticks `[0, K)` (tick `j` answered `true` iff `j < round`), then slot `K + 2h + β`
  for gate `h`, `β ∈ {0,1}`.
* Status of gate `h` at round `t`: const gates are always known (value computed directly);
  at round `0` everything else is unknown; afterwards known iff the two answers agree.

### Tree contraction schedule (static, Abrahamson–Dadoun–Kirkpatrick–Przytycka style)
* `S_{r,0}` = leaf indices divisible by `2^r`. `k` odd at stage `r`: `k / 2^r` odd.
  `isLeft k` iff `lca(k, k+2^r)` is deeper (larger position) than `lca(k-2^r, k)`; `lca(a,b)` =
  largest node whose leaf range contains `a` and `b`.
  `D_{r,L}` = odd left leaves, `S_{r,1} = S_{r,0} \ D_{r,L}`; `D_{r,R}` = odd right leaves,
  `S_{r+1,0} = S_{r,1} \ D_{r,R}`.
* For a set `S` of leaves: `alive y` iff the leaf range of `y` meets `S`; `down y` = lca of the
  smallest and largest `S`-leaf in the range of `y`. Regions: `R(d)` = alive non-leaf nodes `y`
  with `down y = d`; region chains have one alive child per non-bottom node.
* Rounds: `t = 0`: query all regions of `S_{0,0}`. For each substep `(r, φ)`:
  round A: structure `S_{r,φ}`, query only the regions `R(p)` where `p` = compressed parent of a
  removed leaf (all other gates frozen); round B: structure `S_{r,φ+1}`, query all regions.
  Total `1 + 4(log n + 1) ≤ 5 (log n + 1)` rounds; afterwards rounds B with `S = {0}` repeat.
* Query for gate `h0` and `β`: prefix circuit `[0..h0]` of `GS.qsys` where live = unknown gates
  of the region of `h0` (if queried), and an argument `x` of a live gate is dropped iff `x` is
  known with neutral value and its node is in the region or dead.

### Invariant (closure)
* `Cl(R, st)`: every unknown gate of `R`: known args in non-frontier rows are neutral, and some arg
  is unknown or in a frontier row (alive child outside the region). Querying a region preserves
  closure (`live_eq_of_absorb`, `live_eq_of_args`).
* After round A, `R(p)` is closed also w.r.t. its frontier rows (they were frozen); leaf regions
  `R(k)` are fully known after every round B. Hence the merged region `R(q) ∪ R(p)` is closed
  at round B (no chained merges: the sibling region of a removed leaf is not itself a
  `p`-region; proof by the neighbour argument `k ± 2^r` even).
* Closure ⇒ query circuit is one-input-face (layered drawing: region rows at levels `1..m`,
  bottom row at level 1, frontier inputs at level 0, isolated constants far right at level 0,
  apex at level −1; `main_i` at `X = 2i`, `aux_i` at `2i+1`).
* Final: `S = {0}`, the region containing the root has only known frontier, so after one more
  round all its gates are known; `D` accepts iff the input is valid and the root gate
  `(1, 0, main)` is known `true`.

## Variant with stratified query circuits

`LTLPathChecking_mem_AC1_LogDCFL_of_strat` uses the same round algorithm, but every query
circuit is drawn as a stratified monotone planar circuit in the sense of [BLMS, Section 2]
(`Strat.lean`: `Circuit.StratLayering`, `StratMCVPInstance`, `StratMCVP_in_LogDCFL`). The proof
reuses the abstract algorithm and changes only the shape of the queries.

* `Grid.lean`: a *grid* has nodes `(t, j)`; layer `0` holds constants, and every other node is an
  `AND`/`OR` gate reading the node straight below and/or the node diagonally below. Listed layer
  by layer, a grid is a stratified monotone planar circuit (`Grid.strat`), and its value is the
  value of its top-left node (`Grid.eval`).
* `LGrid.lean`, `LGridP.lean`: a *layered system* is a gate system with live gates placed at a
  row `Y` and a column `X`. Arguments lie in the same row at the next column, in the row below
  at a nearby column, or are constants of row `1`, and wires between two rows do not cross.
  `LSys.circ` draws such a system as a grid. Each live gate becomes a grid node; same-row
  arguments are reached through one copy node, and every other wire runs through the band of
  its row along alternating diagonal and straight copy steps. The drawing is stratified
  (`LSys.circ_strat`) and computes the value of the output gate (`LSys.circ_eval`).
* `QueryStrat.lean`: every query system of the algorithm is a layered system for the
  coordinates already used in `QueryOIF.lean` (`FT.qLS_ok`, `FT.qLS_bd`). `FT.stratQ` is its
  grid drawing. It is a stratified instance (`FT.query_strat`), and it computes the value of the
  query gate (`FT.query_strat_eval`).
* `AssemblyStrat.lean`: `roundDecidable_of_specsS` assembles the round algorithm from a query
  function with the specification `QSpecS` (the queries are the circuits `FT.stratQ`) and the
  decision function `dFun`.
* Logspace implementation: `LGridC.lean` expresses the drawing through a few per-gate quantities
  (`LG.LSem`, `LG.Agree`): row, column, kind, at most two arguments with presence flags, and the
  values of the constant gates. The auxiliary notions of the drawing become bounded searches
  over gates. `FDLG.lean` and `FDLGO.lean` give an output program `circO` that writes the grid
  drawing from term builders for these quantities (`LC.Ok.deno_circO`). `FDStrat.lean`
  instantiates the quantities for the query systems (`qSem_agree`, `qLC_ok`), and `FDQS.lean`
  defines the query function `qFunS` (`qFunS_spec`, `qFunS_logspace`).
* `MainStrat.lean`: `ltl_roundDecidable_strat` proves `RoundDecidable LTLPathChecking B 1` for
  every `B` that agrees with the circuit value on stratified instances.
