module

public import RequestProject.ACRound.Circ
public import RequestProject.ACRound.DPDA
public import RequestProject.ACRound.Defs

/-!
# The circuit simulating rounds of oracle queries

Given a circuit family `CB` (for the oracle language `B` of the rounds) and size parameters,
`Lay.circ` is the circuit that simulates `R` rounds of `Nq` queries:

* gates `0`, `1` are the constants `false`, `true`; gates `2 + i` are the inputs;
* for every round `r < R` and query `q < Nq` a *group* of `W` gates: oracle gates computing the
  bits and the length of the query word `u = Q (pack w q a)` (via the oracle language
  `LangF Q`), for every possible length `ℓ ≤ L` a block of `S` gates containing a copy of
  `CB ℓ` reading the bits of `u`, and an answer gate;
* three final gates evaluating the decision function `D`.

The oracle language of `Lay.circ` is `tagU B' (tagU (LangF Q) (LangF D))`, where `B'` is the
oracle language of `CB`.
-/

@[expose] public section

namespace PathChecking

open Classical

/-- The language of the bits and the length of the values of `f`:
`false :: 1^i 0 u` if bit `i` of `f u` is `1`, and `true :: 1^i 0 u` if `|f u| = i`. -/
def LangF (f : Word → Word) : Language :=
  {x | ∃ i u, (x = false :: (List.replicate i true ++ false :: u) ∧ (f u).getD i false = true) ∨
    (x = true :: (List.replicate i true ++ false :: u) ∧ (f u).length = i)}

lemma replicate_true_append_inj {i j : ℕ} {u v : Word}
    (h : List.replicate i true ++ false :: u = List.replicate j true ++ false :: v) :
    i = j ∧ u = v := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => simpa using h
    | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
    cases j with
    | zero => simp [List.replicate_succ] at h
    | succ j =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := ih h
      exact ⟨by omega, h2⟩

lemma mem_LangF (f : Word → Word) (b : Bool) (i : ℕ) (u : Word) :
    b :: (List.replicate i true ++ false :: u) ∈ LangF f ↔
      if b then (f u).length = i else (f u).getD i false = true := by
  constructor
  · rintro ⟨j, v, ⟨h, h'⟩ | ⟨h, h'⟩⟩
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := replicate_true_append_inj h
      simpa using h'
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨rfl, rfl⟩ := replicate_true_append_inj h
      simpa using h'
  · intro h
    cases b
    · exact ⟨i, u, Or.inl ⟨rfl, by simpa using h⟩⟩
    · exact ⟨i, u, Or.inr ⟨rfl, by simpa using h⟩⟩

lemma getElem?_flatMap_range {α : Type*} (m W : ℕ) (f : ℕ → List α)
    (hf : ∀ a < m, (f a).length = W) (a b : ℕ) (ha : a < m) (hb : b < W) :
    ((List.range m).flatMap f)[a * W + b]? = (f a)[b]? := by
  induction m with
  | zero => omega
  | succ m ih =>
    have hlen : ((List.range m).flatMap f).length = m * W := by
      rw [List.length_flatMap, List.map_congr_left (fun a ha => hf a (by simp at ha; omega))]
      simp
    rw [List.range_succ, List.flatMap_append]
    by_cases ham : a < m
    · rw [List.getElem?_append_left (by rw [hlen]; nlinarith)]
      exact ih (fun a ha => hf a (by omega)) ham
    · have : a = m := by omega
      subst this
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]
      simp

lemma length_flatMap_range {α : Type*} (m W : ℕ) (f : ℕ → List α)
    (hf : ∀ a < m, (f a).length = W) : ((List.range m).flatMap f).length = m * W := by
  rw [List.length_flatMap, List.map_congr_left (fun a ha => hf a (by simp at ha; omega))]
  simp

/-- Layout parameters of the round circuit. -/
structure Lay where
  /-- input length -/
  n : ℕ
  /-- queries per round -/
  Nq : ℕ
  /-- number of rounds -/
  R : ℕ
  /-- bound on the lengths of the query words -/
  L : ℕ
  /-- block size -/
  S : ℕ
  /-- the circuit family of the oracle language -/
  CB : ℕ → Circuit

namespace Lay

variable (P : Lay)

/-- Size of a group. -/
def W : ℕ := 2 * (P.L + 1) + (P.L + 1) * P.S + 1

/-- Number of gates before the groups. -/
def P0 : ℕ := P.n + 2

/-- First gate of the group of round `r` and query `q`. -/
def gb (r q : ℕ) : ℕ := P.P0 + (r * P.Nq + q) * P.W

/-- First gate of block `ℓ` of group `(r, q)`. -/
def bb (r q ℓ : ℕ) : ℕ := P.gb r q + 2 * (P.L + 1) + ℓ * P.S

/-- Gate holding the answer to query `q` in round `r` (round `0`: constant `false`). -/
def ans : ℕ → ℕ → ℕ
  | 0, _ => 0
  | r + 1, q => P.gb r q + P.W - 1

/-- Gate of the constant `b`. -/
def bitIdx : Bool → ℕ
  | false => 0
  | true => 1

/-- The gates spelling the word `pack w q a` (with `a` the answers of round `r`). -/
def packArgs (r q : ℕ) : List ℕ :=
  List.replicate P.n 1 ++ [0] ++ (List.range P.n).map (2 + ·) ++
    (List.range P.Nq).map (P.ans r) ++ List.replicate (P.Nq - q) 0 ++ List.replicate q 1

/-- Arguments of the oracle gate asking for bit (`b = false`) or length (`b = true`) `i` of
`Q (pack w q a)` (`t = false`) or of `D (pack w q a)` (`t = true`). -/
def qArgs (t b : Bool) (i r q : ℕ) : List ℕ :=
  [1, bitIdx t, bitIdx b] ++ List.replicate i 1 ++ 0 :: P.packArgs r q

/-- Copy of a gate of `CB ℓ` placed at offset `b0`; input gate `i` becomes an `OR` of gate
`g0 + i`; oracle gates get the tag `false` (gate `0`) in front. -/
def copyGate (b0 g0 : ℕ) (g : Gate) : Gate :=
  match g.kind with
  | .input i => ⟨.or, [g0 + i]⟩
  | .oracle => ⟨.oracle, 0 :: g.args.map (b0 + ·)⟩
  | k => ⟨k, g.args.map (b0 + ·)⟩

/-- Block `ℓ` of group `(r, q)`: copy of `CB ℓ`, padding, and the selection gate. -/
def blockGates (r q ℓ : ℕ) : List Gate :=
  (P.CB ℓ).map (copyGate (P.bb r q ℓ) (P.gb r q)) ++
    List.replicate (P.S - 1 - (P.CB ℓ).length) ⟨.const false, []⟩ ++
    [⟨.and, [P.gb r q + (P.L + 1) + ℓ, P.bb r q ℓ + (P.CB ℓ).length - 1]⟩]

/-- Bit gate `i` of group `(r, q)`. -/
def bitGate (r q i : ℕ) : Gate := ⟨.oracle, P.qArgs false false i r q⟩

/-- Length gate `i` of group `(r, q)`. -/
def lenGate (r q i : ℕ) : Gate := ⟨.oracle, P.qArgs false true i r q⟩

/-- Answer gate of group `(r, q)`. -/
def ansGate (r q : ℕ) : Gate := ⟨.or, (List.range (P.L + 1)).map (fun ℓ => P.bb r q ℓ + P.S - 1)⟩

/-- The gates of group `(r, q)`. -/
def groupGates (r q : ℕ) : List Gate :=
  (List.range (P.L + 1)).map (P.bitGate r q) ++ (List.range (P.L + 1)).map (P.lenGate r q) ++
    (List.range (P.L + 1)).flatMap (P.blockGates r q) ++ [P.ansGate r q]

/-- Constants and inputs. -/
def prefixGates : List Gate :=
  [⟨.const false, []⟩, ⟨.const true, []⟩] ++ (List.range P.n).map (fun i => ⟨.input i, []⟩)

/-- First final gate. -/
def F0 : ℕ := P.P0 + P.R * P.Nq * P.W

/-- The final gates: bit `0` and length `1` of `D (pack w 0 a)`, and their conjunction. -/
def finalGates : List Gate :=
  [⟨.oracle, P.qArgs true false 0 P.R 0⟩, ⟨.oracle, P.qArgs true true 1 P.R 0⟩,
    ⟨.and, [P.F0, P.F0 + 1]⟩]

/-- The round circuit. -/
def circ : Circuit :=
  P.prefixGates ++ (List.range P.R).flatMap (fun r => (List.range P.Nq).flatMap (P.groupGates r)) ++
    P.finalGates

/-! ## Indexing -/

/-- Size hypothesis: every copied circuit is nonempty and fits into a block. -/
def SizeOk : Prop := ∀ ℓ ≤ P.L, P.CB ℓ ≠ [] ∧ (P.CB ℓ).length + 1 ≤ P.S

variable {P}

lemma blockGates_length (h : P.SizeOk) (r q ℓ : ℕ) (hℓ : ℓ ≤ P.L) :
    (P.blockGates r q ℓ).length = P.S := by
  obtain ⟨h1, h2⟩ := h ℓ hℓ
  have := List.length_pos_of_ne_nil h1
  simp [blockGates]; omega

lemma groupGates_length (h : P.SizeOk) (r q : ℕ) : (P.groupGates r q).length = P.W := by
  simp only [groupGates, List.length_append, List.length_map, List.length_range,
    List.length_singleton, W]
  rw [length_flatMap_range _ P.S _ (fun ℓ hℓ => blockGates_length h r q ℓ (by omega))]
  omega

lemma prefixGates_length : P.prefixGates.length = P.P0 := by
  simp [prefixGates, P0]

lemma groups_length (h : P.SizeOk) :
    ((List.range P.R).flatMap (fun r => (List.range P.Nq).flatMap (P.groupGates r))).length =
      P.R * P.Nq * P.W := by
  rw [length_flatMap_range _ (P.Nq * P.W) _ (fun r _ =>
    length_flatMap_range _ P.W _ (fun q _ => groupGates_length h r q))]
  ring

lemma circ_length (h : P.SizeOk) : P.circ.length = P.F0 + 3 := by
  simp only [circ, List.length_append, prefixGates_length, groups_length h, F0, finalGates,
    List.length_cons, List.length_nil]

lemma circ_get_prefix (i : ℕ) (hi : i < P.P0) : P.circ[i]? = P.prefixGates[i]? := by
  unfold circ
  rw [List.append_assoc, List.getElem?_append_left (by rw [prefixGates_length]; exact hi)]

lemma circ_get_group (h : P.SizeOk) (r q t : ℕ) (hr : r < P.R) (hq : q < P.Nq) (ht : t < P.W) :
    P.circ[P.gb r q + t]? = (P.groupGates r q)[t]? := by
  unfold circ
  rw [List.append_assoc, List.getElem?_append_right (by rw [prefixGates_length]; simp only [gb]; omega),
    prefixGates_length, show P.gb r q + t - P.P0 = r * (P.Nq * P.W) + (q * P.W + t) by
      simp only [gb]; rw [Nat.add_assoc, Nat.add_sub_cancel_left]; ring,
    List.getElem?_append_left (by
      rw [groups_length h, show P.R * P.Nq * P.W = P.R * (P.Nq * P.W) by ring]
      have : q * P.W + t < P.Nq * P.W := by nlinarith
      nlinarith [Nat.mul_le_mul_right (P.Nq * P.W) (show r + 1 ≤ P.R from hr)]),
    getElem?_flatMap_range _ (P.Nq * P.W) _ (fun r _ =>
      length_flatMap_range _ P.W _ (fun q _ => groupGates_length h r q)) _ _ hr (by nlinarith),
    getElem?_flatMap_range _ P.W _ (fun q _ => groupGates_length h r q) _ _ hq ht]

lemma circ_get_final (h : P.SizeOk) (t : ℕ) (ht : t < 3) :
    P.circ[P.F0 + t]? = P.finalGates[t]? := by
  unfold circ
  rw [List.getElem?_append_right (by
      simp only [List.length_append, prefixGates_length, groups_length h, F0]; omega)]
  simp only [List.length_append, prefixGates_length, groups_length h, F0]
  congr 1; omega

/-- Local indexing in a group. -/
lemma groupGates_get_bit (r q i : ℕ) (hi : i ≤ P.L) :
    (P.groupGates r q)[i]? = some (P.bitGate r q i) := by
  unfold groupGates
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_map, List.getElem?_range (by omega : i < P.L + 1)]

lemma groupGates_get_len (r q i : ℕ) (hi : i ≤ P.L) :
    (P.groupGates r q)[P.L + 1 + i]? = some (P.lenGate r q i) := by
  unfold groupGates
  rw [List.append_assoc, List.append_assoc, List.getElem?_append_right (by simp),
    List.getElem?_append_left (by simp; omega)]
  simp [List.getElem?_map, List.getElem?_range (by omega : i < P.L + 1)]

lemma groupGates_get_block (h : P.SizeOk) (r q ℓ v : ℕ) (hℓ : ℓ ≤ P.L) (hv : v < P.S) :
    (P.groupGates r q)[2 * (P.L + 1) + ℓ * P.S + v]? = (P.blockGates r q ℓ)[v]? := by
  unfold groupGates
  rw [List.getElem?_append_left (by
      simp only [List.length_append, List.length_map, List.length_range]
      rw [length_flatMap_range _ P.S _ (fun ℓ hℓ => blockGates_length h r q ℓ (by omega))]
      nlinarith),
    List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_map, List.length_range]
  rw [show 2 * (P.L + 1) + ℓ * P.S + v - (P.L + 1 + (P.L + 1)) = ℓ * P.S + v by omega,
    getElem?_flatMap_range _ P.S _ (fun ℓ hℓ => blockGates_length h r q ℓ (by omega)) _ _
      (by omega) hv]

lemma groupGates_get_ans (h : P.SizeOk) (r q : ℕ) :
    (P.groupGates r q)[P.W - 1]? = some (P.ansGate r q) := by
  have hl := groupGates_length h r q
  unfold groupGates at hl ⊢
  rw [List.length_append, List.length_singleton] at hl
  rw [List.getElem?_append_right (by omega), ← hl]
  simp

lemma blockGates_get_copy (r q ℓ v : ℕ) (hv : v < (P.CB ℓ).length) :
    (P.blockGates r q ℓ)[v]? = some (copyGate (P.bb r q ℓ) (P.gb r q) (P.CB ℓ)[v]) := by
  unfold blockGates
  rw [List.append_assoc, List.getElem?_append_left (by simpa using hv)]
  simp [hv]

lemma blockGates_get_pad (r q ℓ v : ℕ)
    (hv1 : (P.CB ℓ).length ≤ v) (hv2 : v + 1 < P.S) :
    (P.blockGates r q ℓ)[v]? = some ⟨.const false, []⟩ := by
  unfold blockGates
  rw [List.append_assoc, List.getElem?_append_right (by simpa using hv1),
    List.getElem?_append_left (by simp; omega)]
  simp only [List.length_map]
  rw [List.getElem?_replicate, if_pos (by omega)]

lemma blockGates_get_sel (h : P.SizeOk) (r q ℓ : ℕ) (hℓ : ℓ ≤ P.L) :
    (P.blockGates r q ℓ)[P.S - 1]? =
      some ⟨.and, [P.gb r q + (P.L + 1) + ℓ, P.bb r q ℓ + (P.CB ℓ).length - 1]⟩ := by
  have hl := blockGates_length h r q ℓ hℓ
  unfold blockGates at hl ⊢
  rw [List.length_append, List.length_singleton] at hl
  rw [List.getElem?_append_right (by omega), ← hl]
  simp

end Lay

end PathChecking
