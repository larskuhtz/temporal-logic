module

public import RequestProject.LTLPath.Strat
public import RequestProject.LTLPath.GSys

/-!
# Grid circuits

A *grid* of width `W` and height `H` has nodes `(t, j)` with `t ≤ H` (the layer) and `j < W` (the
column).  Every node of layer `0` is a constant; every node `(t, j)` with `t ≥ 1` is an `AND` or
`OR` gate reading the node `(t - 1, j)` straight below it and/or the node `(t - 1, j + 1)`
diagonally below it.

The grid is listed layer by layer, and inside a layer from the right to the left
(`Grid.idx`), so that the last gate of the list is the node `(H, 0)`.  Since every node reads only
the columns `j` and `j + 1`, wires between two layers cannot cross, and the grid circuit is a
stratified monotone planar circuit (`Grid.strat`).  Its value is the value `Grid.gv nd H 0` of the
node `(H, 0)` (`Grid.eval`).
-/

@[expose] public section

namespace PathChecking

namespace Grid

/-- Nodes of a grid: constants, and `AND`/`OR` gates reading the node straight below (`s`) and/or
the node diagonally below (`d`). -/
inductive GN
  | cst (b : Bool)
  | gt (k : GateKind) (s d : Bool)

/-- Index of the node `(t, j)` in the list of gates. -/
def idx (W t j : ℕ) : ℕ := t * W + (W - 1 - j)

/-- The gate of the node with index `n`. -/
def gateOf (nd : ℕ → ℕ → GN) (W : ℕ) (n : ℕ) : Gate :=
  match nd (n / W) (W - 1 - n % W) with
  | .cst b => ⟨.const b, []⟩
  | .gt k s d => ⟨k, (if d then [idx W (n / W - 1) (W - 1 - n % W + 1)] else []) ++
      (if s then [idx W (n / W - 1) (W - 1 - n % W)] else [])⟩

/-- The grid circuit. -/
def circ (nd : ℕ → ℕ → GN) (W H : ℕ) : Circuit := GS.pre (gateOf nd W) ((H + 1) * W - 1)

/-- Values of the nodes. -/
def gv (nd : ℕ → ℕ → GN) : ℕ → ℕ → Bool
  | 0, j => match nd 0 j with
    | .cst b => b
    | .gt _ _ _ => false
  | t + 1, j => match nd (t + 1) j with
    | .cst b => b
    | .gt .and s d => (!d || gv nd t (j + 1)) && (!s || gv nd t j)
    | .gt .or s d => (d && gv nd t (j + 1)) || (s && gv nd t j)
    | .gt _ _ _ => false

/-- Well-formed grids. -/
structure OK (nd : ℕ → ℕ → GN) (W H : ℕ) : Prop where
  pos : 0 < W
  bot : ∀ j < W, ∃ b, nd 0 j = .cst b
  up : ∀ t, 1 ≤ t → t ≤ H → ∀ j < W, ∃ k s d, nd t j = .gt k s d ∧ (k = .and ∨ k = .or) ∧
    (s = true ∨ d = true) ∧ (j + 1 = W → d = false)

variable {nd : ℕ → ℕ → GN} {W H : ℕ}

lemma idx_div {t j : ℕ} (hj : j < W) : idx W t j / W = t := by
  unfold idx
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
  simp

lemma idx_mod {t j : ℕ} (hj : j < W) : idx W t j % W = W - 1 - j := by
  unfold idx
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

lemma idx_col {t j : ℕ} (hj : j < W) : W - 1 - idx W t j % W = j := by
  rw [idx_mod hj]; omega

lemma idx_of (hW : 0 < W) (n : ℕ) : n = idx W (n / W) (W - 1 - n % W) := by
  unfold idx
  have := Nat.mod_lt n hW
  have := Nat.div_add_mod n W
  rw [show W - 1 - (W - 1 - n % W) = n % W by omega, Nat.mul_comm]
  omega

lemma col_lt (hW : 0 < W) (n : ℕ) : W - 1 - n % W < W := by omega

lemma gateOf_idx {t j : ℕ} (hj : j < W) : gateOf nd W (idx W t j) =
    match nd t j with
    | .cst b => ⟨.const b, []⟩
    | .gt k s d => ⟨k, (if d then [idx W (t - 1) (j + 1)] else []) ++
        (if s then [idx W (t - 1) j] else [])⟩ := by
  unfold gateOf
  rw [idx_div hj, idx_col hj]

lemma idx_lt_idx {t t' j j' : ℕ} (hj : j < W) (hj' : j' < W) (ht : t < t') :
    idx W t j < idx W t' j' := by
  unfold idx
  have : (t + 1) * W ≤ t' * W := Nat.mul_le_mul_right _ ht
  rw [Nat.add_mul] at this
  omega

lemma ordered (h : OK nd W H) : GS.Ordered (gateOf nd W) := by
  intro n x hx
  have hj : W - 1 - n % W < W := col_lt h.pos n
  have hn := idx_of h.pos n
  generalize W - 1 - n % W = j at hj hn
  generalize n / W = t at hn
  subst hn
  rw [gateOf_idx hj] at hx
  rcases ht : nd t j with b | ⟨k, s, d⟩ <;> rw [ht] at hx
  · simp at hx
  · simp only [List.mem_append] at hx
    have ht0 : t ≠ 0 := by
      rintro rfl
      obtain ⟨b, hb⟩ := h.bot j hj
      rw [hb] at ht
      cases ht
    rcases hx with hx | hx
    · split_ifs at hx with hd
      · simp only [List.mem_singleton] at hx; subst hx
        have hj1 : j + 1 < W ∨ j + 1 = W := by omega
        rcases hj1 with hj1 | hj1
        · exact idx_lt_idx hj1 hj (by omega)
        · unfold idx; rw [show W - 1 - (j + 1) = 0 by omega]
          have : (t - 1) * W + W = t * W := by
            rw [← Nat.succ_mul, show (t - 1).succ = t by omega]
          omega
      · simp at hx
    · split_ifs at hx with hs
      · simp only [List.mem_singleton] at hx; subst hx
        exact idx_lt_idx hj hj (by omega)
      · simp at hx

lemma last_idx (hW : 0 < W) : (H + 1) * W - 1 = idx W H 0 := by
  unfold idx; rw [Nat.add_mul]; omega

/-- Values of the gate system at the nodes. -/
lemma val_idx (h : OK nd W H) : ∀ t, t ≤ H → ∀ j < W, GS.val (gateOf nd W) (idx W t j) = gv nd t j := by
  intro t
  induction t with
  | zero =>
    intro _ j hj
    obtain ⟨b, hb⟩ := h.bot j hj
    rw [GS.val_spec (ordered h), gateOf_idx hj, hb]
    simp [gv, hb, Gate.evalFn]
  | succ t ih =>
    intro ht j hj
    obtain ⟨k, s, d, hk, hko, -, hlast⟩ := h.up (t + 1) (by omega) ht j hj
    rw [GS.val_spec (ordered h), gateOf_idx hj, hk]
    have e1 : d = true → GS.val (gateOf nd W) (idx W t (j + 1)) = gv nd t (j + 1) := by
      intro hd
      exact ih (by omega) (j + 1) (by by_contra hc; have := hlast (by omega); rw [this] at hd; cases hd)
    have e2 := ih (by omega) j hj
    simp only [Nat.add_sub_cancel]
    rcases hko with rfl | rfl
    · simp only [gv, hk, Gate.evalFn]
      cases s <;> cases d <;> simp_all
    · simp only [gv, hk, Gate.evalFn]
      cases s <;> cases d <;> simp_all

/-- **The grid circuit computes the value of the node `(H, 0)`.** -/
theorem eval (h : OK nd W H) : (circ nd W H).eval ∅ [] = gv nd H 0 := by
  unfold circ
  rw [GS.eval_prefix (ordered h), last_idx h.pos]
  exact val_idx h H le_rfl 0 h.pos

lemma lt_len {n : ℕ} (hW : 0 < W) (hn : n < (circ nd W H).length) : n / W ≤ H := by
  unfold circ at hn
  rw [GS.pre_length] at hn
  have : n < (H + 1) * W := by
    have : 1 ≤ (H + 1) * W := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have := (Nat.div_lt_iff_lt_mul hW).2 this
  omega

lemma circ_get (n : ℕ) (hn : n < (circ nd W H).length) : (circ nd W H)[n] = gateOf nd W n := by
  unfold circ; rw [GS.pre_getElem]

/-- Shape of the gate with index `n`. -/
lemma gate_shape (h : OK nd W H) {n : ℕ} (hn : n < (circ nd W H).length) :
    (n / W = 0 ∧ ∃ b, (circ nd W H)[n] = ⟨.const b, []⟩) ∨
    (1 ≤ n / W ∧ ∃ k s d, ((k = .and ∨ k = .or) ∧ (s = true ∨ d = true)) ∧
      (W - 1 - n % W + 1 = W → d = false) ∧
      (circ nd W H)[n] = ⟨k, (if d then [idx W (n / W - 1) (W - 1 - n % W + 1)] else []) ++
        (if s then [idx W (n / W - 1) (W - 1 - n % W)] else [])⟩) := by
  have hle := lt_len h.pos hn
  rw [circ_get n hn]
  unfold gateOf
  have hj := col_lt h.pos n
  rcases Nat.eq_zero_or_pos (n / W) with e | e
  · left
    refine ⟨e, ?_⟩
    obtain ⟨b, hb⟩ := h.bot _ hj
    rw [e, hb]
    exact ⟨b, rfl⟩
  · right
    obtain ⟨k, s, d, hk, hko, hsd, hlast⟩ := h.up (n / W) e hle _ hj
    refine ⟨e, k, s, d, ⟨hko, hsd⟩, hlast, ?_⟩
    rw [hk]

/-- **Grid circuits are stratified monotone planar circuits.** -/
theorem strat (h : OK nd W H) : StratMCVPInstance (circ nd W H) := by
  have hW := h.pos
  have hord := ordered h
  refine ⟨⟨by simp [circ, GS.pre], fun i hi => ⟨fun j hj => ?_, ?_⟩⟩, fun g hg => ?_,
    ⟨fun n => n / W, ?_⟩⟩
  · rw [circ_get i hi] at hj; exact hord i j hj
  · rcases gate_shape h hi with ⟨-, b, hb⟩ | ⟨-, k, s, d, ⟨hko, -⟩, -, hb⟩
    · rw [hb]
    · rw [hb]; rcases hko with rfl | rfl <;> trivial
  · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hg
    rcases gate_shape h hn with ⟨-, b, hb⟩ | ⟨-, k, s, d, ⟨hko, hsd⟩, -, hb⟩
    · rw [hb]; left; exact ⟨b, rfl, rfl⟩
    · rw [hb]; right
      refine ⟨hko, ?_, ?_⟩ <;> cases s <;> cases d <;> simp_all
  · refine ⟨fun i j hij _ => Nat.div_le_div_right hij, fun i hi => ?_, fun i hi j hj => ?_,
      fun i hi => ?_, fun i i' hi hi' hii' hl a ha b hb => ?_⟩
    · rcases gate_shape h hi with ⟨e, b, hb⟩ | ⟨e, k, s, d, ⟨hko, -⟩, -, hb⟩
      · rw [hb]; simp [Gate.IsInput, e]
      · have := (Nat.le_div_iff_mul_le hW).1 e
        rw [hb]; rcases hko with rfl | rfl <;> simp [Gate.IsInput] <;> omega
    · rcases gate_shape h hi with ⟨e, b, hb⟩ | ⟨e, k, s, d, -, hlast, hb⟩
      · rw [hb] at hj; simp at hj
      · rw [hb] at hj
        simp only [List.mem_append] at hj
        rcases hj with hj | hj
        · split_ifs at hj with hd
          · simp only [List.mem_singleton] at hj; subst hj
            have hm := Nat.mod_lt i hW
            rw [idx_div (by by_contra hc; have := hlast (by omega); rw [this] at hd; cases hd)]
            omega
          · simp at hj
        · split_ifs at hj with hs
          · simp only [List.mem_singleton] at hj; subst hj
            rw [idx_div (col_lt hW i)]; omega
          · simp at hj
    · rcases gate_shape h hi with ⟨e, b, hb⟩ | ⟨e, k, s, d, -, hlast, hb⟩
      · rw [hb]; simp
      · rw [hb]
        cases s <;> cases d
        · simp
        · simp
        · simp
        · have hm := Nat.mod_lt i hW
          have hj1 : W - 1 - i % W + 1 < W := by
            by_contra hc; have := hlast (by omega); cases this
          simp only [if_true, List.singleton_append, List.pairwise_cons, List.mem_singleton,
            forall_eq, List.Pairwise.nil, and_true]
          unfold idx; exact ⟨by omega, by simp⟩
    · -- planarity: columns decrease along a layer
      have hci : W - 1 - i % W > W - 1 - i' % W := by
        have h1 := Nat.div_add_mod i W
        have h2 := Nat.div_add_mod i' W
        have := Nat.mod_lt i hW
        have := Nat.mod_lt i' hW
        simp only at hl
        rw [hl] at h1
        omega
      have mem_args : ∀ {m : ℕ} (hm : m < (circ nd W H).length) {x : ℕ},
          x ∈ (circ nd W H)[m].args →
          x = idx W (m / W - 1) (W - 1 - m % W) ∨
            (x = idx W (m / W - 1) (W - 1 - m % W + 1) ∧ W - 1 - m % W + 1 < W) := by
        intro m hm x hx
        rcases gate_shape h hm with ⟨-, b, hb⟩ | ⟨-, k, s, d, -, hlast, hb⟩
        · rw [hb] at hx; simp at hx
        · rw [hb] at hx
          simp only [List.mem_append] at hx
          rcases hx with hx | hx
          · split_ifs at hx with hd
            · simp only [List.mem_singleton] at hx
              right; refine ⟨hx, ?_⟩
              have hm := Nat.mod_lt m hW
              by_contra hc; have := hlast (by omega); rw [this] at hd; cases hd
            · simp at hx
          · split_ifs at hx with hs
            · simp only [List.mem_singleton] at hx; left; exact hx
            · simp at hx
      simp only at hl
      rcases mem_args hi ha with e1 | ⟨e1, -⟩ <;> rcases mem_args hi' hb with e2 | ⟨e2, -⟩ <;>
        (subst e1; subst e2; unfold idx; rw [hl]; omega)

end Grid

end PathChecking
