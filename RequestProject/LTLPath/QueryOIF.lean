module

public import RequestProject.LTLPath.QArgs
public import RequestProject.LTLPath.Layered

/-!
# The query circuits are one-input-face

Fix a round with leaf set `S`, queried regions `Qd` and statuses `st` satisfying the closure
invariant.  The query for gate `h0` is the prefix circuit of `qsysR S Qd st h0 β`.  Its live
gates lie in the rows of the region of `h0`, which form a chain of the formula tree; all other
gates are constants.  We draw it in layers:

* the live gate `(y, i, main)` at `X = 2i`, `(y, i, aux)` at `X = 2i + 1`, on the line
  `depth d - depth y + 1` (`d` the bottom of the region; `depth d - depth y` if `d` is a leaf);
* constants that are arguments of live gates (frontier inputs, gates of the alive children of
  the bottom row) on line `0` at `X = 2i + side`, where `side = 1` for first children;
* all other constants on line `0`, far to the right; the apex on line `-1`.

This is a layered drawing (`Layered`), hence planar; together with the closure invariant
(every live gate keeps an argument) the query circuit is an instance of the one-input-face
monotone planar circuit value problem (`query_oif`).
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

section Query

variable (T) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ)

/-- Edges of the query circuit: kept arguments of live gates. -/
def QE (g x : ℕ) : Prop :=
  T.live S Qd st h0 g = true ∧ x ∈ (T.gate g).args ∧ T.keep S st g x = true

/-- Frontier inputs: non-live kept arguments of live gates. -/
def QFr (x : ℕ) : Prop := (∃ g, T.QE S Qd st h0 g x) ∧ T.live S Qd st h0 x = false

/-- The bottom of the region of `h0`. -/
noncomputable def rd : ℕ := T.down S (T.pos h0)

/-- The line of the row `y`. -/
noncomputable def lvl (y : ℕ) : ℤ :=
  (T.depth (T.rd S h0) : ℤ) - T.depth y + (if T.leaf (T.rd S h0) = true then 0 else 1)

/-- `1` for first children, `0` otherwise. -/
noncomputable def side (x : ℕ) : ℕ := if T.IsChild (T.pos x - 1) (T.pos x) then 1 else 0

/-- Abscissa of a gate. -/
noncomputable def QX (h : ℕ) : ℕ :=
  if T.live S Qd st h0 h = true then 2 * T.ix h + 1 - ty h
  else if T.QFr S Qd st h0 h then 2 * T.ix h + T.side h
  else 2 * T.Wm + 2 + h

/-- Line of a gate. -/
noncomputable def QY (h : ℕ) : ℤ :=
  if T.live S Qd st h0 h = true then T.lvl S h0 (T.pos h) else 0

end Query

variable {S Qd : ℕ → Prop} {st : ℕ → Option Bool} {h0 : ℕ}

lemma live_spec {h : ℕ} (hl : T.live S Qd st h0 h = true) :
    AO (T.gate h) ∧ st h = none ∧ T.InR S (T.rd S h0) (T.pos h) := by
  simp only [live, decide_eq_true_eq] at hl
  exact ⟨hl.2.2.2.1, hl.2.2.1, hl.2.2.2.2⟩

lemma inR_anc {d y : ℕ} (hy : T.nd y = true) (h : T.InR S d y) : T.Anc y d := by
  rw [← h.2.2]; exact (T.down_prop hy).1

lemma live_anc {h : ℕ} (hl : T.live S Qd st h0 h = true) : T.Anc (T.pos h) (T.rd S h0) :=
  inR_anc (gate_AO (live_spec hl).1).2.1 (live_spec hl).2.2

/-- Lines of live gates are positive. -/
lemma lvl_pos {h : ℕ} (hl : T.live S Qd st h0 h = true) : 1 ≤ T.lvl S h0 (T.pos h) := by
  have ha := live_anc hl
  have hle := PT.depth_le_of_anc ha
  unfold lvl
  split_ifs with hlf
  · have hne : T.pos h ≠ T.rd S h0 := by
      intro e; have := (live_spec hl).2.2.2.1; rw [e, hlf] at this; exact absurd this (by simp)
    have := PT.depth_lt_of_anc ha hne
    omega
  · omega

lemma lvl_child {y c : ℕ} (hc : T.IsChild y c) : T.lvl S h0 c = T.lvl S h0 y - 1 := by
  unfold lvl; rw [PT.depth_child hc]; push_cast; ring

/-- Live gates on the same line are in the same row. -/
lemma pos_eq_of_lvl {g g' : ℕ} (hl : T.live S Qd st h0 g = true)
    (hl' : T.live S Qd st h0 g' = true) (e : T.lvl S h0 (T.pos g) = T.lvl S h0 (T.pos g')) :
    T.pos g = T.pos g' := by
  refine PT.eq_of_depth_eq (live_anc hl) (live_anc hl') ?_
  unfold lvl at e; omega

/-- Kept arguments of live gates are live (same row or child row) or frontier arguments. -/
lemma edge_cases (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {g x : ℕ}
    (he : T.QE S Qd st h0 g x) :
    (T.live S Qd st h0 x = true ∧ (T.pos x = T.pos g ∨ T.IsChild (T.pos g) (T.pos x))) ∨
      (T.live S Qd st h0 x = false ∧ ¬ T.NF S (T.pos g) (T.pos x)) := by
  obtain ⟨hl, hx, hk⟩ := he
  obtain ⟨hA, hu, hr⟩ := live_spec hl
  have hsh := ((gate_AO hA).2.2.2.2 x hx).2.2
  by_cases hnf : T.NF S (T.pos g) (T.pos x)
  · left
    refine ⟨?_, hsh⟩
    cases hsx : st x with
    | none => exact live_of_nf' hck hd hl hnf hsx
    | some v =>
      have := (hcl g hA hu hr.1).1 x hx hnf v hsx
      simp [keep, hsx, this, hnf] at hk
  · right
    refine ⟨?_, hnf⟩
    by_contra hlx
    have hr' := (live_spec (by simpa using hlx)).2.2
    exact hnf (Or.inr (Or.inr ⟨hr'.1, hr'.2.1, hr'.2.2.trans hr.2.2.symm⟩))

/-- Frontier arguments come from the bottom row. -/
lemma frontier_row {g x : ℕ} (hl : T.live S Qd st h0 g = true) (hx : x ∈ (T.gate g).args)
    (hnf : ¬ T.NF S (T.pos g) (T.pos x)) :
    (T.leaf (T.rd S h0) = true ∧ T.pos x = T.rd S h0 ∧ T.IsChild (T.pos g) (T.rd S h0)) ∨
      (T.leaf (T.rd S h0) = false ∧ T.pos g = T.rd S h0 ∧ T.IsChild (T.rd S h0) (T.pos x)) := by
  obtain ⟨hA, -, hr⟩ := live_spec hl
  rcases ((gate_AO hA).2.2.2.2 x hx).2.2 with e | hc
  · exact absurd (Or.inl e) hnf
  have hax : T.alive S (T.pos x) := by by_contra h'; exact hnf (Or.inr (Or.inl h'))
  by_cases hdy : T.down S (T.pos g) = T.pos g
  · right
    have e : T.pos g = T.rd S h0 := hdy.symm.trans hr.2.2
    refine ⟨?_, e, e ▸ hc⟩
    rw [← e]; exact hr.2.1
  · left
    have e1 := down_child_eq hc hax hdy
    have hlx : T.leaf (T.pos x) = true := by
      by_contra hl'
      exact hnf (Or.inr (Or.inr ⟨hax, by simpa using hl', e1⟩))
    have e2 : T.pos x = T.rd S h0 := by
      rw [← hr.2.2, ← e1, PT.down_leaf hlx]
    exact ⟨e2 ▸ hlx, e2, e2 ▸ hc⟩

lemma lvl_frontier {g x : ℕ} (hl : T.live S Qd st h0 g = true) (hx : x ∈ (T.gate g).args)
    (hnf : ¬ T.NF S (T.pos g) (T.pos x)) : T.lvl S h0 (T.pos g) = 1 := by
  rcases frontier_row hl hx hnf with ⟨hlf, -, hc⟩ | ⟨hlf, e, -⟩
  · unfold lvl; rw [PT.depth_child hc, if_pos hlf]; push_cast; ring
  · unfold lvl; rw [e, if_neg (by simp [hlf])]; ring

/-! ## Sides -/

lemma side_c1 {y x : ℕ} (hc : T.IsChild y (y + 1)) (e : T.pos x = y + 1) : T.side x = 1 := by
  unfold side; rw [e, if_pos (by simpa using hc)]

lemma not_child_pred_c2 {y : ℕ} (hc : T.IsChild y (T.c2 y)) :
    ¬ T.IsChild (T.c2 y - 1) (T.c2 y) := by
  have hy := hc.1
  have har : 1 ≤ T.ar y := by rcases hc with ⟨-, ⟨h1, -⟩ | ⟨h1, -⟩⟩ <;> omega
  have n1 : T.nd (y + 1) = true := by
    rcases (show T.ar y = 1 ∨ T.ar y = 2 by have := T.ar_le y hy; omega) with e | e
    · exact (T.un y hy e).1
    · exact (T.bin y hy e).1
  have hlt := T.lt_fe _ n1
  intro hcp
  have h1 := hcp.anc.2.2.2
  have hanc : T.Anc (y + 1) (T.c2 y - 1) :=
    ⟨n1, hcp.1, by unfold PT.c2; omega, by unfold PT.c2; omega⟩
  have h2 := hanc.fe_le
  unfold PT.c2 at *; omega

lemma side_c2 {y x : ℕ} (hc : T.IsChild y (T.c2 y)) (e : T.pos x = T.c2 y) : T.side x = 0 := by
  unfold side; rw [e, if_neg (not_child_pred_c2 hc)]

lemma side_le (x : ℕ) : T.side x ≤ 1 := by unfold side; split_ifs <;> omega

/-! ## Coordinates of gates -/

lemma QY_live {h : ℕ} (hl : T.live S Qd st h0 h = true) :
    T.QY S Qd st h0 h = T.lvl S h0 (T.pos h) := by simp [QY, hl]

lemma QY_nl {h : ℕ} (hl : T.live S Qd st h0 h = false) : T.QY S Qd st h0 h = 0 := by
  simp [QY, hl]

lemma QY_nonneg (h : ℕ) : 0 ≤ T.QY S Qd st h0 h := by
  cases hl : T.live S Qd st h0 h
  · rw [QY_nl hl]
  · rw [QY_live hl]; have := lvl_pos hl; omega

lemma QX_live {h : ℕ} (hl : T.live S Qd st h0 h = true) :
    T.QX S Qd st h0 h = 2 * T.ix h + 1 - ty h := by simp [QX, hl]

lemma QX_fr {h : ℕ} (hf : T.QFr S Qd st h0 h) : T.QX S Qd st h0 h = 2 * T.ix h + T.side h := by
  simp [QX, hf.2, hf]

lemma QX_iso {h : ℕ} (hl : T.live S Qd st h0 h = false) (hf : ¬ T.QFr S Qd st h0 h) :
    T.QX S Qd st h0 h = 2 * T.Wm + 2 + h := by simp [QX, hl, hf]

lemma ty_le (h : ℕ) : ty h ≤ 1 := by unfold ty; omega

/-- Shape of an edge of the query circuit. -/
lemma edge_shape (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {g x : ℕ}
    (he : T.QE S Qd st h0 g x) :
    (T.live S Qd st h0 x = true ∧
      ((T.pos x = T.pos g ∧ T.QY S Qd st h0 x = T.QY S Qd st h0 g) ∨
        (T.IsChild (T.pos g) (T.pos x) ∧ T.QY S Qd st h0 x = T.QY S Qd st h0 g - 1))) ∨
    (T.live S Qd st h0 x = false ∧ T.QFr S Qd st h0 x ∧ T.QY S Qd st h0 g = 1 ∧
      T.QY S Qd st h0 x = 0 ∧ ¬ T.NF S (T.pos g) (T.pos x)) := by
  have hl := he.1
  rcases edge_cases hck hd hcl he with ⟨hlx, e | hc⟩ | ⟨hlx, hnf⟩
  · left; exact ⟨hlx, Or.inl ⟨e, by rw [QY_live hlx, QY_live hl, e]⟩⟩
  · left; exact ⟨hlx, Or.inr ⟨hc, by rw [QY_live hlx, QY_live hl, lvl_child hc]⟩⟩
  · right
    exact ⟨hlx, ⟨⟨g, he⟩, hlx⟩, by rw [QY_live hl]; exact lvl_frontier hl he.2.1 hnf,
      QY_nl hlx, hnf⟩

/-- Edges inside a row join consecutive abscissae. -/
lemma same_row_X {g x : ℕ} (he : T.QE S Qd st h0 g x) (hlx : T.live S Qd st h0 x = true)
    (e : T.pos x = T.pos g) : T.QX S Qd st h0 x = T.QX S Qd st h0 g + 1 := by
  have hl := he.1
  rw [QX_live hl, QX_live hlx]
  rcases gate_arg_shape (live_spec hl).1 he.2.1 with ⟨-, -, ⟨a, b, c⟩ | ⟨a, b, c⟩⟩ | ⟨hc, -⟩
  · rw [a, b, c]; omega
  · rw [a, b, c]; omega
  · have := hc.lt; omega

/-- Edges to a child row. -/
lemma child_X (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {g x : ℕ}
    (he : T.QE S Qd st h0 g x) (hne : T.pos x ≠ T.pos g) :
    T.ix x = T.ix g + (if T.kd (T.pos g) = 4 then 1 else 0) ∧
      2 * T.ix x ≤ T.QX S Qd st h0 x ∧ T.QX S Qd st h0 x ≤ 2 * T.ix x + 1 ∧
      (T.kd (T.pos g) = 5 → ty g = 1 → T.QX S Qd st h0 x = 2 * T.ix x) := by
  have hl := he.1
  rcases gate_arg_shape (live_spec hl).1 he.2.1 with ⟨e, -⟩ | ⟨hc, ht, hix, hU⟩
  · exact absurd e hne
  refine ⟨hix, ?_⟩
  rcases edge_shape hck hd hcl he with ⟨hlx, -⟩ | ⟨-, hf, -⟩
  · rw [QX_live hlx, ht]; exact ⟨by omega, by omega, fun _ _ => by omega⟩
  · rw [QX_fr hf]
    refine ⟨by omega, by have := side_le (T := T) x; omega, fun h5 h1 => ?_⟩
    have e2 := hU h5 h1
    rw [side_c2 (e2 ▸ hc) e2]; omega

/-- Facts about a frontier input. -/
lemma fr_facts (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {x : ℕ}
    (hf : T.QFr S Qd st h0 x) :
    x < T.Ng ∧ ty x = 1 ∧ T.ix x < T.Wm ∧
      ((T.leaf (T.rd S h0) = true ∧ T.pos x = T.rd S h0) ∨
        (T.leaf (T.rd S h0) = false ∧ T.IsChild (T.rd S h0) (T.pos x))) := by
  obtain ⟨⟨g, he⟩, hlx⟩ := hf
  have hl := he.1
  have hA := (live_spec hl).1
  have hxN := ((gate_AO hA).2.2.2.2 x he.2.1).2.1
  have hnf : ¬ T.NF S (T.pos g) (T.pos x) := by
    rcases edge_cases hck hd hcl he with ⟨h1, -⟩ | ⟨-, h2⟩
    · rw [h1] at hlx; exact absurd hlx (by simp)
    · exact h2
  have ht : ty x = 1 := by
    rcases gate_arg_shape hA he.2.1 with ⟨e, -⟩ | ⟨-, ht, -⟩
    · exact absurd (Or.inl e) hnf
    · exact ht
  refine ⟨hxN, ht, (idx_decode hxN).2.2.1, ?_⟩
  rcases frontier_row hl he.2.1 hnf with ⟨a, b, -⟩ | ⟨a, -, c⟩
  · exact Or.inl ⟨a, b⟩
  · exact Or.inr ⟨a, c⟩

lemma eq_of_idx {a b : ℕ} (ha : a < T.Ng) (hb : b < T.Ng) (hp : T.pos a = T.pos b)
    (hi : T.ix a = T.ix b) (ht : ty a = ty b) : a = b := by
  rw [← (idx_decode ha).1, ← (idx_decode hb).1, hp, hi, ht]

/-- **Different gates are drawn at different points.** -/
lemma Q_inj (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {a b : ℕ}
    (hx : T.QX S Qd st h0 a = T.QX S Qd st h0 b) (hy : T.QY S Qd st h0 a = T.QY S Qd st h0 b) :
    a = b := by
  cases hla : T.live S Qd st h0 a <;> cases hlb : T.live S Qd st h0 b
  · by_cases hfa : T.QFr S Qd st h0 a <;> by_cases hfb : T.QFr S Qd st h0 b
    · rw [QX_fr hfa, QX_fr hfb] at hx
      obtain ⟨a1, a2, a3, a4⟩ := fr_facts hck hd hcl hfa
      obtain ⟨b1, b2, b3, b4⟩ := fr_facts hck hd hcl hfb
      have sa := side_le (T := T) a
      have sb := side_le (T := T) b
      have hi : T.ix a = T.ix b := by omega
      have hs : T.side a = T.side b := by omega
      refine eq_of_idx a1 b1 ?_ hi (a2.trans b2.symm)
      rcases a4 with ⟨l1, e1⟩ | ⟨l1, c1⟩ <;> rcases b4 with ⟨l2, e2⟩ | ⟨l2, c2⟩
      · rw [e1, e2]
      · rw [l1] at l2; exact absurd l2 (by simp)
      · rw [l1] at l2; exact absurd l2 (by simp)
      · rcases PT.child_eq_cases c1 with f1 | f1 <;> rcases PT.child_eq_cases c2 with f2 | f2
        · rw [f1, f2]
        · rw [side_c1 (f1 ▸ c1) f1, side_c2 (f2 ▸ c2) f2] at hs; omega
        · rw [side_c2 (f1 ▸ c1) f1, side_c1 (f2 ▸ c2) f2] at hs; omega
        · rw [f1, f2]
    · rw [QX_fr hfa, QX_iso hlb hfb] at hx
      obtain ⟨-, -, a3, -⟩ := fr_facts hck hd hcl hfa
      have := side_le (T := T) a; omega
    · rw [QX_iso hla hfa, QX_fr hfb] at hx
      obtain ⟨-, -, b3, -⟩ := fr_facts hck hd hcl hfb
      have := side_le (T := T) b; omega
    · rw [QX_iso hla hfa, QX_iso hlb hfb] at hx; omega
  · rw [QY_nl hla, QY_live hlb] at hy; have := lvl_pos hlb; omega
  · rw [QY_live hla, QY_nl hlb] at hy; have := lvl_pos hla; omega
  · rw [QY_live hla, QY_live hlb] at hy
    rw [QX_live hla, QX_live hlb] at hx
    have hp := pos_eq_of_lvl hla hlb hy
    have ta := ty_le a; have tb := ty_le b
    exact eq_of_idx (gate_AO (live_spec hla).1).1 (gate_AO (live_spec hlb).1).1 hp (by omega)
      (by omega)

lemma pos_ne_of_drop (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {g x : ℕ}
    (he : T.QE S Qd st h0 g x) (hy : T.QY S Qd st h0 g = T.QY S Qd st h0 x + 1) :
    T.pos x ≠ T.pos g := by
  rcases edge_shape hck hd hcl he with ⟨-, ⟨-, e⟩ | ⟨hc, -⟩⟩ | ⟨-, -, -, -, hnf⟩
  · omega
  · have := hc.lt; omega
  · exact fun e => hnf (Or.inl e)

/-- **Edges between two adjacent lines do not cross.** -/
lemma Q_cross (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {a a' b b' : ℕ}
    (ha : T.QE S Qd st h0 a a') (hb : T.QE S Qd st h0 b b')
    (hya : T.QY S Qd st h0 a = T.QY S Qd st h0 a' + 1)
    (hyb : T.QY S Qd st h0 b = T.QY S Qd st h0 b' + 1)
    (hab : T.QY S Qd st h0 a = T.QY S Qd st h0 b)
    (hx : T.QX S Qd st h0 a < T.QX S Qd st h0 b) :
    T.QX S Qd st h0 a' ≤ T.QX S Qd st h0 b' := by
  have hla := ha.1
  have hlb := hb.1
  have hp : T.pos a = T.pos b := by
    rw [QY_live hla, QY_live hlb] at hab; exact pos_eq_of_lvl hla hlb hab
  obtain ⟨ia, la, ua, Ua⟩ := child_X hck hd hcl ha (pos_ne_of_drop hck hd hcl ha hya)
  obtain ⟨ib, lb, ub, -⟩ := child_X hck hd hcl hb (pos_ne_of_drop hck hd hcl hb hyb)
  rw [hp] at ia Ua
  rw [QX_live hla, QX_live hlb] at hx
  have ta := ty_le a; have tb := ty_le b
  rcases lt_trichotomy (T.ix a) (T.ix b) with h | h | h
  · split_ifs at ia ib <;> omega
  · have hta : ty a = 1 := by omega
    have htb : ty b = 0 := by omega
    have h5 := aux_U (live_spec hlb).1 htb
    rw [Ua h5 hta]
    split_ifs at ia ib <;> omega
  · omega

/-! ## The query circuit -/

lemma mem_qsysR_args {β : Bool} {g x : ℕ} :
    x ∈ (T.qsysR S Qd st h0 β g).args ↔ T.QE S Qd st h0 g x := by
  unfold qsysR GS.qsys QE
  split_ifs with hl
  · simp [List.mem_filter, hl]
  · simp [hl]

lemma qsysR_input {β : Bool} {g : ℕ} :
    (T.qsysR S Qd st h0 β g).IsInput ↔ T.live S Qd st h0 g = false := by
  unfold qsysR GS.qsys
  split_ifs with hl
  · rcases live_kind S Qd st h0 g hl with e | e <;> simp [Gate.IsInput, e, hl]
  · simp [Gate.IsInput, hl]

section Circ

variable (T S Qd st h0) in
/-- Abscissae of the vertices of the query circuit with apex. -/
noncomputable def OX {n : ℕ} : Option (Fin n) → ℝ
  | none => ((0 : ℕ) : ℝ)
  | some i => (T.QX S Qd st h0 i.val : ℝ)

variable (T S Qd st h0) in
/-- Lines of the vertices of the query circuit with apex. -/
noncomputable def OY {n : ℕ} : Option (Fin n) → ℤ
  | none => -1
  | some i => T.QY S Qd st h0 i.val

variable {β : Bool}

lemma qget (i : Fin (GS.pre (T.qsysR S Qd st h0 β) h0).length) :
    (GS.pre (T.qsysR S Qd st h0 β) h0)[i] = T.qsysR S Qd st h0 β i.val :=
  GS.pre_getElem _ _ _ i.isLt

lemma adj_ss (i j : Fin (GS.pre (T.qsysR S Qd st h0 β) h0).length) :
    (GS.pre (T.qsysR S Qd st h0 β) h0).apexAdj (some i) (some j) ↔
      T.QE S Qd st h0 i.val j.val ∨ T.QE S Qd st h0 j.val i.val := by
  simp only [Circuit.apexAdj, qget, mem_qsysR_args]

lemma adj_sn (i : Fin (GS.pre (T.qsysR S Qd st h0 β) h0).length) :
    (GS.pre (T.qsysR S Qd st h0 β) h0).apexAdj (some i) none ↔
      T.live S Qd st h0 i.val = false := by
  simp only [Circuit.apexAdj, qget, qsysR_input]

lemma adj_ns (i : Fin (GS.pre (T.qsysR S Qd st h0 β) h0).length) :
    (GS.pre (T.qsysR S Qd st h0 β) h0).apexAdj none (some i) ↔
      T.live S Qd st h0 i.val = false := by
  simp only [Circuit.apexAdj, qget, qsysR_input]

lemma adj_nn : ¬ (GS.pre (T.qsysR S Qd st h0 β) h0).apexAdj none none := by
  simp [Circuit.apexAdj]

lemma OY_ge {n : ℕ} (v : Option (Fin n)) : -1 ≤ T.OY S Qd st h0 v := by
  cases v with
  | none => simp [OY]
  | some i => have := QY_nonneg (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) i.val
              simp only [OY]; omega

lemma edge_drop (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) {g x : ℕ}
    (he : T.QE S Qd st h0 g x) : T.QY S Qd st h0 x ≤ T.QY S Qd st h0 g := by
  rcases edge_shape hck hd hcl he with ⟨-, ⟨-, e⟩ | ⟨-, e⟩⟩ | ⟨-, -, e1, e2, -⟩ <;> omega

/-- **The query circuit has a layered drawing.** -/
theorem query_layered (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) :
    Layered (GS.pre (T.qsysR S Qd st h0 β) h0).apexAdj (T.OX S Qd st h0) (T.OY S Qd st h0) where
  symm := by
    rintro (_ | i) (_ | j) h
    · exact absurd h adj_nn
    · exact (adj_sn j).2 ((adj_ns j).1 h)
    · exact (adj_ns i).2 ((adj_sn i).1 h)
    · exact (adj_ss j i).2 ((adj_ss i j).1 h).symm
  inj := by
    rintro (_ | i) (_ | j) hx hy
    · rfl
    · have := QY_nonneg (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) j.val
      simp only [OY] at hy; omega
    · have := QY_nonneg (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) i.val
      simp only [OY] at hy; omega
    · simp only [OX, Nat.cast_inj] at hx
      simp only [OY] at hy
      exact congrArg some (Fin.ext (Q_inj hck hd hcl hx hy))
  band := by
    rintro (_ | i) (_ | j) h
    · exact absurd h adj_nn
    · simp only [OY, QY_nl ((adj_ns j).1 h)]; omega
    · simp only [OY, QY_nl ((adj_sn i).1 h)]; omega
    · simp only [OY]
      rcases (adj_ss i j).1 h with he | he <;>
        rcases edge_shape hck hd hcl he with ⟨-, ⟨-, e⟩ | ⟨-, e⟩⟩ | ⟨-, -, e1, e2, -⟩ <;> omega
  hor := by
    rintro (_ | i) (_ | j) w h hy hw ⟨h1, h2⟩
    · exact absurd h adj_nn
    · have := QY_nonneg (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) j.val
      simp only [OY] at hy; omega
    · have := QY_nonneg (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) i.val
      simp only [OY] at hy; omega
    · simp only [OY] at hy
      obtain ⟨m, hm⟩ : ∃ m : ℕ, T.OX S Qd st h0 w = (m : ℝ) := by
        cases w with
        | none => exact ⟨0, rfl⟩
        | some k => exact ⟨_, rfl⟩
      rw [hm] at h1 h2
      simp only [OX] at h1 h2
      have h1' : T.QX S Qd st h0 i.val < m := by exact_mod_cast h1
      have h2' : m < T.QX S Qd st h0 j.val := by exact_mod_cast h2
      have hsr : ∀ g x, T.QE S Qd st h0 g x → T.QY S Qd st h0 g = T.QY S Qd st h0 x →
          T.QX S Qd st h0 x = T.QX S Qd st h0 g + 1 := by
        intro g x he hyy
        rcases edge_shape hck hd hcl he with ⟨hlx, ⟨e, -⟩ | ⟨-, e⟩⟩ | ⟨-, -, e1, e2, -⟩
        · exact same_row_X he hlx e
        · omega
        · omega
      rcases (adj_ss i j).1 h with he | he
      · have := hsr _ _ he hy; omega
      · have := hsr _ _ he hy.symm; omega
  cross := by
    intro a a' b b' haa hbb hya hyb hab hx
    have ga := OY_ge (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) a'
    have gb := OY_ge (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) b'
    rcases a with _ | i
    · have e : T.OY S Qd st h0 (none : Option (Fin (GS.pre (T.qsysR S Qd st h0 β) h0).length)) =
          -1 := rfl
      omega
    rcases b with _ | j
    · have e : T.OY S Qd st h0 (none : Option (Fin (GS.pre (T.qsysR S Qd st h0 β) h0).length)) =
          -1 := rfl
      omega
    have down : ∀ (g : Fin (GS.pre (T.qsysR S Qd st h0 β) h0).length) g',
        (GS.pre (T.qsysR S Qd st h0 β) h0).apexAdj (some g) (some g') →
        T.QY S Qd st h0 g.val = T.QY S Qd st h0 g'.val + 1 → T.QE S Qd st h0 g.val g'.val := by
      intro g g' hadj hy
      rcases (adj_ss g g').1 hadj with he | he
      · exact he
      · have := edge_drop hck hd hcl he; omega
    rcases a' with _ | i'
    · have hli := (adj_sn i).1 haa
      simp only [OY, QY_nl hli] at hya hab
      rcases b' with _ | j'
      · exact le_refl _
      · have := QY_nonneg (T := T) (S := S) (Qd := Qd) (st := st) (h0 := h0) j'.val
        simp only [OY] at hyb; omega
    · simp only [OY] at hya hab
      have hei := down i i' haa hya
      have hpos := lvl_pos hei.1
      rw [← QY_live hei.1] at hpos
      rcases b' with _ | j'
      · simp only [OY] at hyb; omega
      · simp only [OY] at hyb
        have hej := down j j' hbb hyb
        simp only [OX, Nat.cast_le, Nat.cast_lt] at hx ⊢
        exact Q_cross hck hd hcl hei hej hya hyb hab hx

/-- **The query circuits are instances of the one-input-face monotone planar circuit value
problem.** -/
theorem query_oif (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) :
    OIFMCVPInstance (GS.pre (T.qsysR S Qd st h0 β) h0) := by
  refine ⟨⟨by simp [GS.pre], fun i hi => ⟨?_, ?_⟩⟩, ?_, ⟨(query_layered hck hd hcl).drawing⟩⟩
  · intro j hj
    rw [GS.pre_getElem] at hj
    exact GS.qsys_ordered gate_ordered st _ _ β i j hj
  · rw [GS.pre_getElem]
    unfold qsysR GS.qsys
    split_ifs with hl
    · rcases live_kind S Qd st h0 i hl with e | e <;> simp [e]
    · simp
  · intro g hg
    simp only [GS.pre, List.mem_map, List.mem_range] at hg
    obtain ⟨i, -, rfl⟩ := hg
    unfold qsysR GS.qsys
    split_ifs with hl
    · right
      refine ⟨live_kind S Qd st h0 i hl, ?_, le_trans (List.length_filter_le _ _) (gate_args_le i)⟩
      obtain ⟨hA, hu, hr⟩ := live_spec hl
      obtain ⟨x, hx, hx'⟩ := (hcl i hA hu hr.1).2
      have hk : T.keep S st i x = true := by
        rcases hx' with h1 | h1 <;> simp [keep, h1]
      exact List.length_pos_of_mem (List.mem_filter.2 ⟨hx, hk⟩)
    · left; exact ⟨_, rfl, rfl⟩

end Circ

end FT

end PathChecking
