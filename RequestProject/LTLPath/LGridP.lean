module

public import RequestProject.LTLPath.LGrid

/-!
# Correctness of the grid drawing of layered systems

`LSys.circ_strat`: the grid drawing of a layered system is a stratified monotone planar circuit.
`LSys.circ_eval`: its value is the value of the output gate.
-/

@[expose] public section

namespace PathChecking

namespace LG

open Grid Classical

namespace LSys

variable {L : LSys} {M Cmax : ℕ}

/-- The value of a grid gate from the values of its diagonal and straight inputs. -/
def comb (k : GateKind) (sb db ds ss : Bool) : Bool :=
  match k with
  | .and => (!db || ds) && (!sb || ss)
  | .or => (db && ds) || (sb && ss)
  | _ => false

/-! ## Arguments -/

lemma col_even (h : ℕ) : L.col M h % 2 = 0 := by unfold col; omega

lemma isR_iff {h x : ℕ} : L.isR h x = true ↔ L.live x = true ∧ L.Y x = L.Y h := by
  simp [isR]

lemma mem_nonR {h x : ℕ} : x ∈ L.nonR h ↔ x ∈ (L.g h).args ∧ L.isR h x = false := by
  simp [nonR]

lemma sArg_or_dArg {h x : ℕ} (hlen : (L.nonR h).length ≤ 2) (hx : x ∈ L.nonR h) :
    L.sArg h = some x ∨ L.dArg h = some x := by
  unfold sArg dArg
  rcases hn : L.nonR h with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> rw [hn] at hx hlen
  · simp at hx
  · simp only [List.mem_singleton] at hx; simp [hx]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    by_cases hab : a = b
    · subst hab; rcases hx with rfl | rfl <;> simp
    · simp only [hab, if_false, Option.some.injEq]
      rcases hx with rfl | rfl
      · rcases le_total x b with h1 | h1
        · right; exact (Nat.min_eq_left h1)
        · left; exact (Nat.max_eq_left h1)
      · rcases le_total a x with h1 | h1
        · left; exact (Nat.max_eq_right h1)
        · right; exact (Nat.min_eq_right h1)
  · simp at hlen <;> omega

lemma sArg_mem {h x : ℕ} (hs : L.sArg h = some x) : x ∈ L.nonR h := by
  unfold sArg at hs
  rcases hn : L.nonR h with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rw [hn] at hs
  · cases hs
  · simp only [Option.some.injEq] at hs; subst hs; simp
  · simp only [Option.some.injEq] at hs; subst hs
    rcases le_total a b with h1 | h1
    · rw [Nat.max_eq_right h1]; simp
    · rw [Nat.max_eq_left h1]; simp

lemma dArg_spec {h z : ℕ} (hd : L.dArg h = some z) :
    z ∈ L.nonR h ∧ ∃ y, L.sArg h = some y ∧ z < y := by
  unfold dArg at hd
  unfold sArg
  rcases hn : L.nonR h with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rw [hn] at hd
  · cases hd
  · cases hd
  · simp only at hd
    split_ifs at hd with hab
    simp only [Option.some.injEq] at hd; subst hd
    refine ⟨?_, max a b, rfl, ?_⟩
    · rcases le_total a b with h1 | h1
      · rw [Nat.min_eq_left h1]; simp
      · rw [Nat.min_eq_right h1]; simp
    · rcases lt_or_gt_of_ne hab with h1 | h1
      · rw [Nat.min_eq_left h1.le, Nat.max_eq_right h1.le]; exact h1
      · rw [Nat.min_eq_right h1.le, Nat.max_eq_left h1.le]; exact h1

lemma sArg_isSome {h : ℕ} : (L.sArg h).isSome = true ↔ L.nonR h ≠ [] := by
  unfold sArg
  rcases L.nonR h with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp

section Hyp

variable (hL : L.OK) (hB : L.Bd M Cmax)
include hL

lemma nonR_len {h : ℕ} (hl : L.live h = true) : (L.nonR h).length ≤ 2 :=
  (List.length_filter_le _ _).trans (hL.len h hl)

lemma R_facts {h x : ℕ} (hl : L.live h = true) (hx : x ∈ (L.g h).args)
    (hr : L.isR h x = true) : L.live x = true ∧ L.Y x = L.Y h ∧ L.X x = L.X h + 1 := by
  rw [isR_iff] at hr
  rcases hL.arg h hl x hx with a | ⟨-, b, -⟩ | ⟨c, -⟩
  · exact a
  · omega
  · rw [c] at hr; cases hr.1

/-- A non-`R` argument is a `V` or an `F` argument. -/
lemma nonR_cases {h x : ℕ} (hl : L.live h = true) (hx : x ∈ L.nonR h) :
    (L.live x = true ∧ L.Y x + 1 = L.Y h ∧ L.X h ≤ L.X x + 1 ∧ L.X x ≤ L.X h + 3) ∨
    (L.live x = false ∧ L.Y h = 1) := by
  rw [mem_nonR] at hx
  rcases hL.arg h hl x hx.1 with a | b | c
  · have : L.isR h x = true := isR_iff.2 ⟨a.1, a.2.1⟩
    rw [hx.2] at this; cases this
  · exact Or.inl b
  · exact Or.inr c

lemma hasR_dArg {h : ℕ} (hl : L.live h = true) (hr : L.hasR h = true) : L.dArg h = none := by
  have hlt : (L.nonR h).length < (L.g h).args.length := by
    unfold hasR at hr
    obtain ⟨r, hr1, hr2⟩ := List.any_eq_true.1 hr
    unfold nonR
    exact List.length_filter_lt_length_iff_exists.2 ⟨r, hr1, by simp [hr2]⟩
  have := hL.len h hl
  unfold dArg
  rcases hn : L.nonR h with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · rfl
  · rw [hn] at hlt; simp at hlt; omega

include hB

lemma gateAt_uniq {b c h h' : ℕ} (e : L.GateAt M b c h) (e' : L.GateAt M b c h') : h = h' := by
  obtain ⟨l, y, cc⟩ := e
  obtain ⟨l', y', cc'⟩ := e'
  have := (hB h l).1; have := (hB h' l').1
  unfold col at cc cc'
  exact hL.inj h h' l l' (by omega) (by omega)

lemma tim_add {h : ℕ} (hl : L.live h = true) : L.tim M Cmax h + L.col M h = 10 * L.Y h + Cmax := by
  unfold tim; have := (hB h hl).2; omega

lemma tim_ge {h : ℕ} (hl : L.live h = true) : 10 ≤ L.tim M Cmax h := by
  have := tim_add hL hB hl; have := hL.ypos h hl; have := (hB h hl).2; omega

/-- Facts about a wire `(h, x)`. -/
lemma wire_facts {h x : ℕ} (hl : L.live h = true) (hx : x ∈ (L.g h).args)
    (hlx : L.live x = true) (hy : L.Y x + 1 = L.Y h) :
    L.col M h ≤ L.slot M h x ∧ L.slot M h x ≤ L.col M x ∧ L.col M x ≤ L.slot M h x + 8 ∧
      (L.slot M h x = L.col M h ∨ L.slot M h x = L.col M h + 1) := by
  have hYh := (hB h hl).1
  have hYx := (hB x hlx).1
  have hxR : L.isR h x = false := by
    cases e : L.isR h x
    · rfl
    · rw [isR_iff] at e; omega
  have hxn : x ∈ L.nonR h := mem_nonR.2 ⟨hx, hxR⟩
  have hX : L.X h ≤ L.X x + 1 ∧ L.X x ≤ L.X h + 3 := by
    rcases nonR_cases hL hl hxn with ⟨-, -, a, b⟩ | ⟨c, -⟩
    · exact ⟨a, b⟩
    · rw [c] at hlx; cases hlx
  unfold slot
  split_ifs with hs
  · unfold col; omega
  · -- the second non-`R` argument
    rcases sArg_or_dArg (nonR_len hL hl) hxn with e | e
    · exact absurd e hs
    obtain ⟨-, y, hy1, hxy⟩ := dArg_spec e
    have hyn := sArg_mem hy1
    have hyV : L.live y = true ∧ L.Y y + 1 = L.Y h ∧ L.X h ≤ L.X y + 1 := by
      rcases nonR_cases hL hl hyn with ⟨a, b, c, -⟩ | ⟨-, c⟩
      · exact ⟨a, b, c⟩
      · have := hL.ypos x hlx; omega
    have hXy : L.X y < L.X x := by
      rcases lt_trichotomy (L.X x) (L.X y) with h1 | h1 | h1
      · have := hL.roword x y hlx hyV.1 (by omega) h1; omega
      · have := hL.inj x y hlx hyV.1 (by omega) h1; omega
      · exact h1
    unfold col; omega

/-- **Different wires do not meet**: the straight part of a wire is not a diagonal step of
another wire. -/
lemma no_conflict {h x : ℕ} (hl : L.live h = true) (hx : x ∈ (L.g h).args)
    (hlx : L.live x = true) (hy : L.Y x + 1 = L.Y h) {j : ℕ}
    (hj : L.col M x - L.slot M h x < j) : ¬ L.DDes M (L.Y x) j (L.slot M h x) := by
  rintro ⟨h', x', hl', hx', hlx', hyx', hy', hc', hs'⟩
  obtain ⟨f1, f2, f3, f4⟩ := wire_facts hL hB hl hx hlx hy
  obtain ⟨g1, g2, g3, g4⟩ := wire_facts hL hB hl' hx' hlx' hy'
  have hYh := (hB h hl).1
  have hYx := (hB x hlx).1
  have hYh' := (hB h' hl').1
  have hYx' := (hB x' hlx').1
  have hXA : L.X x < L.X x' := by
    have hc1 : L.col M x < L.col M x' := by omega
    unfold col at hc1; omega
  have hcol : L.col M h' ≤ L.col M h := by
    have e1 := col_even (L := L) (M := M) h
    have e2 := col_even (L := L) (M := M) h'
    omega
  rcases eq_or_lt_of_le hcol with hc | hc
  · have hh : h' = h := gateAt_uniq hL hB ⟨hl', by omega, hc⟩ ⟨hl, rfl, rfl⟩
    subst hh
    have hxn : x ∈ L.nonR h' := mem_nonR.2 ⟨hx, by
      cases e : L.isR h' x
      · rfl
      · rw [isR_iff] at e; omega⟩
    have hxn' : x' ∈ L.nonR h' := mem_nonR.2 ⟨hx', by
      cases e : L.isR h' x'
      · rfl
      · rw [isR_iff] at e; omega⟩
    unfold slot at *
    by_cases hs : L.sArg h' = some x <;> by_cases hs' : L.sArg h' = some x'
    · rw [hs] at hs'; simp only [Option.some.injEq] at hs'; subst hs'; omega
    · rw [if_pos hs, if_neg hs'] at *; omega
    · rcases sArg_or_dArg (nonR_len hL hl') hxn with e | e
      · exact hs e
      obtain ⟨-, y, hy1, hxy⟩ := dArg_spec e
      have hyx : y = x' := by rw [hs'] at hy1; exact (Option.some.inj hy1).symm
      rw [hyx] at hxy
      have := hL.roword x x' hlx hlx' (by omega) hXA
      omega
    · rcases sArg_or_dArg (nonR_len hL hl') hxn with e | e
      · exact hs e
      rcases sArg_or_dArg (nonR_len hL hl') hxn' with e' | e'
      · exact hs' e'
      rw [e, Option.some.injEq] at e'; subst e'; omega
  · have hX : L.X h' < L.X h := by unfold col at hc; omega
    have := hL.cross h' x' h x hl' hl hx' hx hlx' hlx hy' hy (by omega) hX
    omega

/-! ## Classification of the nodes -/

lemma node_gate {h : ℕ} (hl : L.live h = true) :
    L.node M Cmax (L.col M h) (L.tim M Cmax h) =
      .gt (L.g h).kind (L.sArg h).isSome (L.hasR h || (L.dArg h).isSome) := by
  have ht := tim_add hL hB hl
  have hy := hL.ypos h hl
  have := (hB h hl).2
  have hex : ∃ h', L.GateAt M ((L.tim M Cmax h + L.col M h - Cmax) / 10) (L.col M h) h' :=
    ⟨h, hl, by omega, rfl⟩
  have e : Nat.find hex = h := gateAt_uniq hL hB (Nat.find_spec hex) ⟨hl, by omega, rfl⟩
  unfold node
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_pos (col_even _), dif_pos hex, e]

lemma node_inrow {h : ℕ} (hl : L.live h = true) (hr : L.hasR h = true) :
    L.node M Cmax (L.col M h + 1) (L.tim M Cmax h - 1) = nD := by
  have ht := tim_add hL hB hl
  have hy := hL.ypos h hl
  have := (hB h hl).2
  have he := col_even (L := L) (M := M) h
  unfold node
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos]
  exact ⟨h, ⟨hl, by omega, by omega⟩, hr⟩

lemma node_inrow_S {h : ℕ} (hl : L.live h = true) (hr : L.hasR h = false) :
    L.node M Cmax (L.col M h + 1) (L.tim M Cmax h - 1) = nS := by
  have ht := tim_add hL hB hl
  have hy := hL.ypos h hl
  have := (hB h hl).2
  have he := col_even (L := L) (M := M) h
  unfold node
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_neg]
  rintro ⟨h', hg, hr'⟩
  have := gateAt_uniq hL hB hg ⟨hl, by omega, by omega⟩
  subst this; rw [hr] at hr'; cases hr'

/-- Nodes below band `1` copy straight. -/
lemma node_low {c t : ℕ} (ht : 1 ≤ t) (hc : t + c < Cmax + 10) : L.node M Cmax c t = nS := by
  unfold node
  rw [if_neg (by omega)]
  by_cases h1 : t + c < Cmax
  · rw [if_pos h1]
  rw [if_neg h1]
  have hb : (t + c - Cmax) / 10 = 0 := by omega
  rw [hb]
  split_ifs with h2 h3 h4 h5 h6
  · have := hL.ypos _ (Nat.find_spec h4).1
    have := (Nat.find_spec h4).2.1; omega
  · rfl
  · obtain ⟨h', ⟨hl', hy', -⟩, -⟩ := h5
    have := hL.ypos _ hl'; omega
  · rfl
  · obtain ⟨-, x, -, -, hlx, hyx, -⟩ := h6
    have := hL.ypos _ hlx; omega
  · rfl

/-- Nodes of positive phase. -/
lemma node_phase {c t : ℕ} (ht : 1 ≤ t) (hc : Cmax ≤ t + c) (hφ : (t + c - Cmax) % 10 ≠ 0) :
    L.node M Cmax c t =
      if L.DDes M ((t + c - Cmax) / 10) ((t + c - Cmax) % 10) c then nD else nS := by
  unfold node
  rw [if_neg (by omega), if_neg (by omega), if_neg hφ]

omit hL hB in
lemma not_DDes_odd {b φ c : ℕ} (hp : (c + φ) % 2 = 1) : ¬ L.DDes M b φ c := by
  rintro ⟨-, x, -, -, -, -, -, hc, -⟩
  have := col_even (L := L) (M := M) x
  omega

/-- Shape of the nodes above layer `0`. -/
lemma node_shape {c t : ℕ} (ht : 1 ≤ t) :
    L.node M Cmax c t = nS ∨ (L.node M Cmax c t = nD ∧ c < Cmax) ∨
      ∃ h, L.live h = true ∧ L.col M h = c ∧
        L.node M Cmax c t = .gt (L.g h).kind (L.sArg h).isSome (L.hasR h || (L.dArg h).isSome) := by
  unfold node
  rw [if_neg (by omega)]
  by_cases h1 : t + c < Cmax
  · rw [if_pos h1]; exact Or.inl rfl
  rw [if_neg h1]
  by_cases h2 : (t + c - Cmax) % 10 = 0
  · rw [if_pos h2]
    by_cases h3 : c % 2 = 0
    · rw [if_pos h3]
      by_cases h4 : ∃ h, L.GateAt M ((t + c - Cmax) / 10) c h
      · rw [dif_pos h4]
        exact Or.inr (Or.inr ⟨_, (Nat.find_spec h4).1, (Nat.find_spec h4).2.2, rfl⟩)
      · rw [dif_neg h4]; exact Or.inl rfl
    · rw [if_neg h3]
      by_cases h5 : ∃ h, L.GateAt M ((t + c - Cmax) / 10) (c - 1) h ∧ L.hasR h = true
      · rw [if_pos h5]
        obtain ⟨h', ⟨hl', -, hc'⟩, -⟩ := h5
        have := (hB h' hl').2
        exact Or.inr (Or.inl ⟨rfl, by omega⟩)
      · rw [if_neg h5]; exact Or.inl rfl
  · rw [if_neg h2]
    by_cases h6 : L.DDes M ((t + c - Cmax) / 10) ((t + c - Cmax) % 10) c
    · rw [if_pos h6]
      obtain ⟨-, x, -, -, hlx, -, -, hc', -⟩ := h6
      have := (hB x hlx).2
      exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · rw [if_neg h6]; exact Or.inl rfl

/-! ## Values -/

variable (c0 : ℕ)

omit hL hB in
lemma gv_S {c t : ℕ} (hc : c0 ≤ c) (hn : L.node M Cmax c (t + 1) = nS) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (t + 1) (c - c0) =
      Grid.gv (fun t j => L.node M Cmax (c0 + j) t) t (c - c0) := by
  have e : L.node M Cmax (c0 + (c - c0)) (t + 1) = nS := by
    rw [show c0 + (c - c0) = c by omega]; exact hn
  simp only [Grid.gv, e, nS]
  simp

omit hL hB in
lemma gv_D {c t : ℕ} (hc : c0 ≤ c) (hn : L.node M Cmax c (t + 1) = nD) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (t + 1) (c - c0) =
      Grid.gv (fun t j => L.node M Cmax (c0 + j) t) t (c + 1 - c0) := by
  have e : L.node M Cmax (c0 + (c - c0)) (t + 1) = nD := by
    rw [show c0 + (c - c0) = c by omega]; exact hn
  simp only [Grid.gv, e, nD]
  rw [show c + 1 - c0 = c - c0 + 1 by omega]
  simp

omit hL hB in
lemma gv_zero {c : ℕ} (hc : c0 ≤ c) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) 0 (c - c0) = L.colConst M c := by
  have e : L.node M Cmax (c0 + (c - c0)) 0 = .cst (L.colConst M c) := by
    rw [show c0 + (c - c0) = c by omega]; unfold node; rw [if_pos rfl]
  simp only [Grid.gv, e]

omit hL hB in
lemma gv_gate {c t : ℕ} {k : GateKind} {sb db : Bool} (hc : c0 ≤ c)
    (hn : L.node M Cmax c (t + 1) = .gt k sb db) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (t + 1) (c - c0) =
      comb k sb db (Grid.gv (fun t j => L.node M Cmax (c0 + j) t) t (c + 1 - c0))
        (Grid.gv (fun t j => L.node M Cmax (c0 + j) t) t (c - c0)) := by
  have e : L.node M Cmax (c0 + (c - c0)) (t + 1) = .gt k sb db := by
    rw [show c0 + (c - c0) = c by omega]; exact hn
  rw [show c + 1 - c0 = c - c0 + 1 by omega]
  cases k <;> simp only [Grid.gv, e, comb]

omit hB in
lemma val_const {x : ℕ} (hlx : L.live x = false) : GS.val L.g x = cval (L.g x) := by
  obtain ⟨b, hb⟩ := hL.cst x hlx
  rw [GS.val_spec hL.ord, hb]
  simp [Gate.evalFn, cval]

/-- The first part of a wire: diagonal steps. -/
lemma wire_diag {h x : ℕ} (hl : L.live h = true) (hx : x ∈ (L.g h).args)
    (hlx : L.live x = true) (hy : L.Y x + 1 = L.Y h) (hc0 : c0 ≤ L.col M h)
    (hsrc : Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax x) (L.col M x - c0) =
      GS.val L.g x) :
    ∀ j, 1 ≤ j → j ≤ L.col M x - L.slot M h x →
      Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax x + 2 * j)
        (L.col M x - j - c0) = GS.val L.g x := by
  obtain ⟨f1, f2, f3, f4⟩ := wire_facts hL hB hl hx hlx hy
  have hta := tim_add hL hB hlx
  have hyx := hL.ypos x hlx
  have hDD : ∀ j, 1 ≤ j → j ≤ L.col M x - L.slot M h x →
      L.node M Cmax (L.col M x - j) (L.tim M Cmax x + 2 * j) = nD := by
    intro j hj1 hj2
    rw [node_phase hL hB (by omega) (by omega) (by omega), if_pos]
    have e1 : (L.tim M Cmax x + 2 * j + (L.col M x - j) - Cmax) / 10 = L.Y x := by omega
    have e2 : (L.tim M Cmax x + 2 * j + (L.col M x - j) - Cmax) % 10 = j := by omega
    rw [e1, e2]
    exact ⟨h, x, hl, hx, hlx, rfl, hy, by omega, by omega⟩
  have hSS : ∀ j, 1 ≤ j → j ≤ L.col M x - L.slot M h x →
      L.node M Cmax (L.col M x - j + 1) (L.tim M Cmax x + 2 * j - 1) = nS := by
    intro j hj1 hj2
    rw [node_phase hL hB (by omega) (by omega) (by omega), if_neg]
    apply not_DDes_odd
    have := col_even (L := L) (M := M) x
    omega
  intro j hj1 hj2
  induction j, hj1 using Nat.le_induction with
  | base =>
    have e := gv_D c0 (t := L.tim M Cmax x + 1) (c := L.col M x - 1) (by omega)
      (hDD 1 le_rfl hj2)
    rw [show L.tim M Cmax x + 2 * 1 = L.tim M Cmax x + 1 + 1 by omega, e,
      show L.col M x - 1 + 1 - c0 = L.col M x - c0 by omega]
    have e' := gv_S c0 (t := L.tim M Cmax x) (c := L.col M x) (by omega)
      (by have := hSS 1 le_rfl hj2; rwa [show L.col M x - 1 + 1 = L.col M x by omega,
        show L.tim M Cmax x + 2 * 1 - 1 = L.tim M Cmax x + 1 by omega] at this)
    rw [e', hsrc]
  | succ j hj ih =>
    have e := gv_D c0 (t := L.tim M Cmax x + 2 * j + 1) (c := L.col M x - (j + 1)) (by omega)
      (by have := hDD (j + 1) (by omega) hj2
          rwa [show L.tim M Cmax x + 2 * (j + 1) = L.tim M Cmax x + 2 * j + 1 + 1 by omega] at this)
    rw [show L.tim M Cmax x + 2 * (j + 1) = L.tim M Cmax x + 2 * j + 1 + 1 by omega, e,
      show L.col M x - (j + 1) + 1 - c0 = L.col M x - j - c0 by omega]
    have e' := gv_S c0 (t := L.tim M Cmax x + 2 * j) (c := L.col M x - j) (by omega)
      (by have := hSS (j + 1) (by omega) hj2
          rwa [show L.col M x - (j + 1) + 1 = L.col M x - j by omega,
            show L.tim M Cmax x + 2 * (j + 1) - 1 = L.tim M Cmax x + 2 * j + 1 by omega] at this)
    rw [e', ih (by omega)]

/-- The second part of a wire: straight up the slot. -/
lemma wire_run {h x : ℕ} (hl : L.live h = true) (hx : x ∈ (L.g h).args)
    (hlx : L.live x = true) (hy : L.Y x + 1 = L.Y h) (hc0 : c0 ≤ L.col M h)
    (hsrc : Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax x) (L.col M x - c0) =
      GS.val L.g x) :
    ∀ j, L.col M x - L.slot M h x ≤ j → j ≤ 9 →
      Grid.gv (fun t j => L.node M Cmax (c0 + j) t)
        (L.tim M Cmax x + (L.col M x - L.slot M h x) + j) (L.slot M h x - c0) = GS.val L.g x := by
  obtain ⟨f1, f2, f3, f4⟩ := wire_facts hL hB hl hx hlx hy
  have hta := tim_add hL hB hlx
  have hyx := hL.ypos x hlx
  intro j hj1 hj2
  induction j, hj1 using Nat.le_induction with
  | base =>
    rcases Nat.eq_zero_or_pos (L.col M x - L.slot M h x) with e | e
    · rw [e, show L.slot M h x = L.col M x by omega]; simpa using hsrc
    · have := wire_diag hL hB c0 hl hx hlx hy hc0 hsrc _ e le_rfl
      rw [show L.tim M Cmax x + (L.col M x - L.slot M h x) + (L.col M x - L.slot M h x) =
        L.tim M Cmax x + 2 * (L.col M x - L.slot M h x) by ring,
        show L.slot M h x - c0 = L.col M x - (L.col M x - L.slot M h x) - c0 by omega]
      exact this
  | succ j hj ih =>
    have hn : L.node M Cmax (L.slot M h x)
        (L.tim M Cmax x + (L.col M x - L.slot M h x) + j + 1) = nS := by
      rw [node_phase hL hB (by omega) (by omega) (by omega), if_neg]
      have e1 : (L.tim M Cmax x + (L.col M x - L.slot M h x) + j + 1 + L.slot M h x - Cmax) / 10 =
          L.Y x := by omega
      have e2 : (L.tim M Cmax x + (L.col M x - L.slot M h x) + j + 1 + L.slot M h x - Cmax) % 10 =
          j + 1 := by omega
      rw [e1, e2]
      exact no_conflict hL hB hl hx hlx hy (by omega)
    rw [← Nat.add_assoc, gv_S c0 (by omega) hn, ih (by omega)]

/-- The value of the straight slot fed by a wire. -/
lemma wire_slot_s {h x : ℕ} (hl : L.live h = true) (hx : x ∈ (L.g h).args)
    (hlx : L.live x = true) (hy : L.Y x + 1 = L.Y h) (hc0 : c0 ≤ L.col M h)
    (hs : L.sArg h = some x)
    (hsrc : Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax x) (L.col M x - c0) =
      GS.val L.g x) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax h - 1) (L.col M h - c0) =
      GS.val L.g x := by
  obtain ⟨f1, f2, f3, f4⟩ := wire_facts hL hB hl hx hlx hy
  have hT : L.slot M h x = L.col M h := by unfold slot; rw [if_pos hs]
  have := wire_run hL hB c0 hl hx hlx hy hc0 hsrc 9 (by omega) le_rfl
  have hta := tim_add hL hB hlx
  have htb := tim_add hL hB hl
  rw [hT] at this
  rwa [show L.tim M Cmax x + (L.col M x - L.col M h) + 9 = L.tim M Cmax h - 1 by omega] at this

/-- The value of the diagonal slot fed by a wire. -/
lemma wire_slot_d {h x : ℕ} (hl : L.live h = true) (hx : x ∈ (L.g h).args)
    (hlx : L.live x = true) (hy : L.Y x + 1 = L.Y h) (hc0 : c0 ≤ L.col M h)
    (hs : L.sArg h ≠ some x) (hr : L.hasR h = false)
    (hsrc : Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax x) (L.col M x - c0) =
      GS.val L.g x) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax h - 1) (L.col M h + 1 - c0) =
      GS.val L.g x := by
  obtain ⟨f1, f2, f3, f4⟩ := wire_facts hL hB hl hx hlx hy
  have hT : L.slot M h x = L.col M h + 1 := by unfold slot; rw [if_neg hs]
  have := wire_run hL hB c0 hl hx hlx hy hc0 hsrc 9 (by omega) le_rfl
  have hta := tim_add hL hB hlx
  have htb := tim_add hL hB hl
  have hge := tim_ge hL hB hl
  rw [hT] at this
  rw [show L.tim M Cmax x + (L.col M x - (L.col M h + 1)) + 9 = L.tim M Cmax h - 2 by omega] at this
  have hn := node_inrow_S hL hB hl hr
  rw [show L.tim M Cmax h - 1 = L.tim M Cmax h - 2 + 1 by omega] at hn ⊢
  rw [gv_S c0 (by omega) hn, this]

/-- The value of the straight slot fed by a constant. -/
lemma front_slot_s {h x : ℕ} (hl : L.live h = true) (hc0 : c0 ≤ L.col M h)
    (hs : L.sArg h = some x) (hlx : L.live x = false) (hy : L.Y h = 1) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax h - 1) (L.col M h - c0) =
      GS.val L.g x := by
  have htb := tim_add hL hB hl
  have key : ∀ t, t ≤ L.tim M Cmax h - 1 →
      Grid.gv (fun t j => L.node M Cmax (c0 + j) t) t (L.col M h - c0) = GS.val L.g x := by
    intro t ht
    induction t with
    | zero =>
      rw [gv_zero c0 hc0, val_const hL hlx]
      unfold colConst
      cases hv : cval (L.g x)
      · rw [decide_eq_false]
        rintro (⟨h', x', hg, hs', -, hv'⟩ | ⟨-, -, -, hodd, -⟩)
        · have := gateAt_uniq hL hB hg ⟨hl, hy, rfl⟩
          subst this; rw [hs, Option.some.injEq] at hs'; subst hs'; rw [hv] at hv'; cases hv'
        · have := col_even (L := L) (M := M) h; omega
      · rw [decide_eq_true]; exact Or.inl ⟨h, x, ⟨hl, hy, rfl⟩, hs, hlx, hv⟩
    | succ t ih =>
      rw [gv_S c0 hc0 (node_low hL hB (by omega) (by omega)), ih (by omega)]
  exact key _ le_rfl

/-- The value of the diagonal slot fed by a constant. -/
lemma front_slot_d {h x : ℕ} (hl : L.live h = true) (hc0 : c0 ≤ L.col M h)
    (hd : L.dArg h = some x) (hlx : L.live x = false) (hy : L.Y h = 1) (hr : L.hasR h = false) :
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax h - 1) (L.col M h + 1 - c0) =
      GS.val L.g x := by
  have htb := tim_add hL hB hl
  have hge := tim_ge hL hB hl
  have he := col_even (L := L) (M := M) h
  have key : ∀ t, t ≤ L.tim M Cmax h - 2 →
      Grid.gv (fun t j => L.node M Cmax (c0 + j) t) t (L.col M h + 1 - c0) = GS.val L.g x := by
    intro t ht
    induction t with
    | zero =>
      rw [gv_zero c0 (by omega), val_const hL hlx]
      unfold colConst
      cases hv : cval (L.g x)
      · rw [decide_eq_false]
        rintro (⟨h', -, ⟨-, -, hc'⟩, -⟩ | ⟨h', x', hg, -, hd', -, hv'⟩)
        · have := col_even (L := L) (M := M) h'; omega
        · have := gateAt_uniq hL hB hg ⟨hl, hy, by omega⟩
          subst this; rw [hd, Option.some.injEq] at hd'; subst hd'; rw [hv] at hv'; cases hv'
      · rw [decide_eq_true]
        exact Or.inr ⟨h, x, ⟨hl, hy, by omega⟩, by omega, hd, hlx, hv⟩
    | succ t ih =>
      rw [gv_S c0 (by omega) (node_low hL hB (by omega) (by omega)), ih (by omega)]
  have hn := node_inrow_S hL hB hl hr
  rw [show L.tim M Cmax h - 1 = L.tim M Cmax h - 2 + 1 by omega] at hn ⊢
  rw [gv_S c0 (by omega) hn, key _ le_rfl]

omit hB in
/-- The value of a live gate from the values of its slots. -/
lemma gate_comb {h : ℕ} (hl : L.live h = true) (ds ss : Bool)
    (hR : L.hasR h = true → ∀ x ∈ (L.g h).args, L.isR h x = true → ds = GS.val L.g x)
    (hD : ∀ x, L.dArg h = some x → ds = GS.val L.g x)
    (hS : ∀ x, L.sArg h = some x → ss = GS.val L.g x) :
    GS.val L.g h = comb (L.g h).kind (L.sArg h).isSome (L.hasR h || (L.dArg h).isSome) ds ss := by
  have hlen := nonR_len hL hl
  have hall : ∀ x ∈ (L.g h).args, (L.isR h x = true ∧ L.hasR h = true) ∨
      L.sArg h = some x ∨ L.dArg h = some x := by
    intro x hx
    cases e : L.isR h x
    · right; exact sArg_or_dArg hlen (mem_nonR.2 ⟨hx, e⟩)
    · left; exact ⟨rfl, List.any_eq_true.2 ⟨x, hx, e⟩⟩
  have hmemS : ∀ x, L.sArg h = some x → x ∈ (L.g h).args := fun x e => (mem_nonR.1 (sArg_mem e)).1
  have hmemD : ∀ x, L.dArg h = some x → x ∈ (L.g h).args :=
    fun x e => (mem_nonR.1 (dArg_spec e).1).1
  have hRex : L.hasR h = true → ∃ r ∈ (L.g h).args, L.isR h r = true := fun e => List.any_eq_true.1 e
  rw [GS.val_spec hL.ord]
  rcases hL.kind h hl with hk | hk
  · simp only [comb, hk, Gate.evalFn]
    rw [Bool.eq_iff_iff]
    simp only [List.all_map, List.all_eq_true, Function.comp, id, Bool.and_eq_true,
      Bool.or_eq_true, Bool.not_eq_true']
    constructor
    · intro H
      refine ⟨?_, ?_⟩
      · cases e1 : L.hasR h
        · cases e2 : L.dArg h with
          | none => left; simp
          | some z => right; rw [hD z e2]; exact H z (hmemD z e2)
        · right; obtain ⟨r, hr1, hr2⟩ := hRex e1; rw [hR e1 r hr1 hr2]; exact H r hr1
      · cases e2 : L.sArg h with
        | none => left; simp
        | some y => right; rw [hS y e2]; exact H y (hmemS y e2)
    · rintro ⟨H1, H2⟩ x hx
      rcases hall x hx with ⟨e1, e2⟩ | e | e
      · rw [← hR e2 x hx e1]; rcases H1 with H1 | H1
        · simp [e2] at H1
        · exact H1
      · rw [← hS x e]; rcases H2 with H2 | H2
        · simp [e] at H2
        · exact H2
      · rw [← hD x e]; rcases H1 with H1 | H1
        · simp [e] at H1
        · exact H1
  · simp only [comb, hk, Gate.evalFn]
    rw [Bool.eq_iff_iff]
    simp only [List.any_map, List.any_eq_true, Function.comp, id, Bool.and_eq_true,
      Bool.or_eq_true]
    constructor
    · rintro ⟨x, hx, H⟩
      rcases hall x hx with ⟨e1, e2⟩ | e | e
      · left; exact ⟨by simp [e2], by rw [hR e2 x hx e1]; exact H⟩
      · right; exact ⟨by simp [e], by rw [hS x e]; exact H⟩
      · left; exact ⟨by simp [e], by rw [hD x e]; exact H⟩
    · rintro (⟨H1, H2⟩ | ⟨H1, H2⟩)
      · cases e1 : L.hasR h
        · rw [e1] at H1
          obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 (by simpa using H1)
          exact ⟨z, hmemD z hz, by rw [← hD z hz]; exact H2⟩
        · obtain ⟨r, hr1, hr2⟩ := hRex e1
          exact ⟨r, hr1, by rw [← hR e1 r hr1 hr2]; exact H2⟩
      · obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 H1
        exact ⟨y, hmemS y hy, by rw [← hS y hy]; exact H2⟩

/-- **Values of the live gates in the grid.** -/
theorem gate_val : ∀ n h, L.tim M Cmax h = n → L.live h = true → c0 ≤ L.col M h →
    Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax h) (L.col M h - c0) =
      GS.val L.g h := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h hn hl hc0
  have htb := tim_add hL hB hl
  have hge := tim_ge hL hB hl
  have hy := hL.ypos h hl
  have hYh := (hB h hl).1
  -- the induction hypothesis for the arguments
  have IH : ∀ x, L.live x = true → L.tim M Cmax x < L.tim M Cmax h → c0 ≤ L.col M x →
      Grid.gv (fun t j => L.node M Cmax (c0 + j) t) (L.tim M Cmax x) (L.col M x - c0) =
        GS.val L.g x := fun x hlx hlt hcx => ih _ (by omega) x rfl hlx hcx
  have hVtim : ∀ x ∈ (L.g h).args, L.live x = true → L.Y x + 1 = L.Y h →
      L.tim M Cmax x < L.tim M Cmax h ∧ c0 ≤ L.col M x := by
    intro x hx hlx hyx
    obtain ⟨f1, f2, -, -⟩ := wire_facts hL hB hl hx hlx hyx
    have := tim_add hL hB hlx
    omega
  have hgate := node_gate hL hB hl
  rw [show L.tim M Cmax h = L.tim M Cmax h - 1 + 1 by omega, gv_gate c0 hc0
    (by rw [show L.tim M Cmax h - 1 + 1 = L.tim M Cmax h by omega]; exact hgate)]
  refine (gate_comb hL hl _ _ ?_ ?_ ?_).symm
  · intro hr x hx hxr
    obtain ⟨hlx, hyx, hXx⟩ := R_facts hL hl hx hxr
    have hcx : L.col M x = L.col M h + 2 := by unfold col; omega
    have htx := tim_add hL hB hlx
    have hn := node_inrow hL hB hl hr
    rw [show L.tim M Cmax h - 1 = L.tim M Cmax h - 2 + 1 by omega] at hn ⊢
    rw [gv_D c0 (by omega) hn, show L.col M h + 1 + 1 = L.col M x by omega,
      show L.tim M Cmax h - 2 = L.tim M Cmax x by omega]
    exact IH x hlx (by omega) (by omega)
  · intro x hd
    have hr : L.hasR h = false := by
      cases e : L.hasR h
      · rfl
      · rw [hasR_dArg hL hl e] at hd; cases hd
    obtain ⟨hxn, y, hsy, hxy⟩ := dArg_spec hd
    have hsx : L.sArg h ≠ some x := by rw [hsy]; simp; omega
    rcases nonR_cases hL hl hxn with ⟨hlx, hyx, -, -⟩ | ⟨hlx, hy1⟩
    · have hx := (mem_nonR.1 hxn).1
      obtain ⟨t1, t2⟩ := hVtim x hx hlx hyx
      exact wire_slot_d hL hB c0 hl hx hlx hyx hc0 hsx hr (IH x hlx t1 t2)
    · exact front_slot_d hL hB c0 hl hc0 hd hlx hy1 hr
  · intro x hs
    have hxn := sArg_mem hs
    rcases nonR_cases hL hl hxn with ⟨hlx, hyx, -, -⟩ | ⟨hlx, hy1⟩
    · have hx := (mem_nonR.1 hxn).1
      obtain ⟨t1, t2⟩ := hVtim x hx hlx hyx
      exact wire_slot_s hL hB c0 hl hx hlx hyx hc0 hs (IH x hlx t1 t2)
    · exact front_slot_s hL hB c0 hl hc0 hs hlx hy1

omit c0 in
/-- The grid of a live output gate is well formed. -/
lemma grid_ok {h0 : ℕ} (hl0 : L.live h0 = true) :
    Grid.OK (fun t j => L.node M Cmax (L.col M h0 + j) t) (Cmax + 1 - L.col M h0)
      (L.tim M Cmax h0) := by
  have hb0 := (hB h0 hl0).2
  refine ⟨by omega, fun j _ => ⟨_, by unfold node; rw [if_pos rfl]⟩, fun t ht1 _ j hj => ?_⟩
  rcases node_shape hL hB (c := L.col M h0 + j) ht1 with e | ⟨e, hc⟩ | ⟨h, hl, hc, e⟩
  · exact ⟨.and, true, false, e, Or.inl rfl, Or.inl rfl, fun _ => rfl⟩
  · exact ⟨.and, false, true, e, Or.inl rfl, Or.inr rfl, fun h' => by omega⟩
  · refine ⟨_, _, _, e, hL.kind h hl, ?_, fun h' => by have := (hB h hl).2; omega⟩
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hL.ne h hl)
    cases e' : L.isR h x
    · left
      rw [sArg_isSome]
      exact List.ne_nil_of_mem (mem_nonR.2 ⟨hx, e'⟩)
    · right
      have : L.hasR h = true := List.any_eq_true.2 ⟨x, hx, e'⟩
      simp [this]

omit c0 in
/-- **The grid drawing is a stratified monotone planar circuit.** -/
theorem circ_strat (h0 : ℕ) : StratMCVPInstance (L.circ M Cmax h0) := by
  unfold circ
  split_ifs with hl0
  · exact Grid.strat (grid_ok hL hB hl0)
  · refine ⟨⟨by simp, fun i hi => ?_⟩, fun g hg => ?_, ⟨fun _ => 0, ?_⟩⟩
    · simp only [List.length_singleton, Nat.lt_one_iff] at hi; subst hi
      simp
    · simp only [List.mem_singleton] at hg; subst hg; left; exact ⟨_, rfl, rfl⟩
    · refine ⟨fun _ _ _ _ => le_rfl, fun i hi => ?_, fun i hi j hj => ?_, fun i hi => ?_,
        fun i i' hi hi' hii' _ => ?_⟩
      · simp only [List.length_singleton, Nat.lt_one_iff] at hi; subst hi
        simp [Gate.IsInput]
      · simp only [List.length_singleton, Nat.lt_one_iff] at hi; subst hi
        simp at hj
      · simp only [List.length_singleton, Nat.lt_one_iff] at hi; subst hi
        simp
      · simp only [List.length_singleton, Nat.lt_one_iff] at hi hi'; omega

omit c0 in
/-- **The grid drawing computes the value of the output gate.** -/
theorem circ_eval (h0 : ℕ) : (L.circ M Cmax h0).eval ∅ [] = GS.val L.g h0 := by
  unfold circ
  split_ifs with hl0
  · rw [Grid.eval (grid_ok hL hB hl0)]
    have := gate_val hL hB (L.col M h0) _ h0 rfl hl0 le_rfl
    simpa using this
  · rw [val_const hL (by simpa using hl0)]
    simp [Circuit.eval, Circuit.values, Gate.eval]

end Hyp

end LSys

end LG

end PathChecking
