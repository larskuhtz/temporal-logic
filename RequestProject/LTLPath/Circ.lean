module

public import RequestProject.LTLPath.GSys
public import RequestProject.LTLPath.Sched

/-!
# The global circuit of an LTL path checking instance

A *formula tree* `FT` is a positional tree with node kinds (`0` atom, `1` true, `2` negation,
`3` conjunction, `4` next, `5` until), the truth values of the leaves at every position of the
path (`lv`), the polarity of every node (the parity of the number of negations above it) and the
lasso parameters (stem length `s`, loop length `ℓ ≥ 1`) and a bound `N ≥ F` on the positions.

The global circuit has gates `(p, i, t)` for positions `p < N`, path positions `i < Wm` and
`t ∈ {0 (aux), 1 (main)}`, with index `idx p i t`.  Gate `(p, i, 1)` computes the value of the
subformula at `p` at path position `i` (negated if the polarity of `p` is odd), in negation normal
form, using the window `W p = s + (p + 2) ℓ`; the gates `(p, i, 0)` of until nodes are the
auxiliary gates `φ ∧ X (φ U ψ)`.
-/

@[expose] public section

namespace PathChecking

/-- Formula trees with path data. -/
structure FT extends PT where
  kd : ℕ → ℕ
  lv : ℕ → ℕ → Bool
  pol : ℕ → Bool
  s : ℕ
  ℓ : ℕ
  N : ℕ
  kd_le : ∀ p, nd p = true → kd p ≤ 5
  ar_kd : ∀ p, nd p = true → ar p = (if kd p ≤ 1 then 0 else if kd p = 2 ∨ kd p = 4 then 1 else 2)
  hℓ : 1 ≤ ℓ
  hN : F ≤ N

namespace FT

variable (T : FT)

/-- Window of the node at position `p`. -/
def W (p : ℕ) : ℕ := T.s + (p + 2) * T.ℓ

/-- Number of path positions of all rows. -/
def Wm : ℕ := T.s + (T.N + 1) * T.ℓ

/-- Index of the gate `(p, i, t)`. -/
def idx (p i t : ℕ) : ℕ := 2 * ((T.N - 1 - p) * T.Wm + (T.Wm - 1 - i)) + t

/-- Number of gates. -/
def Ng : ℕ := 2 * T.N * T.Wm

/-- Node position of a gate. -/
def pos (h : ℕ) : ℕ := T.N - 1 - h / 2 / T.Wm

/-- Path position of a gate. -/
def ix (h : ℕ) : ℕ := T.Wm - 1 - h / 2 % T.Wm

/-- Type of a gate (`1` = main, `0` = aux). -/
def ty (h : ℕ) : ℕ := h % 2

/-- The constant gate `false`. -/
def cF : Gate := ⟨.const false, []⟩

/-- `AND` if `b = false`, `OR` if `b = true`. -/
def andOr (b : Bool) : GateKind := if b then .or else .and

/-- The gate `(p, i, t)`. -/
def gateAt (p i t : ℕ) : Gate :=
  if T.nd p = true ∧ i < T.W p then
    if T.kd p ≤ 1 then (if t = 1 then ⟨.const (T.lv p i != T.pol p), []⟩ else cF)
    else if T.kd p = 2 then (if t = 1 then ⟨.and, [T.idx (p + 1) i 1]⟩ else cF)
    else if T.kd p = 4 then (if t = 1 then ⟨.and, [T.idx (p + 1) (i + 1) 1]⟩ else cF)
    else if T.kd p = 3 then
      (if t = 1 then ⟨andOr (T.pol p), [T.idx (p + 1) i 1, T.idx (T.c2 p) i 1]⟩ else cF)
    else
      (if t = 1 then
        (if i + 1 < T.W p then ⟨andOr (!T.pol p), [T.idx (T.c2 p) i 1, T.idx p i 0]⟩
         else ⟨.and, [T.idx (T.c2 p) i 1]⟩)
       else
        (if i + 1 < T.W p then ⟨andOr (T.pol p), [T.idx (p + 1) i 1, T.idx p (i + 1) 1]⟩
         else cF))
  else cF

/-- The global circuit as a gate system. -/
def gate (h : ℕ) : Gate := if h < T.Ng then T.gateAt (T.pos h) (T.ix h) (ty h) else cF

variable {T}

lemma Wm_pos : 0 < T.Wm := by
  unfold Wm; have := T.hℓ; positivity

lemma W_le_Wm {p : ℕ} (hp : p < T.N) : T.W p ≤ T.Wm := by
  unfold W Wm; have : p + 2 ≤ T.N + 1 := by omega
  have := Nat.mul_le_mul_right T.ℓ this; omega

lemma W_succ (p : ℕ) : T.W (p + 1) = T.W p + T.ℓ := by unfold W; ring

lemma W_mono {p q : ℕ} (h : p ≤ q) : T.W p ≤ T.W q := by
  unfold W; have := Nat.mul_le_mul_right T.ℓ (show p + 2 ≤ q + 2 by omega); omega

lemma W_add {p q : ℕ} (h : p < q) : T.W p + T.ℓ ≤ T.W q := by
  rw [← W_succ]; exact W_mono h

lemma idx_lt_Ng {p i t : ℕ} (hp : p < T.N) (hi : i < T.Wm) (ht : t ≤ 1) : T.idx p i t < T.Ng := by
  unfold idx Ng
  have h1 : (T.N - 1 - p) * T.Wm + (T.Wm - 1 - i) < T.N * T.Wm := by
    have : (T.N - 1 - p) * T.Wm + T.Wm ≤ T.N * T.Wm := by
      have := Nat.mul_le_mul_right T.Wm (show T.N - 1 - p + 1 ≤ T.N by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    omega
  nlinarith

lemma decode_idx {p i t : ℕ} (hp : p < T.N) (hi : i < T.Wm) (ht : t ≤ 1) :
    T.pos (T.idx p i t) = p ∧ T.ix (T.idx p i t) = i ∧ ty (T.idx p i t) = t := by
  have hW := (Wm_pos (T := T))
  have e2 : T.idx p i t / 2 = (T.N - 1 - p) * T.Wm + (T.Wm - 1 - i) := by unfold idx; omega
  have e3 : ((T.N - 1 - p) * T.Wm + (T.Wm - 1 - i)) / T.Wm = T.N - 1 - p := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hW, Nat.div_eq_of_lt (by omega)]; simp
  have e4 : ((T.N - 1 - p) * T.Wm + (T.Wm - 1 - i)) % T.Wm = T.Wm - 1 - i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · unfold pos; rw [e2, e3]; omega
  · unfold ix; rw [e2, e4]; omega
  · unfold ty idx; omega

lemma idx_decode {h : ℕ} (hh : h < T.Ng) :
    T.idx (T.pos h) (T.ix h) (ty h) = h ∧ T.pos h < T.N ∧ T.ix h < T.Wm ∧ ty h ≤ 1 := by
  have hW := (Wm_pos (T := T))
  have hq : h / 2 / T.Wm < T.N := by
    unfold Ng at hh
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_lt_of_lt_mul (by nlinarith)
  have hr := Nat.mod_lt (h / 2) hW
  have hdm := Nat.div_add_mod' (h / 2) T.Wm
  unfold idx pos ix ty
  generalize h / 2 / T.Wm = a at *
  generalize h / 2 % T.Wm = b at *
  refine ⟨?_, by omega, by omega, by omega⟩
  have e1 : T.N - 1 - (T.N - 1 - a) = a := by omega
  have e2 : T.Wm - 1 - (T.Wm - 1 - b) = b := by omega
  rw [e1, e2, hdm]
  omega

/-- Gates of deeper rows have smaller indices. -/
lemma idx_lt_of_lt {p c i j t t' : ℕ} (hpc : p < c) (hc : c < T.N) (hj : j < T.Wm)
    (ht' : t' ≤ 1) : T.idx c j t' < T.idx p i t := by
  unfold idx
  have : (T.N - 1 - c) * T.Wm + (T.Wm - 1 - j) < (T.N - 1 - p) * T.Wm := by
    have : (T.N - 1 - c + 1) * T.Wm ≤ (T.N - 1 - p) * T.Wm :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, one_mul] at this; omega
  omega

lemma idx_aux_lt_main (p i : ℕ) : T.idx p i 0 < T.idx p i 1 := by unfold idx; omega

lemma idx_next_lt_aux {p i : ℕ} (hi : i + 1 < T.Wm) : T.idx p (i + 1) 1 < T.idx p i 0 := by
  unfold idx; omega

lemma kd_cases {p : ℕ} (hp : T.nd p = true) :
    T.kd p ≤ 1 ∨ T.kd p = 2 ∨ T.kd p = 3 ∨ T.kd p = 4 ∨ T.kd p = 5 := by
  have := T.kd_le p hp; omega

lemma ar_of_kd {p : ℕ} (hp : T.nd p = true) :
    (T.kd p ≤ 1 → T.ar p = 0) ∧ (T.kd p = 2 ∨ T.kd p = 4 → T.ar p = 1) ∧
      (T.kd p = 3 ∨ T.kd p = 5 → T.ar p = 2) := by
  have h := T.ar_kd p hp
  refine ⟨fun e => by rw [h, if_pos e], fun e => by rw [h, if_neg (by omega), if_pos e],
    fun e => by rw [h, if_neg (by omega), if_neg (by omega)]⟩

lemma child1_lt_N {p : ℕ} (hp : T.nd p = true) (h : T.ar p ≠ 0) : p + 1 < T.N ∧ T.nd (p + 1) = true := by
  have hc : T.nd (p + 1) = true := by
    rcases (show T.ar p = 1 ∨ T.ar p = 2 by have := T.ar_le p hp; omega) with e | e
    · exact (T.un p hp e).1
    · exact (T.bin p hp e).1
  exact ⟨lt_of_lt_of_le (PT.lt_F hc) T.hN, hc⟩

lemma child2_lt_N {p : ℕ} (hp : T.nd p = true) (h : T.ar p = 2) :
    p < T.c2 p ∧ T.c2 p < T.N ∧ T.nd (T.c2 p) = true := by
  obtain ⟨a, b, _⟩ := T.bin p hp h
  have := T.lt_fe _ a
  exact ⟨by unfold PT.c2; omega, lt_of_lt_of_le (PT.lt_F b) T.hN, b⟩

lemma gateAt_args {p i t : ℕ} (hp : p < T.N) (ht : t ≤ 1) :
    ∀ j ∈ (T.gateAt p i t).args, j < T.idx p i t := by
  intro j hj
  unfold gateAt at hj
  by_cases h1 : T.nd p = true ∧ i < T.W p
  swap
  · rw [if_neg h1] at hj; simp [cF] at hj
  rw [if_pos h1] at hj
  have hWp := W_le_Wm (T := T) hp
  have ha := ar_of_kd h1.1
  rcases kd_cases h1.1 with e | e | e | e | e
  · rw [if_pos e] at hj; split_ifs at hj <;> simp [cF] at hj
  · rw [if_neg (by omega), if_pos e] at hj
    split_ifs at hj with h2
    · simp only [List.mem_singleton] at hj
      have hc := child1_lt_N h1.1 (by rw [ha.2.1 (Or.inl e)]; omega)
      rw [hj]; exact idx_lt_of_lt (by omega) hc.1 (by omega) (by omega)
    · simp [cF] at hj
  · have e2 : T.ar p = 2 := ha.2.2 (Or.inl e)
    have hc := child1_lt_N h1.1 (by omega)
    have hc2 := child2_lt_N h1.1 e2
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e] at hj
    split_ifs at hj with h2
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact idx_lt_of_lt (by omega) hc.1 (by omega) (by omega)
      · exact idx_lt_of_lt hc2.1 hc2.2.1 (by omega) (by omega)
    · simp [cF] at hj
  · rw [if_neg (by omega), if_neg (by omega), if_pos e] at hj
    split_ifs at hj with h2
    · simp only [List.mem_singleton] at hj
      have hc := child1_lt_N h1.1 (by rw [ha.2.1 (Or.inr e)]; omega)
      rw [hj]
      refine idx_lt_of_lt (by omega) hc.1 ?_ (by omega)
      have := W_le_Wm (T := T) hc.1; rw [W_succ] at this; have := T.hℓ; omega
    · simp [cF] at hj
  · have e2 : T.ar p = 2 := ha.2.2 (Or.inr e)
    have hc := child1_lt_N h1.1 (by omega)
    have hc2 := child2_lt_N h1.1 e2
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at hj
    split_ifs at hj with h2 h3 h4
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · exact idx_lt_of_lt hc2.1 hc2.2.1 (by omega) (by omega)
      · rw [h2]; exact idx_aux_lt_main p i
    · simp only [List.mem_singleton] at hj
      rw [hj]; exact idx_lt_of_lt hc2.1 hc2.2.1 (by omega) (by omega)
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
      have ht0 : t = 0 := by omega
      rcases hj with rfl | rfl
      · exact idx_lt_of_lt (by omega) hc.1 (by omega) (by omega)
      · rw [ht0]; exact idx_next_lt_aux (by omega)
    · simp [cF] at hj

/-- **The global circuit is ordered.** -/
theorem gate_ordered : GS.Ordered T.gate := by
  intro h j hj
  unfold gate at hj
  split_ifs at hj with hh
  · obtain ⟨e, hp, hi, ht⟩ := idx_decode hh
    have := gateAt_args hp ht j hj
    rwa [e] at this
  · simp [cF] at hj


variable {T : FT}

/-- `AND`/`OR` gates. -/
def AO (g : Gate) : Prop := g.kind = .and ∨ g.kind = .or

lemma andOr_AO (b : Bool) (l : List ℕ) : AO ⟨andOr b, l⟩ := by
  cases b <;> simp [AO, andOr]

/-- Structure of the `AND`/`OR` gates of the global circuit. -/
theorem gate_AO {h : ℕ} (hA : AO (T.gate h)) :
    h < T.Ng ∧ T.nd (T.pos h) = true ∧ T.leaf (T.pos h) = false ∧ T.ix h < T.W (T.pos h) ∧
      ∀ x ∈ (T.gate h).args, x < h ∧ x < T.Ng ∧
        (T.pos x = T.pos h ∨ T.IsChild (T.pos h) (T.pos x)) := by
  unfold gate at hA ⊢
  by_cases hh : h < T.Ng
  swap
  · rw [if_neg hh] at hA; simp [AO, cF] at hA
  rw [if_pos hh] at hA ⊢
  obtain ⟨e, hp, hi, ht⟩ := idx_decode hh
  set p := T.pos h
  set i := T.ix h
  set t := ty h
  have hargs := gateAt_args (T := T) (i := i) hp ht
  rw [e] at hargs
  unfold gateAt at hA
  by_cases h1 : T.nd p = true ∧ i < T.W p
  swap
  · rw [if_neg h1] at hA; simp [AO, cF] at hA
  have hl : T.leaf p = false := by
    by_contra hl'
    have : T.kd p ≤ 1 := by
      have := (T.ar_kd p h1.1); simp [PT.leaf, h1.1] at hl'
      rw [hl'] at this; split_ifs at this <;> omega
    rw [if_pos h1, if_pos this] at hA; split_ifs at hA <;> simp [AO, cF] at hA
  refine ⟨hh, h1.1, hl, h1.2, fun x hx => ⟨hargs x hx, ?_⟩⟩
  have hWp := W_le_Wm (T := T) hp
  have ha := ar_of_kd h1.1
  unfold gateAt at hx
  rw [if_pos h1] at hx
  have hpos : ∀ q j u, q < T.N → j < T.Wm → u ≤ 1 → x = T.idx q j u →
      x < T.Ng ∧ T.pos x = q := fun q j u hq hj hu hx' =>
    ⟨hx' ▸ idx_lt_Ng hq hj hu, by rw [hx']; exact (decode_idx hq hj hu).1⟩
  have c1 : ∀ j u, j < T.Wm → u ≤ 1 → T.ar p ≠ 0 → x = T.idx (p + 1) j u →
      x < T.Ng ∧ (T.pos x = p ∨ T.IsChild p (T.pos x)) := by
    intro j u hj hu har hx'
    have hc := child1_lt_N h1.1 har
    obtain ⟨a, b⟩ := hpos _ j u hc.1 hj hu hx'
    exact ⟨a, Or.inr (b ▸ ⟨h1.1, Or.inl ⟨by omega, rfl⟩⟩)⟩
  have c2 : ∀ j u, j < T.Wm → u ≤ 1 → T.ar p = 2 → x = T.idx (T.c2 p) j u →
      x < T.Ng ∧ (T.pos x = p ∨ T.IsChild p (T.pos x)) := by
    intro j u hj hu har hx'
    have hc := child2_lt_N h1.1 har
    obtain ⟨a, b⟩ := hpos _ j u hc.2.1 hj hu hx'
    exact ⟨a, Or.inr (b ▸ ⟨h1.1, Or.inr ⟨har, rfl⟩⟩)⟩
  have c0 : ∀ j u, j < T.Wm → u ≤ 1 → x = T.idx p j u →
      x < T.Ng ∧ (T.pos x = p ∨ T.IsChild p (T.pos x)) := by
    intro j u hj hu hx'
    obtain ⟨a, b⟩ := hpos _ j u hp hj hu hx'
    exact ⟨a, Or.inl b⟩
  rcases kd_cases h1.1 with e' | e' | e' | e' | e'
  · rw [if_pos e'] at hx; split_ifs at hx <;> simp [cF] at hx
  · rw [if_neg (by omega), if_pos e'] at hx
    split_ifs at hx
    · simp only [List.mem_singleton] at hx
      exact c1 i 1 (by omega) le_rfl (by rw [ha.2.1 (Or.inl e')]; omega) hx
    · simp [cF] at hx
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos e'] at hx
    split_ifs at hx
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact c1 i 1 (by omega) le_rfl (by rw [ha.2.2 (Or.inl e')]; omega) hx
      · exact c2 i 1 (by omega) le_rfl (ha.2.2 (Or.inl e')) hx
    · simp [cF] at hx
  · rw [if_neg (by omega), if_neg (by omega), if_pos e'] at hx
    split_ifs at hx
    · simp only [List.mem_singleton] at hx
      have hc := child1_lt_N h1.1 (by rw [ha.2.1 (Or.inr e')]; omega)
      refine c1 (i + 1) 1 ?_ le_rfl (by rw [ha.2.1 (Or.inr e')]; omega) hx
      have := W_le_Wm (T := T) hc.1; rw [W_succ] at this; have := T.hℓ; omega
    · simp [cF] at hx
  · have e2 : T.ar p = 2 := ha.2.2 (Or.inr e')
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] at hx
    split_ifs at hx
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact c2 i 1 (by omega) le_rfl e2 hx
      · exact c0 i 0 (by omega) (by omega) hx
    · simp only [List.mem_singleton] at hx
      exact c2 i 1 (by omega) le_rfl e2 hx
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with hx | hx
      · exact c1 i 1 (by omega) le_rfl (by omega) hx
      · exact c0 (i + 1) 1 (by omega) le_rfl hx
    · simp [cF] at hx

/-- The gates of the global circuit are monotone. -/
theorem gate_mono : GS.Mono T.gate := by
  intro h
  unfold gate
  split_ifs
  swap
  · exact Or.inr (Or.inr ⟨false, rfl, rfl⟩)
  unfold gateAt
  split_ifs <;> first
    | exact Or.inr (Or.inr ⟨_, rfl, rfl⟩)
    | exact Or.inl rfl
    | (rcases andOr_AO (T.pol (T.pos h)) [] with e | e <;> simp_all [andOr, AO])

end FT

end PathChecking
