module

public import RequestProject.LTLPath.Down

/-!
# The tree contraction schedule

Stage `r` of the contraction starts with the leaves whose index is divisible by `2^r`
(`S0 r`).  The *odd* leaves (index an odd multiple of `2^r`) are removed in two substeps: first
those lying below the first child of their compressed parent (`DL r`), then the remaining ones
(`DR r`), which lie below the second child of their compressed parent.

Main facts: the removed leaves are separated by remaining leaves (`sep_DL`, `sep_DR`), and the
sibling region of a removed leaf is not itself the region of a compressed parent of a removed
leaf (`noChain_L`, `noChain_R`): no two merges of a substep are chained.
-/

@[expose] public section

namespace PathChecking

namespace PT

variable {T : PT}

open Classical

/-- Leaves of stage `r`. -/
def S0 (T : PT) (r : ℕ) (k : ℕ) : Prop := k < T.L ∧ 2 ^ r ∣ k

/-- Odd leaves of stage `r`. -/
def Odd2 (r k : ℕ) : Prop := k / 2 ^ r % 2 = 1

/-- Odd leaves below the first child of their compressed parent. -/
def DL (T : PT) (r : ℕ) (k : ℕ) : Prop :=
  T.S0 r k ∧ Odd2 r k ∧ T.Cont (T.par (T.S0 r) k + 1) k

/-- Leaves after the first substep. -/
def S1 (T : PT) (r : ℕ) (k : ℕ) : Prop := T.S0 r k ∧ ¬ T.DL r k

/-- The remaining odd leaves. -/
def DR (T : PT) (r : ℕ) (k : ℕ) : Prop := T.S1 r k ∧ Odd2 r k

lemma S1_DR_iff (r k : ℕ) : (T.S1 r k ∧ ¬ T.DR r k) ↔ T.S0 (r + 1) k := by
  unfold S1 DR DL S0 Odd2
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, ?_⟩
    have h5 : ¬ k / 2 ^ r % 2 = 1 := fun h => h4 ⟨⟨⟨h1, h2⟩, h3⟩, h⟩
    obtain ⟨j, rfl⟩ := h2
    rw [Nat.mul_div_cancel_left _ (by positivity)] at h5
    obtain ⟨i, rfl⟩ : 2 ∣ j := by omega
    exact ⟨i, by ring⟩
  · rintro ⟨h1, j, rfl⟩
    have hd : 2 ^ r ∣ 2 ^ (r + 1) * j := ⟨2 * j, by ring⟩
    have hodd : ¬ 2 ^ (r + 1) * j / 2 ^ r % 2 = 1 := by
      rw [show 2 ^ (r + 1) * j = 2 ^ r * (2 * j) by ring, Nat.mul_div_cancel_left _ (by positivity)]
      omega
    exact ⟨⟨⟨h1, hd⟩, fun h => hodd h.2.1⟩, fun h => hodd h.2⟩

/-- Leaf sets of stage `r`: multiples of `2^r` containing all multiples of `2^(r+1)`. -/
structure Good (T : PT) (r : ℕ) (S : ℕ → Prop) : Prop where
  sub : ∀ m, S m → m < T.L ∧ 2 ^ r ∣ m
  even : ∀ m, m < T.L → 2 ^ (r + 1) ∣ m → S m

lemma good_S0 (r : ℕ) : T.Good r (T.S0 r) :=
  ⟨fun m h => h, fun m hm hd => ⟨hm, dvd_trans (pow_dvd_pow 2 (by omega)) hd⟩⟩

lemma not_odd_of_dvd {r m : ℕ} (h : 2 ^ (r + 1) ∣ m) : ¬ Odd2 r m := by
  obtain ⟨j, rfl⟩ := h
  unfold Odd2
  rw [show 2 ^ (r + 1) * j = 2 ^ r * (2 * j) by ring, Nat.mul_div_cancel_left _ (by positivity)]
  omega

lemma good_S1 (r : ℕ) : T.Good r (T.S1 r) :=
  ⟨fun m h => h.1, fun m hm hd => ⟨(good_S0 r).even m hm hd, fun h => not_odd_of_dvd hd h.2.1⟩⟩

/-- Arithmetic of odd multiples. -/
lemma odd_mul {r k : ℕ} (hd : 2 ^ r ∣ k) (ho : Odd2 r k) :
    ∃ j, k = 2 ^ r * (2 * j + 1) := by
  obtain ⟨i, rfl⟩ := hd
  unfold Odd2 at ho
  rw [Nat.mul_div_cancel_left _ (by positivity)] at ho
  exact ⟨i / 2, by congr 1; omega⟩

lemma even_succ {r k : ℕ} (hd : 2 ^ r ∣ k) (ho : Odd2 r k) : 2 ^ (r + 1) ∣ k + 2 ^ r := by
  obtain ⟨j, rfl⟩ := odd_mul hd ho
  exact ⟨j + 1, by ring⟩

lemma even_pred {r k : ℕ} (hd : 2 ^ r ∣ k) (ho : Odd2 r k) : 2 ^ (r + 1) ∣ k - 2 ^ r ∧ 2 ^ r ≤ k := by
  obtain ⟨j, rfl⟩ := odd_mul hd ho
  refine ⟨⟨j, ?_⟩, ?_⟩
  · rw [show 2 ^ r * (2 * j + 1) = 2 ^ (r + 1) * j + 2 ^ r by ring]; simp
  · nlinarith [Nat.one_le_two_pow (n := r)]

/-- Removed leaves are separated. -/
lemma sep_of_odd {r : ℕ} {S D : ℕ → Prop} (hS : T.Good r S) (hD : ∀ k, D k → S k ∧ Odd2 r k) :
    Sep S D := by
  intro k₁ k₂ h1 h2 hlt
  obtain ⟨s1, o1⟩ := hD k₁ h1
  obtain ⟨s2, o2⟩ := hD k₂ h2
  obtain ⟨j1, e1⟩ := odd_mul (hS.sub _ s1).2 o1
  obtain ⟨j2, e2⟩ := odd_mul (hS.sub _ s2).2 o2
  have hj : j1 < j2 := by
    by_contra h
    have : 2 ^ r * (2 * j2 + 1) ≤ 2 ^ r * (2 * j1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega
  have hp := Nat.one_le_two_pow (n := r)
  refine ⟨k₁ + 2 ^ r, hS.even _ ?_ (even_succ (hS.sub _ s1).2 o1), fun h => ?_, by omega, ?_⟩
  · have := (hS.sub _ s2).1
    have : 2 ^ r * (2 * j1 + 1) + 2 ^ r < 2 ^ r * (2 * j2 + 1) := by nlinarith
    omega
  · exact not_odd_of_dvd (even_succ (hS.sub _ s1).2 o1) (hD _ h).2
  · rw [e1, e2]; nlinarith

lemma sep_DL (r : ℕ) : Sep (T.S0 r) (T.DL r) :=
  sep_of_odd (good_S0 r) (fun k h => ⟨h.1, h.2.1⟩)

lemma sep_DR (r : ℕ) : Sep (T.S1 r) (T.DR r) :=
  sep_of_odd (good_S1 r) (fun k h => ⟨h.1, h.2⟩)

lemma lix_one : T.lix 1 = 0 := by
  have : T.leaf 0 = false := by
    have h := T.nd_ge 0
    cases e : T.nd 0
    · simp [leaf, e]
    · exact absurd (h e) (by omega)
  simp [lix, List.range_one, this]

lemma cont_root {k : ℕ} (hk : k < T.L) : T.Cont 1 k := by
  refine ⟨by rw [lix_one]; omega, ?_⟩
  rw [T.fe_one]; exact hk

lemma par_spec_good {r : ℕ} {S : ℕ → Prop} (hS : T.Good r S) {k : ℕ} (hk : S k) (ho : Odd2 r k) :
    T.nd (T.par S k) = true ∧ T.Cont (T.par S k) k ∧
      ∃ k', S k' ∧ k' ≠ k ∧ T.Cont (T.par S k) k' := by
  have hkL := (hS.sub k hk).1
  have h0 : S 0 := hS.even 0 (by omega) (dvd_zero _)
  have hk0 : (0 : ℕ) ≠ k := by
    obtain ⟨j, e⟩ := odd_mul (hS.sub k hk).2 ho
    have := Nat.one_le_two_pow (n := r)
    intro h; rw [← h] at e; nlinarith
  exact par_prop T.nd_one (cont_root hkL) h0 hk0 (cont_root (by omega))

lemma par_nonleaf {S : ℕ → Prop} {k : ℕ} (h : T.nd (T.par S k) = true ∧ T.Cont (T.par S k) k ∧
      ∃ k', S k' ∧ k' ≠ k ∧ T.Cont (T.par S k) k') : T.leaf (T.par S k) = false := by
  obtain ⟨p1, p2, k', -, p4, p5⟩ := h
  by_contra hl'
  have hl'' : T.leaf (T.par S k) = true := by simpa using hl'
  have e1 := lix_fe_leaf hl''
  have := p2.1; have := p2.2; have := p5.1; have := p5.2
  omega

lemma child1_of_nonleaf {p : ℕ} (hp : T.nd p = true) (hl : T.leaf p = false) :
    T.IsChild p (p + 1) := by
  refine ⟨hp, Or.inl ⟨?_, rfl⟩⟩
  by_contra h; simp [leaf, hp, show T.ar p = 0 by omega] at hl

/-- The child of a node containing a leaf. -/
lemma child_cases' {p k : ℕ} (hp : T.nd p = true) (hl : T.leaf p = false) (hk : T.Cont p k) :
    T.Cont (p + 1) k ∨ (T.IsChild p (T.c2 p) ∧ T.Cont (T.c2 p) k) := by
  rcases cont_child_cases hp hk hl with ⟨_, h⟩ | h
  · exact Or.inl h
  · exact Or.inr h

lemma mul_ge_add {r a b : ℕ} (ha : 2 ^ r ∣ a) (hb : 2 ^ r ∣ b) (h : a < b) : a + 2 ^ r ≤ b := by
  obtain ⟨i, rfl⟩ := ha; obtain ⟨j, rfl⟩ := hb
  have : i < j := by
    by_contra h'; push_neg at h'; have := Nat.mul_le_mul_left (2 ^ r) h'; omega
  nlinarith

/-- **Neighbour lemma**, first child. -/
lemma nbr_c1 {r : ℕ} {S : ℕ → Prop} (hS : T.Good r S) {k : ℕ} (hk : S k) (ho : Odd2 r k)
    (hc : T.Cont (T.par S k + 1) k) :
    T.IsChild (T.par S k) (T.c2 (T.par S k)) ∧ T.Cont (T.c2 (T.par S k)) (k + 2 ^ r) ∧
      S (k + 2 ^ r) := by
  have hp2 := Nat.one_le_two_pow (n := r)
  have hps := par_spec_good hS hk ho
  have hl := par_nonleaf hps
  obtain ⟨p1, p2, k', p3, p4, p5⟩ := hps
  have hc1 := child1_of_nonleaf p1 hl
  rcases child_cases' p1 hl p5 with h | ⟨hc2, h⟩
  · exact absurd (par_child_only hc1 hc k' p3 h) p4
  have hkk' : k < k' := by have := hc.2; have := h.1; unfold c2 at *; omega
  have hle := mul_ge_add (hS.sub k hk).2 (hS.sub k' p3).2 hkk'
  have hm : S (k + 2 ^ r) := hS.even _ (by have := (hS.sub k' p3).1; omega)
    (even_succ (hS.sub k hk).2 ho)
  refine ⟨hc2, ⟨?_, by have := h.2; omega⟩, hm⟩
  by_contra hlt
  have : T.Cont (T.par S k + 1) (k + 2 ^ r) := ⟨by have := hc.1; omega, by unfold c2 at hlt; omega⟩
  have := par_child_only hc1 hc _ hm this
  have := Nat.one_le_two_pow (n := r)
  omega

/-- **Neighbour lemma**, second child. -/
lemma nbr_c2 {r : ℕ} {S : ℕ → Prop} (hS : T.Good r S) {k : ℕ} (hk : S k) (ho : Odd2 r k)
    (hc : T.Cont (T.c2 (T.par S k)) k) :
    T.Cont (T.par S k + 1) (k - 2 ^ r) ∧ S (k - 2 ^ r) := by
  have hp2 := Nat.one_le_two_pow (n := r)
  have hps := par_spec_good hS hk ho
  have hl := par_nonleaf hps
  obtain ⟨p1, p2, k', p3, p4, p5⟩ := hps
  have hc1 := child1_of_nonleaf p1 hl
  rcases child_cases' p1 hl p5 with h | ⟨hc2, h⟩
  swap
  · exact absurd (par_child_only hc2 hc k' p3 h) p4
  have hc2 : T.IsChild (T.par S k) (T.c2 (T.par S k)) := by
    rcases child_cases' p1 hl p2 with h' | ⟨h'', _⟩
    · exfalso; have := h'.2; have := hc.1; unfold c2 at *; omega
    · exact h''
  have hkk' : k' < k := by have := h.2; have := hc.1; unfold c2 at *; omega
  have hle := mul_ge_add (hS.sub k' p3).2 (hS.sub k hk).2 hkk'
  obtain ⟨he, hrk⟩ := even_pred (hS.sub k hk).2 ho
  have hm : S (k - 2 ^ r) := hS.even _ (by have := (hS.sub k hk).1; omega) he
  refine ⟨⟨by have := h.1; omega, ?_⟩, hm⟩
  by_contra hlt
  have : T.Cont (T.c2 (T.par S k)) (k - 2 ^ r) := ⟨by unfold c2; omega, by have := hc.2; omega⟩
  have := par_child_only hc2 hc _ hm this
  have := Nat.one_le_two_pow (n := r)
  omega

/-- **No chained merges**, first substep. -/
theorem noChain_L {r : ℕ} {S D : ℕ → Prop} (hS : T.Good r S)
    (hD : ∀ k, D k → S k ∧ Odd2 r k ∧ T.Cont (T.par S k + 1) k) {k : ℕ} (hk : D k) :
    ¬ T.PSet S D (T.down S (T.c2 (T.par S k))) := by
  rintro ⟨k'', hk'', hd⟩
  obtain ⟨s, o, hc⟩ := hD k hk
  obtain ⟨s'', o'', hc''⟩ := hD k'' hk''
  obtain ⟨hc2, hm, hmS⟩ := nbr_c1 hS s o hc
  have hsame := (down_prop (S := S) hc2.nd).2
  rw [← hd] at hsame
  have hps := par_spec_good hS s'' o''
  have hl := par_nonleaf hps
  have hmd := (hsame _ hmS).1 hm
  have hk''c := (hsame _ s'').2 hps.2.1
  rcases child_cases' hps.1 hl hmd with h | ⟨_, h⟩
  · have := par_child_only (child1_of_nonleaf hps.1 hl) hc'' _ hmS h
    exact not_odd_of_dvd (even_succ (hS.sub k s).2 o) (this ▸ o'')
  · have h1 : k'' < k + 2 ^ r := by have := hc''.2; have := h.1; unfold c2 at *; omega
    have h2 : k < k'' := by have := hc.2; have := hk''c.1; unfold c2 at *; omega
    have := mul_ge_add (hS.sub k s).2 (hS.sub k'' s'').2 h2
    omega

/-- **No chained merges**, second substep. -/
theorem noChain_R {r : ℕ} {S D : ℕ → Prop} (hS : T.Good r S)
    (hD : ∀ k, D k → S k ∧ Odd2 r k ∧ T.Cont (T.c2 (T.par S k)) k) {k : ℕ} (hk : D k) :
    ¬ T.PSet S D (T.down S (T.par S k + 1)) := by
  rintro ⟨k'', hk'', hd⟩
  obtain ⟨s, o, hc⟩ := hD k hk
  obtain ⟨s'', o'', hc''⟩ := hD k'' hk''
  obtain ⟨hm, hmS⟩ := nbr_c2 hS s o hc
  have hpk := par_spec_good hS s o
  have hc1 := child1_of_nonleaf hpk.1 (par_nonleaf hpk)
  have hsame := (down_prop (S := S) hc1.nd).2
  rw [← hd] at hsame
  have hps := par_spec_good hS s'' o''
  have hl := par_nonleaf hps
  have hmd := (hsame _ hmS).1 hm
  have hk''c := (hsame _ s'').2 hps.2.1
  obtain ⟨-, hrk⟩ := even_pred (hS.sub k s).2 o
  rcases child_cases' hps.1 hl hmd with h | ⟨hc2, h⟩
  · have h1 : k - 2 ^ r < k'' := by have := hc''.1; have := h.2; unfold c2 at *; omega
    have h2 : k'' < k := by have := hc.1; have := hk''c.2; unfold c2 at *; omega
    have := mul_ge_add (hS.sub k'' s'').2 (hS.sub k s).2 h2
    omega
  · have := par_child_only hc2 hc'' _ hmS h
    exact not_odd_of_dvd (even_pred (hS.sub k s).2 o).1 (this ▸ o'')

/-- In the second substep, compressed parents are the same as at the start of the stage. -/
lemma par_S1 {r k : ℕ} (hk : T.S1 r k) (ho : Odd2 r k) : T.par (T.S1 r) k = T.par (T.S0 r) k := by
  have h1 := par_spec_good (good_S1 r) hk ho
  have h0 := par_spec_good (good_S0 r) hk.1 ho
  refine le_antisymm ?_ ?_
  · obtain ⟨p1, p2, k', p3, p4, p5⟩ := h1
    exact le_par p1 p2 p3.1 p4 p5
  · have hl := par_nonleaf h0
    rcases child_cases' h0.1 hl h0.2.1 with h | ⟨_, h⟩
    · obtain ⟨hc2, hm, hmS⟩ := nbr_c1 (good_S0 r) hk.1 ho h
      have hmS1 : T.S1 r (k + 2 ^ r) := (good_S1 r).even _ hmS.1 (even_succ hk.1.2 ho)
      exact le_par h0.1 h0.2.1 hmS1 (by have := Nat.one_le_two_pow (n := r); omega) (hc2.cont hm)
    · obtain ⟨hm, hmS⟩ := nbr_c2 (good_S0 r) hk.1 ho h
      have hmS1 : T.S1 r (k - 2 ^ r) := (good_S1 r).even _ hmS.1 (even_pred hk.1.2 ho).1
      have := (even_pred hk.1.2 ho).2
      exact le_par h0.1 h0.2.1 hmS1 (by have := Nat.one_le_two_pow (n := r); omega)
        ((child1_of_nonleaf h0.1 hl).cont hm)

/-- The leaves removed in the second substep lie below the second child of their compressed
parent. -/
lemma DR_c2 {r k : ℕ} (hk : T.DR r k) : T.Cont (T.c2 (T.par (T.S1 r) k)) k := by
  rw [par_S1 hk.1 hk.2]
  have h0 := par_spec_good (good_S0 r) hk.1.1 hk.2
  rcases child_cases' h0.1 (par_nonleaf h0) h0.2.1 with h | ⟨_, h⟩
  · exact absurd ⟨hk.1.1, hk.2, h⟩ hk.1.2
  · exact h

/-! ## Regions with a single leaf, and the no-chain condition -/

/-- A node with a single leaf of `S` lies in a leaf region. -/
lemma leaf_down_of_unique {S : ℕ → Prop} {y : ℕ} (hy : T.nd y = true) (ha : T.alive S y)
    (hu : ∀ k1 k2, S k1 → S k2 → T.Cont y k1 → T.Cont y k2 → k1 = k2) :
    T.leaf (T.down S y) = true := by
  rcases down_shape hy ha with h | ⟨c, c', hc, hc', hne, ⟨k, hk, hkc⟩, ⟨k', hk', hkc'⟩⟩
  · exact h
  exfalso
  have hs := (down_prop (S := S) hy).2
  have e := hu k k' hk hk' ((hs k hk).2 (hc.cont hkc)) ((hs k' hk').2 (hc'.cont hkc'))
  subst e
  exact child_disjoint hc hc' hne hkc hkc'

/-- A node that loses all its leaves in a separated removal had a single leaf. -/
lemma unique_of_dead {S D : ℕ → Prop} (hsep : Sep S D) {y : ℕ}
    (hy' : ¬ T.alive (fun k => S k ∧ ¬ D k) y) :
    ∀ k1 k2, S k1 → S k2 → T.Cont y k1 → T.Cont y k2 → k1 = k2 := by
  have key : ∀ k1 k2, S k1 → S k2 → T.Cont y k1 → T.Cont y k2 → k1 < k2 → False := by
    intro k1 k2 h1 h2 c1 c2 hlt
    have d1 : D k1 := by by_contra h; exact hy' ⟨k1, ⟨h1, h⟩, c1⟩
    have d2 : D k2 := by by_contra h; exact hy' ⟨k2, ⟨h2, h⟩, c2⟩
    obtain ⟨m, hm, hmD, hm1, hm2⟩ := hsep k1 k2 d1 d2 hlt
    exact hy' ⟨m, ⟨hm, hmD⟩, ⟨by have := c1.1; omega, by have := c2.2; omega⟩⟩
  intro k1 k2 h1 h2 c1 c2
  rcases lt_trichotomy k1 k2 with h | h | h
  · exact (key _ _ h1 h2 c1 c2 h).elim
  · exact h
  · exact (key _ _ h2 h1 c2 c1 h).elim

/-- **No chained merges** (generic form): an alive child of the compressed parent of a removed
leaf lies in a leaf region or in a region that is not queried. -/
def NoChain (T : PT) (S D : ℕ → Prop) : Prop :=
  ∀ k, D k → ∀ c, T.IsChild (T.par S k) c → T.alive S c → T.leaf (T.down S c) = false →
    ¬ T.PSet S D (T.down S c)

lemma child_eq_cases {y c : ℕ} (hc : T.IsChild y c) : c = y + 1 ∨ c = T.c2 y := by
  rcases hc with ⟨_, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma leaf_down_child_par {S : ℕ → Prop} {k c : ℕ} (hc : T.IsChild (T.par S k) c)
    (ha : T.alive S c) (hkc : T.Cont c k) : T.leaf (T.down S c) = true :=
  leaf_down_of_unique hc.nd ha fun k1 k2 h1 h2 c1 c2 =>
    (par_child_only hc hkc k1 h1 c1).trans (par_child_only hc hkc k2 h2 c2).symm

lemma noChain_DL (r : ℕ) : T.NoChain (T.S0 r) (T.DL r) := by
  intro k hk c hc ha hl
  rcases child_eq_cases hc with rfl | rfl
  · rw [leaf_down_child_par hc ha hk.2.2] at hl; exact absurd hl (by simp)
  · exact noChain_L (good_S0 r) (fun k h => h) hk

lemma noChain_DR (r : ℕ) : T.NoChain (T.S1 r) (T.DR r) := by
  intro k hk c hc ha hl
  rcases child_eq_cases hc with rfl | rfl
  · exact noChain_R (good_S1 r) (fun k h => ⟨h.1, h.2, DR_c2 h⟩) hk
  · rw [leaf_down_child_par hc ha (DR_c2 hk)] at hl; exact absurd hl (by simp)

end PT

end PathChecking
