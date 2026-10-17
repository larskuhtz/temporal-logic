module

public import RequestProject.LTLPath.OIF

/-!
# Layered straight-line drawings are planar

`layeredDrawing`: if the vertices of a graph are placed on horizontal integer lines such that

* every edge joins two vertices on the same line or on adjacent lines,
* no vertex lies strictly inside a horizontal edge, and
* edges between two adjacent lines do not cross (their order on the upper line agrees with the
  order on the lower line),

then the straight-line drawing is planar.
-/

@[expose] public section

namespace PathChecking

lemma mem_segment_coords {p q z : ℝ × ℝ} (h : z ∈ segment ℝ p q) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ z.1 = (1 - θ) * p.1 + θ * q.1 ∧ z.2 = (1 - θ) * p.2 + θ * q.2 := by
  rw [segment_eq_image] at h
  obtain ⟨θ, ⟨h0, h1⟩, rfl⟩ := h
  exact ⟨θ, h0, h1, by simp, by simp⟩

/-- Hypotheses of a layered drawing. -/
structure Layered {V : Type*} (adj : V → V → Prop) (X : V → ℝ) (Y : V → ℤ) : Prop where
  symm : ∀ u v, adj u v → adj v u
  inj : ∀ u v, X u = X v → Y u = Y v → u = v
  band : ∀ u v, adj u v → Y u = Y v ∨ Y u = Y v + 1 ∨ Y v = Y u + 1
  hor : ∀ u v w, adj u v → Y u = Y v → Y w = Y u → ¬ (X u < X w ∧ X w < X v)
  cross : ∀ a a' b b', adj a a' → adj b b' → Y a = Y a' + 1 → Y b = Y b' + 1 → Y a = Y b →
    X a < X b → X a' ≤ X b'

namespace Layered

variable {V : Type*} {adj : V → V → Prop} {X : V → ℝ} {Y : V → ℤ}

/-- The position of a vertex. -/
def pos (X : V → ℝ) (Y : V → ℤ) (v : V) : ℝ × ℝ := (X v, (Y v : ℝ))

lemma pos_inj (h : Layered adj X Y) : Function.Injective (pos X Y) := by
  intro u v e
  simp only [pos, Prod.mk.injEq, Int.cast_inj] at e
  exact h.inj u v e.1 e.2

lemma int_unit {θ : ℝ} {k : ℤ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h : θ = k) : θ = 0 ∨ θ = 1 := by
  subst h
  have a : (0 : ℤ) ≤ k := by exact_mod_cast h0
  have b : k ≤ 1 := by exact_mod_cast h1
  interval_cases k <;> simp

/-- A point of an edge on an integer line is an endpoint, or the edge is horizontal and the
point lies strictly inside. -/
lemma int_point (h : Layered adj X Y) {u v : V} (huv : adj u v) {z : ℝ × ℝ}
    (hz : z ∈ segment ℝ (pos X Y u) (pos X Y v)) {k : ℤ} (hk : z.2 = k) :
    z = pos X Y u ∨ z = pos X Y v ∨
      (Y u = Y v ∧ Y u = k ∧ ((X u < z.1 ∧ z.1 < X v) ∨ (X v < z.1 ∧ z.1 < X u))) := by
  obtain ⟨θ, h0, h1, e1, e2⟩ := mem_segment_coords hz
  simp only [pos] at e1 e2
  rcases h.band u v huv with hb | hb | hb
  · rw [hb] at e2
    have hk' : Y v = k := by
      have : ((Y v : ℤ) : ℝ) = k := by rw [← hk, e2]; ring
      exact_mod_cast this
    rcases eq_or_lt_of_le h0 with h0' | h0'
    · left; ext <;> simp [pos, e1, e2, ← h0', hb]
    rcases eq_or_lt_of_le h1 with h1' | h1'
    · right; left; ext <;> simp [pos, e1, e2, h1']
    rcases lt_trichotomy (X u) (X v) with c | c | c
    · right; right
      exact ⟨hb, by rw [hb, hk'], Or.inl ⟨by rw [e1]; nlinarith, by rw [e1]; nlinarith⟩⟩
    · have : u = v := h.inj u v c hb
      subst this
      exact Or.inl (by ext <;> simp [pos, e1, e2] <;> ring)
    · right; right
      exact ⟨hb, by rw [hb, hk'], Or.inr ⟨by rw [e1]; nlinarith, by rw [e1]; nlinarith⟩⟩
  · rw [hb] at e2
    push_cast at e2
    have : θ = ((Y v + 1 - k : ℤ) : ℝ) := by push_cast; linarith
    rcases int_unit h0 h1 this with t | t
    · left; ext <;> simp [pos, e1, e2, t, hb]
    · right; left; ext <;> simp [pos, e1, e2, t]
  · rw [hb] at e2
    push_cast at e2
    have : θ = ((k - Y u : ℤ) : ℝ) := by push_cast; linarith
    rcases int_unit h0 h1 this with t | t
    · left; ext <;> simp [pos, e1, e2, t]
    · right; left; ext <;> simp [pos, e1, e2, t, hb]

/-- **Layered drawings are planar.** -/
def drawing (h : Layered adj X Y) : StraightLineDrawing adj where
  pos := pos X Y
  inj := h.pos_inj
  vertex_off_edge := by
    intro u v w huv hwu hwv hw
    have hk : (pos X Y w).2 = Y w := rfl
    rcases h.int_point huv hw hk with e | e | ⟨e1, e2, e3⟩
    · exact hwu (h.pos_inj e)
    · exact hwv (h.pos_inj e)
    · simp only [pos] at e3
      rcases e3 with e3 | e3
      · exact h.hor u v w huv e1 (e2.symm) e3
      · exact h.hor v u w (h.symm u v huv) e1.symm (by rw [← e2, e1]) e3
  edges_meet := by
    intro u v u' v' huv hu'v' hne1 hne2 z hz hz'
    by_cases hint : ∃ k : ℤ, z.2 = k
    · obtain ⟨k, hk⟩ := hint
      have A := h.int_point huv hz hk
      have B := h.int_point hu'v' hz' hk
      -- helper: an endpoint position strictly inside a horizontal edge is impossible
      have inside : ∀ (a b c : V), adj a b → Y a = Y b → Y a = k → z = pos X Y c →
          ((X a < z.1 ∧ z.1 < X b) ∨ (X b < z.1 ∧ z.1 < X a)) → False := by
        intro a b c hab hy hyk hc hin
        have hYc : Y c = k := by
          have : ((Y c : ℤ) : ℝ) = k := by rw [← hk, hc]; rfl
          exact_mod_cast this
        have hx : z.1 = X c := by rw [hc]; rfl
        rw [hx] at hin
        rcases hin with hin | hin
        · exact h.hor a b c hab hy (by rw [hYc, hyk]) hin
        · exact h.hor b a c (h.symm a b hab) hy.symm (by rw [hYc, ← hy, hyk]) hin
      rcases A with A | A | ⟨a1, a2, a3⟩ <;> rcases B with B | B | ⟨b1, b2, b3⟩
      · exact ⟨u, Or.inl rfl, Or.inl (h.pos_inj (A.symm.trans B)), A⟩
      · exact ⟨u, Or.inl rfl, Or.inr (h.pos_inj (A.symm.trans B)), A⟩
      · exact (inside u' v' u hu'v' b1 b2 A b3).elim
      · exact ⟨v, Or.inr rfl, Or.inl (h.pos_inj (A.symm.trans B)), A⟩
      · exact ⟨v, Or.inr rfl, Or.inr (h.pos_inj (A.symm.trans B)), A⟩
      · exact (inside u' v' v hu'v' b1 b2 A b3).elim
      · exact (inside u v u' huv a1 a2 B a3).elim
      · exact (inside u v v' huv a1 a2 B a3).elim
      · exfalso
        -- two horizontal edges on the same line overlapping in an inner point
        have hY : ∀ c : V, Y c = k → (c = u ∨ c = v) → (c = u' ∨ c = v') → False → True :=
          fun _ _ _ _ _ => trivial
        clear hY
        have endp : ∀ (c : V) (a b : V), adj a b → Y a = Y b → Y a = k → Y c = k →
            ((X a < X c ∧ X c < X b) ∨ (X b < X c ∧ X c < X a)) → False := by
          intro c a b hab hy hyk hyc hin
          rcases hin with hin | hin
          · exact h.hor a b c hab hy (by rw [hyc, hyk]) hin
          · exact h.hor b a c (h.symm a b hab) hy.symm (by rw [hyc, ← hy, hyk]) hin
        have hYu : Y u = k := a2
        have hYv : Y v = k := by rw [← a1, a2]
        have hYu' : Y u' = k := b2
        have hYv' : Y v' = k := by rw [← b1, b2]
        have e := endp
        have nu' := e u' u v huv a1 a2 hYu'
        have nv' := e v' u v huv a1 a2 hYv'
        have nu := e u u' v' hu'v' b1 b2 hYu
        have nv := e v u' v' hu'v' b1 b2 hYv
        have xinj : ∀ c d : V, Y c = k → Y d = k → X c = X d → c = d :=
          fun c d hc hd hx => h.inj c d hx (by rw [hc, hd])
        rcases a3 with a3 | a3 <;> rcases b3 with b3 | b3
        · have h1 : X u = X u' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nu' (Or.inl ⟨hh, by linarith⟩)
            · exact nu (Or.inl ⟨hh, by linarith⟩)
          have h2 : X v = X v' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nv (Or.inl ⟨by linarith, hh⟩)
            · exact nv' (Or.inl ⟨by linarith, hh⟩)
          exact hne1 ⟨xinj _ _ hYu hYu' h1, xinj _ _ hYv hYv' h2⟩
        · have h1 : X u = X v' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nv' (Or.inl ⟨hh, by linarith⟩)
            · exact nu (Or.inr ⟨hh, by linarith⟩)
          have h2 : X v = X u' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nv (Or.inr ⟨by linarith, hh⟩)
            · exact nu' (Or.inl ⟨by linarith, hh⟩)
          exact hne2 ⟨xinj _ _ hYu hYv' h1, xinj _ _ hYv hYu' h2⟩
        · have h1 : X v = X u' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nu' (Or.inr ⟨hh, by linarith⟩)
            · exact nv (Or.inl ⟨hh, by linarith⟩)
          have h2 : X u = X v' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nu (Or.inl ⟨by linarith, hh⟩)
            · exact nv' (Or.inr ⟨by linarith, hh⟩)
          exact hne2 ⟨xinj _ _ hYu hYv' h2, xinj _ _ hYv hYu' h1⟩
        · have h1 : X v = X v' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nv' (Or.inr ⟨hh, by linarith⟩)
            · exact nv (Or.inr ⟨hh, by linarith⟩)
          have h2 : X u = X u' := by
            by_contra hh
            rcases lt_or_gt_of_ne hh with hh | hh
            · exact nu (Or.inr ⟨by linarith, hh⟩)
            · exact nu' (Or.inr ⟨by linarith, hh⟩)
          exact hne1 ⟨xinj _ _ hYu hYu' h2, xinj _ _ hYv hYv' h1⟩
    · exfalso
      -- both edges are band edges of the same band, with the same parameter
      have orient : ∀ a b : V, adj a b → z ∈ segment ℝ (pos X Y a) (pos X Y b) →
          ∃ t d θ, adj t d ∧ Y t = Y d + 1 ∧ ((t = a ∧ d = b) ∨ (t = b ∧ d = a)) ∧
            0 < θ ∧ θ < 1 ∧ z.1 = (1 - θ) * X t + θ * X d ∧ z.2 = Y t - θ := by
        intro a b hab hz
        obtain ⟨θ, h0, h1, e1, e2⟩ := mem_segment_coords hz
        simp only [pos] at e1 e2
        have h0' : 0 < θ := by
          rcases eq_or_lt_of_le h0 with e | e
          · exact (hint ⟨Y a, by rw [e2, ← e]; ring⟩).elim
          · exact e
        have h1' : θ < 1 := by
          rcases eq_or_lt_of_le h1 with e | e
          · exact (hint ⟨Y b, by rw [e2, e]; ring⟩).elim
          · exact e
        rcases h.band a b hab with hb | hb | hb
        · exact (hint ⟨Y b, by rw [e2, hb]; ring⟩).elim
        · exact ⟨a, b, θ, hab, hb, Or.inl ⟨rfl, rfl⟩, h0', h1', e1, by rw [e2, hb]; push_cast; ring⟩
        · refine ⟨b, a, 1 - θ, h.symm a b hab, hb, Or.inr ⟨rfl, rfl⟩, by linarith, by linarith,
            by rw [e1]; ring, by rw [e2, hb]; push_cast; ring⟩
      obtain ⟨t, d, θ, htd, hy, ho, h0, h1, e1, e2⟩ := orient u v huv hz
      obtain ⟨t', d', θ', htd', hy', ho', h0', h1', e1', e2'⟩ := orient u' v' hu'v' hz'
      have hθ : ∃ m : ℤ, θ' = θ + m := ⟨Y t' - Y t, by push_cast; linarith⟩
      obtain ⟨m, hm⟩ := hθ
      have hm0 : m = 0 := by
        have a : (-1 : ℝ) < m := by linarith
        have b : (m : ℝ) < 1 := by linarith
        have a' : (-1 : ℤ) < m := by exact_mod_cast a
        have b' : m < 1 := by exact_mod_cast b
        omega
      subst hm0
      simp only [Int.cast_zero, add_zero] at hm
      rw [hm] at e1' e2'
      have hYt : Y t = Y t' := by
        have : ((Y t : ℤ) : ℝ) = Y t' := by linarith
        exact_mod_cast this
      rcases lt_trichotomy (X t) (X t') with c | c | c
      · have := h.cross t d t' d' htd htd' hy hy' hYt c
        have : (1 - θ) * X t + θ * X d < (1 - θ) * X t' + θ * X d' := by nlinarith
        linarith
      · have htt : t = t' := h.inj t t' c hYt
        subst htt
        have hd : X d = X d' := by
          have : θ * X d = θ * X d' := by linarith
          exact mul_left_cancel₀ (ne_of_gt h0) this
        have hdd : d = d' := h.inj d d' hd (by omega)
        subst hdd
        rcases ho with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases ho' with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> subst_vars <;>
          simp_all
      · have := h.cross t' d' t d htd' htd hy' hy hYt.symm c
        have : (1 - θ) * X t' + θ * X d' < (1 - θ) * X t + θ * X d := by nlinarith
        linarith

end Layered

end PathChecking
