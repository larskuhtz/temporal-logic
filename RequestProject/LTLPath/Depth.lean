module

public import RequestProject.LTLPath.Sched

/-!
# Depth of nodes

`depth y` is the number of ancestors of `y` (including `y`).  A child is one level deeper than
its parent (`depth_child`), proper descendants are deeper (`depth_lt_of_anc`), and two
ancestors of the same node with the same depth are equal (`eq_of_depth_eq`).
-/

@[expose] public section

namespace PathChecking

namespace PT

variable {T : PT}

open Classical

/-- Number of ancestors of `y` (including `y`). -/
noncomputable def depth (T : PT) (y : ℕ) : ℕ :=
  ((Finset.range T.F).filter fun z => T.Anc z y).card

lemma anc_mem {z y : ℕ} (h : T.Anc z y) : z ∈ (Finset.range T.F).filter fun z => T.Anc z y :=
  Finset.mem_filter.2 ⟨Finset.mem_range.2 (lt_F h.1), h⟩

lemma depth_lt_of_anc {y z : ℕ} (h : T.Anc y z) (hne : y ≠ z) : T.depth y < T.depth z := by
  unfold depth
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hs => ?_⟩
  · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_filter.2 ⟨h1, h2.trans h⟩
  · have := (Finset.mem_filter.1 (hs (anc_mem (Anc.refl h.2.1)))).2
    have := this.2.2.1; have := h.2.2.1
    exact hne (by omega)

lemma depth_child {y c : ℕ} (hc : T.IsChild y c) : T.depth c = T.depth y + 1 := by
  unfold depth
  have hyc := hc.lt
  have e : ((Finset.range T.F).filter fun z => T.Anc z c) =
      insert c ((Finset.range T.F).filter fun z => T.Anc z y) := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hz, ha⟩
      by_cases hzc : z = c
      · exact Or.inl hzc
      right
      refine ⟨hz, ?_⟩
      by_cases hzy : z ≤ y
      · exact Anc.chain ha hc.anc hzy
      exfalso
      have hyz : T.Anc y z := Anc.chain hc.anc ha (by omega)
      obtain ⟨c', hc', hc'z⟩ := desc_child hyz (by omega)
      have := child_unique_of_anc hc hc' (Anc.refl hc.nd) (hc'z.trans ha)
      subst this
      have := hc'z.2.2.1; have := ha.2.2.1
      exact hzc (by omega)
    · rintro (rfl | ⟨hz, ha⟩)
      · exact ⟨lt_F hc.nd, Anc.refl hc.nd⟩
      · exact ⟨hz, ha.trans hc.anc⟩
  rw [e, Finset.card_insert_of_notMem]
  intro hm
  have := (Finset.mem_filter.1 hm).2.2.2.1
  omega

lemma eq_of_depth_eq {y y' d : ℕ} (h : T.Anc y d) (h' : T.Anc y' d)
    (he : T.depth y = T.depth y') : y = y' := by
  rcases le_total y y' with hl | hl
  · by_contra hne
    have := depth_lt_of_anc (Anc.chain h h' hl) hne; omega
  · by_contra hne
    have := depth_lt_of_anc (Anc.chain h' h hl) (Ne.symm hne); omega

lemma depth_le_of_anc {y z : ℕ} (h : T.Anc y z) : T.depth y ≤ T.depth z := by
  by_cases e : y = z
  · rw [e]
  · exact (depth_lt_of_anc h e).le

end PT

end PathChecking
