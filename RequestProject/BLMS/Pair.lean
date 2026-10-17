module

public import RequestProject.BLMS.Layered

/-!
# Discarding and merging intervals

The two key facts behind the algorithm of [BLMS, Section 5], stated for the abstract layered
circuits of `RequestProject/BLMS/Layered.lean`:

* `LC.discard`: an interval `I` that dies (alone) at layer `e + 1` can be removed from the input
  if the evaluation of `I` together with its left neighbour `H` and with its right neighbour `J`
  shows no interaction (`PushData H I e`, `DiscData I J e`);
* `LC.merge`: if two neighbouring intervals `I`, `J` merge in the evaluation of `I ∪ J` alone
  (`MergeData I J e`), then the gap between them can be filled.

Both facts are a precise version of [BLMS, Propositions 8 and 9].  The conditions on simultaneous
deaths (`PushData.fin`, `DiscData.fin`) are needed: without them the algorithm of [BLMS] as stated
in the paper may give a wrong answer.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

open Set

namespace LC

variable (c : LC)

/-- `X` lies to the left of `Y`, with at least one position between them. -/
def Sep (X Y : Set ℕ) : Prop := ∀ x ∈ X, ∀ y ∈ Y, x + 1 < y

/-- At layer `l` the images of `I` and `J` are nonempty and separated. -/
def PSep (I J : Set ℕ) (l : ℕ) : Prop :=
  (c.ev l I).Nonempty ∧ (c.ev l J).Nonempty ∧ Sep (c.ev l I) (c.ev l J)

/-- An `AND` gate of layer `l + 1` with one argument in the image of `I` and one in the image
of `J`. -/
def Bridge (I J : Set ℕ) (l : ℕ) : Prop :=
  ∃ i ∈ c.gates l, c.isAnd i = true ∧ c.lo i ∈ c.ev l I ∧ c.hi i ∈ c.ev l J

/-- An `AND` gate of layer `l + 1` with its left argument in the image of `I` and its right
argument beyond the image of `J`. -/
def RSpan (I J : Set ℕ) (l : ℕ) : Prop :=
  ∃ i ∈ c.gates l, c.isAnd i = true ∧ c.lo i ∈ c.ev l I ∧ ∀ y ∈ c.ev l J, y < c.hi i

/-- An `AND` gate of layer `l + 1` with its right argument in the image of `J` and its left
argument before the image of `I`. -/
def LSpan (I J : Set ℕ) (l : ℕ) : Prop :=
  ∃ i ∈ c.gates l, c.isAnd i = true ∧ c.hi i ∈ c.ev l J ∧ ∀ x ∈ c.ev l I, c.lo i < x

/-- The images of `I` and `J` at layer `l + 1` are both nonempty but not separated. -/
def Touch (I J : Set ℕ) (l : ℕ) : Prop :=
  (c.ev (l + 1) I).Nonempty ∧ (c.ev (l + 1) J).Nonempty ∧ ¬ Sep (c.ev (l + 1) I) (c.ev (l + 1) J)

/-- `I` dies at layer `e + 1` without interacting with its left neighbour `H`. -/
structure PushData (H I : Set ℕ) (e : ℕ) : Prop where
  sep : ∀ l ≤ e, c.PSep H I l
  nob : ∀ l ≤ e, ¬ c.Bridge H I l
  dead : c.ev (e + 1) I = ∅
  fin : (c.ev (e + 1) H).Nonempty ∨ ¬ c.LSpan H I e

/-- `I` dies at layer `e + 1` without interacting with its right neighbour `J`. -/
structure DiscData (I J : Set ℕ) (e : ℕ) : Prop where
  sep : ∀ l ≤ e, c.PSep I J l
  nob : ∀ l ≤ e, ¬ c.Bridge I J l
  dead : c.ev (e + 1) I = ∅
  fin : (c.ev (e + 1) J).Nonempty ∨ ¬ c.RSpan I J e

/-- `I` and `J` merge at layer `e + 1`. -/
structure MergeData (I J : Set ℕ) (e : ℕ) : Prop where
  sep : ∀ l ≤ e, c.PSep I J l
  nob : ∀ l < e, ¬ c.Bridge I J l
  ev : c.Bridge I J e ∨ c.Touch I J e

variable {c}

lemma lt_of_le_not_mem {X : Set ℕ} (hX : X.OrdConnected) {z x : ℕ} (hx : x ∈ X) (hzx : z ≤ x)
    (hz : z ∉ X) : ∀ y ∈ X, z < y := by
  intro y hy
  by_contra h
  exact hz (hX.out hy hx ⟨by omega, hzx⟩)

lemma gt_of_ge_not_mem {X : Set ℕ} (hX : X.OrdConnected) {z x : ℕ} (hx : x ∈ X) (hzx : x ≤ z)
    (hz : z ∉ X) : ∀ y ∈ X, y < z := by
  intro y hy
  by_contra h
  exact hz (hX.out hx hy ⟨hzx, by omega⟩)

/-- The core of `discard`, with abstract left and right windows. -/
lemma discard_core (hP : c.Planar) {A B I : Set ℕ} {e : ℕ} (he : e < c.D)
    (Lft Rgt : ℕ → Set ℕ) (hIe : ∀ l ≤ e, (c.ev l I).Nonempty) (hId : c.ev (e + 1) I = ∅)
    (h0 : A ∪ B ⊆ Lft 0 ∪ Rgt 0)
    (hL1 : ∀ l < e, c.step l (Lft l) ⊆ Lft (l + 1))
    (hR1 : ∀ l < e, c.step l (Rgt l) ⊆ Rgt (l + 1))
    (hLI : ∀ l ≤ e, ∀ z ∈ Lft l, ∀ x ∈ c.ev l I, z < x)
    (hIR : ∀ l ≤ e, ∀ x ∈ c.ev l I, ∀ z ∈ Rgt l, x < z)
    (hmL : ∀ l ≤ e, ∀ i ∈ c.gates l, c.isAnd i = true → ¬ (c.lo i ∈ Lft l ∧ c.hi i ∈ c.ev l I))
    (hmR : ∀ l ≤ e, ∀ i ∈ c.gates l, c.isAnd i = true → ¬ (c.lo i ∈ c.ev l I ∧ c.hi i ∈ Rgt l)) :
    c.ev c.D (A ∪ B ∪ I) = c.ev c.D (A ∪ B) := by
  -- the window invariant
  have win : ∀ l ≤ e, c.ev l (A ∪ B) ⊆ Lft l ∪ Rgt l := by
    intro l
    induction l with
    | zero => intro _; exact h0
    | succ l ih =>
      intro hl
      have hsub := c.step_mono (ih (by omega)) l
      refine fun z hz => ?_
      have hz' := hsub hz
      -- no `AND` gate is split between the two windows: it would kill `I`
      have hsplit : ∀ i ∈ c.gates l, c.isAnd i = true → c.lo i ∈ Lft l ∪ Rgt l →
          c.hi i ∈ Lft l ∪ Rgt l →
          (c.lo i ∈ Lft l ∧ c.hi i ∈ Lft l) ∨ (c.lo i ∈ Rgt l ∧ c.hi i ∈ Rgt l) := by
        intro i hi hA h1 h2
        obtain ⟨x, hx⟩ := hIe l (by omega)
        have hle := hP.le l (by omega) i hi
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact Or.inl ⟨h1, h2⟩
        · exfalso
          have hkill : c.step l (c.ev l I) = ∅ := step_eq_empty_of_span hP (by omega) hi
            (fun y hy => ⟨hLI l (by omega) _ h1 y hy, hIR l (by omega) y hy _ h2⟩)
          have := hIe (l + 1) hl
          rw [ev_succ, hkill] at this
          exact this.ne_empty rfl
        · exfalso
          have a1 := hIR l (by omega) x hx _ h1
          have a2 := hLI l (by omega) _ h2 x hx
          omega
        · exact Or.inr ⟨h1, h2⟩
      rw [step_union hsplit] at hz'
      rcases hz' with hz' | hz'
      · exact Or.inl (hL1 l (by omega) hz')
      · exact Or.inr (hR1 l (by omega) hz')
  -- evaluation splits until `I` dies
  have split : ∀ l ≤ e + 1, c.ev l (A ∪ B ∪ I) = c.ev l (A ∪ B) ∪ c.ev l I := by
    intro l
    induction l with
    | zero => intro _; rfl
    | succ l ih =>
      intro hl
      rw [ev_succ, ih (by omega), ev_succ, ev_succ]
      apply step_union
      intro i hi hA h1 h2
      have w := win l (by omega)
      by_cases hlo : c.lo i ∈ c.ev l I <;> by_cases hhi : c.hi i ∈ c.ev l I
      · exact Or.inr ⟨hlo, hhi⟩
      · have h2' : c.hi i ∈ c.ev l (A ∪ B) := by
          rcases h2 with h2 | h2
          · exact h2
          · exact absurd h2 hhi
        rcases w h2' with h | h
        · exfalso
          have := hLI l (by omega) _ h _ hlo
          have := hP.le l (by omega) i hi
          omega
        · exact absurd ⟨hlo, h⟩ (hmR l (by omega) i hi hA)
      · have h1' : c.lo i ∈ c.ev l (A ∪ B) := by
          rcases h1 with h1 | h1
          · exact h1
          · exact absurd h1 hlo
        rcases w h1' with h | h
        · exact absurd ⟨h, hhi⟩ (hmL l (by omega) i hi hA)
        · exfalso
          have := hIR l (by omega) _ hhi _ h
          have := hP.le l (by omega) i hi
          omega
      · have h1' : c.lo i ∈ c.ev l (A ∪ B) := by
          rcases h1 with h1 | h1
          · exact h1
          · exact absurd h1 hlo
        have h2' : c.hi i ∈ c.ev l (A ∪ B) := by
          rcases h2 with h2 | h2
          · exact h2
          · exact absurd h2 hhi
        exact Or.inl ⟨h1', h2'⟩
  have heq : c.ev (e + 1) (A ∪ B ∪ I) = c.ev (e + 1) (A ∪ B) := by
    rw [split (e + 1) le_rfl, hId, union_empty]
  exact ev_congr heq _ (by omega)

/-- Facts about the left window `{z | ∃ h ∈ ev l H, z ≤ h}`. -/
lemma left_window (hP : c.Planar) {H I : Set ℕ} {e : ℕ} (he : e < c.D) (hH : H.OrdConnected)
    (hd : c.PushData H I e) :
    (∀ l < e, c.step l {z | ∃ h ∈ c.ev l H, z ≤ h} ⊆ {z | ∃ h ∈ c.ev (l + 1) H, z ≤ h}) ∧
    (∀ l ≤ e, ∀ z ∈ {z | ∃ h ∈ c.ev l H, z ≤ h}, ∀ x ∈ c.ev l I, z < x) ∧
    (∀ l ≤ e, ∀ i ∈ c.gates l, c.isAnd i = true →
      ¬ (c.lo i ∈ {z | ∃ h ∈ c.ev l H, z ≤ h} ∧ c.hi i ∈ c.ev l I)) := by
  refine ⟨fun l hl => ?_, fun l hl z hz x hx => ?_, fun l hl i hi hA => ?_⟩
  · intro z hz
    exact step_right_bound hP (by omega) (ev_ordConnected hP hH l (by omega))
      ((hd.sep (l + 1) (by omega)).1) (fun z hz => hz) z hz
  · obtain ⟨h, hh, hzh⟩ := hz
    have := (hd.sep l hl).2.2 h hh x hx
    omega
  · rintro ⟨⟨h, hh, hlo⟩, hhi⟩
    by_cases hm : c.lo i ∈ c.ev l H
    · exact hd.nob l hl ⟨i, hi, hA, hm, hhi⟩
    have hlt := lt_of_le_not_mem (ev_ordConnected hP hH l (by omega)) hh hlo hm
    have hkill : c.step l (c.ev l H) = ∅ := step_eq_empty_of_span hP (by omega) hi
      (fun y hy => ⟨hlt y hy, by have := (hd.sep l hl).2.2 y hy _ hhi; omega⟩)
    rcases Nat.lt_or_ge l e with hle | hle
    · have := (hd.sep (l + 1) (by omega)).1
      rw [ev_succ, hkill] at this
      exact this.ne_empty rfl
    · have hle' : l = e := by omega
      subst hle'
      rcases hd.fin with hf | hf
      · rw [ev_succ, hkill] at hf
        exact hf.ne_empty rfl
      · exact hf ⟨i, hi, hA, hhi, hlt⟩

/-- Facts about the right window `{z | ∃ j ∈ ev l J, j ≤ z}`. -/
lemma right_window (hP : c.Planar) {I J : Set ℕ} {e : ℕ} (he : e < c.D) (hJ : J.OrdConnected)
    (hd : c.DiscData I J e) :
    (∀ l < e, c.step l {z | ∃ j ∈ c.ev l J, j ≤ z} ⊆ {z | ∃ j ∈ c.ev (l + 1) J, j ≤ z}) ∧
    (∀ l ≤ e, ∀ x ∈ c.ev l I, ∀ z ∈ {z | ∃ j ∈ c.ev l J, j ≤ z}, x < z) ∧
    (∀ l ≤ e, ∀ i ∈ c.gates l, c.isAnd i = true →
      ¬ (c.lo i ∈ c.ev l I ∧ c.hi i ∈ {z | ∃ j ∈ c.ev l J, j ≤ z})) := by
  refine ⟨fun l hl => ?_, fun l hl x hx z hz => ?_, fun l hl i hi hA => ?_⟩
  · intro z hz
    exact step_left_bound hP (by omega) (ev_ordConnected hP hJ l (by omega))
      ((hd.sep (l + 1) (by omega)).2.1) (fun z hz => hz) z hz
  · obtain ⟨j, hj, hjz⟩ := hz
    have := (hd.sep l hl).2.2 x hx j hj
    omega
  · rintro ⟨hlo, ⟨j, hj, hhi⟩⟩
    by_cases hm : c.hi i ∈ c.ev l J
    · exact hd.nob l hl ⟨i, hi, hA, hlo, hm⟩
    have hgt := gt_of_ge_not_mem (ev_ordConnected hP hJ l (by omega)) hj hhi hm
    have hkill : c.step l (c.ev l J) = ∅ := step_eq_empty_of_span hP (by omega) hi
      (fun y hy => ⟨by have := (hd.sep l hl).2.2 _ hlo y hy; omega, hgt y hy⟩)
    rcases Nat.lt_or_ge l e with hle | hle
    · have := (hd.sep (l + 1) (by omega)).2.1
      rw [ev_succ, hkill] at this
      exact this.ne_empty rfl
    · have hle' : l = e := by omega
      subst hle'
      rcases hd.fin with hf | hf
      · rw [ev_succ, hkill] at hf
        exact hf.ne_empty rfl
      · exact hf ⟨i, hi, hA, hlo, hgt⟩

/-- **Discarding a dying interval** (a precise version of [BLMS, Proposition 9]).  `A` is the
part of the input to the left of `I`, bounded by the left neighbour `H` of `I`, and `B` the part
to the right of `I`, bounded by the right neighbour `J`; either part may be empty. -/
theorem discard (hP : c.Planar) {A B I : Set ℕ} {e : ℕ} (he : e < c.D)
    (hIe : ∀ l ≤ e, (c.ev l I).Nonempty) (hId : c.ev (e + 1) I = ∅)
    (hL : A = ∅ ∨ ∃ H : Set ℕ, H.OrdConnected ∧ (∀ a ∈ A, ∃ h ∈ H, a ≤ h) ∧ c.PushData H I e)
    (hR : B = ∅ ∨ ∃ J : Set ℕ, J.OrdConnected ∧ (∀ b ∈ B, ∃ j ∈ J, j ≤ b) ∧ c.DiscData I J e) :
    c.ev c.D (A ∪ B ∪ I) = c.ev c.D (A ∪ B) := by
  obtain ⟨Lft, hA0, hL1, hLI, hmL⟩ : ∃ Lft : ℕ → Set ℕ, A ⊆ Lft 0 ∧
      (∀ l < e, c.step l (Lft l) ⊆ Lft (l + 1)) ∧
      (∀ l ≤ e, ∀ z ∈ Lft l, ∀ x ∈ c.ev l I, z < x) ∧
      (∀ l ≤ e, ∀ i ∈ c.gates l, c.isAnd i = true → ¬ (c.lo i ∈ Lft l ∧ c.hi i ∈ c.ev l I)) := by
    rcases hL with rfl | ⟨H, hH, hAH, hd⟩
    · exact ⟨fun _ => ∅, empty_subset _, fun l _ => by simp [step_empty],
        fun _ _ _ h => absurd h (notMem_empty _), fun _ _ _ _ _ h => notMem_empty _ h.1⟩
    · obtain ⟨a1, a2, a3⟩ := left_window hP he hH hd
      exact ⟨fun l => {z | ∃ h ∈ c.ev l H, z ≤ h}, hAH, a1, a2, a3⟩
  obtain ⟨Rgt, hB0, hR1, hIR, hmR⟩ : ∃ Rgt : ℕ → Set ℕ, B ⊆ Rgt 0 ∧
      (∀ l < e, c.step l (Rgt l) ⊆ Rgt (l + 1)) ∧
      (∀ l ≤ e, ∀ x ∈ c.ev l I, ∀ z ∈ Rgt l, x < z) ∧
      (∀ l ≤ e, ∀ i ∈ c.gates l, c.isAnd i = true → ¬ (c.lo i ∈ c.ev l I ∧ c.hi i ∈ Rgt l)) := by
    rcases hR with rfl | ⟨J, hJ, hBJ, hd⟩
    · exact ⟨fun _ => ∅, empty_subset _, fun l _ => by simp [step_empty],
        fun _ _ _ _ _ h => absurd h (notMem_empty _), fun _ _ _ _ _ h => notMem_empty _ h.2⟩
    · obtain ⟨a1, a2, a3⟩ := right_window hP he hJ hd
      exact ⟨fun l => {z | ∃ j ∈ c.ev l J, j ≤ z}, hBJ, a1, a2, a3⟩
  exact discard_core hP he Lft Rgt hIe hId (union_subset_union hA0 hB0) hL1 hR1 hLI hIR hmL hmR

/-- **Merging two intervals** (a precise version of [BLMS, Proposition 8]): if `I` and `J` merge
in the evaluation of `I ∪ J`, then any set `G` of positions between them can be added to the
input. -/
theorem merge (hP : c.Planar) {A B I J G : Set ℕ} {e : ℕ} (he : e < c.D)
    (hI : I.OrdConnected) (hJ : J.OrdConnected)
    (hA : ∀ a ∈ A, ∀ x ∈ I, a < x) (hB : ∀ b ∈ B, ∀ y ∈ J, y < b)
    (hG : ∀ z ∈ G, (∀ x ∈ I, x < z) ∧ ∀ y ∈ J, z < y) (hM : c.MergeData I J e) :
    c.ev c.D (A ∪ I ∪ J ∪ B ∪ G) = c.ev c.D (A ∪ I ∪ J ∪ B) := by
  set Y := A ∪ I ∪ J ∪ B with hY
  have oI : ∀ l ≤ e, (c.ev l I).OrdConnected := fun l hl => ev_ordConnected hP hI l (by omega)
  have oJ : ∀ l ≤ e, (c.ev l J).OrdConnected := fun l hl => ev_ordConnected hP hJ l (by omega)
  -- (a) the window invariant
  have win : ∀ l ≤ e, c.ev l Y ⊆ {z | ∃ x ∈ c.ev l I, z ≤ x} ∪ {z | ∃ y ∈ c.ev l J, y ≤ z} := by
    intro l
    induction l with
    | zero =>
      intro _
      obtain ⟨x0, hx0⟩ := (hM.sep 0 (Nat.zero_le _)).1
      obtain ⟨y0, hy0⟩ := (hM.sep 0 (Nat.zero_le _)).2.1
      rintro z (((hz | hz) | hz) | hz)
      · exact Or.inl ⟨x0, hx0, le_of_lt (hA z hz x0 hx0)⟩
      · exact Or.inl ⟨z, hz, le_rfl⟩
      · exact Or.inr ⟨z, hz, le_rfl⟩
      · exact Or.inr ⟨y0, hy0, le_of_lt (hB z hz y0 hy0)⟩
    | succ l ih =>
      intro hl
      have hsub := c.step_mono (ih (by omega)) l
      have hsplit : ∀ i ∈ c.gates l, c.isAnd i = true →
          c.lo i ∈ {z | ∃ x ∈ c.ev l I, z ≤ x} ∪ {z | ∃ y ∈ c.ev l J, y ≤ z} →
          c.hi i ∈ {z | ∃ x ∈ c.ev l I, z ≤ x} ∪ {z | ∃ y ∈ c.ev l J, y ≤ z} →
          (c.lo i ∈ {z | ∃ x ∈ c.ev l I, z ≤ x} ∧ c.hi i ∈ {z | ∃ x ∈ c.ev l I, z ≤ x}) ∨
          (c.lo i ∈ {z | ∃ y ∈ c.ev l J, y ≤ z} ∧ c.hi i ∈ {z | ∃ y ∈ c.ev l J, y ≤ z}) := by
        intro i hi hA' h1 h2
        have hs := (hM.sep l (by omega)).2.2
        have hle := hP.le l (by omega) i hi
        rcases h1 with ⟨x, hx, h1⟩ | ⟨y, hy, h1⟩ <;> rcases h2 with ⟨x', hx', h2⟩ | ⟨y', hy', h2⟩
        · exact Or.inl ⟨⟨x, hx, h1⟩, ⟨x', hx', h2⟩⟩
        · exfalso
          by_cases hlo : c.lo i ∈ c.ev l I
          · by_cases hhi : c.hi i ∈ c.ev l J
            · exact hM.nob l (by omega) ⟨i, hi, hA', hlo, hhi⟩
            · have hgt := gt_of_ge_not_mem (oJ l (by omega)) hy' h2 hhi
              have hk : c.step l (c.ev l J) = ∅ := step_eq_empty_of_span hP (by omega) hi
                (fun y hy => ⟨by have := hs _ hlo y hy; omega, hgt y hy⟩)
              have := (hM.sep (l + 1) hl).2.1
              rw [ev_succ, hk] at this
              exact this.ne_empty rfl
          · have hlt := lt_of_le_not_mem (oI l (by omega)) hx h1 hlo
            have hk : c.step l (c.ev l I) = ∅ := step_eq_empty_of_span hP (by omega) hi
              (fun y hy => ⟨hlt y hy, by have := hs y hy y' hy'; omega⟩)
            have := (hM.sep (l + 1) hl).1
            rw [ev_succ, hk] at this
            exact this.ne_empty rfl
        · exfalso
          have := hs x' hx' y hy
          omega
        · exact Or.inr ⟨⟨y, hy, h1⟩, ⟨y', hy', h2⟩⟩
      intro z hz
      have hz' := hsub hz
      rw [step_union hsplit] at hz'
      rcases hz' with hz' | hz'
      · exact Or.inl (step_right_bound hP (by omega) (oI l (by omega)) (hM.sep (l + 1) hl).1
          (fun z hz => hz) z hz')
      · exact Or.inr (step_left_bound hP (by omega) (oJ l (by omega)) (hM.sep (l + 1) hl).2.1
          (fun z hz => hz) z hz')
  -- a gate that is true on `Y' ⊆ Y ∪ gap` but not on `Y` reads a gap position
  have readsGap : ∀ l ≤ e, ∀ z, c.ev l (Y ∪ G) ⊆ c.ev l Y ∪
      {z | (∀ x ∈ c.ev l I, x < z) ∧ ∀ y ∈ c.ev l J, z < y} →
      z ∈ c.step l (c.ev l (Y ∪ G)) → z ∉ c.step l (c.ev l Y) →
      z ∈ c.gates l ∧ ∃ a, (a = c.lo z ∨ a = c.hi z) ∧
        (∀ x ∈ c.ev l I, x < a) ∧ ∀ y ∈ c.ev l J, a < y := by
    intro l hl z hsub hz hnz
    refine ⟨hz.1, ?_⟩
    have hmono : c.ev l Y ⊆ c.ev l (Y ∪ G) := c.ev_mono subset_union_left l
    by_contra hcon
    push_neg at hcon
    apply hnz
    refine ⟨hz.1, ?_⟩
    have key : ∀ a, (a = c.lo z ∨ a = c.hi z) → a ∈ c.ev l (Y ∪ G) → a ∈ c.ev l Y := by
      intro a ha hmem
      rcases hsub hmem with h | h
      · exact h
      · exfalso
        obtain ⟨x, hx, hxa⟩ : ∃ x ∈ c.ev l I, a ≤ x := by
          by_contra hh
          push_neg at hh
          obtain ⟨y, hy, hya⟩ := hcon a ha (fun x hx => hh x hx)
          exact absurd (h.2 y hy) (by omega)
        exact absurd (h.1 x hx) (by omega)
    have hv := hz.2
    unfold gval at hv ⊢
    split_ifs at hv ⊢
    · exact ⟨key _ (Or.inl rfl) hv.1, key _ (Or.inr rfl) hv.2⟩
    · rcases hv with hv | hv
      · exact Or.inl (key _ (Or.inl rfl) hv)
      · exact Or.inr (key _ (Or.inr rfl) hv)
  -- such a gate lies strictly between the images of `I` and `J`
  have between : ∀ l ≤ e, ∀ z, z ∈ c.gates l → z ∉ c.step l (c.ev l Y) →
      (∃ a, (a = c.lo z ∨ a = c.hi z) ∧ (∀ x ∈ c.ev l I, x < a) ∧ ∀ y ∈ c.ev l J, a < y) →
      (∀ x ∈ c.ev (l + 1) I, x < z) ∧ ∀ y ∈ c.ev (l + 1) J, z < y := by
    intro l hl z hzg hnz ⟨a, ha, haI, haJ⟩
    have hlez := hP.le l (by omega) z hzg
    have haz : c.lo z ≤ a ∧ a ≤ c.hi z := by rcases ha with rfl | rfl <;> omega
    constructor
    · intro x hx
      rcases lt_trichotomy x z with h | rfl | h
      · exact h
      · exact absurd (c.step_mono (c.ev_mono (by intro t ht; simp [hY]; tauto) l) l hx) hnz
      · exfalso
        have h1 := hP.mono l (by omega) z hzg x hx.1 h
        have hlex := hP.le l (by omega) x hx.1
        obtain ⟨x0, hx0, hx0le⟩ : ∃ x0 ∈ c.ev l I, c.lo x ≤ x0 := by
          have := hx.2; unfold gval at this
          split_ifs at this
          · exact ⟨_, this.1, le_rfl⟩
          · rcases this with h | h
            · exact ⟨_, h, le_rfl⟩
            · exact ⟨_, h, hlex⟩
        have := haI x0 hx0
        omega
    · intro y hy
      rcases lt_trichotomy z y with h | rfl | h
      · exact h
      · exact absurd (c.step_mono (c.ev_mono (by intro t ht; simp [hY]; tauto) l) l hy) hnz
      · exfalso
        have h1 := hP.mono l (by omega) y hy.1 z hzg h
        have hley := hP.le l (by omega) y hy.1
        obtain ⟨y0, hy0, hy0le⟩ : ∃ y0 ∈ c.ev l J, y0 ≤ c.hi y := by
          have := hy.2; unfold gval at this
          split_ifs at this
          · exact ⟨_, this.2, le_rfl⟩
          · rcases this with h | h
            · exact ⟨_, h, hley⟩
            · exact ⟨_, h, le_rfl⟩
        have := haJ y0 hy0
        omega
  -- (b) the extra positions stay in the gap
  have gap : ∀ l ≤ e, c.ev l (Y ∪ G) ⊆ c.ev l Y ∪
      {z | (∀ x ∈ c.ev l I, x < z) ∧ ∀ y ∈ c.ev l J, z < y} := by
    intro l
    induction l with
    | zero =>
      intro _ z hz
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (hG z hz)
    | succ l ih =>
      intro hl z hz
      by_cases hz' : z ∈ c.step l (c.ev l Y)
      · exact Or.inl hz'
      · obtain ⟨hzg, hex⟩ := readsGap l (by omega) z (ih (by omega)) hz hz'
        exact Or.inr (between l (by omega) z hzg hz' hex)
  -- (c) at layer `e + 1` the two evaluations agree
  have last : c.ev (e + 1) (Y ∪ G) = c.ev (e + 1) Y := by
    refine subset_antisymm (fun z hz => ?_) (c.ev_mono subset_union_left _)
    by_contra hnz
    obtain ⟨hzg, a, ha, haI, haJ⟩ := readsGap e le_rfl z (gap e le_rfl) hz hnz
    have hlez := hP.le e he z hzg
    have haz : c.lo z ≤ a ∧ a ≤ c.hi z := by rcases ha with rfl | rfl <;> omega
    rcases hM.ev with ⟨b, hb, hbA, hbI, hbJ⟩ | ⟨hIn, hJn, hns⟩
    · rcases lt_trichotomy z b with h | rfl | h
      · have := hP.mono e he z hzg b hb h
        have := haI _ hbI
        omega
      · have := haI _ hbI
        have := haJ _ hbJ
        omega
      · have := hP.mono e he b hb z hzg h
        have := haJ _ hbJ
        have := hP.le e he b hb
        omega
    · obtain ⟨hbI, hbJ⟩ := between e le_rfl z hzg hnz ⟨a, ha, haI, haJ⟩
      apply hns
      intro x hx y hy
      have := hbI x hx
      have := hbJ y hy
      omega
  exact ev_congr last _ (by omega)

end LC

end BLMS

end PathChecking
