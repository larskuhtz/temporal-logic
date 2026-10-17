module

public import RequestProject.LTLPath.Round

/-!
# Phases of the contraction

`Inv S st`: correct statuses, known constants, known dead gates, closure and known leaf regions
for the leaf set `S`.  A *phase* removing the separated leaves `D ⊆ S` (with no chained merges)
consists of a round A (structure `S`, querying the regions of the compressed parents of `D`)
and a round B (structure `S \ D`, querying all regions); it preserves the invariant
(`phase`).  Stage `r` consists of two phases and goes from `S0 r` to `S0 (r + 1)` (`stage_inv`).
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-- The invariant of the algorithm for the leaf set `S`. -/
structure Inv (T : FT) (S : ℕ → Prop) (st : ℕ → Option Bool) : Prop where
  correct : GS.Correct T.gate st
  ck : T.ConstKnown st
  dead : T.Dead S st
  cl : T.Cl S st
  lk : T.LeafKnown S st

lemma ao_of_unknown {st : ℕ → Option Bool} (hck : T.ConstKnown st) {x : ℕ} (hu : st x = none) :
    AO (T.gate x) := by
  by_contra hn
  obtain ⟨b, hb⟩ := not_ao_const (gate_mono x) hn
  rw [hck x b hb] at hu; exact absurd hu (by simp)

/-- In round A, frontier arguments of queried regions are frozen. -/
lemma frozen {S D : ℕ → Prop} {st : ℕ → Option Bool} (hnc : T.NoChain S D)
    (hck : T.ConstKnown st) (hlk : T.LeafKnown S st) :
    ∀ h x, AO (T.gate h) → st h = none → T.alive S (T.pos h) →
      T.PSet S D (T.down S (T.pos h)) → x ∈ (T.gate h).args →
      ¬ T.NF S (T.pos h) (T.pos x) → T.step S (T.PSet S D) st x = st x := by
  intro h x hA hu hal hq hx hnf
  cases hsx : st x with
  | some b => exact step_known hsx
  | none =>
  rw [← hsx]; apply step_unqueried
  have hxA := ao_of_unknown hck hsx
  obtain ⟨-, -, -, -, hargs⟩ := gate_AO hA
  obtain ⟨-, -, hxl, -, -⟩ := gate_AO hxA
  rcases (hargs x hx).2.2 with e | hc
  · exact absurd (Or.inl e) hnf
  have hax : T.alive S (T.pos x) := by by_contra h'; exact hnf (Or.inr (Or.inl h'))
  have hdx : T.down S (T.pos x) ≠ T.down S (T.pos h) := fun e =>
    hnf (Or.inr (Or.inr ⟨hax, hxl, e⟩))
  have hdh : T.down S (T.pos h) = T.pos h := by
    by_contra hne; exact hdx (down_child_eq hc hax hne)
  obtain ⟨k, hk, hpk⟩ := hq
  rw [hdh] at hpk
  have hlx : T.leaf (T.down S (T.pos x)) = false := by
    by_contra hl; exact hlk x hxA hax (by simpa using hl) (by rw [hsx])
  exact hnc k hk (T.pos x) (by rw [hpk]; exact hc) hax hlx

lemma alive_of_alive_diff {S D : ℕ → Prop} {y : ℕ} (h : T.alive (fun k => S k ∧ ¬ D k) y) :
    T.alive S y := by
  obtain ⟨k, ⟨hk, -⟩, hc⟩ := h; exact ⟨k, hk, hc⟩

/-- Dead gates after removing `D`. -/
lemma dead_merge {S D : ℕ → Prop} {st : ℕ → Option Bool} (hsep : PT.Sep S D)
    (hd : T.Dead S st) (hlk : T.LeafKnown S st) : T.Dead (fun k => S k ∧ ¬ D k) st := by
  intro h hA hna
  by_cases ha : T.alive S (T.pos h)
  · obtain ⟨-, hnd, -, -, -⟩ := gate_AO hA
    exact hlk h hA ha (PT.leaf_down_of_unique hnd ha (PT.unique_of_dead hsep hna))
  · exact hd h hA ha

/-- Closure after removing `D`. -/
lemma cl_merge {S D : ℕ → Prop} {st : ℕ → Option Bool} (hDS : ∀ k, D k → S k)
    (hsep : PT.Sep S D) (hcl : T.Cl S st)
    (hF : ∀ h, AO (T.gate h) → st h = none → T.alive S (T.pos h) →
      T.PSet S D (T.down S (T.pos h)) → T.FCl st h) :
    T.Cl (fun k => S k ∧ ¬ D k) st := by
  intro h hA hu hal'
  have hal := alive_of_alive_diff hal'
  obtain ⟨-, -, -, -, hargs⟩ := gate_AO hA
  by_cases hP : T.PSet S D (T.down S (T.pos h))
  · obtain ⟨F1, x, hx, hxu⟩ := hF h hA hu hal hP
    exact ⟨fun x hx _ v hv => F1 x hx v hv, x, hx, Or.inl hxu⟩
  · obtain ⟨C1, x, hx, hx'⟩ := hcl h hA hu hal
    have nm : ∀ y ∈ (T.gate h).args, T.NF (fun k => S k ∧ ¬ D k) (T.pos h) (T.pos y) →
        T.NF S (T.pos h) (T.pos y) := fun y hy =>
      PT.nf_merge hDS hsep hal' hP (hargs y hy).2.2
    refine ⟨fun y hy hnf v hv => C1 y hy (nm y hy hnf) v hv, x, hx, ?_⟩
    rcases hx' with h1 | h1
    · exact Or.inl h1
    · exact Or.inr fun h2 => h1 (nm x hx h2)

/-- Round A of a phase. -/
noncomputable def roundA (T : FT) (S D : ℕ → Prop) (st : ℕ → Option Bool) : ℕ → Option Bool :=
  T.step S (T.PSet S D) st

/-- Round B: query all regions. -/
noncomputable def roundB (T : FT) (S : ℕ → Prop) (st : ℕ → Option Bool) : ℕ → Option Bool :=
  T.step S (fun _ => True) st

/-- Round B preserves the invariant of a leaf set whose dead gates and closure are known. -/
lemma roundB_inv {S : ℕ → Prop} {st : ℕ → Option Bool} (hc : GS.Correct T.gate st)
    (hck : T.ConstKnown st) (hd : T.Dead S st) (hcl : T.Cl S st) : T.Inv S (T.roundB S st) :=
  ⟨step_correct hc, step_constKnown hck, step_dead hd, step_cl hck hd hcl,
    fun _ hA hal hl => step_leaf hck hd hA hal hl trivial⟩

/-- After round A, the statuses satisfy the hypotheses of round B for `S \ D`. -/
theorem roundA_facts {S D : ℕ → Prop} {st : ℕ → Option Bool} (hDS : ∀ k, D k → S k)
    (hsep : PT.Sep S D) (hnc : T.NoChain S D) (hI : T.Inv S st) :
    GS.Correct T.gate (T.roundA S D st) ∧ T.ConstKnown (T.roundA S D st) ∧
      T.Dead (fun k => S k ∧ ¬ D k) (T.roundA S D st) ∧
      T.Cl (fun k => S k ∧ ¬ D k) (T.roundA S D st) := by
  have F : ∀ h, AO (T.gate h) → T.roundA S D st h = none → T.alive S (T.pos h) →
      T.PSet S D (T.down S (T.pos h)) → T.FCl (T.roundA S D st) h :=
    fun h hA hu hal hq => step_fcl hI.ck hI.dead hI.cl (frozen hnc hI.ck hI.lk) hA hu hal hq
  exact ⟨step_correct hI.correct, step_constKnown hI.ck,
    dead_merge hsep (step_dead hI.dead) (step_leafKnown hI.lk),
    cl_merge hDS hsep (step_cl hI.ck hI.dead hI.cl) F⟩

/-- **A phase preserves the invariant.** -/
theorem phase {S D : ℕ → Prop} {st : ℕ → Option Bool} (hDS : ∀ k, D k → S k)
    (hsep : PT.Sep S D) (hnc : T.NoChain S D) (hI : T.Inv S st) :
    T.Inv (fun k => S k ∧ ¬ D k) (T.roundB (fun k => S k ∧ ¬ D k) (T.roundA S D st)) := by
  obtain ⟨a, b, c, d⟩ := roundA_facts hDS hsep hnc hI
  exact roundB_inv a b c d

/-- The four rounds of stage `r`. -/
noncomputable def stage (T : FT) (r : ℕ) (st : ℕ → Option Bool) : ℕ → Option Bool :=
  T.roundB (T.S0 (r + 1)) (T.roundA (T.S1 r) (T.DR r)
    (T.roundB (T.S1 r) (T.roundA (T.S0 r) (T.DL r) st)))

lemma S1_diff_DR (r : ℕ) : (fun k => T.S1 r k ∧ ¬ T.DR r k) = T.S0 (r + 1) :=
  funext fun k => propext (PT.S1_DR_iff r k)

/-- **A stage preserves the invariant.** -/
theorem stage_inv {r : ℕ} {st : ℕ → Option Bool} (hI : T.Inv (T.S0 r) st) :
    T.Inv (T.S0 (r + 1)) (T.stage r st) := by
  have h1 : T.Inv (T.S1 r) (T.roundB (T.S1 r) (T.roundA (T.S0 r) (T.DL r) st)) :=
    phase (fun k h => h.1) (PT.sep_DL r) (PT.noChain_DL r) hI
  have h2 := phase (fun k h => h.1) (PT.sep_DR r) (PT.noChain_DR r) h1
  rw [S1_diff_DR] at h2
  exact h2

end FT

end PathChecking
