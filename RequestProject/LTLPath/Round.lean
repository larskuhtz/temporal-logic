module

public import RequestProject.LTLPath.Circ

/-!
# One round of region queries

For a set `S` of leaves and a set `Qd` of queried regions (given by their `down` node), the
query for gate `h0` is the prefix circuit of the query system in which the *live* gates are the
unknown `AND`/`OR` gates of the region of `h0` (if that region is queried), and an argument `x`
of a live gate `h` is dropped iff `x` is known with the neutral value of `h` and lies in a
non-frontier row (`NF`).  `step S Qd st` are the new statuses (assuming correct answers).

Invariants: correct statuses, known constants, known dead gates (`Dead`), closure (`Cl`),
full closure of a gate (`FCl`) and known leaf regions (`LeafKnown`).
-/

@[expose] public section

namespace PathChecking

namespace FT

variable {T : FT}

open Classical

/-- `y` lies in the region with `down` node `d`. -/
def InR (T : FT) (S : ℕ → Prop) (d y : ℕ) : Prop :=
  T.alive S y ∧ T.leaf y = false ∧ T.down S y = d

/-- The live gates of the query for `h0`. -/
noncomputable def live (T : FT) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) :
    ℕ → Bool := fun h =>
  decide (Qd (T.down S (T.pos h0)) ∧ T.InR S (T.down S (T.pos h0)) (T.pos h0) ∧ st h = none ∧
    AO (T.gate h) ∧ T.InR S (T.down S (T.pos h0)) (T.pos h))

/-- Kept arguments. -/
noncomputable def keep (T : FT) (S : ℕ → Prop) (st : ℕ → Option Bool) : ℕ → ℕ → Bool :=
  fun h x => !decide (st x = some (GS.neutral (T.gate h).kind) ∧ T.NF S (T.pos h) (T.pos x))

/-- The query system for gate `h0` and the value `β` of unknown non-live gates. -/
noncomputable def qsysR (T : FT) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) (β : Bool) :
    ℕ → Gate :=
  GS.qsys T.gate st (T.live S Qd st h0) (T.keep S st) β

/-- The answer of the query for gate `h0` and `β` (if the oracle answers correctly). -/
noncomputable def ans (T : FT) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) (β : Bool) :
    Bool :=
  GS.val (T.qsysR S Qd st h0 β) h0

/-- New statuses after a round. -/
noncomputable def step (T : FT) (S Qd : ℕ → Prop) (st : ℕ → Option Bool) : ℕ → Option Bool :=
  fun h0 => GS.dec (T.ans S Qd st h0 false) (T.ans S Qd st h0 true)

/-! ## Invariants -/

/-- Constant gates are known. -/
def ConstKnown (T : FT) (st : ℕ → Option Bool) : Prop :=
  ∀ h b, (T.gate h).kind = .const b → st h = some b

/-- Gates of dead nodes are known. -/
def Dead (T : FT) (S : ℕ → Prop) (st : ℕ → Option Bool) : Prop :=
  ∀ h, AO (T.gate h) → ¬ T.alive S (T.pos h) → st h ≠ none

/-- Closure: known non-frontier arguments of unknown gates are neutral, and every unknown gate
has an unknown or frontier argument. -/
def Cl (T : FT) (S : ℕ → Prop) (st : ℕ → Option Bool) : Prop :=
  ∀ h, AO (T.gate h) → st h = none → T.alive S (T.pos h) →
    (∀ x ∈ (T.gate h).args, T.NF S (T.pos h) (T.pos x) → ∀ v, st x = some v →
      v = GS.neutral (T.gate h).kind) ∧
    (∃ x ∈ (T.gate h).args, st x = none ∨ ¬ T.NF S (T.pos h) (T.pos x))

/-- Full closure of a gate: all known arguments are neutral and some argument is unknown. -/
def FCl (T : FT) (st : ℕ → Option Bool) (h : ℕ) : Prop :=
  (∀ x ∈ (T.gate h).args, ∀ v, st x = some v → v = GS.neutral (T.gate h).kind) ∧
    (∃ x ∈ (T.gate h).args, st x = none)

/-- Gates of leaf regions are known. -/
def LeafKnown (T : FT) (S : ℕ → Prop) (st : ℕ → Option Bool) : Prop :=
  ∀ h, AO (T.gate h) → T.alive S (T.pos h) → T.leaf (T.down S (T.pos h)) = true → st h ≠ none

/-! ## Basic facts -/

lemma ao_kind {g : Gate} (h : AO g) : g.kind = .and ∨ g.kind = .or := h

lemma admissible (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) :
    GS.Admissible T.gate st (T.live S Qd st h0) (T.keep S st) := by
  constructor
  · intro h hl
    simp only [live, decide_eq_true_eq] at hl
    exact hl.2.2.2.1
  · intro h hl x hx hk
    simp only [keep, Bool.not_eq_false', decide_eq_true_eq] at hk
    exact hk.1

lemma not_ao_const {g : Gate} (hm : g.kind = .and ∨ g.kind = .or ∨ ∃ b, g.kind = .const b ∧ g.args = [])
    (h : ¬ AO g) : ∃ b, g.kind = .const b := by
  rcases hm with e | e | ⟨b, e, -⟩
  · exact absurd (Or.inl e) h
  · exact absurd (Or.inr e) h
  · exact ⟨b, e⟩

/-- **New statuses are correct.** -/
theorem step_correct {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hc : GS.Correct T.gate st) :
    GS.Correct T.gate (T.step S Qd st) := by
  intro h b hb
  exact GS.dec_correct gate_ordered hc (admissible S Qd st h) hb

/-- Known gates stay known. -/
lemma step_known {S Qd : ℕ → Prop} {st : ℕ → Option Bool} {h : ℕ} {b : Bool}
    (hs : st h = some b) : T.step S Qd st h = some b := by
  have hl : T.live S Qd st h h = false := by
    simp [live, hs]
  unfold step ans qsysR
  rw [GS.val_qsys_dead gate_ordered hl, GS.val_qsys_dead gate_ordered hl, hs]
  simp [GS.dec]

/-- Gates outside queried regions keep their status. -/
lemma step_unqueried {S Qd : ℕ → Prop} {st : ℕ → Option Bool} {h : ℕ}
    (hq : ¬ Qd (T.down S (T.pos h))) : T.step S Qd st h = st h := by
  have hl : T.live S Qd st h h = false := by
    simp [live, hq]
  unfold step ans qsysR
  rw [GS.val_qsys_dead gate_ordered hl, GS.val_qsys_dead gate_ordered hl]
  cases st h <;> simp [GS.dec]

lemma step_constKnown {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (h : T.ConstKnown st) :
    T.ConstKnown (T.step S Qd st) := fun h' b e => step_known (h h' b e)

lemma step_dead {S S' Qd : ℕ → Prop} {st : ℕ → Option Bool} (h : T.Dead S' st) :
    T.Dead S' (T.step S Qd st) := by
  intro h' ha hd
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (h h' ha hd)
  rw [step_known hb]; simp

lemma step_leafKnown {S S' Qd : ℕ → Prop} {st : ℕ → Option Bool} (h : T.LeafKnown S' st) :
    T.LeafKnown S' (T.step S Qd st) := by
  intro h' ha hal hl
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 (h h' ha hal hl)
  rw [step_known hb]; simp

/-- The live set of the query for `h0` depends only on the region of `h0`. -/
lemma live_congr {S Qd : ℕ → Prop} {st : ℕ → Option Bool} {h0 h1 : ℕ}
    (e : T.down S (T.pos h0) = T.down S (T.pos h1))
    (e' : T.InR S (T.down S (T.pos h0)) (T.pos h0) ↔ T.InR S (T.down S (T.pos h1)) (T.pos h1)) :
    T.live S Qd st h0 = T.live S Qd st h1 := by
  funext h
  simp only [live, e]
  rw [e] at e'
  simp only [e']

/-- An unknown non-frontier argument of a live gate is live. -/
lemma live_of_nf {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) {h x : ℕ} (hl : T.live S Qd st h h = true) (hx : x ∈ (T.gate h).args)
    (hnf : T.NF S (T.pos h) (T.pos x)) (hu : st x = none) :
    T.live S Qd st h x = true ∧ T.live S Qd st x = T.live S Qd st h := by
  simp only [live, decide_eq_true_eq] at hl
  obtain ⟨hq, hr, -, -, -⟩ := hl
  have hxA : AO (T.gate x) := by
    by_contra hn
    obtain ⟨b, hb⟩ := not_ao_const (gate_mono x) hn
    rw [hck x b hb] at hu; exact absurd hu (by simp)
  have hxr : T.InR S (T.down S (T.pos h)) (T.pos x) := by
    rcases hnf with e | e | e
    · rw [e]; exact hr
    · exact absurd hu (hd x hxA e)
    · exact ⟨e.1, e.2.1, e.2.2⟩
  have hx' := hxr
  obtain ⟨-, -, hdx⟩ := hxr
  refine ⟨?_, live_congr hdx ?_⟩
  · simp only [live, decide_eq_true_eq]
    exact ⟨hq, hr, hu, hxA, hx'⟩
  · rw [hdx]; exact ⟨fun _ => hr, fun _ => hx'⟩

/-- An unknown argument in a non-frontier row lies in the same region. -/
lemma down_eq_of_nf {S : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) {h x : ℕ} (hnf : T.NF S (T.pos h) (T.pos x)) (hu : st x = none) :
    T.down S (T.pos x) = T.down S (T.pos h) := by
  have hxA : AO (T.gate x) := by
    by_contra hn
    obtain ⟨b, hb⟩ := not_ao_const (gate_mono x) hn
    rw [hck x b hb] at hu; exact absurd hu (by simp)
  rcases hnf with e | e | e
  · rw [e]
  · exact absurd hu (hd x hxA e)
  · exact e.2.2

lemma dec_none {a b : Bool} (h : GS.dec a b = none) : a ≠ b := by
  unfold GS.dec at h; split_ifs at h with e; exact e

lemma dec_some {a b v : Bool} (h : GS.dec a b = some v) : a = v ∧ b = v := by
  unfold GS.dec at h; split_ifs at h with e
  · cases h; exact ⟨rfl, e.symm⟩

lemma live_kind (S Qd : ℕ → Prop) (st : ℕ → Option Bool) (h0 : ℕ) :
    ∀ h, T.live S Qd st h0 h = true → (T.gate h).kind = .and ∨ (T.gate h).kind = .or :=
  (admissible S Qd st h0).kind

/-- Equal answers for a live argument whose status is known after the round. -/
lemma ans_eq_of_step {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) {h x : ℕ} (hl : T.live S Qd st h h = true) (hx : x ∈ (T.gate h).args)
    (hnf : T.NF S (T.pos h) (T.pos x)) (hu : st x = none) {v : Bool}
    (hv : T.step S Qd st x = some v) :
    GS.val (T.qsysR S Qd st h false) x = v ∧ GS.val (T.qsysR S Qd st h true) x = v := by
  obtain ⟨-, heq⟩ := live_of_nf hck hd hl hx hnf hu
  have := dec_some hv
  unfold ans qsysR at this
  rw [heq] at this
  exact this

/-- **Querying preserves closure.** -/
theorem step_cl {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) (hcl : T.Cl S st) : T.Cl S (T.step S Qd st) := by
  intro h hA hu' hal
  have hu : st h = none := by
    cases e : st h with
    | none => rfl
    | some b => rw [step_known e] at hu'; exact absurd hu' (by simp)
  obtain ⟨hlt, hnd, hlf, hiw, hargs⟩ := gate_AO hA
  obtain ⟨C1, C2⟩ := hcl h hA hu hal
  by_cases hq : Qd (T.down S (T.pos h))
  · have hr : T.InR S (T.down S (T.pos h)) (T.pos h) := ⟨hal, hlf, rfl⟩
    have hl : T.live S Qd st h h = true := by
      simp only [live, decide_eq_true_eq]; exact ⟨hq, hr, hu, hA, hr⟩
    have hne := dec_none hu'
    unfold ans at hne
    have hdead : ∀ x b, st x = some b → ∀ β, GS.val (T.qsysR S Qd st h β) x = b := by
      intro x b hb β
      have hlx : T.live S Qd st h x = false := by simp [live, hb]
      unfold qsysR; rw [GS.val_qsys_dead gate_ordered hlx, hb]; rfl
    refine ⟨fun x hx hnf v hv => ?_, ?_⟩
    · cases hsx : st x with
      | some b =>
        rw [step_known hsx] at hv; obtain rfl := Option.some.inj hv; exact C1 x hx hnf _ hsx
      | none =>
        obtain ⟨e0, e1⟩ := ans_eq_of_step hck hd hl hx hnf hsx hv
        by_contra hvn
        have hva : v = GS.absorb (T.gate h).kind := by
          unfold GS.absorb; revert hvn; cases v <;> cases GS.neutral (T.gate h).kind <;> simp
        apply hne
        unfold qsysR at e0 e1 ⊢
        refine GS.live_eq_of_absorb gate_ordered (live_kind S Qd st h) hl hx ?_ (e0.trans hva)
          (e1.trans hva)
        simp [keep, hsx]
    · by_contra hcon
      push_neg at hcon
      apply hne
      unfold qsysR
      refine GS.live_eq_of_args gate_ordered hl fun x hx _ => ?_
      obtain ⟨hsn, hnf⟩ := hcon x hx
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hsn
      cases hsx : st x with
      | some b =>
        have := hdead x b hsx
        unfold qsysR at this; rw [this, this]
      | none =>
        obtain ⟨e0, e1⟩ := ans_eq_of_step hck hd hl hx hnf hsx hv
        unfold qsysR at e0 e1; rw [e0, e1]
  · have hstep : ∀ x ∈ (T.gate h).args, T.NF S (T.pos h) (T.pos x) →
        T.step S Qd st x = st x := by
      intro x hx hnf
      cases hsx : st x with
      | some b => exact step_known hsx
      | none =>
        rw [← hsx]; apply step_unqueried
        rw [down_eq_of_nf hck hd hnf hsx]; exact hq
    refine ⟨fun x hx hnf v hv => C1 x hx hnf v (by rw [← hstep x hx hnf]; exact hv), ?_⟩
    obtain ⟨x, hx, hx'⟩ := C2
    refine ⟨x, hx, ?_⟩
    by_cases hnf : T.NF S (T.pos h) (T.pos x)
    · left; rw [hstep x hx hnf]; exact hx'.resolve_right (not_not.2 hnf)
    · right; exact hnf

/-- **Full closure after a round with frozen frontier.** If every frontier argument of an
unknown gate of a queried region keeps its status in the round, then every gate of a queried
region that is still unknown afterwards is fully closed. -/
theorem step_fcl {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) (hcl : T.Cl S st)
    (hfr : ∀ h x, AO (T.gate h) → st h = none → T.alive S (T.pos h) →
      Qd (T.down S (T.pos h)) → x ∈ (T.gate h).args →
      ¬ T.NF S (T.pos h) (T.pos x) → T.step S Qd st x = st x)
    {h : ℕ} (hA : AO (T.gate h)) (hu' : T.step S Qd st h = none) (hal : T.alive S (T.pos h))
    (hq : Qd (T.down S (T.pos h))) : T.FCl (T.step S Qd st) h := by
  have hu : st h = none := by
    cases e : st h with
    | none => rfl
    | some b => rw [step_known e] at hu'; exact absurd hu' (by simp)
  obtain ⟨hlt, hnd, hlf, hiw, hargs⟩ := gate_AO hA
  obtain ⟨C1, C2⟩ := hcl h hA hu hal
  have hr : T.InR S (T.down S (T.pos h)) (T.pos h) := ⟨hal, hlf, rfl⟩
  have hl : T.live S Qd st h h = true := by
    simp only [live, decide_eq_true_eq]; exact ⟨hq, hr, hu, hA, hr⟩
  have hne := dec_none hu'
  unfold ans at hne
  have hdead : ∀ x b, st x = some b → ∀ β, GS.val (T.qsysR S Qd st h β) x = b := by
    intro x b hb β
    have hlx : T.live S Qd st h x = false := by simp [live, hb]
    unfold qsysR; rw [GS.val_qsys_dead gate_ordered hlx, hb]; rfl
  have habs : ∀ x ∈ (T.gate h).args, T.keep S st h x = true → ∀ v,
      GS.val (T.qsysR S Qd st h false) x = v → GS.val (T.qsysR S Qd st h true) x = v →
      v = GS.neutral (T.gate h).kind := by
    intro x hx hk v e0 e1
    by_contra hvn
    have hva : v = GS.absorb (T.gate h).kind := by
      unfold GS.absorb; revert hvn; cases v <;> cases GS.neutral (T.gate h).kind <;> simp
    apply hne
    unfold qsysR at e0 e1 ⊢
    exact GS.live_eq_of_absorb gate_ordered (live_kind S Qd st h) hl hx hk (e0.trans hva)
      (e1.trans hva)
  refine ⟨fun x hx v hv => ?_, ?_⟩
  · by_cases hnf : T.NF S (T.pos h) (T.pos x)
    · cases hsx : st x with
      | some b =>
        rw [step_known hsx] at hv; obtain rfl := Option.some.inj hv; exact C1 x hx hnf _ hsx
      | none =>
        obtain ⟨e0, e1⟩ := ans_eq_of_step hck hd hl hx hnf hsx hv
        exact habs x hx (by simp [keep, hsx]) v e0 e1
    · rw [hfr h x hA hu hal hq hx hnf] at hv
      exact habs x hx (by simp [keep, hnf]) v (hdead x v hv false) (hdead x v hv true)
  · by_contra hcon
    push_neg at hcon
    apply hne
    unfold qsysR
    refine GS.live_eq_of_args gate_ordered hl fun x hx _ => ?_
    have hsn := hcon x hx
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hsn
    cases hsx : st x with
    | some b =>
      have := hdead x b hsx
      unfold qsysR at this; rw [this, this]
    | none =>
      by_cases hnf : T.NF S (T.pos h) (T.pos x)
      · obtain ⟨e0, e1⟩ := ans_eq_of_step hck hd hl hx hnf hsx hv
        unfold qsysR at e0 e1; rw [e0, e1]
      · rw [hfr h x hA hu hal hq hx hnf, hsx] at hv; exact absurd hv (by simp)

/-- A child alive below a non-branching node lies in the same region. -/
lemma down_child_eq {S : ℕ → Prop} {y c : ℕ} (hc : T.IsChild y c) (ha : T.alive S c)
    (hne : T.down S y ≠ y) : T.down S c = T.down S y := by
  refine (T.down_single hc ha fun c' hc' hne' ha' => hne ?_).symm
  exact T.down_branch hc hc' hne'.symm ha ha'

/-- An unknown non-frontier argument of a live gate is live (any query). -/
lemma live_of_nf' {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) {h0 h x : ℕ} (hl : T.live S Qd st h0 h = true)
    (hnf : T.NF S (T.pos h) (T.pos x)) (hu : st x = none) : T.live S Qd st h0 x = true := by
  simp only [live, decide_eq_true_eq] at hl ⊢
  obtain ⟨hq, hr0, -, -, hr⟩ := hl
  have hxA : AO (T.gate x) := by
    by_contra hn
    obtain ⟨b, hb⟩ := not_ao_const (gate_mono x) hn
    rw [hck x b hb] at hu; exact absurd hu (by simp)
  refine ⟨hq, hr0, hu, hxA, ?_⟩
  rcases hnf with e | e | e
  · rw [e]; exact hr
  · exact absurd hu (hd x hxA e)
  · exact ⟨e.1, e.2.1, e.2.2.trans hr.2.2⟩

/-- If all unknown arguments of live gates are non-frontier, the two answers agree on live and
known gates. -/
lemma ans_eq_all {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) (h0 : ℕ)
    (hfr : ∀ x y, T.live S Qd st h0 x = true → y ∈ (T.gate x).args → st y = none →
      T.NF S (T.pos x) (T.pos y)) :
    ∀ x, (T.live S Qd st h0 x = true ∨ st x ≠ none) →
      GS.val (T.qsysR S Qd st h0 false) x = GS.val (T.qsysR S Qd st h0 true) x := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    by_cases hlx : T.live S Qd st h0 x = true
    · unfold qsysR
      refine GS.live_eq_of_args gate_ordered hlx fun y hy _ => ?_
      have hyx : y < x := gate_ordered x y hy
      refine ih y hyx ?_
      by_cases hsy : st y = none
      · exact Or.inl (live_of_nf' hck hd hlx (hfr x y hlx hy hsy) hsy)
      · exact Or.inr hsy
    · have hsx := hx.resolve_left hlx
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 hsx
      have hl' : T.live S Qd st h0 x = false := by simpa using hlx
      unfold qsysR
      rw [GS.val_qsys_dead gate_ordered hl', GS.val_qsys_dead gate_ordered hl', hb]; rfl

/-- **Leaf regions become known** in a round that queries them. -/
theorem step_leaf {S Qd : ℕ → Prop} {st : ℕ → Option Bool} (hck : T.ConstKnown st)
    (hd : T.Dead S st) {h : ℕ} (hA : AO (T.gate h)) (hal : T.alive S (T.pos h))
    (hlf : T.leaf (T.down S (T.pos h)) = true) (hq : Qd (T.down S (T.pos h))) :
    T.step S Qd st h ≠ none := by
  cases e : st h with
  | some b => rw [step_known e]; simp
  | none =>
  obtain ⟨-, -, hl0, -, -⟩ := gate_AO hA
  have hr : T.InR S (T.down S (T.pos h)) (T.pos h) := ⟨hal, hl0, rfl⟩
  have hl : T.live S Qd st h h = true := by
    simp only [live, decide_eq_true_eq]; exact ⟨hq, hr, e, hA, hr⟩
  have heq := ans_eq_all hck hd h (fun x y hlx hy hsy => ?_) h (Or.inl hl)
  · unfold step; unfold ans; rw [heq]; simp [GS.dec]
  have hlx' := hlx
  simp only [live, decide_eq_true_eq] at hlx'
  obtain ⟨-, -, -, hxA, hrx⟩ := hlx'
  have hyA : AO (T.gate y) := by
    by_contra hn
    obtain ⟨b, hb⟩ := not_ao_const (gate_mono y) hn
    rw [hck y b hb] at hsy; exact absurd hsy (by simp)
  obtain ⟨-, -, -, -, hargs⟩ := gate_AO hxA
  obtain ⟨-, -, hyl, -, -⟩ := gate_AO hyA
  rcases (hargs y hy).2.2 with e' | hc
  · exact Or.inl e'
  by_cases hay : T.alive S (T.pos y)
  · right; right
    have hne : T.down S (T.pos x) ≠ T.pos x := by
      intro h'; rw [← hrx.2.2, h', hrx.2.1] at hlf; exact absurd hlf (by simp)
    exact ⟨hay, hyl, down_child_eq hc hay hne⟩
  · exact Or.inr (Or.inl hay)

end FT

end PathChecking
