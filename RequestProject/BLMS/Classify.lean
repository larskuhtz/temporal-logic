module

public import RequestProject.BLMS.Pair

/-!
# Computing images of intervals and classifying pairs of intervals

Computable versions of the evaluation of one or two intervals, as used by the algorithm of
[BLMS99, Section 5]:

* `stepI l (a, b)` is the image `[a', b')` of the interval `[a, b)` under one evaluation step,
  computed by a left-to-right scan over the gates of the next layer (`stepI_spec`);
* `loneAcc (a, b)` says whether the interval `[a, b)` alone makes the circuit accept
  (`loneAcc_iff`);
* `classify I J` simulates the evaluation of two separated intervals `I < J` until the first
  layer at which they merge or one of them dies, and says whether `I` and `J` should be merged,
  whether `J` should be pushed (it dies first), or whether `I` should be discarded
  (`classify_spec`).
-/

@[expose] public section

namespace PathChecking

namespace BLMS

open Set

namespace LC

variable (c : LC)

/-- `x ∈ [a, b)` as a Boolean. -/
def inI (a b x : ℕ) : Bool := decide (a ≤ x ∧ x < b)

/-- Value of gate `i` on the interval `[a, b)`. -/
def gvalB (a b i : ℕ) : Bool :=
  if c.isAnd i = true then inI a b (c.lo i) && inI a b (c.hi i)
  else inI a b (c.lo i) || inI a b (c.hi i)

/-- Number of gates of layer `l + 1`. -/
def wid (l : ℕ) : ℕ := c.bd (l + 2) - c.bd (l + 1)

/-- One step of the scan computing the first and last true gate. -/
def scanStep (p q : ℕ × ℕ) (i : ℕ) : ℕ × ℕ :=
  if c.gvalB p.1 p.2 i = true then (if q.1 < q.2 then (q.1, i + 1) else (i, i + 1)) else q

/-- The image of the interval `[p.1, p.2)` under the step from layer `l` to layer `l + 1`. -/
def stepI (l : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (List.range (c.wid l)).foldl (fun q k => c.scanStep p q (c.bd (l + 1) + k)) (0, 0)

/-- The image of `[p.1, p.2)` at layer `l`. -/
def iterI : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, p => p
  | l + 1, p => c.stepI l (iterI l p)

/-- The interval `[p.1, p.2)` alone makes the circuit accept. -/
def loneAcc (p : ℕ × ℕ) : Bool := decide ((c.iterI c.D p).1 < (c.iterI c.D p).2)

/-- `∃ k < n, P k`, computed by a left-to-right scan. -/
def anyR (n : ℕ) (P : ℕ → Bool) : Bool := (List.range n).foldl (fun acc k => acc || P k) false

/-- An `AND` gate of layer `l + 1` with arguments in `[ia, ib)` and `[ja, jb)`. -/
def bridgeB (l ia ib ja jb : ℕ) : Bool :=
  anyR (c.wid l) fun k => c.isAnd (c.bd (l + 1) + k) && inI ia ib (c.lo (c.bd (l + 1) + k)) &&
    inI ja jb (c.hi (c.bd (l + 1) + k))

/-- An `AND` gate of layer `l + 1` with left argument in `[ia, ib)` and right argument `≥ jb`. -/
def rspanB (l ia ib jb : ℕ) : Bool :=
  anyR (c.wid l) fun k => c.isAnd (c.bd (l + 1) + k) && inI ia ib (c.lo (c.bd (l + 1) + k)) &&
    decide (jb ≤ c.hi (c.bd (l + 1) + k))

/-- Outcomes of the classification of a pair of intervals. -/
inductive Outc
  | merge
  | push
  | disc
  deriving DecidableEq

/-- State of the simulation of a pair of intervals. -/
inductive PSt
  | run (ia ib ja jb : ℕ)
  | done (o : Outc)

/-- One step of the simulation of a pair of intervals. -/
def pstep (l : ℕ) : PSt → PSt
  | .done o => .done o
  | .run ia ib ja jb =>
    if c.bridgeB l ia ib ja jb = true then .done .merge
    else if (c.stepI l (ia, ib)).1 < (c.stepI l (ia, ib)).2 ∧
        (c.stepI l (ja, jb)).1 < (c.stepI l (ja, jb)).2 ∧
        (c.stepI l (ja, jb)).1 ≤ (c.stepI l (ia, ib)).2 then .done .merge
    else if ¬ (c.stepI l (ia, ib)).1 < (c.stepI l (ia, ib)).2 ∧
        ¬ (c.stepI l (ja, jb)).1 < (c.stepI l (ja, jb)).2 then
      (if c.rspanB l ia ib jb = true then .done .push else .done .disc)
    else if ¬ (c.stepI l (ja, jb)).1 < (c.stepI l (ja, jb)).2 then .done .push
    else if ¬ (c.stepI l (ia, ib)).1 < (c.stepI l (ia, ib)).2 then .done .disc
    else .run (c.stepI l (ia, ib)).1 (c.stepI l (ia, ib)).2 (c.stepI l (ja, jb)).1
      (c.stepI l (ja, jb)).2

/-- The simulation after `k` steps. -/
def pfold (k : ℕ) (I J : ℕ × ℕ) : PSt :=
  (List.range k).foldl (fun s l => c.pstep l s) (.run I.1 I.2 J.1 J.2)

/-- Classification of a pair of intervals `I < J`. -/
def classify (I J : ℕ × ℕ) : Outc :=
  match c.pfold c.D I J with
  | .done o => o
  | .run .. => .disc

variable {c}

lemma inI_iff (a b x : ℕ) : inI a b x = true ↔ x ∈ Ico a b := by
  simp [inI]

lemma gvalB_iff (a b i : ℕ) : c.gvalB a b i = true ↔ c.gval (Ico a b) i := by
  unfold gvalB gval
  split_ifs <;> simp [inI_iff]

lemma anyR_iff (n : ℕ) (P : ℕ → Bool) : anyR n P = true ↔ ∃ k < n, P k = true := by
  unfold anyR
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      rcases Nat.lt_or_ge k n with h' | h'
      · exact Or.inl ⟨k, h', h⟩
      · have : k = n := by omega
        subst this; exact Or.inr h

lemma mem_gates_iff (l i : ℕ) : i ∈ c.gates l ↔ ∃ k < c.wid l, i = c.bd (l + 1) + k := by
  simp only [gates, mem_Ico, wid]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨i - c.bd (l + 1), by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩; omega

lemma bridgeB_iff (l ia ib ja jb : ℕ) : c.bridgeB l ia ib ja jb = true ↔
    ∃ i ∈ c.gates l, c.isAnd i = true ∧ c.lo i ∈ Ico ia ib ∧ c.hi i ∈ Ico ja jb := by
  rw [bridgeB, anyR_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    simp only [Bool.and_eq_true, inI_iff] at h
    exact ⟨_, (mem_gates_iff l _).2 ⟨k, hk, rfl⟩, h.1.1, h.1.2, h.2⟩
  · rintro ⟨i, hi, h1, h2, h3⟩
    obtain ⟨k, hk, rfl⟩ := (mem_gates_iff l i).1 hi
    exact ⟨k, hk, by simp [inI_iff, h1, h2, h3]⟩

lemma rspanB_iff (l ia ib jb : ℕ) : c.rspanB l ia ib jb = true ↔
    ∃ i ∈ c.gates l, c.isAnd i = true ∧ c.lo i ∈ Ico ia ib ∧ jb ≤ c.hi i := by
  rw [rspanB, anyR_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    simp only [Bool.and_eq_true, inI_iff, decide_eq_true_eq] at h
    exact ⟨_, (mem_gates_iff l _).2 ⟨k, hk, rfl⟩, h.1.1, h.1.2, h.2⟩
  · rintro ⟨i, hi, h1, h2, h3⟩
    obtain ⟨k, hk, rfl⟩ := (mem_gates_iff l i).1 hi
    exact ⟨k, hk, by simp [inI_iff, h1, h2, h3]⟩

/-- The scan computes the first and the last true gate. -/
lemma scan_spec (l : ℕ) (p : ℕ × ℕ) : ∀ k, k ≤ c.wid l →
    let q := (List.range k).foldl (fun q k => c.scanStep p q (c.bd (l + 1) + k)) (0, 0)
    let T := {i | i ∈ c.step l (Ico p.1 p.2) ∧ i < c.bd (l + 1) + k}
    (T = ∅ → q = (0, 0)) ∧
    (T.Nonempty → q.1 ∈ T ∧ q.2 - 1 ∈ T ∧ q.1 < q.2 ∧ ∀ i ∈ T, q.1 ≤ i ∧ i < q.2) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil]
    refine ⟨fun _ => trivial, fun ⟨i, hi⟩ => ?_⟩
    exact absurd hi.2 (by have := hi.1.1.1; omega)
  | succ k ih =>
    intro hk
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set q := (List.range k).foldl (fun q k => c.scanStep p q (c.bd (l + 1) + k)) (0, 0) with hq
    set i0 := c.bd (l + 1) + k with hi0
    have hi0g : i0 ∈ c.gates l := by simp only [gates, mem_Ico, wid] at *; omega
    have hT : {i | i ∈ c.step l (Ico p.1 p.2) ∧ i < c.bd (l + 1) + (k + 1)} =
        {i | i ∈ c.step l (Ico p.1 p.2) ∧ i < c.bd (l + 1) + k} ∪
          (if c.gvalB p.1 p.2 i0 = true then {i0} else ∅) := by
      ext i
      simp only [mem_setOf_eq, mem_union]
      split_ifs with hg
      · simp only [mem_singleton_iff]
        constructor
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_or_ge i i0 with h | h
          · exact Or.inl ⟨h1, h⟩
          · exact Or.inr (by omega)
        · rintro (⟨h1, h2⟩ | rfl)
          · exact ⟨h1, by omega⟩
          · exact ⟨⟨hi0g, (gvalB_iff _ _ _).1 hg⟩, by omega⟩
      · simp only [mem_empty_iff_false, or_false]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, ?_⟩
          rcases Nat.lt_or_ge i i0 with h | h
          · exact h
          · have : i = i0 := by omega
            subst this
            exact absurd ((gvalB_iff _ _ _).2 h1.2) hg
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
    rw [hT]
    unfold scanStep
    by_cases hg : c.gvalB p.1 p.2 i0 = true
    · have hmem : i0 ∈ c.step l (Ico p.1 p.2) := ⟨hi0g, (gvalB_iff _ _ _).1 hg⟩
      simp only [hg, if_true]
      refine ⟨fun h => ?_, fun _ => ?_⟩
      · exfalso
        have : i0 ∈ ({i | i ∈ c.step l (Ico p.1 p.2) ∧ i < c.bd (l + 1) + k} ∪ {i0}) := by simp
        rw [h] at this; exact this
      · by_cases hne : {i | i ∈ c.step l (Ico p.1 p.2) ∧ i < c.bd (l + 1) + k}.Nonempty
        · obtain ⟨a1, a2, a3, a4⟩ := ih2 hne
          simp only [a3, if_true]
          refine ⟨Or.inl a1, Or.inr (by simp), by have := a1.2; omega, fun i hi => ?_⟩
          rcases hi with hi | hi
          · have := a4 i hi; have := hi.2; omega
          · simp only [mem_singleton_iff] at hi; subst hi
            obtain ⟨j, hj⟩ := hne
            have := a4 j hj; have := hj.2; omega
        · have he : {i | i ∈ c.step l (Ico p.1 p.2) ∧ i < c.bd (l + 1) + k} = ∅ :=
            not_nonempty_iff_eq_empty.1 hne
          have := ih1 he
          rw [this]
          simp only [lt_self_iff_false, if_false]
          refine ⟨Or.inr (by simp), Or.inr (by simp), by omega, fun i hi => ?_⟩
          rw [he] at hi
          simp only [empty_union, mem_singleton_iff] at hi
          subst hi; omega
    · simp only [hg, Bool.false_eq_true, if_false, union_empty]
      exact ⟨ih1, ih2⟩

lemma stepI_spec (hP : c.Planar) {l : ℕ} (hl : l < c.D) (p : ℕ × ℕ) :
    Ico (c.stepI l p).1 (c.stepI l p).2 = c.step l (Ico p.1 p.2) := by
  obtain ⟨h1, h2⟩ := scan_spec l p (c.wid l) le_rfl
  have hT : {i | i ∈ c.step l (Ico p.1 p.2) ∧ i < c.bd (l + 1) + c.wid l} =
      c.step l (Ico p.1 p.2) := by
    ext i
    simp only [mem_setOf_eq, and_iff_left_iff_imp]
    intro hi; have := hi.1; simp only [gates, mem_Ico, wid] at *; omega
  rw [hT] at h1 h2
  change Ico (c.stepI l p).1 (c.stepI l p).2 = _ at *
  rcases eq_empty_or_nonempty (c.step l (Ico p.1 p.2)) with he | hne
  · have := h1 he
    unfold stepI at *
    rw [this, he]; simp
  · obtain ⟨a1, a2, a3, a4⟩ := h2 hne
    unfold stepI at *
    ext i
    constructor
    · intro hi
      have hoc := step_ordConnected hP hl (ordConnected_Ico (a := p.1) (b := p.2))
      exact hoc.out a1 a2 ⟨hi.1, by have := hi.2; omega⟩
    · intro hi; exact a4 i hi

lemma iterI_spec (hP : c.Planar) (p : ℕ × ℕ) : ∀ l, l ≤ c.D →
    Ico (c.iterI l p).1 (c.iterI l p).2 = c.ev l (Ico p.1 p.2)
  | 0, _ => rfl
  | l + 1, h => by
    rw [iterI, stepI_spec hP (by omega), iterI_spec hP p l (by omega), ev_succ]

lemma loneAcc_iff (hP : c.Planar) (p : ℕ × ℕ) : c.loneAcc p = true ↔ c.out (Ico p.1 p.2) := by
  rw [loneAcc, out, ← iterI_spec hP p c.D le_rfl, decide_eq_true_eq, nonempty_Ico]

/-- If an interval does not make the circuit accept, it dies at some layer. -/
lemma exists_death {X : Set ℕ} (hX : X.Nonempty) (hout : ¬ c.out X) :
    ∃ e < c.D, (∀ l ≤ e, (c.ev l X).Nonempty) ∧ c.ev (e + 1) X = ∅ := by
  have hex : ∃ l, c.ev l X = ∅ := ⟨c.D, not_nonempty_iff_eq_empty.1 hout⟩
  classical
  let m := Nat.find hex
  have hm : c.ev m X = ∅ := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at hm
    exact hX.ne_empty hm
  have hlt : ∀ l < m, (c.ev l X).Nonempty := fun l hl =>
    nonempty_iff_ne_empty.2 (Nat.find_min hex hl)
  have hmD : m ≤ c.D := Nat.find_min' hex (not_nonempty_iff_eq_empty.1 hout)
  refine ⟨m - 1, by omega, fun l hl => hlt l (by omega), ?_⟩
  rw [show m - 1 + 1 = m by omega]; exact hm

/-- The first death layer is unique. -/
lemma death_unique {X : Set ℕ} {e e' : ℕ} (h1 : ∀ l ≤ e, (c.ev l X).Nonempty)
    (h2 : c.ev (e + 1) X = ∅) (h1' : ∀ l ≤ e', (c.ev l X).Nonempty)
    (h2' : c.ev (e' + 1) X = ∅) : e = e' := by
  have dead : ∀ {f : ℕ}, c.ev (f + 1) X = ∅ → ∀ k, f + 1 ≤ k → c.ev k X = ∅ := by
    intro f hf k hk
    rw [ev_congr (S := X) (T := ∅) (by rw [hf, ev_empty]) k hk, ev_empty]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact (h1' (e + 1) (by omega)).ne_empty (dead h2 _ le_rfl)
  · exact (h1 (e' + 1) (by omega)).ne_empty (dead h2' _ le_rfl)

/-- `RSpan` and `LSpan` exclude each other. -/
lemma not_lspan_of_rspan (hP : c.Planar) {I J : Set ℕ} {l : ℕ} (hl : l < c.D)
    (hs : Sep (c.ev l I) (c.ev l J)) (hr : c.RSpan I J l) : ¬ c.LSpan I J l := by
  rintro ⟨g', hg', hA', hhi', hlo'⟩
  obtain ⟨g, hg, hA, hlo, hhi⟩ := hr
  rcases lt_trichotomy g g' with h | rfl | h
  · have := hP.mono l hl g hg g' hg' h
    have := hlo' _ hlo
    have := hP.le l hl g hg
    omega
  · have := hhi _ hhi'; omega
  · have := hP.mono l hl g' hg' g hg h
    have := hs _ hlo _ hhi'
    omega

/-- **Specification of the classification.**  For two nonempty separated intervals that do not
make the circuit accept alone, the classification yields the data needed by `merge` and
`discard`. -/
theorem classify_spec (hP : c.Planar) {I J : ℕ × ℕ} (hI : I.1 < I.2) (hJ : J.1 < J.2)
    (hIJ : I.2 < J.1) (hoI : ¬ c.out (Ico I.1 I.2)) :
    (c.classify I J = .merge → ∃ e < c.D, c.MergeData (Ico I.1 I.2) (Ico J.1 J.2) e) ∧
    (c.classify I J = .push → ∃ e < c.D, c.PushData (Ico I.1 I.2) (Ico J.1 J.2) e) ∧
    (c.classify I J = .disc → ∃ e < c.D, c.DiscData (Ico I.1 I.2) (Ico J.1 J.2) e) := by
  set SI := Ico I.1 I.2
  set SJ := Ico J.1 J.2
  -- the invariant of the simulation
  have inv : ∀ k ≤ c.D,
      (∀ ia ib ja jb, c.pfold k I J = .run ia ib ja jb →
        Ico ia ib = c.ev k SI ∧ Ico ja jb = c.ev k SJ ∧ (∀ l ≤ k, c.PSep SI SJ l) ∧
          (∀ l < k, ¬ c.Bridge SI SJ l)) ∧
      (c.pfold k I J = .done .merge → ∃ e < k, c.MergeData SI SJ e) ∧
      (c.pfold k I J = .done .push → ∃ e < k, c.PushData SI SJ e) ∧
      (c.pfold k I J = .done .disc → ∃ e < k, c.DiscData SI SJ e) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun ia ib ja jb h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
      · simp only [pfold, List.range_zero, List.foldl_nil, PSt.run.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨rfl, rfl, fun l hl => ?_, fun l hl => absurd hl (Nat.not_lt_zero _)⟩
        have : l = 0 := by omega
        subst this
        refine ⟨nonempty_Ico.2 hI, nonempty_Ico.2 hJ, fun x hx y hy => ?_⟩
        simp only [ev_zero, SI, SJ, mem_Ico] at hx hy; omega
      all_goals simp [pfold] at h
    | succ k ih =>
      intro hk
      obtain ⟨ihr, ihm, ihp, ihd⟩ := ih (by omega)
      have hfold : c.pfold (k + 1) I J = c.pstep k (c.pfold k I J) := by
        simp [pfold, List.range_succ, List.foldl_append]
      rw [hfold]
      rcases hs : c.pfold k I J with ⟨ia, ib, ja, jb⟩ | o
      · obtain ⟨eI, eJ, hsep, hnob⟩ := ihr ia ib ja jb hs
        have hkD : k < c.D := by omega
        have sI : Ico (c.stepI k (ia, ib)).1 (c.stepI k (ia, ib)).2 = c.ev (k + 1) SI := by
          rw [stepI_spec hP hkD, ev_succ, ← eI]
        have sJ : Ico (c.stepI k (ja, jb)).1 (c.stepI k (ja, jb)).2 = c.ev (k + 1) SJ := by
          rw [stepI_spec hP hkD, ev_succ, ← eJ]
        have hbr : c.bridgeB k ia ib ja jb = true ↔ c.Bridge SI SJ k := by
          rw [bridgeB_iff, Bridge, ← eI, ← eJ]
        obtain ⟨neI, neJ, sepk⟩ := hsep k le_rfl
        have hrs : c.rspanB k ia ib jb = true ↔ c.RSpan SI SJ k := by
          rw [rspanB_iff, RSpan, ← eI, ← eJ]
          have hjab : ja < jb := by rw [← eJ] at neJ; exact nonempty_Ico.1 neJ
          constructor
          · rintro ⟨i, hi, h1, h2, h3⟩
            exact ⟨i, hi, h1, h2, fun y hy => by simp only [mem_Ico] at hy; omega⟩
          · rintro ⟨i, hi, h1, h2, h3⟩
            exact ⟨i, hi, h1, h2, by have := h3 (jb - 1) (by simp; omega); omega⟩
        have liveI : (c.stepI k (ia, ib)).1 < (c.stepI k (ia, ib)).2 ↔
            (c.ev (k + 1) SI).Nonempty := by rw [← sI, nonempty_Ico]
        have liveJ : (c.stepI k (ja, jb)).1 < (c.stepI k (ja, jb)).2 ↔
            (c.ev (k + 1) SJ).Nonempty := by rw [← sJ, nonempty_Ico]
        have sepIff : (c.stepI k (ja, jb)).1 ≤ (c.stepI k (ia, ib)).2 →
            (c.stepI k (ia, ib)).1 < (c.stepI k (ia, ib)).2 →
            (c.stepI k (ja, jb)).1 < (c.stepI k (ja, jb)).2 →
            ¬ Sep (c.ev (k + 1) SI) (c.ev (k + 1) SJ) := by
          intro h hlt h' hsp
          rw [← sI, ← sJ] at hsp
          have := hsp ((c.stepI k (ia, ib)).2 - 1) (by simp; omega)
            (c.stepI k (ja, jb)).1 (by simp; omega)
          omega
        have nobAll : ¬ c.Bridge SI SJ k → ∀ l ≤ k, ¬ c.Bridge SI SJ l := by
          intro h l hl
          rcases Nat.lt_or_ge l k with h' | h'
          · exact hnob l h'
          · have : l = k := by omega
            subst this; exact h
        simp only [pstep]
        set A1 := (c.stepI k (ia, ib)).1
        set A2 := (c.stepI k (ia, ib)).2
        set B1 := (c.stepI k (ja, jb)).1
        set B2 := (c.stepI k (ja, jb)).2
        by_cases h1 : c.bridgeB k ia ib ja jb = true
        · rw [if_pos h1]
          refine ⟨fun _ _ _ _ h => by simp at h, fun _ => ?_, fun h => by simp at h,
            fun h => by simp at h⟩
          exact ⟨k, by omega, ⟨hsep, hnob, Or.inl (hbr.1 h1)⟩⟩
        rw [if_neg h1]
        have hnb : ∀ l ≤ k, ¬ c.Bridge SI SJ l := nobAll (fun hb => h1 (hbr.2 hb))
        by_cases h2 : A1 < A2 ∧ B1 < B2 ∧ B1 ≤ A2
        · rw [if_pos h2]
          refine ⟨fun _ _ _ _ h => by simp at h, fun _ => ?_, fun h => by simp at h,
            fun h => by simp at h⟩
          exact ⟨k, by omega, ⟨hsep, hnob, Or.inr ⟨liveI.1 h2.1, liveJ.1 h2.2.1,
            sepIff h2.2.2 h2.1 h2.2.1⟩⟩⟩
        rw [if_neg h2]
        by_cases h3 : ¬ A1 < A2 ∧ ¬ B1 < B2
        · rw [if_pos h3]
          have dI : c.ev (k + 1) SI = ∅ := not_nonempty_iff_eq_empty.1 (fun hh => h3.1 (liveI.2 hh))
          have dJ : c.ev (k + 1) SJ = ∅ := not_nonempty_iff_eq_empty.1 (fun hh => h3.2 (liveJ.2 hh))
          by_cases h4 : c.rspanB k ia ib jb = true
          · rw [if_pos h4]
            refine ⟨fun _ _ _ _ h => by simp at h, fun h => by simp at h, fun _ => ?_,
              fun h => by simp at h⟩
            exact ⟨k, by omega, ⟨hsep, hnb, dJ,
              Or.inr (not_lspan_of_rspan hP hkD sepk (hrs.1 h4))⟩⟩
          · rw [if_neg h4]
            refine ⟨fun _ _ _ _ h => by simp at h, fun h => by simp at h, fun h => by simp at h,
              fun _ => ?_⟩
            exact ⟨k, by omega, ⟨hsep, hnb, dI, Or.inr (fun hh => h4 (hrs.2 hh))⟩⟩
        rw [if_neg h3]
        by_cases h5 : ¬ B1 < B2
        · rw [if_pos h5]
          refine ⟨fun _ _ _ _ h => by simp at h, fun h => by simp at h, fun _ => ?_,
            fun h => by simp at h⟩
          have hA : A1 < A2 := by by_contra hh; exact h3 ⟨hh, h5⟩
          exact ⟨k, by omega, ⟨hsep, hnb,
            not_nonempty_iff_eq_empty.1 (fun hh => h5 (liveJ.2 hh)), Or.inl (liveI.1 hA)⟩⟩
        rw [if_neg h5]
        by_cases h6 : ¬ A1 < A2
        · rw [if_pos h6]
          refine ⟨fun _ _ _ _ h => by simp at h, fun h => by simp at h, fun h => by simp at h,
            fun _ => ?_⟩
          have hB : B1 < B2 := by by_contra hh; exact h5 hh
          exact ⟨k, by omega, ⟨hsep, hnb,
            not_nonempty_iff_eq_empty.1 (fun hh => h6 (liveI.2 hh)), Or.inl (liveJ.1 hB)⟩⟩
        rw [if_neg h6]
        have hA : A1 < A2 := by by_contra hh; exact h6 hh
        have hB : B1 < B2 := by by_contra hh; exact h5 hh
        refine ⟨fun ia' ib' ja' jb' h => ?_, fun h => by simp at h, fun h => by simp at h,
          fun h => by simp at h⟩
        simp only [PSt.run.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        refine ⟨sI, sJ, fun l hl => ?_, fun l hl => ?_⟩
        · rcases Nat.lt_or_ge l (k + 1) with h' | h'
          · exact hsep l (by omega)
          · have : l = k + 1 := by omega
            subst this
            refine ⟨liveI.1 hA, liveJ.1 hB, ?_⟩
            rw [← sI, ← sJ]
            intro x hx y hy
            simp only [mem_Ico] at hx hy
            have hnt : ¬ B1 ≤ A2 := fun hh => h2 ⟨hA, hB, hh⟩
            omega
        · exact hnb l (by omega)
      · simp only [pstep]
        refine ⟨fun _ _ _ _ h => by simp at h, fun h => ?_, fun h => ?_, fun h => ?_⟩
        · obtain ⟨e, he, hd⟩ := ihm (by simp at h; rw [hs, h]); exact ⟨e, by omega, hd⟩
        · obtain ⟨e, he, hd⟩ := ihp (by simp at h; rw [hs, h]); exact ⟨e, by omega, hd⟩
        · obtain ⟨e, he, hd⟩ := ihd (by simp at h; rw [hs, h]); exact ⟨e, by omega, hd⟩
  obtain ⟨ir, im, ip, id⟩ := inv c.D le_rfl
  unfold classify
  rcases hs : c.pfold c.D I J with ⟨ia, ib, ja, jb⟩ | o
  · exfalso
    obtain ⟨-, -, hsep, -⟩ := ir ia ib ja jb hs
    exact hoI (hsep c.D le_rfl).1
  · simp only
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> subst h
    · exact im hs
    · exact ip hs
    · exact id hs

end LC

end BLMS

end PathChecking
