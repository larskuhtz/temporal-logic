module

public import RequestProject.BLMS.Classify

/-!
# The pushdown algorithm of [BLMS, Section 5]

The algorithm considers the maximal true intervals of the input from left to right.  It keeps a
stack of intervals and a current interval `J`; a virtual interval `vL` sits below the stack, and
the virtual interval `vR` is used as `J` when all input intervals have been seen.  In each step
it looks at the top `I` of the stack and at `J`:

* if `I = vL` and `J = vR`, it rejects;
* if `J` alone makes the circuit accept, it accepts;
* if `I = vL`, it pushes `J` and continues with the next input interval;
* otherwise it classifies the pair `(I, J)` (`LC.classify`): it merges `I` and `J` into the new
  current interval, or pushes `J` and continues with the next input interval, or discards `I`.

Intervals are represented by numeric codes, and the algorithm is phrased as a machine `mstep` on
lists of codes (the stack, current interval on top) driven by the table `tab`: on a configuration
`cJ :: cI :: rest` it either accepts, rejects, or replaces `cJ :: cI` by a list of codes.  This
is exactly what the pushdown automaton of `RequestProject/BLMS/DPDA.lean` does.

The main result `LC.mrun_correct` says that after `3 N + 3` steps (where `N` is the number of
input gates) the machine has accepted iff the circuit accepts the input.
-/

@[expose] public section

namespace PathChecking

namespace BLMS

open Set

/-- The least `p < N` with `P p`, or `N` if there is none (computed by a left-to-right scan). -/
def firstF (P : ℕ → Bool) (N : ℕ) : ℕ :=
  (List.range N).foldl (fun r p => if r = N ∧ P p = true then p else r) N

lemma firstF_aux (P : ℕ → Bool) (N : ℕ) : ∀ k ≤ N,
    let r := (List.range k).foldl (fun r p => if r = N ∧ P p = true then p else r) N
    (r = N ∧ ∀ q < k, P q = false) ∨ (r < k ∧ P r = true ∧ ∀ q < r, P q = false) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases ih (by omega) with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · rw [h1]
      by_cases hp : P k = true
      · rw [if_pos ⟨rfl, hp⟩]
        exact Or.inr ⟨by omega, hp, h2⟩
      · rw [if_neg (fun h => hp h.2)]
        refine Or.inl ⟨rfl, fun q hq => ?_⟩
        rcases Nat.lt_or_ge q k with h | h
        · exact h2 q h
        · have : q = k := by omega
          subst this; simpa using hp
    · rw [if_neg (fun h => by omega)]
      exact Or.inr ⟨by omega, h2, h3⟩

lemma firstF_spec (P : ℕ → Bool) (N : ℕ) :
    (firstF P N = N ∧ ∀ q < N, P q = false) ∨
      (firstF P N < N ∧ P (firstF P N) = true ∧ ∀ q < firstF P N, P q = false) :=
  firstF_aux P N N le_rfl

namespace LC

variable (c : LC) (inp : ℕ → Bool)

/-- Number of input gates. -/
def N : ℕ := c.bd 1

/-- The set of true input gates. -/
def X0 : Set ℕ := {p | p < c.N ∧ inp p = true}

/-- The virtual left interval. -/
def vL : ℕ × ℕ := (0, 0)

/-- The virtual right interval. -/
def vR : ℕ × ℕ := (c.N, c.N)

/-- The first maximal true input interval starting at or after `d`, or `vR`. -/
def nextRun (d : ℕ) : ℕ × ℕ :=
  if firstF (fun p => decide (d ≤ p) && inp p) c.N < c.N then
    (firstF (fun p => decide (d ≤ p) && inp p) c.N,
      firstF (fun q => decide (firstF (fun p => decide (d ≤ p) && inp p) c.N < q) && !inp q) c.N)
  else c.vR

/-- Actions of the algorithm. -/
inductive Act
  | accept
  | reject
  | merge
  | push
  | disc
  deriving DecidableEq

/-- The action of the algorithm on top of stack `I` and current interval `J`. -/
def action (I J : ℕ × ℕ) : Act :=
  if J = c.vR then (if I = vL then .reject else .disc)
  else if c.loneAcc J = true then .accept
  else if I = vL then .push
  else match c.classify I J with
    | .merge => .merge
    | .push => .push
    | .disc => .disc

/-- Numeric code of an interval. -/
def code (p : ℕ × ℕ) : ℕ := p.1 * (c.N + 1) + p.2

/-- Decoding. -/
def dec (k : ℕ) : ℕ × ℕ := (k / (c.N + 1), k % (c.N + 1))

/-- Entries of the table. -/
inductive TRes
  | acc
  | rej
  | scr (s : List ℕ)

/-- The table: what to do on top of stack `cI` and current interval `cJ` (codes). -/
def tab (cI cJ : ℕ) : TRes :=
  match c.action (c.dec cI) (c.dec cJ) with
  | .accept => .acc
  | .reject => .rej
  | .merge => .scr [c.code ((c.dec cI).1, (c.dec cJ).2)]
  | .push => .scr [cI, cJ, c.code (c.nextRun inp (c.dec cJ).2)]
  | .disc => .scr [cJ]

/-- Results of the code machine. -/
inductive MRes
  | acc
  | rej
  | cont (l : List ℕ)

/-- One step of the code machine. -/
def mstep : List ℕ → MRes
  | cJ :: cI :: rest =>
    match c.tab inp cI cJ with
    | .acc => .acc
    | .rej => .rej
    | .scr s => .cont (s.reverse ++ rest)
  | _ => .rej

/-- `k` steps of the code machine. -/
def mrun : ℕ → MRes → MRes
  | 0, r => r
  | k + 1, .cont l => mrun k (c.mstep inp l)
  | _ + 1, r => r

/-- The configuration of the code machine for stack `stk` and current interval `J`. -/
def cfg (stk : List (ℕ × ℕ)) (J : ℕ × ℕ) : List ℕ :=
  c.code J :: (stk.map c.code ++ [c.code vL])

/-- The input represented by a state of the algorithm. -/
def Y (stk : List (ℕ × ℕ)) (J : ℕ × ℕ) : Set ℕ :=
  {x | ∃ K ∈ stk, x ∈ Ico K.1 K.2} ∪ Ico J.1 J.2 ∪ {p | J.2 ≤ p ∧ p ∈ c.X0 inp}

/-- The invariant of the algorithm. -/
structure Inv (stk : List (ℕ × ℕ)) (J : ℕ × ℕ) : Prop where
  jle : J.2 ≤ c.N
  jend : J.2 = c.N ∨ inp J.2 = false
  jv : J = c.vR ∨ J.1 < J.2
  sreal : ∀ K ∈ stk, K.1 < K.2 ∧ K.2 ≤ c.N ∧ ¬ c.out (Ico K.1 K.2)
  sord : stk.Pairwise (fun K' K => K.2 < K'.1)
  spush : stk.IsChain (fun K' K => ∃ e < c.D, c.PushData (Ico K.1 K.2) (Ico K'.1 K'.2) e)
  top : J.1 < J.2 → ∀ K ∈ stk.head?, K.2 < J.1
  val : c.out (c.Y inp stk J) ↔ c.out (c.X0 inp)

/-- The potential. -/
def pot (stk : List (ℕ × ℕ)) (J : ℕ × ℕ) : ℕ :=
  3 * (c.N - J.2) + stk.length + (if J.1 < J.2 then 2 else 0)

variable {c inp}

lemma dec_code {p : ℕ × ℕ} (h : p.2 ≤ c.N) : c.dec (c.code p) = p := by
  obtain ⟨a, b⟩ := p
  simp only [dec, code] at *
  have h1 : (a * (c.N + 1) + b) / (c.N + 1) = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]; simp
  have h2 : (a * (c.N + 1) + b) % (c.N + 1) = b := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2]

/-- The properties of `nextRun`. -/
lemma nextRun_spec {d : ℕ} (hd : d ≤ c.N) :
    let r := c.nextRun inp d
    r.2 ≤ c.N ∧ (r.2 = c.N ∨ inp r.2 = false) ∧
    (r = c.vR ∨ ((d ≤ r.1 ∧ (inp d = false → d < r.1)) ∧ r.1 < r.2)) ∧
    {p | d ≤ p ∧ p ∈ c.X0 inp} = Ico r.1 r.2 ∪ {p | r.2 ≤ p ∧ p ∈ c.X0 inp} := by
  intro r
  have hr : r = c.nextRun inp d := rfl
  unfold nextRun at hr
  rcases firstF_spec (fun p => decide (d ≤ p) && inp p) c.N with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [if_neg (by omega)] at hr
    rw [hr]
    refine ⟨by simp [vR], Or.inl (by simp [vR]), Or.inl rfl, ?_⟩
    ext p
    simp only [mem_setOf_eq, X0, vR, mem_union, mem_Ico]
    constructor
    · rintro ⟨hdp, hpN, hp⟩
      have := h2 p hpN
      simp [hdp, hp] at this
    · rintro (h | ⟨h, h', -⟩) <;> omega
  · rw [if_pos h1] at hr
    set p0 := firstF (fun p => decide (d ≤ p) && inp p) c.N
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    rcases firstF_spec (fun q => decide (p0 < q) && !inp q) c.N with ⟨g1, g2⟩ | ⟨g1, g2, g3⟩
    · rw [hr]; simp only
      rw [g1]
      refine ⟨le_rfl, Or.inl rfl, Or.inr ⟨?_, h1⟩, ?_⟩
      · refine ⟨h2.1, fun hd' => lt_of_le_of_ne h2.1 (fun h => ?_)⟩
        rw [← h] at h2; simp [hd'] at h2
      · ext p
        simp only [mem_setOf_eq, X0, mem_union, mem_Ico]
        constructor
        · rintro ⟨hdp, hpN, hp⟩
          rcases Nat.lt_or_ge p p0 with h | h
          · have := h3 p h; simp [hdp, hp] at this
          · exact Or.inl ⟨h, hpN⟩
        · rintro (⟨ha, hb⟩ | ⟨ha, hb, -⟩)
          · refine ⟨by omega, hb, ?_⟩
            rcases Nat.lt_or_ge p0 p with h | h
            · have := g2 p hb; simpa [h] using this
            · have : p = p0 := by omega
              rw [this]; exact h2.2
          · omega
    · rw [hr]; simp only
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at g2
      refine ⟨by omega, Or.inr g2.2, Or.inr ⟨?_, g2.1⟩, ?_⟩
      · refine ⟨h2.1, fun hd' => lt_of_le_of_ne h2.1 (fun h => ?_)⟩
        rw [← h] at h2; simp [hd'] at h2
      · set q0 := firstF (fun q => decide (p0 < q) && !inp q) c.N
        ext p
        simp only [mem_setOf_eq, X0, mem_union, mem_Ico]
        constructor
        · rintro ⟨hdp, hpN, hp⟩
          rcases Nat.lt_or_ge p p0 with h | h
          · have := h3 p h; simp [hdp, hp] at this
          · rcases Nat.lt_or_ge p q0 with h' | h'
            · exact Or.inl ⟨h, h'⟩
            · exact Or.inr ⟨h', hpN, hp⟩
        · rintro (⟨ha, hb⟩ | ⟨ha, hb, hc⟩)
          · refine ⟨by omega, by omega, ?_⟩
            rcases Nat.lt_or_ge p0 p with h | h
            · have := g3 p hb; simpa [h] using this
            · have : p = p0 := by omega
              rw [this]; exact h2.2
          · exact ⟨by omega, hb, hc⟩

lemma Y_vR (stk : List (ℕ × ℕ)) : c.Y inp stk c.vR = {x | ∃ K ∈ stk, x ∈ Ico K.1 K.2} := by
  ext x
  simp only [Y, vR, X0, mem_union, mem_setOf_eq, mem_Ico]
  constructor
  · rintro ((h | h) | ⟨h1, h2, -⟩)
    · exact h
    · omega
    · omega
  · intro h; exact Or.inl (Or.inl h)

lemma Y_cons (K : ℕ × ℕ) (stk : List (ℕ × ℕ)) (J : ℕ × ℕ) :
    c.Y inp (K :: stk) J = {x | ∃ K ∈ stk, x ∈ Ico K.1 K.2} ∪
      (Ico J.1 J.2 ∪ {p | J.2 ≤ p ∧ p ∈ c.X0 inp}) ∪ Ico K.1 K.2 := by
  ext x
  simp only [Y, List.mem_cons, mem_union, mem_setOf_eq]
  constructor
  · rintro ((⟨K', hK', hx⟩ | h) | h)
    · rcases hK' with rfl | hK'
      · exact Or.inr hx
      · exact Or.inl (Or.inl ⟨K', hK', hx⟩)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((⟨K', hK', hx⟩ | h | h) | h)
    · exact Or.inl (Or.inl ⟨K', Or.inr hK', hx⟩)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl ⟨K, Or.inl rfl, h⟩)

/-- Discarding the top of the stack. -/
lemma discard_top (hP : c.Planar) {K : ℕ × ℕ} {stk : List (ℕ × ℕ)} {J : ℕ × ℕ}
    (hI : Inv c inp (K :: stk) J) {e : ℕ} (he : e < c.D)
    (hIe : ∀ l ≤ e, (c.ev l (Ico K.1 K.2)).Nonempty) (hId : c.ev (e + 1) (Ico K.1 K.2) = ∅)
    (hR : Ico J.1 J.2 ∪ {p | J.2 ≤ p ∧ p ∈ c.X0 inp} = ∅ ∨
      ∃ J' : Set ℕ, J'.OrdConnected ∧
        (∀ b ∈ Ico J.1 J.2 ∪ {p | J.2 ≤ p ∧ p ∈ c.X0 inp}, ∃ j ∈ J', j ≤ b) ∧
        c.DiscData (Ico K.1 K.2) J' e) :
    c.out (c.Y inp stk J) ↔ c.out (c.Y inp (K :: stk) J) := by
  have key := discard hP (A := {x | ∃ K ∈ stk, x ∈ Ico K.1 K.2}) he hIe hId ?_ hR
  · rw [Y_cons, out, out, key]; simp only [Y, union_assoc]
  rcases hs : stk with _ | ⟨H, rest⟩
  · left; ext x; simp
  · right
    rw [hs] at hI
    refine ⟨Ico H.1 H.2, ordConnected_Ico, ?_, ?_⟩
    · rintro a ⟨K', hK', ha⟩
      rcases List.mem_cons.1 hK' with rfl | hK'
      · exact ⟨a, ha, le_rfl⟩
      · have h1 := hI.sord
        simp only [List.pairwise_cons] at h1
        have h2 := h1.2.1 K' hK'
        have h3 := (hI.sreal H (by simp)).1
        simp only [mem_Ico] at ha
        exact ⟨H.1, by simp [h3], by omega⟩
    · have hc := hI.spush
      simp only [List.isChain_cons_cons] at hc
      obtain ⟨e', he', hd⟩ := hc.1
      have : e' = e := death_unique (fun l hl => (hd.sep l hl).2.1) hd.dead hIe hId
      subst this
      exact hd

lemma Y_out_mono_J {stk : List (ℕ × ℕ)} {J : ℕ × ℕ} (h : c.out (Ico J.1 J.2)) :
    c.out (c.Y inp stk J) :=
  out_mono (fun x hx => Or.inl (Or.inr hx)) h

/-- Pushing the current interval. -/
lemma inv_push {stk : List (ℕ × ℕ)} {J : ℕ × ℕ} (hI : Inv c inp stk J) (hJ : J.1 < J.2)
    (hoJ : ¬ c.out (Ico J.1 J.2))
    (hp : stk = [] ∨ ∃ K stk', stk = K :: stk' ∧ ∃ e < c.D, c.PushData (Ico K.1 K.2) (Ico J.1 J.2) e) :
    Inv c inp (J :: stk) (c.nextRun inp J.2) ∧
      c.pot (J :: stk) (c.nextRun inp J.2) < c.pot stk J := by
  obtain ⟨r1, r2, r3, r4⟩ := nextRun_spec (c := c) (inp := inp) hI.jle
  set r := c.nextRun inp J.2
  have hbelow : ∀ K ∈ stk, K.2 < J.1 := by
    rcases hs : stk with _ | ⟨H, t⟩
    · simp
    · rw [hs] at hI
      intro K hK
      have htop := hI.top hJ H (by simp)
      rcases List.mem_cons.1 hK with rfl | hK
      · exact htop
      · have h1 := (List.pairwise_cons.1 hI.sord).1 K hK
        have h2 := (hI.sreal H (by simp)).1
        omega
  refine ⟨⟨r1, r2, r3.imp id (fun h => h.2), fun K hK => ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rcases List.mem_cons.1 hK with rfl | hK
    · exact ⟨hJ, hI.jle, hoJ⟩
    · exact hI.sreal K hK
  · exact List.pairwise_cons.2 ⟨fun K hK => hbelow K hK, hI.sord⟩
  · rcases hp with rfl | ⟨K, stk', rfl, hd⟩
    · simp
    · exact List.isChain_cons_cons.2 ⟨hd, hI.spush⟩
  · intro hr K hK
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hK
    subst hK
    rcases r3 with h | h
    · rw [h] at hr; simp [vR] at hr
    · rcases hI.jend with he | he
      · have := h.1.1; have := h.2; omega
      · exact h.1.2 he
  · rw [← hI.val]
    have : c.Y inp (J :: stk) r = c.Y inp stk J := by
      simp only [Y, r4]
      ext x
      simp only [mem_union, mem_setOf_eq, List.mem_cons]
      constructor
      · rintro ((⟨K, hK, hx⟩ | hx) | hx)
        · rcases hK with rfl | hK
          · exact Or.inl (Or.inr hx)
          · exact Or.inl (Or.inl ⟨K, hK, hx⟩)
        · exact Or.inr (Or.inl hx)
        · exact Or.inr (Or.inr hx)
      · rintro ((⟨K, hK, hx⟩ | hx) | hx | hx)
        · exact Or.inl (Or.inl ⟨K, Or.inr hK, hx⟩)
        · exact Or.inl (Or.inl ⟨J, Or.inl rfl, hx⟩)
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
    rw [this]
  · simp only [pot, List.length_cons, if_pos hJ]
    rcases r3 with h | h
    · rw [h]; simp [vR]
    · rw [if_pos h.2]; omega

/-- Popping the top of the stack. -/
lemma inv_pop {K : ℕ × ℕ} {stk : List (ℕ × ℕ)} {J : ℕ × ℕ} (hI : Inv c inp (K :: stk) J)
    (hv : c.out (c.Y inp stk J) ↔ c.out (c.Y inp (K :: stk) J)) :
    Inv c inp stk J ∧ c.pot stk J < c.pot (K :: stk) J := by
  refine ⟨⟨hI.jle, hI.jend, hI.jv, fun K' hK' => hI.sreal K' (by simp [hK']),
    (List.pairwise_cons.1 hI.sord).2, hI.spush.tail, fun hJ K' hK' => ?_, hv.trans hI.val⟩, ?_⟩
  · rcases stk with _ | ⟨H, t⟩
    · simp at hK'
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hK'
      subst hK'
      have h1 := (List.pairwise_cons.1 hI.sord).1 H (by simp)
      have h2 := (hI.sreal K (by simp)).1
      have h3 := hI.top hJ K (by simp)
      omega
  · simp [pot]

/-- Merging the top of the stack with the current interval. -/
lemma inv_merge {K : ℕ × ℕ} {stk : List (ℕ × ℕ)} {J : ℕ × ℕ} (hI : Inv c inp (K :: stk) J)
    (hJ : J.1 < J.2)
    (hv : c.out (c.Y inp stk (K.1, J.2)) ↔ c.out (c.Y inp (K :: stk) J)) :
    Inv c inp stk (K.1, J.2) ∧ c.pot stk (K.1, J.2) < c.pot (K :: stk) J := by
  have hK := hI.sreal K (by simp)
  have htop := hI.top hJ K (by simp)
  refine ⟨⟨hI.jle, hI.jend, Or.inr (by simp only; omega), fun K' hK' => hI.sreal K' (by simp [hK']),
    (List.pairwise_cons.1 hI.sord).2, hI.spush.tail, fun _ K' hK' => ?_, hv.trans hI.val⟩, ?_⟩
  · rcases stk with _ | ⟨H, t⟩
    · simp at hK'
    · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hK'
      subst hK'
      exact (List.pairwise_cons.1 hI.sord).1 H (by simp)
  · simp only [pot, List.length_cons]
    rw [if_pos (by omega : K.1 < J.2), if_pos hJ]
    omega

/-- **One step of the algorithm** preserves the invariant, decreases the potential, and accepts
or rejects correctly. -/
theorem mstep_spec (hP : c.Planar) {stk : List (ℕ × ℕ)} {J : ℕ × ℕ} (hI : Inv c inp stk J) :
    (c.mstep inp (c.cfg stk J) = .acc → c.out (c.X0 inp)) ∧
    (c.mstep inp (c.cfg stk J) = .rej → ¬ c.out (c.X0 inp)) ∧
    (∀ l, c.mstep inp (c.cfg stk J) = .cont l →
      ∃ stk' J', l = c.cfg stk' J' ∧ Inv c inp stk' J' ∧ c.pot stk' J' < c.pot stk J) := by
  have hdJ : c.dec (c.code J) = J := dec_code hI.jle
  rcases hs : stk with _ | ⟨K, stk'⟩
  · -- empty stack: the top is `vL`
    rw [hs] at hI
    have hstep : c.mstep inp (c.cfg [] J) = match c.action vL J with
        | .accept => .acc | .reject => .rej
        | .merge => .cont ([c.code (vL.1, J.2)].reverse)
        | .push => .cont ([c.code vL, c.code J, c.code (c.nextRun inp J.2)].reverse)
        | .disc => .cont [c.code J] := by
      have hdv : c.dec (c.code vL) = vL := dec_code (by simp [vL])
      simp only [cfg, List.map_nil, List.nil_append, mstep, tab, hdv, hdJ]
      cases c.action vL J <;> simp
    rw [hstep]
    by_cases hJv : J = c.vR
    · have : c.action vL J = .reject := by simp [action, hJv]
      rw [this]
      refine ⟨fun h => by simp at h, fun _ => ?_, fun l h => by simp at h⟩
      rw [← hI.val, hJv, Y_vR]
      simpa using (out_empty (c := c))
    have hJ : J.1 < J.2 := hI.jv.resolve_left hJv
    by_cases hacc : c.loneAcc J = true
    · have : c.action vL J = .accept := by simp [action, hJv, hacc]
      rw [this]
      refine ⟨fun _ => hI.val.1 (Y_out_mono_J ((loneAcc_iff hP J).1 hacc)),
        fun h => by simp at h, fun l h => by simp at h⟩
    have : c.action vL J = .push := by simp [action, hJv, hacc]
    rw [this]
    refine ⟨fun h => by simp at h, fun h => by simp at h, fun l h => ?_⟩
    simp only [MRes.cont.injEq] at h
    subst h
    have hoJ : ¬ c.out (Ico J.1 J.2) := fun h => hacc ((loneAcc_iff hP J).2 h)
    obtain ⟨h1, h2⟩ := inv_push hI hJ hoJ (Or.inl rfl)
    exact ⟨[J], c.nextRun inp J.2, by simp [cfg], h1, h2⟩
  · -- the top is the real interval `K`
    rw [hs] at hI
    have hK := hI.sreal K (by simp)
    have hdK : c.dec (c.code K) = K := dec_code hK.2.1
    have hKvL : K ≠ vL := by intro h; rw [h] at hK; simp [vL] at hK
    have hstep : c.mstep inp (c.cfg (K :: stk') J) = match c.action K J with
        | .accept => .acc | .reject => .rej
        | .merge => .cont (c.cfg stk' (K.1, J.2))
        | .push => .cont (c.cfg (J :: K :: stk') (c.nextRun inp J.2))
        | .disc => .cont (c.cfg stk' J) := by
      simp only [cfg, List.map_cons, List.cons_append, mstep, tab, hdK, hdJ]
      cases c.action K J <;> simp
    rw [hstep]
    by_cases hJv : J = c.vR
    · have : c.action K J = .disc := by simp [action, hJv, hKvL]
      rw [this]
      refine ⟨fun h => by simp at h, fun h => by simp at h, fun l h => ?_⟩
      simp only [MRes.cont.injEq] at h
      subst h
      obtain ⟨e, he, hIe, hId⟩ := exists_death (nonempty_Ico.2 hK.1) hK.2.2
      have hv := discard_top hP hI he hIe hId (Or.inl (by
        rw [hJv]; ext x; simp [vR, X0]; omega))
      obtain ⟨h1, h2⟩ := inv_pop hI hv
      exact ⟨stk', J, rfl, h1, h2⟩
    have hJ : J.1 < J.2 := hI.jv.resolve_left hJv
    by_cases hacc : c.loneAcc J = true
    · have : c.action K J = .accept := by simp [action, hJv, hacc]
      rw [this]
      refine ⟨fun _ => hI.val.1 (Y_out_mono_J ((loneAcc_iff hP J).1 hacc)),
        fun h => by simp at h, fun l h => by simp at h⟩
    have hoJ : ¬ c.out (Ico J.1 J.2) := fun h => hacc ((loneAcc_iff hP J).2 h)
    have htop := hI.top hJ K (by simp)
    obtain ⟨cm, cp, cd⟩ := classify_spec hP hK.1 hJ htop hK.2.2
    have hact : c.action K J = match c.classify K J with
        | .merge => .merge | .push => .push | .disc => .disc := by
      simp [action, hJv, hacc, hKvL]
    rw [hact]
    rcases hcl : c.classify K J
    · -- merge
      obtain ⟨e, he, hd⟩ := cm hcl
      refine ⟨fun h => by simp at h, fun h => by simp at h, fun l h => ?_⟩
      simp only [MRes.cont.injEq] at h
      subst h
      have key := merge hP (A := {x | ∃ K ∈ stk', x ∈ Ico K.1 K.2})
        (B := {p | J.2 ≤ p ∧ p ∈ c.X0 inp}) (G := Ico K.2 J.1) he ordConnected_Ico
        ordConnected_Ico ?_ ?_ ?_ hd
      · have hv : c.out (c.Y inp stk' (K.1, J.2)) ↔ c.out (c.Y inp (K :: stk') J) := by
          have hI3 : Ico K.1 J.2 = Ico K.1 K.2 ∪ Ico J.1 J.2 ∪ Ico K.2 J.1 := by
            ext x; simp only [mem_union, mem_Ico]; omega
          have e1 : c.Y inp stk' (K.1, J.2) = {x | ∃ K ∈ stk', x ∈ Ico K.1 K.2} ∪ Ico K.1 K.2 ∪
              Ico J.1 J.2 ∪ {p | J.2 ≤ p ∧ p ∈ c.X0 inp} ∪ Ico K.2 J.1 := by
            simp only [Y]; rw [hI3]; ext x; simp only [mem_union]; tauto
          have e2 : c.Y inp (K :: stk') J = {x | ∃ K ∈ stk', x ∈ Ico K.1 K.2} ∪ Ico K.1 K.2 ∪
              Ico J.1 J.2 ∪ {p | J.2 ≤ p ∧ p ∈ c.X0 inp} := by
            rw [Y_cons]; ext x; simp only [mem_union]; tauto
          rw [e1, e2, out, out, key]
        obtain ⟨h1, h2⟩ := inv_merge hI hJ hv
        exact ⟨stk', (K.1, J.2), rfl, h1, h2⟩
      · rintro a ⟨K', hK', ha⟩ x hx
        have := (List.pairwise_cons.1 hI.sord).1 K' hK'
        simp only [mem_Ico] at ha hx; omega
      · rintro b ⟨hb, -⟩ y hy
        simp only [mem_Ico] at hy; omega
      · intro z hz
        simp only [mem_Ico] at hz
        exact ⟨fun x hx => by simp only [mem_Ico] at hx; omega,
          fun y hy => by simp only [mem_Ico] at hy; omega⟩
    · -- push
      obtain ⟨e, he, hd⟩ := cp hcl
      refine ⟨fun h => by simp at h, fun h => by simp at h, fun l h => ?_⟩
      simp only [MRes.cont.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := inv_push hI hJ hoJ (Or.inr ⟨K, stk', rfl, e, he, hd⟩)
      exact ⟨J :: K :: stk', c.nextRun inp J.2, rfl, h1, h2⟩
    · -- discard
      obtain ⟨e, he, hd⟩ := cd hcl
      refine ⟨fun h => by simp at h, fun h => by simp at h, fun l h => ?_⟩
      simp only [MRes.cont.injEq] at h
      subst h
      have hb' : ∀ b ∈ Ico J.1 J.2 ∪ {p | J.2 ≤ p ∧ p ∈ c.X0 inp}, ∃ j ∈ Ico J.1 J.2, j ≤ b := by
        intro b hb
        refine ⟨J.1, ⟨le_rfl, hJ⟩, ?_⟩
        rcases hb with hb | hb
        · exact hb.1
        · have := hb.1; omega
      have hv := discard_top hP hI he (fun l hl => (hd.sep l hl).1) hd.dead (Or.inr
        ⟨Ico J.1 J.2, ordConnected_Ico, hb', hd⟩)
      obtain ⟨h1, h2⟩ := inv_pop hI hv
      exact ⟨stk', J, rfl, h1, h2⟩

lemma mrun_acc (k : ℕ) : c.mrun inp k .acc = .acc := by
  cases k <;> rfl

lemma mrun_rej (k : ℕ) : c.mrun inp k .rej = .rej := by
  cases k <;> rfl

lemma mrun_spec (hP : c.Planar) : ∀ k (stk : List (ℕ × ℕ)) (J : ℕ × ℕ), Inv c inp stk J →
    c.pot stk J < k →
    (c.out (c.X0 inp) → c.mrun inp k (.cont (c.cfg stk J)) = .acc) ∧
    (¬ c.out (c.X0 inp) → c.mrun inp k (.cont (c.cfg stk J)) = .rej) := by
  intro k
  induction k with
  | zero => intro _ _ _ h; omega
  | succ k ih =>
    intro stk J hI hk
    obtain ⟨ha, hr, hc⟩ := mstep_spec hP hI
    simp only [mrun]
    rcases hm : c.mstep inp (c.cfg stk J) with _ | _ | l
    · exact ⟨fun _ => mrun_acc k, fun h => absurd (ha hm) h⟩
    · exact ⟨fun h => absurd h (hr hm), fun _ => mrun_rej k⟩
    · obtain ⟨stk', J', rfl, hI', hp⟩ := hc l hm
      exact ih stk' J' hI' (by omega)

/-- The initial state satisfies the invariant. -/
lemma inv_init : Inv c inp [] (c.nextRun inp 0) ∧ c.pot [] (c.nextRun inp 0) ≤ 3 * c.N + 2 := by
  obtain ⟨r1, r2, r3, r4⟩ := nextRun_spec (c := c) (inp := inp) (Nat.zero_le _)
  refine ⟨⟨r1, r2, r3.imp id (fun h => h.2), fun K hK => by simp at hK, List.Pairwise.nil,
    List.isChain_nil, fun _ K hK => by simp at hK, ?_⟩, ?_⟩
  · have : c.Y inp [] (c.nextRun inp 0) = c.X0 inp := by
      simp only [Y, List.not_mem_nil, false_and, exists_false, setOf_false, empty_union]
      rw [← r4]; ext x; simp
    rw [this]
  · simp only [pot, List.length_nil]
    split_ifs <;> omega

/-- **Correctness of the algorithm.** -/
theorem mrun_correct (hP : c.Planar) {T : ℕ} (hT : 3 * c.N + 3 ≤ T) :
    (c.out (c.X0 inp) → c.mrun inp T (.cont (c.cfg [] (c.nextRun inp 0))) = .acc) ∧
    (¬ c.out (c.X0 inp) → c.mrun inp T (.cont (c.cfg [] (c.nextRun inp 0))) = .rej) := by
  obtain ⟨h1, h2⟩ := inv_init (c := c) (inp := inp)
  exact mrun_spec hP T [] _ h1 (by omega)

end LC

end BLMS

end PathChecking
