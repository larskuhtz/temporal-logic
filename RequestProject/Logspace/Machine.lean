module

public import RequestProject.Logspace.Prog
public import RequestProject.Logspace.Bits

/-!
# Compiling goto programs into logspace Turing machines

The work tape has `K + 2` tracks: a left-end marker, an "allocated" flag and one track per
register.  Cell `0` holds the marker; register `r` is stored in binary (least significant
bit first) on track `r` of cells `1, 2, …`.  Cells `1 … A` are allocated, where `A` is at
least the bit length of every register; the zero test scans the allocated region.

Each goto instruction is simulated by a macro that starts and ends with the work head on
the marker.  The work head never goes beyond cell `A + 1`, and `A ≤ size B` when all
registers stay `≤ B`.
-/

@[expose] public section

namespace PathChecking

namespace LS

/-! ## Reachability with an invariant -/

/-- `c'` is reachable from `c` and all configurations on the way satisfy `P`. -/
def Reach (M : TM) (w : Word) (P : M.Cfg → Prop) (c c' : M.Cfg) : Prop :=
  ∃ t, (M.step w)^[t] c = c' ∧ ∀ i ≤ t, P ((M.step w)^[i] c)

namespace Reach

variable {M : TM} {w : Word} {P : M.Cfg → Prop}

lemma refl {c : M.Cfg} (hc : P c) : Reach M w P c c := ⟨0, rfl, fun i hi => by
  obtain rfl : i = 0 := by omega
  exact hc⟩

lemma trans {c₁ c₂ c₃ : M.Cfg} (h₁ : Reach M w P c₁ c₂) (h₂ : Reach M w P c₂ c₃) :
    Reach M w P c₁ c₃ := by
  obtain ⟨t₁, e₁, p₁⟩ := h₁
  obtain ⟨t₂, e₂, p₂⟩ := h₂
  refine ⟨t₂ + t₁, by rw [Function.iterate_add_apply, e₁, e₂], fun i hi => ?_⟩
  rcases Nat.lt_or_ge i t₁ with h | h
  · exact p₁ i h.le
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + t₁ := ⟨i - t₁, by omega⟩
    rw [Function.iterate_add_apply, e₁]
    exact p₂ j (by omega)

lemma single {c c' : M.Cfg} (h : M.step w c = c') (hc : P c) (hc' : P c') :
    Reach M w P c c' := ⟨1, by simpa using h, fun i hi => by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
  · exact hc
  · simpa [h] using hc'⟩

lemma head {c c' c'' : M.Cfg} (h : M.step w c = c') (hc : P c) (h' : Reach M w P c' c'') :
    Reach M w P c c'' := by
  obtain ⟨t, e, p⟩ := h'
  refine ⟨t + 1, by rw [Function.iterate_succ_apply, h, e], fun i hi => ?_⟩
  rcases i with _ | i
  · exact hc
  · rw [Function.iterate_succ_apply, h]; exact p i (by omega)

end Reach

/-! ## The machine -/

/-- Phases of the macros. -/
inductive Ph
  | init
  | bnd
  | carry
  | zsJ
  | zsD
  | retB
  | borrow
  | ret
  deriving DecidableEq, Fintype

/-- Work tape cells: marker, allocated flag, one bit per register. -/
abbrev Cell (K : ℕ) := Bool × Bool × (Fin K → Bool)

/-- The marker cell (cell `0`). -/
def markCell {K : ℕ} : Cell K := (true, false, fun _ => false)

/-- The blank cell. -/
def blankCell {K : ℕ} : Cell K := (false, false, fun _ => false)

/-- Set the bit of register `r` in a cell (and mark the cell as allocated). -/
def setBit {K : ℕ} (c : Cell K) (r : Fin K) (b : Bool) : Cell K :=
  (c.1, true, Function.update c.2.2 r b)

/-- Program counters, clamped to `0 … N`. -/
def clampPc (N x : ℕ) : Fin (N + 1) := ⟨min x N, by omega⟩

/-- States of the machine: program counter and phase. -/
abbrev MQ (N : ℕ) := Fin (N + 1) × Ph

variable {K : ℕ}

/-- Transition function. -/
def delta (code : List (GI K)) (N : ℕ) (q : MQ N) (i : InSym) (c : Cell K) :
    MQ N × Cell K × Dir × Dir × Option Bool :=
  match q.2, code.getD q.1.val .halt with
  | .init, _ => ((q.1, .bnd), markCell, .stay, .stay, none)
  | .bnd, .inc _ => ((q.1, .carry), c, .right, .stay, none)
  | .bnd, .dec _ => ((q.1, .zsD), c, .right, .stay, none)
  | .bnd, .jz _ _ => ((q.1, .zsJ), c, .right, .stay, none)
  | .bnd, .jsym s t =>
      ((if i = s then clampPc N t else clampPc N (q.1.val + 1), .bnd), c, .stay, .stay, none)
  | .bnd, .left => ((clampPc N (q.1.val + 1), .bnd), c, .stay, .left, none)
  | .bnd, .right => ((clampPc N (q.1.val + 1), .bnd), c, .stay, .right, none)
  | .bnd, .out b => ((clampPc N (q.1.val + 1), .bnd), c, .stay, .stay, some b)
  | .bnd, .jmp t => ((clampPc N t, .bnd), c, .stay, .stay, none)
  | .carry, .inc r =>
      if c.2.2 r then ((q.1, .carry), setBit c r false, .right, .stay, none)
      else ((clampPc N (q.1.val + 1), .ret), setBit c r true, .left, .stay, none)
  | .zsJ, .jz r t =>
      if c.2.1 = false then ((clampPc N t, .ret), c, .left, .stay, none)
      else if c.2.2 r then ((clampPc N (q.1.val + 1), .ret), c, .left, .stay, none)
      else ((q.1, .zsJ), c, .right, .stay, none)
  | .zsD, .dec r =>
      if c.2.1 = false then ((clampPc N (q.1.val + 1), .ret), c, .left, .stay, none)
      else if c.2.2 r then ((q.1, .retB), c, .left, .stay, none)
      else ((q.1, .zsD), c, .right, .stay, none)
  | .retB, _ =>
      if c.1 then ((q.1, .borrow), c, .right, .stay, none)
      else ((q.1, .retB), c, .left, .stay, none)
  | .borrow, .dec r =>
      if c.2.2 r then ((clampPc N (q.1.val + 1), .ret), setBit c r false, .left, .stay, none)
      else ((q.1, .borrow), setBit c r true, .right, .stay, none)
  | .ret, _ =>
      if c.1 then ((q.1, .bnd), c, .stay, .stay, none)
      else ((q.1, .ret), c, .left, .stay, none)
  | _, _ => (q, c, .stay, .stay, none)

/-- Halting states: boundary phase at a `halt` instruction. -/
def haltQ (code : List (GI K)) (N : ℕ) (q : MQ N) : Bool :=
  match q.2, code.getD q.1.val .halt with
  | .bnd, .halt => true
  | _, _ => false

/-- The Turing machine simulating a goto program. -/
def machine (code : List (GI K)) (N : ℕ) : TM where
  Q := MQ N
  Γ := Cell K
  blank := blankCell
  start := (0, .init)
  halt := haltQ code N
  δ := delta code N

lemma machine_step (code : List (GI K)) (N : ℕ) (w : Word) (q : MQ N) (ip : ℕ)
    (T : ℕ → Cell K) (wp : ℕ) (o : List Bool) (hq : haltQ code N q = false) :
    (machine code N).step w ⟨q, ip, T, wp, o⟩ =
      ⟨(delta code N q (inputSym w ip) (T wp)).1,
        min ((delta code N q (inputSym w ip) (T wp)).2.2.2.1.move ip) (w.length + 1),
        Function.update T wp (delta code N q (inputSym w ip) (T wp)).2.1,
        (delta code N q (inputSym w ip) (T wp)).2.2.1.move wp,
        o ++ (delta code N q (inputSym w ip) (T wp)).2.2.2.2.toList⟩ := by
  simp only [TM.step, machine, hq]
  rfl

/-! ## Tapes -/

/-- The tape with allocated region `1 … A` and register tracks `g`. -/
def tapeOf (A : ℕ) (g : Fin K → ℕ → Bool) : ℕ → Cell K := fun p =>
  if p = 0 then markCell else (false, decide (p ≤ A), fun r => g r (p - 1))

/-- The tape encoding the register file `ρ`. -/
def encTape (A : ℕ) (ρ : Fin K → ℕ) : ℕ → Cell K := tapeOf A (fun r i => (ρ r).testBit i)

lemma tapeOf_zero (A : ℕ) (g : Fin K → ℕ → Bool) : tapeOf A g 0 = markCell := rfl

lemma tapeOf_pos (A : ℕ) (g : Fin K → ℕ → Bool) {p : ℕ} (hp : p ≠ 0) :
    tapeOf A g p = (false, decide (p ≤ A), fun r => g r (p - 1)) := by
  simp [tapeOf, hp]

lemma update_tapeOf (A p : ℕ) (g : Fin K → ℕ → Bool) (r : Fin K) (b : Bool) (hp : 1 ≤ p)
    (hpA : p ≤ A + 1) :
    Function.update (tapeOf A g) p (setBit (tapeOf A g p) r b) =
      tapeOf (max A p) (Function.update g r (Function.update (g r) (p - 1) b)) := by
  funext q
  by_cases hq : q = p
  · subst hq
    rw [Function.update_self, tapeOf_pos _ _ (by omega), tapeOf_pos _ _ (by omega)]
    simp only [setBit]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · simp
    · funext r'
      by_cases hr : r' = r
      · subst hr; simp
      · simp [Function.update_of_ne hr]
  · rw [Function.update_of_ne hq]
    by_cases hq0 : q = 0
    · subst hq0; rfl
    · rw [tapeOf_pos _ _ hq0, tapeOf_pos _ _ hq0]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · simp only [decide_eq_decide]; omega
      · funext r'
        by_cases hr : r' = r
        · subst hr; simp only [Function.update_self]
          rw [Function.update_of_ne (by omega)]
        · simp [Function.update_of_ne hr]


lemma encTape_update (A : ℕ) (ρ : Fin K → ℕ) (r : Fin K) (x : ℕ) :
    encTape A (Function.update ρ r x) =
      tapeOf A (Function.update (fun r i => (ρ r).testBit i) r (fun i => x.testBit i)) := by
  unfold encTape; congr 1; funext r' i
  by_cases h : r' = r
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma encTape_eq (A : ℕ) (ρ : Fin K → ℕ) (r : Fin K) :
    encTape A ρ =
      tapeOf A (Function.update (fun r i => (ρ r).testBit i) r (fun i => (ρ r).testBit i)) := by
  rw [← encTape_update, Function.update_eq_self]

/-! ## Equations for the transition function -/

section Delta

variable (code : List (GI K)) (N : ℕ) (pc : Fin (N + 1)) (i : InSym) (c : Cell K)

lemma delta_ret : delta code N (pc, .ret) i c =
    if c.1 then ((pc, .bnd), c, .stay, .stay, none) else ((pc, .ret), c, .left, .stay, none) := by
  cases code.getD pc.val .halt <;> simp only [delta]

lemma delta_retB : delta code N (pc, .retB) i c =
    if c.1 then ((pc, .borrow), c, .right, .stay, none)
    else ((pc, .retB), c, .left, .stay, none) := by
  cases code.getD pc.val .halt <;> simp only [delta]

lemma delta_init : delta code N (pc, .init) i c = ((pc, .bnd), markCell, .stay, .stay, none) := by
  cases code.getD pc.val .halt <;> simp only [delta]

variable {code N pc}

lemma delta_carry {r : Fin K} (h : code.getD pc.val .halt = .inc r) :
    delta code N (pc, .carry) i c =
      if c.2.2 r then ((pc, .carry), setBit c r false, .right, .stay, none)
      else ((clampPc N (pc.val + 1), .ret), setBit c r true, .left, .stay, none) := by
  simp only [delta, h]

lemma delta_zsJ {r : Fin K} {t : ℕ} (h : code.getD pc.val .halt = .jz r t) :
    delta code N (pc, .zsJ) i c =
      if c.2.1 = false then ((clampPc N t, .ret), c, .left, .stay, none)
      else if c.2.2 r then ((clampPc N (pc.val + 1), .ret), c, .left, .stay, none)
      else ((pc, .zsJ), c, .right, .stay, none) := by
  simp only [delta, h]

lemma delta_zsD {r : Fin K} (h : code.getD pc.val .halt = .dec r) :
    delta code N (pc, .zsD) i c =
      if c.2.1 = false then ((clampPc N (pc.val + 1), .ret), c, .left, .stay, none)
      else if c.2.2 r then ((pc, .retB), c, .left, .stay, none)
      else ((pc, .zsD), c, .right, .stay, none) := by
  simp only [delta, h]

lemma delta_borrow {r : Fin K} (h : code.getD pc.val .halt = .dec r) :
    delta code N (pc, .borrow) i c =
      if c.2.2 r then ((clampPc N (pc.val + 1), .ret), setBit c r false, .left, .stay, none)
      else ((pc, .borrow), setBit c r true, .right, .stay, none) := by
  simp only [delta, h]

end Delta

lemma haltQ_of_ne_bnd (code : List (GI K)) (N : ℕ) (pc : Fin (N + 1)) (ph : Ph)
    (h : ph ≠ .bnd) : haltQ code N (pc, ph) = false := by
  cases ph <;> simp_all [haltQ]

/-! ## The macros -/

section Macros

variable {code : List (GI K)} {N : ℕ} {w : Word} {Bd : ℕ}

/-- The space invariant. -/
def Pb (code : List (GI K)) (N Bd : ℕ) (c : (machine code N).Cfg) : Prop := c.workPos ≤ Bd

lemma reach_ret (pc : Fin (N + 1)) (ip : ℕ) (hip : ip ≤ w.length + 1) (T : ℕ → Cell K)
    (o : List Bool) (hT0 : (T 0).1 = true) :
    ∀ p, p ≤ Bd → (∀ i, 1 ≤ i → i ≤ p → (T i).1 = false) →
      Reach (machine code N) w (Pb code N Bd) ⟨(pc, .ret), ip, T, p, o⟩
        ⟨(pc, .bnd), ip, T, 0, o⟩ := by
  intro p
  induction p with
  | zero =>
    intro hB _
    apply Reach.single _ (by simp [Pb]) (by simp [Pb])
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_ret]
    simp [hT0, Dir.move, hip]
  | succ p ih =>
    intro hB hT
    refine Reach.head ?_ (by simp [Pb]; omega) (ih (by omega) (fun i h1 h2 => hT i h1 (by omega)))
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_ret]
    simp [hT (p + 1) (by omega) le_rfl, Dir.move, hip]

lemma reach_retB (pc : Fin (N + 1)) (ip : ℕ) (hip : ip ≤ w.length + 1) (T : ℕ → Cell K)
    (o : List Bool) (hT0 : (T 0).1 = true) (hB1 : 1 ≤ Bd) :
    ∀ p, p ≤ Bd → (∀ i, 1 ≤ i → i ≤ p → (T i).1 = false) →
      Reach (machine code N) w (Pb code N Bd) ⟨(pc, .retB), ip, T, p, o⟩
        ⟨(pc, .borrow), ip, T, 1, o⟩ := by
  intro p
  induction p with
  | zero =>
    intro hB _
    apply Reach.single _ (by simp [Pb]) (by simp [Pb]; omega)
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_retB]
    simp [hT0, Dir.move, hip]
  | succ p ih =>
    intro hB hT
    refine Reach.head ?_ (by simp [Pb]; omega) (ih (by omega) (fun i h1 h2 => hT i h1 (by omega)))
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_retB]
    simp [hT (p + 1) (by omega) le_rfl, Dir.move, hip]

lemma tapeOf_mark_false (A : ℕ) (g : Fin K → ℕ → Bool) (i : ℕ) (hi : 1 ≤ i) :
    (tapeOf A g i).1 = false := by
  rw [tapeOf_pos _ _ (by omega)]

lemma update_tapeOf' (A m : ℕ) (g : Fin K → ℕ → Bool) (r : Fin K) (X : ℕ → Bool) (b : Bool)
    (hm : m ≤ A) :
    Function.update (tapeOf A (Function.update g r X)) (1 + m)
        (setBit (tapeOf A (Function.update g r X) (1 + m)) r b) =
      tapeOf (max A (1 + m)) (Function.update g r (Function.update X m b)) := by
  rw [update_tapeOf _ _ _ _ _ (by omega) (by omega), Function.update_idem, Function.update_self,
    show 1 + m - 1 = m by omega]

lemma tapeOf_alloc (A : ℕ) (g : Fin K → ℕ → Bool) (m : ℕ) (hm : m < A) :
    (tapeOf A g (1 + m)).2.1 = true := by
  rw [tapeOf_pos _ _ (by omega)]; simp; omega

lemma tapeOf_unalloc (A : ℕ) (g : Fin K → ℕ → Bool) : (tapeOf A g (1 + A)).2.1 = false := by
  rw [tapeOf_pos _ _ (by omega)]; simp

lemma tapeOf_bit (A : ℕ) (g : Fin K → ℕ → Bool) (m : ℕ) (r : Fin K) :
    (tapeOf A g (1 + m)).2.2 r = g r m := by
  rw [tapeOf_pos _ _ (by omega)]; simp

/-- Scanning for a nonzero bit (zero test of a jump). -/
lemma reach_zsJ (pc : Fin (N + 1)) (r : Fin K) (t : ℕ) (hins : code.getD pc.val .halt = .jz r t)
    (ip : ℕ) (hip : ip ≤ w.length + 1) (o : List Bool) (A : ℕ) (g : Fin K → ℕ → Bool) :
    ∀ m, m ≤ A → 1 + m ≤ Bd → (∀ i < m, g r i = false) →
      Reach (machine code N) w (Pb code N Bd) ⟨(pc, .zsJ), ip, tapeOf A g, 1, o⟩
        ⟨(pc, .zsJ), ip, tapeOf A g, 1 + m, o⟩ := by
  intro m
  induction m with
  | zero => intro _ hB _; exact Reach.refl (by simp [Pb]; omega)
  | succ m ih =>
    intro hm hB hg
    refine (ih (by omega) (by omega) (fun i hi => hg i (by omega))).trans
      (Reach.single ?_ (by simp [Pb]; omega) (by simp [Pb]; omega))
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_zsJ _ _ hins,
      tapeOf_alloc _ _ _ (by omega), tapeOf_bit, hg m (by omega)]
    simp only [Bool.true_eq_false, Bool.false_eq_true, if_false, Dir.move, min_eq_left hip, Function.update_eq_self,
      Option.toList_none, List.append_nil]
    rfl

/-- Scanning for a nonzero bit (decrement). -/
lemma reach_zsD (pc : Fin (N + 1)) (r : Fin K) (hins : code.getD pc.val .halt = .dec r)
    (ip : ℕ) (hip : ip ≤ w.length + 1) (o : List Bool) (A : ℕ) (g : Fin K → ℕ → Bool) :
    ∀ m, m ≤ A → 1 + m ≤ Bd → (∀ i < m, g r i = false) →
      Reach (machine code N) w (Pb code N Bd) ⟨(pc, .zsD), ip, tapeOf A g, 1, o⟩
        ⟨(pc, .zsD), ip, tapeOf A g, 1 + m, o⟩ := by
  intro m
  induction m with
  | zero => intro _ hB _; exact Reach.refl (by simp [Pb]; omega)
  | succ m ih =>
    intro hm hB hg
    refine (ih (by omega) (by omega) (fun i hi => hg i (by omega))).trans
      (Reach.single ?_ (by simp [Pb]; omega) (by simp [Pb]; omega))
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_zsD _ _ hins,
      tapeOf_alloc _ _ _ (by omega), tapeOf_bit, hg m (by omega)]
    simp only [Bool.true_eq_false, Bool.false_eq_true, if_false, Dir.move, min_eq_left hip, Function.update_eq_self,
      Option.toList_none, List.append_nil]
    rfl

/-- The carry loop of an increment. -/
lemma reach_carry (pc : Fin (N + 1)) (r : Fin K) (hins : code.getD pc.val .halt = .inc r)
    (ip : ℕ) (hip : ip ≤ w.length + 1) (o : List Bool) (A : ℕ) (g : Fin K → ℕ → Bool)
    (v : ℕ) :
    ∀ m, m ≤ A → 1 + m ≤ Bd → (∀ i < m, v.testBit i = true) →
      Reach (machine code N) w (Pb code N Bd)
        ⟨(pc, .carry), ip, tapeOf A (Function.update g r (fun i => v.testBit i)), 1, o⟩
        ⟨(pc, .carry), ip, tapeOf A (Function.update g r
          (fun i => if i < m then false else v.testBit i)), 1 + m, o⟩ := by
  intro m
  induction m with
  | zero => intro _ hB _; exact Reach.refl (by simp [Pb]; omega)
  | succ m ih =>
    intro hm hB hv
    refine (ih (by omega) (by omega) (fun i hi => hv i (by omega))).trans
      (Reach.single ?_ (by simp [Pb]; omega) (by simp [Pb]; omega))
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_carry _ _ hins]
    have hb : (tapeOf A (Function.update g r (fun i => if i < m then false else v.testBit i))
        (1 + m)).2.2 r = true := by
      rw [tapeOf_bit]; simp [hv m (by omega)]
    rw [if_pos hb]
    simp only [Dir.move, min_eq_left hip, Option.toList_none, List.append_nil]
    rw [update_tapeOf' _ _ _ _ _ _ (by omega), max_eq_left (by omega)]
    have hX : Function.update (fun i => if i < m then false else v.testBit i) m false =
        fun i => if i < m + 1 then false else v.testBit i := by
      funext i
      by_cases h : i = m
      · subst h; simp
      · rw [Function.update_of_ne h]
        split_ifs <;> first | rfl | omega
    rw [hX]
    rfl

/-- The borrow loop of a decrement. -/
lemma reach_borrow (pc : Fin (N + 1)) (r : Fin K) (hins : code.getD pc.val .halt = .dec r)
    (ip : ℕ) (hip : ip ≤ w.length + 1) (o : List Bool) (A : ℕ) (g : Fin K → ℕ → Bool)
    (v : ℕ) :
    ∀ m, m ≤ A → 1 + m ≤ Bd → (∀ i < m, v.testBit i = false) →
      Reach (machine code N) w (Pb code N Bd)
        ⟨(pc, .borrow), ip, tapeOf A (Function.update g r (fun i => v.testBit i)), 1, o⟩
        ⟨(pc, .borrow), ip, tapeOf A (Function.update g r
          (fun i => if i < m then true else v.testBit i)), 1 + m, o⟩ := by
  intro m
  induction m with
  | zero => intro _ hB _; exact Reach.refl (by simp [Pb]; omega)
  | succ m ih =>
    intro hm hB hv
    refine (ih (by omega) (by omega) (fun i hi => hv i (by omega))).trans
      (Reach.single ?_ (by simp [Pb]; omega) (by simp [Pb]; omega))
    rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_borrow _ _ hins]
    have hb : (tapeOf A (Function.update g r (fun i => if i < m then true else v.testBit i))
        (1 + m)).2.2 r = false := by
      rw [tapeOf_bit]; simp [hv m (by omega)]
    rw [if_neg (by rw [hb]; simp)]
    simp only [Dir.move, min_eq_left hip, Option.toList_none, List.append_nil]
    rw [update_tapeOf' _ _ _ _ _ _ (by omega), max_eq_left (by omega)]
    have hX : Function.update (fun i => if i < m then true else v.testBit i) m true =
        fun i => if i < m + 1 then true else v.testBit i := by
      funext i
      by_cases h : i = m
      · subst h; simp
      · rw [Function.update_of_ne h]
        split_ifs <;> first | rfl | omega
    rw [hX]
    rfl


end Macros


/-! ## Simulation of goto instructions -/

section Sim

variable {code : List (GI K)} {N : ℕ} {w : Word} {B : ℕ}

/-- The machine configuration representing the goto state `(pc, σ)` with allocated region
`1 … A`. -/
def cfgOf (code : List (GI K)) (N pc : ℕ) (σ : St K) (A : ℕ) : (machine code N).Cfg :=
  ⟨(clampPc N pc, .bnd), σ.pos, encTape A σ.reg, 0, σ.out⟩

lemma clampPc_val {N pc : ℕ} (h : pc ≤ N) : (clampPc N pc).val = pc := by
  simp [clampPc, h]

lemma haltQ_bnd {pcF : Fin (N + 1)} {ins : GI K} (hi : code.getD pcF.val .halt = ins)
    (hne : ins ≠ .halt) : haltQ code N (pcF, .bnd) = false := by
  simp only [haltQ, hi]; cases ins <;> simp_all

lemma encTape_mark (A : ℕ) (ρ : Fin K → ℕ) : (encTape A ρ 0).1 = true := rfl

lemma encTape_mark_pos (A : ℕ) (ρ : Fin K → ℕ) (i : ℕ) (hi : 1 ≤ i) :
    (encTape A ρ i).1 = false := tapeOf_mark_false _ _ _ hi

lemma lt_two_pow_of_bits {x n : ℕ} (h : ∀ i, n ≤ i → x.testBit i = false) : x < 2 ^ n :=
  Nat.lt_pow_two_of_testBit x (fun i hi => h i hi)

/-- Simulation of an increment. -/
lemma sim_inc (pc : ℕ) (hpc : pc ≤ N) (σ : St K) (r : Fin K) (hi : code.getD pc .halt = .inc r)
    (A : ℕ) (hA : A ≤ Nat.size B) (hρ : ∀ r, σ.reg r < 2 ^ A) (hpos : σ.pos ≤ w.length + 1)
    (hB : σ.reg r + 1 ≤ B) :
    ∃ A', A' ≤ Nat.size B ∧ (∀ r', (σ.setReg r (σ.reg r + 1)).reg r' < 2 ^ A') ∧
      Reach (machine code N) w (Pb code N (Nat.size B + 1)) (cfgOf code N pc σ A)
        (cfgOf code N (pc + 1) (σ.setReg r (σ.reg r + 1)) A') := by
  set v := σ.reg r with hv
  have hiF : code.getD (clampPc N pc).val .halt = .inc r := by rw [clampPc_val hpc]; exact hi
  have hex : ∃ j, v.testBit j = false := ⟨A, Nat.testBit_eq_false_of_lt (hρ r)⟩
  classical
  set j := Nat.find hex with hj
  have h0 : v.testBit j = false := Nat.find_spec hex
  have h1 : ∀ i < j, v.testBit i = true := fun i hi => by
    have := Nat.find_min hex hi; simpa using this
  have hjA : j ≤ A := Nat.find_min' hex (Nat.testBit_eq_false_of_lt (hρ r))
  have hsucc := testBit_succ_of_trailing v j h1 h0
  have hjB : j + 1 ≤ Nat.size B ∨ j < A := by
    rcases Nat.lt_or_ge j A with h | h
    · exact Or.inr h
    · left
      have : 2 ^ j ≤ v + 1 := Nat.ge_two_pow_of_testBit (by rw [hsucc]; simp)
      have := Nat.lt_size.2 (le_trans this hB); omega
  refine ⟨max A (1 + j), by omega, fun r' => ?_, ?_⟩
  · by_cases hr : r' = r
    · rw [hr]
      simp only [St.setReg_reg, Function.update_self]
      apply lt_two_pow_of_bits
      intro i hi
      rw [hsucc, if_neg (by omega), if_neg (by omega)]
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hρ r)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    · simp only [St.setReg_reg, Function.update_of_ne hr]
      exact lt_of_lt_of_le (hρ r') (Nat.pow_le_pow_right (by norm_num) (by omega))
  · -- step into the carry phase
    refine Reach.head (c' := ⟨(clampPc N pc, .carry), σ.pos, encTape A σ.reg, 1, σ.out⟩) ?_
      (by simp [cfgOf, Pb]) ?_
    · rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
      simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
        Option.toList_none, List.append_nil]
    rw [encTape_eq A σ.reg r]
    refine (reach_carry _ r hiF σ.pos hpos σ.out A _ v j hjA (by omega) h1).trans ?_
    -- the final carry step
    refine Reach.head (c' := ⟨(clampPc N (pc + 1), .ret), σ.pos,
      encTape (max A (1 + j)) (σ.setReg r (v + 1)).reg, j, σ.out⟩) ?_ (by simp [Pb]; omega) ?_
    · rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)),
        delta_carry _ _ hiF]
      have hb : (tapeOf A (Function.update (fun r i => (σ.reg r).testBit i) r
          (fun i => if i < j then false else v.testBit i)) (1 + j)).2.2 r = false := by
        rw [tapeOf_bit]; simp [h0]
      rw [if_neg (by rw [hb]; simp)]
      simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil]
      rw [update_tapeOf' _ _ _ _ _ _ hjA, St.setReg_reg, encTape_update, clampPc_val hpc]
      have hX : Function.update (fun i => if i < j then false else v.testBit i) j true =
          fun i => (v + 1).testBit i := by
        funext i; rw [hsucc]
        by_cases h : i = j
        · subst h; simp
        · rw [Function.update_of_ne h]; simp [h]
      rw [hX]
      (congr 1; omega)
    · exact reach_ret _ σ.pos hpos _ σ.out (encTape_mark _ _) j (by omega)
        (fun i h1 _ => encTape_mark_pos _ _ i h1)

/-- Simulation of a jump on zero. -/
lemma sim_jz (pc : ℕ) (hpc : pc ≤ N) (σ : St K) (r : Fin K) (t : ℕ)
    (hi : code.getD pc .halt = .jz r t)
    (A : ℕ) (hA : A ≤ Nat.size B) (hρ : ∀ r, σ.reg r < 2 ^ A) (hpos : σ.pos ≤ w.length + 1) :
    Reach (machine code N) w (Pb code N (Nat.size B + 1)) (cfgOf code N pc σ A)
        (cfgOf code N (if σ.reg r = 0 then t else pc + 1) σ A) := by
  set v := σ.reg r with hv
  have hiF : code.getD (clampPc N pc).val .halt = .jz r t := by rw [clampPc_val hpc]; exact hi
  refine Reach.head (c' := ⟨(clampPc N pc, .zsJ), σ.pos, encTape A σ.reg, 1, σ.out⟩) ?_
    (by simp [cfgOf, Pb]) ?_
  · rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  by_cases hv0 : v = 0
  · rw [if_pos hv0]
    refine (reach_zsJ _ r t hiF σ.pos hpos σ.out A _ A le_rfl (by omega)
      (fun i _ => by simp [← hv, hv0])).trans ?_
    refine Reach.head (c' := ⟨(clampPc N t, .ret), σ.pos, encTape A σ.reg, A, σ.out⟩) ?_
      (by simp [Pb]; omega) ?_
    · rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)),
        delta_zsJ _ _ hiF]
      have := tapeOf_unalloc (K := K) A (fun r i => (σ.reg r).testBit i)
      rw [if_pos this]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil]
      (congr 1; omega)
    · exact reach_ret _ σ.pos hpos _ σ.out (encTape_mark _ _) A (by omega)
        (fun i h1 _ => encTape_mark_pos _ _ i h1)
  · rw [if_neg hv0]
    classical
    have hex : ∃ j, v.testBit j = true := Nat.exists_testBit_of_ne_zero hv0
    set j := Nat.find hex with hj
    have h0 : v.testBit j = true := Nat.find_spec hex
    have h1 : ∀ i < j, v.testBit i = false := fun i hi => by
      have := Nat.find_min hex hi; simpa using this
    have hjA : j < A := by
      by_contra hc
      have := Nat.ge_two_pow_of_testBit h0
      have := hρ r
      have : 2 ^ A ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine (reach_zsJ _ r t hiF σ.pos hpos σ.out A _ j hjA.le (by omega) h1).trans ?_
    refine Reach.head (c' := ⟨(clampPc N (pc + 1), .ret), σ.pos, encTape A σ.reg, j, σ.out⟩) ?_
      (by simp [Pb]; omega) ?_
    · rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)),
        delta_zsJ _ _ hiF]
      have ha := tapeOf_alloc (K := K) A (fun r i => (σ.reg r).testBit i) j hjA
      have hb : (tapeOf A (fun r i => (σ.reg r).testBit i) (1 + j)).2.2 r = true := by
        rw [tapeOf_bit]; exact h0
      rw [if_neg (by rw [ha]; simp), if_pos hb]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil, clampPc_val hpc]
      (congr 1; omega)
    · exact reach_ret _ σ.pos hpos _ σ.out (encTape_mark _ _) j (by omega)
        (fun i h1 _ => encTape_mark_pos _ _ i h1)

/-- Simulation of a decrement. -/
lemma sim_dec (pc : ℕ) (hpc : pc ≤ N) (σ : St K) (r : Fin K)
    (hi : code.getD pc .halt = .dec r)
    (A : ℕ) (hA : A ≤ Nat.size B) (hρ : ∀ r, σ.reg r < 2 ^ A) (hpos : σ.pos ≤ w.length + 1) :
    (∀ r', (σ.setReg r (σ.reg r - 1)).reg r' < 2 ^ A) ∧
    Reach (machine code N) w (Pb code N (Nat.size B + 1)) (cfgOf code N pc σ A)
        (cfgOf code N (pc + 1) (σ.setReg r (σ.reg r - 1)) A) := by
  set v := σ.reg r with hv
  have hiF : code.getD (clampPc N pc).val .halt = .dec r := by rw [clampPc_val hpc]; exact hi
  refine ⟨fun r' => ?_, ?_⟩
  · by_cases hr : r' = r
    · subst hr; simp only [St.setReg_reg, Function.update_self]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (hρ _)
    · simp only [St.setReg_reg, Function.update_of_ne hr]; exact hρ r'
  refine Reach.head (c' := ⟨(clampPc N pc, .zsD), σ.pos, encTape A σ.reg, 1, σ.out⟩) ?_
    (by simp [cfgOf, Pb]) ?_
  · rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  by_cases hv0 : v = 0
  · have hσ : σ.setReg r (σ.reg r - 1) = σ := by
      have : σ.reg r - 1 = σ.reg r := by omega
      rw [this]; cases σ; simp [St.setReg]
    rw [hσ]
    refine (reach_zsD _ r hiF σ.pos hpos σ.out A _ A le_rfl (by omega)
      (fun i _ => by simp [← hv, hv0])).trans ?_
    refine Reach.head (c' := ⟨(clampPc N (pc + 1), .ret), σ.pos, encTape A σ.reg, A, σ.out⟩) ?_
      (by simp [Pb]; omega) ?_
    · rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)),
        delta_zsD _ _ hiF]
      have := tapeOf_unalloc (K := K) A (fun r i => (σ.reg r).testBit i)
      rw [if_pos this]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil, clampPc_val hpc]
      (congr 1; omega)
    · exact reach_ret _ σ.pos hpos _ σ.out (encTape_mark _ _) A (by omega)
        (fun i h1 _ => encTape_mark_pos _ _ i h1)
  · classical
    have hex : ∃ j, v.testBit j = true := Nat.exists_testBit_of_ne_zero hv0
    set j := Nat.find hex with hj
    have h0 : v.testBit j = true := Nat.find_spec hex
    have h1 : ∀ i < j, v.testBit i = false := fun i hi => by
      have := Nat.find_min hex hi; simpa using this
    have hjA : j < A := by
      by_contra hc
      have := Nat.ge_two_pow_of_testBit h0
      have := hρ r
      have : 2 ^ A ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hpred := testBit_pred_of_trailing v j h1 h0
    refine (reach_zsD _ r hiF σ.pos hpos σ.out A _ j hjA.le (by omega) h1).trans ?_
    refine Reach.head (c' := ⟨(clampPc N pc, .retB), σ.pos, encTape A σ.reg, j, σ.out⟩) ?_
      (by simp [Pb]; omega) ?_
    · rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)),
        delta_zsD _ _ hiF]
      have ha := tapeOf_alloc (K := K) A (fun r i => (σ.reg r).testBit i) j hjA
      have hb : (tapeOf A (fun r i => (σ.reg r).testBit i) (1 + j)).2.2 r = true := by
        rw [tapeOf_bit]; exact h0
      rw [if_neg (by rw [ha]; simp), if_pos hb]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil]
      (congr 1; omega)
    refine (reach_retB _ σ.pos hpos _ σ.out (encTape_mark _ _) (by omega) j (by omega)
        (fun i h1 _ => encTape_mark_pos _ _ i h1)).trans ?_
    rw [encTape_eq A σ.reg r]
    refine (reach_borrow _ r hiF σ.pos hpos σ.out A _ v j hjA.le (by omega) h1).trans ?_
    refine Reach.head (c' := ⟨(clampPc N (pc + 1), .ret), σ.pos,
      encTape A (σ.setReg r (v - 1)).reg, j, σ.out⟩) ?_ (by simp [Pb]; omega) ?_
    · rw [machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)),
        delta_borrow _ _ hiF]
      have hb : (tapeOf A (Function.update (fun r i => (σ.reg r).testBit i) r
          (fun i => if i < j then true else v.testBit i)) (1 + j)).2.2 r = true := by
        rw [tapeOf_bit]; simp [h0]
      rw [if_pos hb]
      simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil]
      rw [update_tapeOf' _ _ _ _ _ _ hjA.le, max_eq_left (by omega), St.setReg_reg,
        encTape_update, clampPc_val hpc]
      have hX : Function.update (fun i => if i < j then true else v.testBit i) j false =
          fun i => (v - 1).testBit i := by
        funext i; rw [hpred]
        by_cases h : i = j
        · subst h; simp
        · rw [Function.update_of_ne h]; simp [h]
      rw [hX]
      (congr 1; omega)
    · exact reach_ret _ σ.pos hpos _ σ.out (encTape_mark _ _) j (by omega)
        (fun i h1 _ => encTape_mark_pos _ _ i h1)

end Sim


section Run

variable {code : List (GI K)} {N : ℕ} {w : Word} {B : ℕ}

/-- Simulation of a single goto step. -/
lemma sim_step (a : ℕ × St K) (ha : a.1 ≤ N) (A : ℕ)
    (hA : A ≤ Nat.size B) (hρ : ∀ r, a.2.reg r < 2 ^ A) (hg : Good w B a.2)
    (hg' : Good w B (gstep code w a).2) :
    ∃ A', A' ≤ Nat.size B ∧ (∀ r, (gstep code w a).2.reg r < 2 ^ A') ∧
      Reach (machine code N) w (Pb code N (Nat.size B + 1)) (cfgOf code N a.1 a.2 A)
        (cfgOf code N (gstep code w a).1 (gstep code w a).2 A') := by
  obtain ⟨pc, σ⟩ := a
  simp only at ha hρ hg hg' ⊢
  have hpos := hg.1
  unfold gstep at hg' ⊢
  simp only at hg' ⊢
  cases hi : code.getD pc .halt with
  | inc r =>
    rw [hi] at hg'
    simp only [gexec] at hg' ⊢
    have := hg'.2 r
    simp only [St.setReg_reg, Function.update_self] at this
    exact sim_inc pc ha σ r hi A hA hρ hpos this
  | dec r =>
    simp only [gexec]
    exact ⟨A, hA, (sim_dec pc ha σ r hi A hA hρ hpos).1, (sim_dec pc ha σ r hi A hA hρ hpos).2⟩
  | jz r t =>
    simp only [gexec]
    exact ⟨A, hA, hρ, sim_jz pc ha σ r t hi A hA hρ hpos⟩
  | halt =>
    simp only [gexec]
    exact ⟨A, hA, hρ, Reach.refl (by simp [cfgOf, Pb])⟩
  | jsym s t =>
    have hiF : code.getD (clampPc N pc).val .halt = .jsym s t := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hρ, Reach.single ?_ (by simp [cfgOf, Pb]) (by simp [cfgOf, Pb])⟩
    rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, gexec, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf, clampPc_val ha]
    split_ifs <;> rfl
  | left =>
    have hiF : code.getD (clampPc N pc).val .halt = .left := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hρ, Reach.single ?_ (by simp [cfgOf, Pb]) (by simp [cfgOf, Pb])⟩
    rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, gexec, Dir.move, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf, clampPc_val ha]
    rw [min_eq_left (by omega)]
  | right =>
    have hiF : code.getD (clampPc N pc).val .halt = .right := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hρ, Reach.single ?_ (by simp [cfgOf, Pb]) (by simp [cfgOf, Pb])⟩
    rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, gexec, Dir.move, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf, clampPc_val ha]
  | out b =>
    have hiF : code.getD (clampPc N pc).val .halt = .out b := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hρ, Reach.single ?_ (by simp [cfgOf, Pb]) (by simp [cfgOf, Pb])⟩
    rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hi, gexec, Dir.move, min_eq_left hpos, Function.update_eq_self,
      cfgOf, clampPc_val ha]
    rfl
  | jmp t =>
    have hiF : code.getD (clampPc N pc).val .halt = .jmp t := by rw [clampPc_val ha]; exact hi
    refine ⟨A, hA, hρ, Reach.single ?_ (by simp [cfgOf, Pb]) (by simp [cfgOf, Pb])⟩
    rw [cfgOf, machine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, gexec, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil, cfgOf]

/-- Simulation of a run of a goto program. -/
lemma sim_gsteps
    (hinv : ∀ a : ℕ × St K, a.1 ≤ N → (gstep code w a).1 ≤ N)
    {a b : ℕ × St K} (h : GSteps code w B a b) (ha : a.1 ≤ N) (A : ℕ)
    (hA : A ≤ Nat.size B) (hρ : ∀ r, a.2.reg r < 2 ^ A) (hg : Good w B a.2) :
    ∃ A', A' ≤ Nat.size B ∧ (∀ r, b.2.reg r < 2 ^ A') ∧ b.1 ≤ N ∧ Good w B b.2 ∧
      Reach (machine code N) w (Pb code N (Nat.size B + 1)) (cfgOf code N a.1 a.2 A)
        (cfgOf code N b.1 b.2 A') := by
  induction h with
  | refl => exact ⟨A, hA, hρ, ha, hg, Reach.refl (by simp [cfgOf, Pb])⟩
  | tail _ hst ih =>
    obtain ⟨A₁, hA₁, hρ₁, hb₁, hg₁, hr₁⟩ := ih
    obtain ⟨hst, hgc⟩ := hst
    subst hst
    obtain ⟨A₂, hA₂, hρ₂, hr₂⟩ := sim_step _ hb₁ A₁ hA₁ hρ₁ hg₁ hgc
    exact ⟨A₂, hA₂, hρ₂, hinv _ hb₁, hgc, hr₁.trans hr₂⟩

end Run

/-! ## Main theorem -/

lemma iterate_halted (M : TM) (w : Word) (c : M.Cfg) (h : M.halt c.state = true) (n : ℕ) :
    (M.step w)^[n] c = c :=
  Function.iterate_fixed (by simp [TM.step, h]) n

/-- **Programs with logarithmically bounded registers compute logspace functions.**
If, for every input `w`, the program `P` terminates with output `f w` while all its
registers stay `≤ B w`, where `B w < 2 ^ (d (⌊log₂ |w|⌋ + 1))`, then `f` is computable
in logarithmic space (by the Turing machine `machine P.code (clen P)`). -/
theorem logspaceComputable_of_prog {K : ℕ} (P : Stmt K) (f : Word → Word) (B : Word → ℕ)
    (d : ℕ) (hB : ∀ w, B w < 2 ^ (d * (Nat.log 2 w.length + 1)))
    (hP : ∀ w, ∃ σ', Eval w (B w) P (St.init K) σ' ∧ σ'.out = f w) :
    LogspaceComputable f := by
  have hN : P.code.getD (clen P) .halt = .halt := code_halt P
  have hinv : ∀ (w : Word) (a : ℕ × St K), a.1 ≤ clen P → (gstep P.code w a).1 ≤ clen P :=
    fun w a ha => gstep_pc_le P w a ha
  -- the main simulation, for each input
  have key : ∀ w, ∃ T, (machine P.code (clen P)).HaltsWith w T (f w) ∧
      ∀ t, ((machine P.code (clen P)).run w t).workPos ≤ Nat.size (B w) + 1 := by
    intro w
    obtain ⟨σ', hev, hout⟩ := hP w
    have hg0 : Good w (B w) (St.init K) := ⟨by simp [St.init], fun r => by simp [St.init]⟩
    have hrun := code_sim hev hg0
    obtain ⟨A', -, -, -, -, hreach⟩ := sim_gsteps (hinv w) hrun (by simp) 0 (by simp)
      (by simp [St.init]) hg0
    have hinit0 : (machine P.code (clen P)).init =
        ⟨((0 : Fin (clen P + 1)), Ph.init), 0, fun _ => blankCell, 0, []⟩ := rfl
    have hinit : (machine P.code (clen P)).step w (machine P.code (clen P)).init =
        cfgOf P.code (clen P) 0 (St.init K) 0 := by
      rw [hinit0, machine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)),
        delta_init]
      simp only [Dir.move, min_eq_left (Nat.zero_le _), Option.toList_none, List.append_nil,
        cfgOf, St.init]
      congr 1
      funext p
      by_cases hp : p = 0
      · subst hp; simp [encTape, tapeOf]
      · rw [Function.update_of_ne hp]
        simp [encTape, tapeOf, hp, blankCell]
    have hreach' := Reach.head hinit (by rw [hinit0]; simp [Pb]) hreach
    obtain ⟨T, hT, hTb⟩ := hreach'
    have hhalt : (machine P.code (clen P)).halt ((machine P.code (clen P)).run w T).state =
        true := by
      rw [TM.run, hT]
      show haltQ P.code (clen P) (clampPc (clen P) (clen P), Ph.bnd) = true
      simp only [haltQ, clampPc_val le_rfl, hN]
    refine ⟨T, ⟨hhalt, by rw [TM.run, hT]; simp [cfgOf, hout]⟩, fun t => ?_⟩
    rcases Nat.lt_or_ge T t with h | h
    · obtain ⟨k, rfl⟩ : ∃ k, t = k + T := ⟨t - T, by omega⟩
      rw [TM.run, Function.iterate_add_apply, ← TM.run, iterate_halted _ w _ hhalt]
      exact hTb T le_rfl
    · exact hTb t h
  refine ⟨machine P.code (clen P), d + 1, fun w => ?_, fun w t => ?_⟩
  · obtain ⟨T, hT, -⟩ := key w
    exact ⟨T, hT⟩
  · obtain ⟨T, -, hb⟩ := key w
    have h1 := hb t
    have h2 : Nat.size (B w) ≤ d * (Nat.log 2 w.length + 1) := Nat.size_le.2 (hB w)
    nlinarith

end LS

end PathChecking
