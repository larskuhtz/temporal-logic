module

public import RequestProject.PTime.Prog
public import RequestProject.Logspace.Machine

/-!
# Compiling goto programs with memory into Turing machines, with time bounds

The work tape has `K + 4` tracks: the left-end marker, the "allocated" flag, one track per
register (in binary, least significant bit first), a *cursor* track (cells `1 … cur` are
marked, so the cursor is the first unmarked cell) and the *memory* track.  We reuse the tape
layout `LS.tapeOf` with `K + 2` register-like tracks.

Every goto instruction is simulated by a macro that starts and ends on the marker and takes at
most `4 A + 5` steps, where `A` is the size of the allocated region.
-/

@[expose] public section

namespace PathChecking

namespace PT

open LS

/-! ## Reachability with a time bound -/

/-- `c'` is reachable from `c` in at most `n` steps. -/
def RB (M : TM) (w : Word) (n : ℕ) (c c' : M.Cfg) : Prop :=
  ∃ t ≤ n, (M.step w)^[t] c = c'

namespace RB

variable {M : TM} {w : Word}

lemma refl (c : M.Cfg) : RB M w 0 c c := ⟨0, le_rfl, rfl⟩

lemma mono {n m : ℕ} {c c' : M.Cfg} (h : RB M w n c c') (hm : n ≤ m) : RB M w m c c' := by
  obtain ⟨t, ht, e⟩ := h; exact ⟨t, by omega, e⟩

lemma trans {n m : ℕ} {c₁ c₂ c₃ : M.Cfg} (h₁ : RB M w n c₁ c₂) (h₂ : RB M w m c₂ c₃) :
    RB M w (n + m) c₁ c₃ := by
  obtain ⟨t₁, h1, e₁⟩ := h₁
  obtain ⟨t₂, h2, e₂⟩ := h₂
  exact ⟨t₂ + t₁, by omega, by rw [Function.iterate_add_apply, e₁, e₂]⟩

lemma single {c c' : M.Cfg} (h : M.step w c = c') : RB M w 1 c c' :=
  ⟨1, le_rfl, by simpa using h⟩

lemma head {n : ℕ} {c c' c'' : M.Cfg} (h : M.step w c = c') (h' : RB M w n c' c'') :
    RB M w (n + 1) c c'' := by
  have := (single h).trans h'
  exact this.mono (by omega)

end RB

/-! ## Tracks -/

variable {K : ℕ}

/-- Track of register `r`. -/
def trR (r : Fin K) : Fin (K + 2) := ⟨r.val, by omega⟩

/-- The cursor track. -/
def trP : Fin (K + 2) := ⟨K, by omega⟩

/-- The memory track. -/
def trM : Fin (K + 2) := ⟨K + 1, by omega⟩

lemma trR_ne_trP (r : Fin K) : trR r ≠ trP := by
  intro h; have := congrArg Fin.val h; simp [trR, trP] at this; omega

lemma trR_ne_trM (r : Fin K) : trR r ≠ trM := by
  intro h; have := congrArg Fin.val h; simp [trR, trM] at this; omega

lemma trP_ne_trM : (trP : Fin (K + 2)) ≠ trM := by
  intro h; have := congrArg Fin.val h; simp [trP, trM] at this

lemma trR_inj {r s : Fin K} (h : trR r = trR s) : r = s := by
  ext; have := congrArg Fin.val h; simpa [trR] using this

/-- Contents of the tracks for a program state. -/
def gOf (σ : PSt K) : Fin (K + 2) → ℕ → Bool := fun t i =>
  if h : t.val < K then (σ.base.reg ⟨t.val, h⟩).testBit i
  else if t.val = K then decide (i < σ.cur) else decide (i ∈ σ.mem)

lemma gOf_trR (σ : PSt K) (r : Fin K) : gOf σ (trR r) = fun i => (σ.base.reg r).testBit i := by
  funext i; simp [gOf, trR]

lemma gOf_trP (σ : PSt K) : gOf σ trP = fun i => decide (i < σ.cur) := by
  funext i; simp [gOf, trP]

lemma gOf_trM (σ : PSt K) : gOf σ trM = fun i => decide (i ∈ σ.mem) := by
  funext i; simp [gOf, trM]

lemma gOf_eq_update (σ : PSt K) (t : Fin (K + 2)) :
    gOf σ = Function.update (gOf σ) t (gOf σ t) := by simp

lemma gOf_setReg (σ : PSt K) (r : Fin K) (v : ℕ) :
    gOf { σ with base := σ.base.setReg r v } =
      Function.update (gOf σ) (trR r) (fun i => v.testBit i) := by
  funext t i
  by_cases ht : t = trR r
  · subst ht; simp [gOf, trR]
  · rw [Function.update_of_ne ht]
    simp only [gOf]
    split_ifs with h1
    · have : (⟨t.val, h1⟩ : Fin K) ≠ r := fun h => ht (by ext; simp [trR, ← h])
      simp [St.setReg, Function.update_of_ne this]
    · rfl
    · rfl

lemma gOf_cur (σ : PSt K) (c : ℕ) :
    gOf { σ with cur := c } = Function.update (gOf σ) trP (fun i => decide (i < c)) := by
  funext t i
  by_cases ht : t = trP
  · subst ht; simp [gOf, trP]
  · rw [Function.update_of_ne ht]
    simp only [gOf]
    split_ifs with h1 h2
    · rfl
    · exact absurd (Fin.ext (by simpa [trP] using h2)) ht
    · rfl

lemma gOf_mem (σ : PSt K) (m : Finset ℕ) :
    gOf { σ with mem := m } = Function.update (gOf σ) trM (fun i => decide (i ∈ m)) := by
  funext t i
  by_cases ht : t = trM
  · subst ht; simp [gOf, trM]
  · rw [Function.update_of_ne ht]
    simp only [gOf]
    split_ifs with h1 h2
    · rfl
    · rfl
    · exact absurd (Fin.ext (by simp [trM]; omega)) ht

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
  | crS
  | clS
  | clB
  | msS
  | jmS
  deriving DecidableEq, Fintype

/-- States: program counter and phase. -/
abbrev MQ (N : ℕ) := Fin (N + 1) × Ph

/-- Transition function. -/
def delta (code : List (PGI K)) (N : ℕ) (q : MQ N) (i : InSym) (c : Cell (K + 2)) :
    MQ N × Cell (K + 2) × Dir × Dir × Option Bool :=
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
  | .bnd, .cr => ((q.1, .crS), c, .right, .stay, none)
  | .bnd, .cl => ((q.1, .clS), c, .right, .stay, none)
  | .bnd, .mset => ((q.1, .msS), c, .right, .stay, none)
  | .bnd, .jm _ => ((q.1, .jmS), c, .right, .stay, none)
  | .carry, .inc r =>
      if c.2.2 (trR r) then ((q.1, .carry), setBit c (trR r) false, .right, .stay, none)
      else ((clampPc N (q.1.val + 1), .ret), setBit c (trR r) true, .left, .stay, none)
  | .zsJ, .jz r t =>
      if c.2.1 = false then ((clampPc N t, .ret), c, .left, .stay, none)
      else if c.2.2 (trR r) then ((clampPc N (q.1.val + 1), .ret), c, .left, .stay, none)
      else ((q.1, .zsJ), c, .right, .stay, none)
  | .zsD, .dec r =>
      if c.2.1 = false then ((clampPc N (q.1.val + 1), .ret), c, .left, .stay, none)
      else if c.2.2 (trR r) then ((q.1, .retB), c, .left, .stay, none)
      else ((q.1, .zsD), c, .right, .stay, none)
  | .retB, _ =>
      if c.1 then ((q.1, .borrow), c, .right, .stay, none)
      else ((q.1, .retB), c, .left, .stay, none)
  | .borrow, .dec r =>
      if c.2.2 (trR r) then
        ((clampPc N (q.1.val + 1), .ret), setBit c (trR r) false, .left, .stay, none)
      else ((q.1, .borrow), setBit c (trR r) true, .right, .stay, none)
  | .ret, _ =>
      if c.1 then ((q.1, .bnd), c, .stay, .stay, none)
      else ((q.1, .ret), c, .left, .stay, none)
  | .crS, .cr =>
      if c.2.2 trP then ((q.1, .crS), c, .right, .stay, none)
      else ((clampPc N (q.1.val + 1), .ret), setBit c trP true, .left, .stay, none)
  | .msS, .mset =>
      if c.2.2 trP then ((q.1, .msS), c, .right, .stay, none)
      else ((clampPc N (q.1.val + 1), .ret), setBit c trM true, .left, .stay, none)
  | .jmS, .jm t =>
      if c.2.2 trP then ((q.1, .jmS), c, .right, .stay, none)
      else ((if c.2.2 trM then clampPc N t else clampPc N (q.1.val + 1), .ret), c, .left,
        .stay, none)
  | .clS, .cl =>
      if c.2.2 trP then ((q.1, .clS), c, .right, .stay, none)
      else ((q.1, .clB), c, .left, .stay, none)
  | .clB, .cl =>
      if c.1 then ((clampPc N (q.1.val + 1), .bnd), c, .stay, .stay, none)
      else ((clampPc N (q.1.val + 1), .ret), setBit c trP false, .left, .stay, none)
  | _, _ => (q, c, .stay, .stay, none)

/-- Halting states: boundary phase at a `halt` instruction. -/
def haltQ (code : List (PGI K)) (N : ℕ) (q : MQ N) : Bool :=
  match q.2, code.getD q.1.val .halt with
  | .bnd, .halt => true
  | _, _ => false

/-- The Turing machine simulating a goto program with memory. -/
def pmachine (code : List (PGI K)) (N : ℕ) : TM where
  Q := MQ N
  Γ := Cell (K + 2)
  blank := blankCell
  start := (0, .init)
  halt := haltQ code N
  δ := delta code N

lemma pmachine_step (code : List (PGI K)) (N : ℕ) (w : Word) (q : MQ N) (ip : ℕ)
    (T : ℕ → Cell (K + 2)) (wp : ℕ) (o : List Bool) (hq : haltQ code N q = false) :
    (pmachine code N).step w ⟨q, ip, T, wp, o⟩ =
      ⟨(delta code N q (inputSym w ip) (T wp)).1,
        min ((delta code N q (inputSym w ip) (T wp)).2.2.2.1.move ip) (w.length + 1),
        Function.update T wp (delta code N q (inputSym w ip) (T wp)).2.1,
        (delta code N q (inputSym w ip) (T wp)).2.2.1.move wp,
        o ++ (delta code N q (inputSym w ip) (T wp)).2.2.2.2.toList⟩ := by
  simp only [TM.step, pmachine, hq]
  rfl

lemma haltQ_of_ne_bnd (code : List (PGI K)) (N : ℕ) (pc : Fin (N + 1)) (ph : Ph)
    (h : ph ≠ .bnd) : haltQ code N (pc, ph) = false := by
  cases ph <;> simp_all [haltQ]

section Delta

variable (code : List (PGI K)) (N : ℕ) (pc : Fin (N + 1)) (i : InSym) (c : Cell (K + 2))

lemma delta_ret : delta code N (pc, .ret) i c =
    if c.1 then ((pc, .bnd), c, .stay, .stay, none) else ((pc, .ret), c, .left, .stay, none) := by
  cases code.getD pc.val .halt <;> simp only [delta]

lemma delta_retB : delta code N (pc, .retB) i c =
    if c.1 then ((pc, .borrow), c, .right, .stay, none)
    else ((pc, .retB), c, .left, .stay, none) := by
  cases code.getD pc.val .halt <;> simp only [delta]

lemma delta_init : delta code N (pc, .init) i c = ((pc, .bnd), markCell, .stay, .stay, none) := by
  cases code.getD pc.val .halt <;> simp only [delta]

end Delta

/-! ## The macros -/

section Macros

variable {code : List (PGI K)} {N : ℕ} {w : Word}

lemma reach_ret (pc : Fin (N + 1)) (ip : ℕ) (hip : ip ≤ w.length + 1) (T : ℕ → Cell (K + 2))
    (o : List Bool) (hT0 : (T 0).1 = true) :
    ∀ p, (∀ i, 1 ≤ i → i ≤ p → (T i).1 = false) →
      RB (pmachine code N) w (p + 1) ⟨(pc, .ret), ip, T, p, o⟩ ⟨(pc, .bnd), ip, T, 0, o⟩ := by
  intro p
  induction p with
  | zero =>
    intro _
    apply RB.single
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_ret]
    simp [hT0, Dir.move, hip]
  | succ p ih =>
    intro hT
    refine RB.head ?_ (ih (fun i h1 h2 => hT i h1 (by omega)))
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_ret]
    simp [hT (p + 1) (by omega) le_rfl, Dir.move, hip]

lemma reach_retB (pc : Fin (N + 1)) (ip : ℕ) (hip : ip ≤ w.length + 1) (T : ℕ → Cell (K + 2))
    (o : List Bool) (hT0 : (T 0).1 = true) :
    ∀ p, (∀ i, 1 ≤ i → i ≤ p → (T i).1 = false) →
      RB (pmachine code N) w (p + 1) ⟨(pc, .retB), ip, T, p, o⟩
        ⟨(pc, .borrow), ip, T, 1, o⟩ := by
  intro p
  induction p with
  | zero =>
    intro _
    apply RB.single
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_retB]
    simp [hT0, Dir.move, hip]
  | succ p ih =>
    intro hT
    refine RB.head ?_ (ih (fun i h1 h2 => hT i h1 (by omega)))
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide)), delta_retB]
    simp [hT (p + 1) (by omega) le_rfl, Dir.move, hip]

/-- A generic right scan that leaves the tape unchanged while a predicate holds. -/
lemma reach_scan (pc : Fin (N + 1)) (ph : Ph) (hph : ph ≠ .bnd) (Pc : Cell (K + 2) → Prop)
    (hδ : ∀ i c, Pc c → delta code N (pc, ph) i c = ((pc, ph), c, .right, .stay, none))
    (ip : ℕ) (hip : ip ≤ w.length + 1) (o : List Bool) (T : ℕ → Cell (K + 2)) :
    ∀ m, (∀ i < m, Pc (T (1 + i))) →
      RB (pmachine code N) w m ⟨(pc, ph), ip, T, 1, o⟩ ⟨(pc, ph), ip, T, 1 + m, o⟩ := by
  intro m
  induction m with
  | zero => intro _; exact RB.refl _
  | succ m ih =>
    intro hP
    refine (ih (fun i hi => hP i (by omega))).trans (RB.single ?_)
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ hph), hδ _ _ (hP m (by omega))]
    simp only [Dir.move, min_eq_left hip, Function.update_eq_self, Option.toList_none,
      List.append_nil]
    rfl

/-- The carry loop of an increment. -/
lemma reach_carry (pc : Fin (N + 1)) (r : Fin K) (hins : code.getD pc.val .halt = .inc r)
    (ip : ℕ) (hip : ip ≤ w.length + 1) (o : List Bool) (A : ℕ) (g : Fin (K + 2) → ℕ → Bool)
    (v : ℕ) :
    ∀ m, m ≤ A → (∀ i < m, v.testBit i = true) →
      RB (pmachine code N) w m
        ⟨(pc, .carry), ip, tapeOf A (Function.update g (trR r) (fun i => v.testBit i)), 1, o⟩
        ⟨(pc, .carry), ip, tapeOf A (Function.update g (trR r)
          (fun i => if i < m then false else v.testBit i)), 1 + m, o⟩ := by
  intro m
  induction m with
  | zero => intro _ _; simp only [Nat.not_lt_zero, if_false]; exact RB.refl _
  | succ m ih =>
    intro hm hv
    refine (ih (by omega) (fun i hi => hv i (by omega))).trans (RB.single ?_)
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
    simp only [delta, hins]
    have hb : (tapeOf A (Function.update g (trR r) (fun i => if i < m then false else v.testBit i))
        (1 + m)).2.2 (trR r) = true := by
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
    (ip : ℕ) (hip : ip ≤ w.length + 1) (o : List Bool) (A : ℕ) (g : Fin (K + 2) → ℕ → Bool)
    (v : ℕ) :
    ∀ m, m ≤ A → (∀ i < m, v.testBit i = false) →
      RB (pmachine code N) w m
        ⟨(pc, .borrow), ip, tapeOf A (Function.update g (trR r) (fun i => v.testBit i)), 1, o⟩
        ⟨(pc, .borrow), ip, tapeOf A (Function.update g (trR r)
          (fun i => if i < m then true else v.testBit i)), 1 + m, o⟩ := by
  intro m
  induction m with
  | zero => intro _ _; simp only [Nat.not_lt_zero, if_false]; exact RB.refl _
  | succ m ih =>
    intro hm hv
    refine (ih (by omega) (fun i hi => hv i (by omega))).trans (RB.single ?_)
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
    simp only [delta, hins]
    have hb : (tapeOf A (Function.update g (trR r) (fun i => if i < m then true else v.testBit i))
        (1 + m)).2.2 (trR r) = false := by
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

end PT

end PathChecking
