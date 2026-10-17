module

public import RequestProject.PTime.Machine

/-!
# Simulation of goto instructions by the machine, with time bounds

Each goto instruction is simulated in at most `4 A + 5` machine steps, where `A` is the size of
the allocated region of the work tape (`A ≤ B + 1` throughout).
-/

@[expose] public section

namespace PathChecking

namespace PT

open LS

variable {K : ℕ}

/-- The tape invariant: all register values, the cursor and the memory fit into the allocated
region `1 … A`. -/
def Inv (A : ℕ) (σ : PSt K) : Prop :=
  (∀ r, σ.base.reg r < 2 ^ A) ∧ σ.cur ≤ A ∧ ∀ i ∈ σ.mem, i < A

/-- The machine configuration representing the goto state `(pc, σ)`. -/
def cfgOf (code : List (PGI K)) (N pc : ℕ) (σ : PSt K) (A : ℕ) : (pmachine code N).Cfg :=
  ⟨(clampPc N pc, .bnd), σ.base.pos, tapeOf A (gOf σ), 0, σ.base.out⟩

section Sim

variable {code : List (PGI K)} {N : ℕ} {w : Word} {B : ℕ}

lemma haltQ_bnd {pcF : Fin (N + 1)} {ins : PGI K} (hi : code.getD pcF.val .halt = ins)
    (hne : ins ≠ .halt) : haltQ code N (pcF, .bnd) = false := by
  simp only [haltQ, hi]; cases ins <;> simp_all

lemma tapeOf_mark0 (A : ℕ) (g : Fin (K + 2) → ℕ → Bool) : (tapeOf A g 0).1 = true := by
  rw [tapeOf_zero]; rfl

lemma Inv.mono {A A' : ℕ} {σ : PSt K} (h : Inv A σ) (hA : A ≤ A') : Inv A' σ := by
  refine ⟨fun r => lt_of_lt_of_le (h.1 r) (Nat.pow_le_pow_right (by norm_num) hA),
    by have := h.2.1; omega, fun i hi => by have := h.2.2 i hi; omega⟩

lemma tape_split (A : ℕ) (σ : PSt K) (t : Fin (K + 2)) :
    tapeOf A (gOf σ) = tapeOf A (Function.update (gOf σ) t (gOf σ t)) := by
  rw [Function.update_eq_self]

/-- Simulation of an increment. -/
lemma sim_inc (pc : ℕ) (hpc : pc ≤ N) (σ : PSt K) (r : Fin K)
    (hi : code.getD pc .halt = .inc r) (A : ℕ) (hInv : Inv A σ)
    (hpos : σ.base.pos ≤ w.length + 1) (hB : σ.base.reg r + 1 ≤ B) (hA : A ≤ B + 1) :
    ∃ A', A' ≤ B + 1 ∧ Inv A' { σ with base := σ.base.setReg r (σ.base.reg r + 1) } ∧
      RB (pmachine code N) w (4 * A + 5) (cfgOf code N pc σ A)
        (cfgOf code N (pc + 1) { σ with base := σ.base.setReg r (σ.base.reg r + 1) } A') := by
  set v := σ.base.reg r with hv
  have hiF : code.getD (clampPc N pc).val .halt = .inc r := by rw [clampPc_val hpc]; exact hi
  have hex : ∃ j, v.testBit j = false := ⟨A, Nat.testBit_eq_false_of_lt (hInv.1 r)⟩
  classical
  set j := Nat.find hex with hj
  have h0 : v.testBit j = false := Nat.find_spec hex
  have h1 : ∀ i < j, v.testBit i = true := fun i hi => by
    have := Nat.find_min hex hi; simpa using this
  have hjA : j ≤ A := Nat.find_min' hex (Nat.testBit_eq_false_of_lt (hInv.1 r))
  have hsucc := testBit_succ_of_trailing v j h1 h0
  have hjB : j + 1 ≤ B ∨ j < A := by
    rcases Nat.lt_or_ge j A with h | h
    · exact Or.inr h
    · left
      have : 2 ^ j ≤ v + 1 := Nat.ge_two_pow_of_testBit (by rw [hsucc]; simp)
      have := Nat.lt_two_pow_self (n := j)
      omega
  refine ⟨max A (1 + j), by omega, ⟨fun r' => ?_, by have := hInv.2.1; simp; omega,
    fun i hi => by have := hInv.2.2 i hi; omega⟩, ?_⟩
  · by_cases hr : r' = r
    · rw [hr]
      simp only [St.setReg_reg, Function.update_self]
      apply lt_two_pow_of_bits
      intro i hi
      rw [hsucc, if_neg (by omega), if_neg (by omega)]
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (hInv.1 r)
        (Nat.pow_le_pow_right (by norm_num) (by omega)))
    · simp only [St.setReg_reg, Function.update_of_ne hr]
      exact lt_of_lt_of_le (hInv.1 r') (Nat.pow_le_pow_right (by norm_num) (by omega))
  · have eT := tape_split A σ (trR r)
    rw [gOf_trR] at eT
    have hstep : (pmachine code N).step w (cfgOf code N pc σ A) =
        ⟨(clampPc N pc, .carry), σ.base.pos, tapeOf A (gOf σ), 1, σ.base.out⟩ := by
      rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
      simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
        Option.toList_none, List.append_nil]
    have hlast : (pmachine code N).step w ⟨(clampPc N pc, .carry), σ.base.pos,
        tapeOf A (Function.update (gOf σ) (trR r)
          (fun i => if i < j then false else v.testBit i)), 1 + j, σ.base.out⟩ =
        ⟨(clampPc N (pc + 1), .ret), σ.base.pos,
          tapeOf (max A (1 + j)) (gOf { σ with base := σ.base.setReg r (v + 1) }), j,
          σ.base.out⟩ := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF]
      have hb : (tapeOf A (Function.update (gOf σ) (trR r)
          (fun i => if i < j then false else v.testBit i)) (1 + j)).2.2 (trR r) = false := by
        rw [tapeOf_bit]; simp [h0]
      rw [if_neg (by rw [hb]; simp)]
      simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil]
      rw [update_tapeOf' _ _ _ _ _ _ hjA, gOf_setReg, clampPc_val hpc]
      have hX : Function.update (fun i => if i < j then false else v.testBit i) j true =
          fun i => (v + 1).testBit i := by
        funext i; rw [hsucc]
        by_cases h : i = j
        · subst h; simp
        · rw [Function.update_of_ne h]; simp [h]
      rw [hX]
      (congr 1; omega)
    have hrest := (reach_carry _ r hiF σ.base.pos hpos σ.base.out A _ v j hjA h1).trans
      (RB.head hlast (reach_ret _ σ.base.pos hpos _ σ.base.out (tapeOf_mark0 _ _) j
        (fun i h1 _ => tapeOf_mark_false _ _ i h1)))
    rw [← eT] at hrest
    exact (RB.head hstep hrest).mono (by omega)

/-- Simulation of a jump on zero. -/
lemma sim_jz (pc : ℕ) (hpc : pc ≤ N) (σ : PSt K) (r : Fin K) (t : ℕ)
    (hi : code.getD pc .halt = .jz r t) (A : ℕ) (hInv : Inv A σ)
    (hpos : σ.base.pos ≤ w.length + 1) :
    RB (pmachine code N) w (4 * A + 5) (cfgOf code N pc σ A)
        (cfgOf code N (if σ.base.reg r = 0 then t else pc + 1) σ A) := by
  set v := σ.base.reg r with hv
  have hiF : code.getD (clampPc N pc).val .halt = .jz r t := by rw [clampPc_val hpc]; exact hi
  have hstep : (pmachine code N).step w (cfgOf code N pc σ A) =
      ⟨(clampPc N pc, .zsJ), σ.base.pos, tapeOf A (gOf σ), 1, σ.base.out⟩ := by
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  have hδ : ∀ i (c : Cell (K + 2)), (c.2.1 = true ∧ c.2.2 (trR r) = false) →
      delta code N (clampPc N pc, .zsJ) i c = ((clampPc N pc, .zsJ), c, .right, .stay, none) := by
    intro i c ⟨h1, h2⟩; simp only [delta, hiF]; simp [h1, h2]
  by_cases hv0 : v = 0
  · rw [if_pos hv0]
    have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
      (tapeOf A (gOf σ)) A (fun i hi => ⟨tapeOf_alloc _ _ _ hi, by
        rw [tapeOf_bit, gOf_trR]; simp [← hv, hv0]⟩)
    have hlast : (pmachine code N).step w ⟨(clampPc N pc, .zsJ), σ.base.pos, tapeOf A (gOf σ),
        1 + A, σ.base.out⟩ = ⟨(clampPc N t, .ret), σ.base.pos, tapeOf A (gOf σ), A,
          σ.base.out⟩ := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF]
      rw [if_pos (tapeOf_unalloc _ _)]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil]
      (congr 1; omega)
    have := hscan.trans (RB.head hlast (reach_ret _ σ.base.pos hpos _ σ.base.out
      (tapeOf_mark0 _ _) A (fun i h1 _ => tapeOf_mark_false _ _ i h1)))
    exact (RB.head hstep this).mono (by omega)
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
      have := hInv.1 r
      have : 2 ^ A ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
      (tapeOf A (gOf σ)) j (fun i hi => ⟨tapeOf_alloc _ _ _ (by omega), by
        rw [tapeOf_bit, gOf_trR]; exact h1 i hi⟩)
    have hlast : (pmachine code N).step w ⟨(clampPc N pc, .zsJ), σ.base.pos, tapeOf A (gOf σ),
        1 + j, σ.base.out⟩ = ⟨(clampPc N (pc + 1), .ret), σ.base.pos, tapeOf A (gOf σ), j,
          σ.base.out⟩ := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF]
      have ha := tapeOf_alloc A (gOf σ) j hjA
      have hb : (tapeOf A (gOf σ) (1 + j)).2.2 (trR r) = true := by
        rw [tapeOf_bit, gOf_trR]; exact h0
      rw [if_neg (by rw [ha]; simp), if_pos hb]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil, clampPc_val hpc]
      (congr 1; omega)
    have := hscan.trans (RB.head hlast (reach_ret _ σ.base.pos hpos _ σ.base.out
      (tapeOf_mark0 _ _) j (fun i h1 _ => tapeOf_mark_false _ _ i h1)))
    exact (RB.head hstep this).mono (by omega)

/-- Simulation of a decrement. -/
lemma sim_dec (pc : ℕ) (hpc : pc ≤ N) (σ : PSt K) (r : Fin K)
    (hi : code.getD pc .halt = .dec r) (A : ℕ) (hInv : Inv A σ)
    (hpos : σ.base.pos ≤ w.length + 1) :
    Inv A { σ with base := σ.base.setReg r (σ.base.reg r - 1) } ∧
    RB (pmachine code N) w (4 * A + 5) (cfgOf code N pc σ A)
        (cfgOf code N (pc + 1) { σ with base := σ.base.setReg r (σ.base.reg r - 1) } A) := by
  set v := σ.base.reg r with hv
  have hiF : code.getD (clampPc N pc).val .halt = .dec r := by rw [clampPc_val hpc]; exact hi
  refine ⟨⟨fun r' => ?_, hInv.2.1, hInv.2.2⟩, ?_⟩
  · by_cases hr : r' = r
    · subst hr; simp only [St.setReg_reg, Function.update_self]
      exact lt_of_le_of_lt (Nat.sub_le _ _) (hInv.1 _)
    · simp only [St.setReg_reg, Function.update_of_ne hr]; exact hInv.1 r'
  have hstep : (pmachine code N).step w (cfgOf code N pc σ A) =
      ⟨(clampPc N pc, .zsD), σ.base.pos, tapeOf A (gOf σ), 1, σ.base.out⟩ := by
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  have hδ : ∀ i (c : Cell (K + 2)), (c.2.1 = true ∧ c.2.2 (trR r) = false) →
      delta code N (clampPc N pc, .zsD) i c = ((clampPc N pc, .zsD), c, .right, .stay, none) := by
    intro i c ⟨h1, h2⟩; simp only [delta, hiF]; simp [h1, h2]
  by_cases hv0 : v = 0
  · have hσ : { σ with base := σ.base.setReg r (σ.base.reg r - 1) } = σ := by
      have : σ.base.reg r - 1 = σ.base.reg r := by omega
      rw [this]; obtain ⟨⟨p, ρ, o⟩, c, m⟩ := σ; simp [St.setReg]
    rw [hσ]
    have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
      (tapeOf A (gOf σ)) A (fun i hi => ⟨tapeOf_alloc _ _ _ hi, by
        rw [tapeOf_bit, gOf_trR]; simp [← hv, hv0]⟩)
    have hlast : (pmachine code N).step w ⟨(clampPc N pc, .zsD), σ.base.pos, tapeOf A (gOf σ),
        1 + A, σ.base.out⟩ = ⟨(clampPc N (pc + 1), .ret), σ.base.pos, tapeOf A (gOf σ), A,
          σ.base.out⟩ := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF]
      rw [if_pos (tapeOf_unalloc _ _)]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil, clampPc_val hpc]
      (congr 1; omega)
    have := hscan.trans (RB.head hlast (reach_ret _ σ.base.pos hpos _ σ.base.out
      (tapeOf_mark0 _ _) A (fun i h1 _ => tapeOf_mark_false _ _ i h1)))
    exact (RB.head hstep this).mono (by omega)
  · classical
    have hex : ∃ j, v.testBit j = true := Nat.exists_testBit_of_ne_zero hv0
    set j := Nat.find hex with hj
    have h0 : v.testBit j = true := Nat.find_spec hex
    have h1 : ∀ i < j, v.testBit i = false := fun i hi => by
      have := Nat.find_min hex hi; simpa using this
    have hjA : j < A := by
      by_contra hc
      have := Nat.ge_two_pow_of_testBit h0
      have := hInv.1 r
      have : 2 ^ A ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hpred := testBit_pred_of_trailing v j h1 h0
    have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
      (tapeOf A (gOf σ)) j (fun i hi => ⟨tapeOf_alloc _ _ _ (by omega), by
        rw [tapeOf_bit, gOf_trR]; exact h1 i hi⟩)
    have hl1 : (pmachine code N).step w ⟨(clampPc N pc, .zsD), σ.base.pos, tapeOf A (gOf σ),
        1 + j, σ.base.out⟩ = ⟨(clampPc N pc, .retB), σ.base.pos, tapeOf A (gOf σ), j,
          σ.base.out⟩ := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF]
      have ha := tapeOf_alloc A (gOf σ) j hjA
      have hb : (tapeOf A (gOf σ) (1 + j)).2.2 (trR r) = true := by
        rw [tapeOf_bit, gOf_trR]; exact h0
      rw [if_neg (by rw [ha]; simp), if_pos hb]
      simp only [Dir.move, min_eq_left hpos, Function.update_eq_self, Option.toList_none,
        List.append_nil]
      (congr 1; omega)
    have hrb := reach_retB (code := code) (w := w) (clampPc N pc) σ.base.pos hpos _ σ.base.out
      (tapeOf_mark0 A (gOf σ)) j (fun i h1 _ => tapeOf_mark_false _ _ i h1)
    have eT := tape_split A σ (trR r)
    rw [gOf_trR] at eT
    have hbor := reach_borrow (w := w) _ r hiF σ.base.pos hpos σ.base.out A (gOf σ) v j hjA.le h1
    rw [← eT] at hbor
    have hl2 : (pmachine code N).step w ⟨(clampPc N pc, .borrow), σ.base.pos,
        tapeOf A (Function.update (gOf σ) (trR r)
          (fun i => if i < j then true else v.testBit i)), 1 + j, σ.base.out⟩ =
        ⟨(clampPc N (pc + 1), .ret), σ.base.pos,
          tapeOf A (gOf { σ with base := σ.base.setReg r (v - 1) }), j, σ.base.out⟩ := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF]
      have hb : (tapeOf A (Function.update (gOf σ) (trR r)
          (fun i => if i < j then true else v.testBit i)) (1 + j)).2.2 (trR r) = true := by
        rw [tapeOf_bit]; simp [h0]
      rw [if_pos hb]
      simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil]
      rw [update_tapeOf' _ _ _ _ _ _ hjA.le, max_eq_left (by omega), gOf_setReg, clampPc_val hpc]
      have hX : Function.update (fun i => if i < j then true else v.testBit i) j false =
          fun i => (v - 1).testBit i := by
        funext i; rw [hpred]
        by_cases h : i = j
        · subst h; simp
        · rw [Function.update_of_ne h]; simp [h]
      rw [hX]
      (congr 1; omega)
    have := hscan.trans (RB.head hl1 (hrb.trans (hbor.trans (RB.head hl2
      (reach_ret _ σ.base.pos hpos _ σ.base.out (tapeOf_mark0 _ _) j
        (fun i h1 _ => tapeOf_mark_false _ _ i h1))))))
    exact (RB.head hstep this).mono (by omega)

lemma scan_cur_pred (A : ℕ) (σ : PSt K) :
    ∀ i < σ.cur, (fun c : Cell (K + 2) => c.2.2 trP = true) (tapeOf A (gOf σ) (1 + i)) := by
  intro i hi; show (tapeOf A (gOf σ) (1 + i)).2.2 trP = true
  rw [tapeOf_bit, gOf_trP]; simpa using hi

lemma tapeOf_cur_bit (A : ℕ) (σ : PSt K) : (tapeOf A (gOf σ) (1 + σ.cur)).2.2 trP = false := by
  rw [tapeOf_bit, gOf_trP]; simp

/-- Simulation of a cursor move to the right. -/
lemma sim_cr (pc : ℕ) (hpc : pc ≤ N) (σ : PSt K) (hi : code.getD pc .halt = .cr) (A : ℕ)
    (hInv : Inv A σ) (hpos : σ.base.pos ≤ w.length + 1) (hcB : σ.cur < B) (hA : A ≤ B + 1) :
    max A (1 + σ.cur) ≤ B + 1 ∧ Inv (max A (1 + σ.cur)) { σ with cur := σ.cur + 1 } ∧
      RB (pmachine code N) w (4 * A + 5) (cfgOf code N pc σ A)
        (cfgOf code N (pc + 1) { σ with cur := σ.cur + 1 } (max A (1 + σ.cur))) := by
  have hiF : code.getD (clampPc N pc).val .halt = .cr := by rw [clampPc_val hpc]; exact hi
  have hcA := hInv.2.1
  refine ⟨by omega, ?_, ?_⟩
  · exact ⟨fun r => lt_of_lt_of_le (hInv.1 r) (Nat.pow_le_pow_right (by norm_num) (by omega)),
      by dsimp only; omega, fun i hi => by have := hInv.2.2 i hi; omega⟩
  have hstep : (pmachine code N).step w (cfgOf code N pc σ A) =
      ⟨(clampPc N pc, .crS), σ.base.pos, tapeOf A (gOf σ), 1, σ.base.out⟩ := by
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  have hδ : ∀ i (c : Cell (K + 2)), c.2.2 trP = true →
      delta code N (clampPc N pc, .crS) i c = ((clampPc N pc, .crS), c, .right, .stay, none) := by
    intro i c h1; simp only [delta, hiF]; simp [h1]
  have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
    (tapeOf A (gOf σ)) σ.cur (scan_cur_pred A σ)
  have hlast : (pmachine code N).step w ⟨(clampPc N pc, .crS), σ.base.pos, tapeOf A (gOf σ),
      1 + σ.cur, σ.base.out⟩ = ⟨(clampPc N (pc + 1), .ret), σ.base.pos,
        tapeOf (max A (1 + σ.cur)) (gOf { σ with cur := σ.cur + 1 }), σ.cur, σ.base.out⟩ := by
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
    simp only [delta, hiF]
    rw [if_neg (by rw [tapeOf_cur_bit]; simp)]
    simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil]
    rw [tape_split A σ trP, gOf_trP, update_tapeOf' _ _ _ _ _ _ hcA, gOf_cur σ (σ.cur + 1), clampPc_val hpc]
    have hX : Function.update (fun i => decide (i < σ.cur)) σ.cur true =
        fun i => decide (i < σ.cur + 1) := by
      funext i
      by_cases h : i = σ.cur
      · subst h; simp
      · rw [Function.update_of_ne h]; simp only [decide_eq_decide]; omega
    rw [hX]
    (congr 1; omega)
  have := hscan.trans (RB.head hlast (reach_ret _ σ.base.pos hpos _ σ.base.out
    (tapeOf_mark0 _ _) σ.cur (fun i h1 _ => tapeOf_mark_false _ _ i h1)))
  exact (RB.head hstep this).mono (by omega)

/-- Simulation of setting the memory bit under the cursor. -/
lemma sim_mset (pc : ℕ) (hpc : pc ≤ N) (σ : PSt K) (hi : code.getD pc .halt = .mset) (A : ℕ)
    (hInv : Inv A σ) (hpos : σ.base.pos ≤ w.length + 1) :
    Inv (max A (1 + σ.cur)) { σ with mem := insert σ.cur σ.mem } ∧
      RB (pmachine code N) w (4 * A + 5) (cfgOf code N pc σ A)
        (cfgOf code N (pc + 1) { σ with mem := insert σ.cur σ.mem } (max A (1 + σ.cur))) := by
  have hiF : code.getD (clampPc N pc).val .halt = .mset := by rw [clampPc_val hpc]; exact hi
  have hcA := hInv.2.1
  refine ⟨⟨fun r => lt_of_lt_of_le (hInv.1 r) (Nat.pow_le_pow_right (by norm_num) (by omega)),
      by dsimp only; omega, fun i hi => ?_⟩, ?_⟩
  · simp only [Finset.mem_insert] at hi
    rcases hi with rfl | hi
    · omega
    · have := hInv.2.2 i hi; omega
  have hstep : (pmachine code N).step w (cfgOf code N pc σ A) =
      ⟨(clampPc N pc, .msS), σ.base.pos, tapeOf A (gOf σ), 1, σ.base.out⟩ := by
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  have hδ : ∀ i (c : Cell (K + 2)), c.2.2 trP = true →
      delta code N (clampPc N pc, .msS) i c = ((clampPc N pc, .msS), c, .right, .stay, none) := by
    intro i c h1; simp only [delta, hiF]; simp [h1]
  have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
    (tapeOf A (gOf σ)) σ.cur (scan_cur_pred A σ)
  have hlast : (pmachine code N).step w ⟨(clampPc N pc, .msS), σ.base.pos, tapeOf A (gOf σ),
      1 + σ.cur, σ.base.out⟩ = ⟨(clampPc N (pc + 1), .ret), σ.base.pos,
        tapeOf (max A (1 + σ.cur)) (gOf { σ with mem := insert σ.cur σ.mem }), σ.cur,
        σ.base.out⟩ := by
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
    simp only [delta, hiF]
    rw [if_neg (by rw [tapeOf_cur_bit]; simp)]
    simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil]
    rw [tape_split A σ trM, gOf_trM, update_tapeOf' _ _ _ _ _ _ hcA, gOf_mem σ (insert σ.cur σ.mem), clampPc_val hpc]
    have hX : Function.update (fun i => decide (i ∈ σ.mem)) σ.cur true =
        fun i => decide (i ∈ insert σ.cur σ.mem) := by
      funext i
      by_cases h : i = σ.cur
      · subst h; simp
      · rw [Function.update_of_ne h]; simp [h]
    rw [hX]
    (congr 1; omega)
  have := hscan.trans (RB.head hlast (reach_ret _ σ.base.pos hpos _ σ.base.out
    (tapeOf_mark0 _ _) σ.cur (fun i h1 _ => tapeOf_mark_false _ _ i h1)))
  exact (RB.head hstep this).mono (by omega)

/-- Simulation of a jump on the memory bit under the cursor. -/
lemma sim_jm (pc : ℕ) (hpc : pc ≤ N) (σ : PSt K) (t : ℕ) (hi : code.getD pc .halt = .jm t)
    (A : ℕ) (hInv : Inv A σ) (hpos : σ.base.pos ≤ w.length + 1) :
    RB (pmachine code N) w (4 * A + 5) (cfgOf code N pc σ A)
        (cfgOf code N (if σ.cur ∈ σ.mem then t else pc + 1) σ A) := by
  have hiF : code.getD (clampPc N pc).val .halt = .jm t := by rw [clampPc_val hpc]; exact hi
  have hcA := hInv.2.1
  have hstep : (pmachine code N).step w (cfgOf code N pc σ A) =
      ⟨(clampPc N pc, .jmS), σ.base.pos, tapeOf A (gOf σ), 1, σ.base.out⟩ := by
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  have hδ : ∀ i (c : Cell (K + 2)), c.2.2 trP = true →
      delta code N (clampPc N pc, .jmS) i c = ((clampPc N pc, .jmS), c, .right, .stay, none) := by
    intro i c h1; simp only [delta, hiF]; simp [h1]
  have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
    (tapeOf A (gOf σ)) σ.cur (scan_cur_pred A σ)
  have hlast : (pmachine code N).step w ⟨(clampPc N pc, .jmS), σ.base.pos, tapeOf A (gOf σ),
      1 + σ.cur, σ.base.out⟩ = ⟨(clampPc N (if σ.cur ∈ σ.mem then t else pc + 1), .ret),
        σ.base.pos, tapeOf A (gOf σ), σ.cur, σ.base.out⟩ := by
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
    simp only [delta, hiF]
    rw [if_neg (by rw [tapeOf_cur_bit]; simp)]
    have hm : (tapeOf A (gOf σ) (1 + σ.cur)).2.2 trM = decide (σ.cur ∈ σ.mem) := by
      rw [tapeOf_bit, gOf_trM]
    simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil,
      Function.update_eq_self, hm, clampPc_val hpc]
    by_cases h : σ.cur ∈ σ.mem
    · simp only [h, decide_true, if_true]; (congr 1; omega)
    · simp only [h, decide_false, Bool.false_eq_true, if_false]; (congr 1; omega)
  have := hscan.trans (RB.head hlast (reach_ret _ σ.base.pos hpos _ σ.base.out
    (tapeOf_mark0 _ _) σ.cur (fun i h1 _ => tapeOf_mark_false _ _ i h1)))
  exact (RB.head hstep this).mono (by omega)

/-- Simulation of a cursor move to the left. -/
lemma sim_cl (pc : ℕ) (hpc : pc ≤ N) (σ : PSt K) (hi : code.getD pc .halt = .cl) (A : ℕ)
    (hInv : Inv A σ) (hpos : σ.base.pos ≤ w.length + 1) :
    Inv A { σ with cur := σ.cur - 1 } ∧
      RB (pmachine code N) w (4 * A + 5) (cfgOf code N pc σ A)
        (cfgOf code N (pc + 1) { σ with cur := σ.cur - 1 } A) := by
  have hiF : code.getD (clampPc N pc).val .halt = .cl := by rw [clampPc_val hpc]; exact hi
  have hcA := hInv.2.1
  refine ⟨⟨hInv.1, by simp; omega, hInv.2.2⟩, ?_⟩
  have hstep : (pmachine code N).step w (cfgOf code N pc σ A) =
      ⟨(clampPc N pc, .clS), σ.base.pos, tapeOf A (gOf σ), 1, σ.base.out⟩ := by
    rw [cfgOf, pmachine_step _ _ _ _ _ _ _ _ (haltQ_bnd hiF (by simp))]
    simp only [delta, hiF, Dir.move, min_eq_left hpos, Function.update_eq_self,
      Option.toList_none, List.append_nil]
  have hδ : ∀ i (c : Cell (K + 2)), c.2.2 trP = true →
      delta code N (clampPc N pc, .clS) i c = ((clampPc N pc, .clS), c, .right, .stay, none) := by
    intro i c h1; simp only [delta, hiF]; simp [h1]
  have hscan := reach_scan (w := w) _ _ (by decide) _ hδ σ.base.pos hpos σ.base.out
    (tapeOf A (gOf σ)) σ.cur (scan_cur_pred A σ)
  have hl1 : (pmachine code N).step w ⟨(clampPc N pc, .clS), σ.base.pos, tapeOf A (gOf σ),
      1 + σ.cur, σ.base.out⟩ = ⟨(clampPc N pc, .clB), σ.base.pos, tapeOf A (gOf σ), σ.cur,
        σ.base.out⟩ := by
    rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
    simp only [delta, hiF]
    rw [if_neg (by rw [tapeOf_cur_bit]; simp)]
    simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil,
      Function.update_eq_self]
    (congr 1; omega)
  rcases Nat.eq_zero_or_eq_succ_pred σ.cur with h0 | hs
  · have hσ : { σ with cur := σ.cur - 1 } = σ := by
      obtain ⟨b, c, m⟩ := σ; simp only at h0; subst h0; rfl
    rw [hσ]
    have hl2 : (pmachine code N).step w ⟨(clampPc N pc, .clB), σ.base.pos, tapeOf A (gOf σ),
        σ.cur, σ.base.out⟩ = cfgOf code N (pc + 1) σ A := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF, h0]
      rw [if_pos (tapeOf_mark0 _ _)]
      simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil,
        Function.update_eq_self, clampPc_val hpc, cfgOf]
    have := hscan.trans (RB.head hl1 (RB.single hl2))
    exact (RB.head hstep this).mono (by omega)
  · set c := σ.cur - 1 with hc
    have hcur : σ.cur = c + 1 := by omega
    have hl2 : (pmachine code N).step w ⟨(clampPc N pc, .clB), σ.base.pos, tapeOf A (gOf σ),
        σ.cur, σ.base.out⟩ = ⟨(clampPc N (pc + 1), .ret), σ.base.pos,
          tapeOf A (gOf { σ with cur := c }), c, σ.base.out⟩ := by
      rw [pmachine_step _ _ _ _ _ _ _ _ (haltQ_of_ne_bnd _ _ _ _ (by decide))]
      simp only [delta, hiF]
      rw [if_neg (by rw [tapeOf_mark_false _ _ _ (by omega)]; simp)]
      simp only [Dir.move, min_eq_left hpos, Option.toList_none, List.append_nil]
      rw [tape_split A σ trP, gOf_trP, hcur, show c + 1 = 1 + c by omega,
        update_tapeOf' _ _ _ _ _ _ (by omega), max_eq_left (by omega), gOf_cur σ c, clampPc_val hpc]
      have hX : Function.update (fun i => decide (i < 1 + c)) c false =
          fun i => decide (i < c) := by
        funext i
        by_cases h : i = c
        · subst h; simp
        · rw [Function.update_of_ne h]; simp only [decide_eq_decide]; omega
      rw [hX]
      (congr 1; omega)
    have := hscan.trans (RB.head hl1 (RB.head hl2 (reach_ret _ σ.base.pos hpos _ σ.base.out
      (tapeOf_mark0 _ _) c (fun i h1 _ => tapeOf_mark_false _ _ i h1))))
    exact (RB.head hstep this).mono (by omega)

end Sim

end PT

end PathChecking
