module

public import RequestProject.Logspace.Arith
public import RequestProject.Logspace.OutBound

/-!
# Simulating one Turing machine step by a register program

The state, work head position and work tape of a Turing machine `M` are stored in registers
`ρ 0` (state index), `ρ 1` (work head position), `ρ 2` (cells left of the head, in base
`|Γ|`, nearest cell least significant) and `ρ 3` (cells from the head up to a bound `S`,
head cell least significant).  The blank symbol has digit `0`.

`simStep` performs one step, given the code of the current input symbol in register `ρ 7`.
What happens with the input head and the output is left to two parameter programs
`inMv` and `outAct`, so that the same code serves for simulating a machine on the real input
and on a virtual input.
-/

@[expose] public section

namespace PathChecking

open Classical

/-! ## Codes -/

/-- Number of work tape symbols. -/
noncomputable def TM.nG (M : TM) : ℕ := Fintype.card M.Γ

/-- Number of states. -/
noncomputable def TM.nQ (M : TM) : ℕ := Fintype.card M.Q

lemma TM.nG_pos (M : TM) : 0 < M.nG := Fintype.card_pos_iff.2 ⟨M.blank⟩

/-- Numbering of states. -/
noncomputable def TM.eQ (M : TM) : M.Q ≃ Fin M.nQ := Fintype.equivFin _

/-- Numbering of work tape symbols, with the blank numbered `0`. -/
noncomputable def TM.eG (M : TM) : M.Γ ≃ Fin M.nG :=
  (Fintype.equivFin _).trans (Equiv.swap ((Fintype.equivFin _) M.blank) ⟨0, M.nG_pos⟩)

/-- Digit of a work tape symbol. -/
noncomputable def TM.gc (M : TM) (g : M.Γ) : ℕ := M.eG g

lemma TM.gc_blank (M : TM) : M.gc M.blank = 0 := by
  unfold TM.gc TM.eG
  rw [Equiv.trans_apply]
  exact congrArg Fin.val (Equiv.swap_apply_left _ _)

lemma TM.gc_lt (M : TM) (g : M.Γ) : M.gc g < M.nG := (M.eG g).2

lemma TM.eQ_lt (M : TM) (q : M.Q) : (M.eQ q : ℕ) < M.nQ := (M.eQ q).2

/-- Code of an input symbol. -/
def symCode : InSym → ℕ
  | .lend => 0
  | .rend => 1
  | .bit false => 2
  | .bit true => 3

/-- Decoding of input symbol codes. -/
def symOf : Fin 4 → InSym
  | 0 => .lend
  | 1 => .rend
  | 2 => .bit false
  | 3 => .bit true

lemma symCode_lt (x : InSym) : symCode x < 4 := by
  rcases x with _ | _ | ⟨_ | _⟩ <;> simp [symCode]

lemma symOf_symCode (x : InSym) : symOf ⟨symCode x, symCode_lt x⟩ = x := by
  rcases x with _ | _ | ⟨_ | _⟩ <;> rfl

namespace LS

open scoped LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-! ## Tape encodings -/

/-- Cells `0 … p-1`, cell `p-1` least significant. -/
noncomputable def encL (M : TM) (T : ℕ → M.Γ) : ℕ → ℕ
  | 0 => 0
  | p + 1 => M.nG * encL M T p + M.gc (T p)

/-- Cells `p … p+n-1`, cell `p` least significant. -/
noncomputable def encR (M : TM) (T : ℕ → M.Γ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | p, n + 1 => M.gc (T p) + M.nG * encR M T (p + 1) n

lemma encL_congr (M : TM) {T T' : ℕ → M.Γ} (p : ℕ) (h : ∀ j < p, T j = T' j) :
    encL M T p = encL M T' p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    simp only [encL, ih (fun j hj => h j (by omega)), h p (by omega)]

lemma encR_congr (M : TM) {T T' : ℕ → M.Γ} (n : ℕ) :
    ∀ p, (∀ j, p ≤ j → j < p + n → T j = T' j) → encR M T p n = encR M T' p n := by
  induction n with
  | zero => intro p _; rfl
  | succ n ih =>
    intro p h
    simp only [encR, h p le_rfl (by omega), ih (p + 1) (fun j h1 h2 => h j (by omega) (by omega))]

lemma encL_lt (M : TM) (T : ℕ → M.Γ) (p : ℕ) : encL M T p < M.nG ^ p := by
  induction p with
  | zero => simp [encL]
  | succ p ih =>
    simp only [encL, pow_succ]
    have := M.gc_lt (T p)
    have : M.nG * encL M T p + M.nG ≤ M.nG * M.nG ^ p := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    nlinarith

lemma encR_lt (M : TM) (T : ℕ → M.Γ) (n : ℕ) : ∀ p, encR M T p n < M.nG ^ n := by
  induction n with
  | zero => intro p; simp [encR]
  | succ n ih =>
    intro p
    simp only [encR, pow_succ]
    have := M.gc_lt (T p)
    have h := ih (p + 1)
    have : M.nG * encR M T (p + 1) n + M.nG ≤ M.nG * M.nG ^ n := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
    nlinarith

lemma encR_blank (M : TM) (n p : ℕ) : encR M (fun _ => M.blank) p n = 0 := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [encR, ih, M.gc_blank]

/-! ## Register layout -/

/-- The simulation state `σ` represents state `st`, work head position `wp` and work tape
`T`, for the space bound `S`. -/
def Rep (M : TM) (ρ : Fin 8 → Fin K) (S : ℕ) (st : M.Q) (wp : ℕ) (T : ℕ → M.Γ) (σ : St K) :
    Prop :=
  σ.reg (ρ 0) = M.eQ st ∧ σ.reg (ρ 1) = wp ∧ wp ≤ S ∧ σ.reg (ρ 2) = encL M T wp ∧
    σ.reg (ρ 3) = encR M T wp (S + 1 - wp)

/-! ## The step program -/

/-- Writing a symbol and moving the work head (the head cell has already been popped from
`ρ 3`). Temporaries: `ρ 4`, `ρ 5`. -/
noncomputable def tapeAct (M : TM) (ρ : Fin 8 → Fin K) (g : M.Γ) : Dir → Stmt K
  | .right => mulAdd (ρ 2) (ρ 5) M.nG (M.gc g) ⨟ .inc (ρ 1)
  | .stay => mulAdd (ρ 3) (ρ 5) M.nG (M.gc g)
  | .left => mulAdd (ρ 3) (ρ 5) M.nG (M.gc g) ⨟
      .ite (.zero (ρ 1)) .skip
        (.dec (ρ 1) ⨟ divMod (ρ 2) (ρ 5) (ρ 4) M.nG ⨟ addTo (ρ 5) (ρ 2) ⨟
          mulAdd (ρ 3) (ρ 5) M.nG 0 ⨟ addTo (ρ 4) (ρ 3))

/-- The action for state `st`, input symbol `x` and work symbol `c`. -/
noncomputable def act (M : TM) (ρ : Fin 8 → Fin K) (inMv : InSym → Dir → Stmt K)
    (outAct : Option Bool → Stmt K) (st : M.Q) (x : InSym) (c : M.Γ) : Stmt K :=
  setC (ρ 0) (M.eQ (M.δ st x c).1) ⨟ setC (ρ 6) (if M.halt (M.δ st x c).1 then 0 else 1) ⨟
    tapeAct M ρ (M.δ st x c).2.1 (M.δ st x c).2.2.1 ⨟ inMv x (M.δ st x c).2.2.2.1 ⨟
    outAct (M.δ st x c).2.2.2.2

/-- One simulation step: pop the head cell into `ρ 4` and dispatch on state, input symbol
(`ρ 7`) and head cell. -/
noncomputable def simStep (M : TM) (ρ : Fin 8 → Fin K) (inMv : InSym → Dir → Stmt K)
    (outAct : Option Bool → Stmt K) : Stmt K :=
  divMod (ρ 3) (ρ 5) (ρ 4) M.nG ⨟ addTo (ρ 5) (ρ 3) ⨟
    caseReg (ρ 0) (List.ofFn fun i : Fin M.nQ =>
      caseReg (ρ 7) (List.ofFn fun j : Fin 4 =>
        caseReg (ρ 4) (List.ofFn fun k : Fin M.nG =>
          act M ρ inMv outAct (M.eQ.symm i) (symOf j) (M.eG.symm k))))

/-! ## Correctness -/

section Correct

variable (M : TM) (ρ : Fin 8 → Fin K) (hρ : Function.Injective ρ)
include hρ

lemma ach_tapeAct (S : ℕ) (g : M.Γ) (dw : Dir) (wp : ℕ) (T : ℕ → M.Γ) (σ : St K)
    (hwp : wp ≤ S) (hwp' : dw.move wp ≤ S) (hB : S + 1 + M.nG ^ (S + 2) ≤ B)
    (h1 : σ.reg (ρ 1) = wp) (h2 : σ.reg (ρ 2) = encL M T wp)
    (h3 : σ.reg (ρ 3) = encR M T (wp + 1) (S - wp)) :
    Ach w B (tapeAct M ρ g dw) σ (fun σ' => σ'.pos = σ.pos ∧ σ'.out = σ.out ∧
      σ'.reg (ρ 1) = dw.move wp ∧
      σ'.reg (ρ 2) = encL M (Function.update T wp g) (dw.move wp) ∧
      σ'.reg (ρ 3) = encR M (Function.update T wp g) (dw.move wp) (S + 1 - dw.move wp) ∧
      ∀ x, x ≠ ρ 1 → x ≠ ρ 2 → x ≠ ρ 3 → x ≠ ρ 4 → x ≠ ρ 5 → σ'.reg x = σ.reg x) := by
  have hG := M.nG_pos
  have hpow : ∀ n, n ≤ S + 2 → M.nG ^ n ≤ M.nG ^ (S + 2) := fun n hn =>
    Nat.pow_le_pow_right hG hn
  have ne : ∀ i j : Fin 8, i ≠ j → ρ i ≠ ρ j := fun i j h => hρ.ne h
  have eLu : encL M (Function.update T wp g) wp = encL M T wp :=
    encL_congr M wp (fun j hj => by rw [Function.update_of_ne (by omega)])
  have eRu : ∀ n, encR M (Function.update T wp g) (wp + 1) n = encR M T (wp + 1) n :=
    fun n => encR_congr M n _ (fun j hj _ => by rw [Function.update_of_ne (by omega)])
  have hR := encR_lt M T (S - wp) (wp + 1)
  have hL := encL_lt M T wp
  have hRS : M.nG ^ (S - wp) * M.nG ^ 2 ≤ M.nG ^ (S + 2) := by
    rw [← pow_add]; exact hpow _ (by omega)
  cases dw with
  | right =>
    simp only [Dir.move] at hwp' ⊢
    have hLb : M.nG * encL M T wp + M.gc g ≤ B := by
      have := M.gc_lt g
      have : M.nG * encL M T wp + M.nG ≤ M.nG ^ (wp + 1) := by
        rw [pow_succ, ← Nat.mul_succ, mul_comm]; exact Nat.mul_le_mul_right _ hL
      have := hpow (wp + 1) (by omega)
      omega
    refine ach_seq (ach_mulAdd _ _ (ne 2 5 (by decide)) _ _ _ _ (by rw [h2]; exact hLb) ?_)
    refine ach_inc (by simp [St.setReg_apply, ne 1 5 (by decide), ne 1 2 (by decide), h1]; omega) ?_
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [St.setReg_apply, ne 1 5 (by decide), ne 1 2 (by decide), h1]
    · simp only [St.setReg_apply, if_neg (ne 2 1 (by decide)), if_neg (ne 2 5 (by decide)),
        if_true, h2, encL, eLu, Function.update_self]
    · simp only [St.setReg_apply, if_neg (ne 3 1 (by decide)), if_neg (ne 3 5 (by decide)),
        if_neg (ne 3 2 (by decide)), h3, eRu]
      congr 1; omega
    · intro x hx1 hx2 hx3 hx4 hx5
      simp [St.setReg_apply, hx1, hx2, hx5]
  | stay =>
    simp only [Dir.move]
    have hb : M.nG * encR M T (wp + 1) (S - wp) + M.gc g ≤ B := by
      have := M.gc_lt g
      have : M.nG * encR M T (wp + 1) (S - wp) + M.nG ≤ M.nG ^ (S - wp) * M.nG := by
        rw [← Nat.mul_succ, mul_comm]; exact Nat.mul_le_mul_right _ hR
      have : M.nG ^ (S - wp) * M.nG ≤ M.nG ^ (S - wp) * M.nG ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith)
      omega
    refine ach_mulAdd _ _ (ne 3 5 (by decide)) _ _ _ _ (by rw [h3]; exact hb) ?_
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [St.setReg_apply, ne 1 5 (by decide), ne 1 3 (by decide), h1]
    · simp [St.setReg_apply, ne 2 5 (by decide), ne 2 3 (by decide), h2, eLu]
    · simp only [St.setReg_apply, if_neg (ne 3 5 (by decide)), if_true, h3]
      rw [show S + 1 - wp = (S - wp) + 1 by omega, encR, Function.update_self, eRu]
      ring
    · intro x hx1 hx2 hx3 hx4 hx5
      simp [St.setReg_apply, hx3, hx5]
  | left =>
    simp only [Dir.move] at hwp' ⊢
    have hb : M.nG * encR M T (wp + 1) (S - wp) + M.gc g ≤ B := by
      have := M.gc_lt g
      have : M.nG * encR M T (wp + 1) (S - wp) + M.nG ≤ M.nG ^ (S - wp) * M.nG := by
        rw [← Nat.mul_succ, mul_comm]; exact Nat.mul_le_mul_right _ hR
      have : M.nG ^ (S - wp) * M.nG ≤ M.nG ^ (S - wp) * M.nG ^ 2 :=
        Nat.mul_le_mul_left _ (by nlinarith)
      omega
    refine ach_seq (ach_mulAdd _ _ (ne 3 5 (by decide)) _ _ _ _ (by rw [h3]; exact hb) ?_)
    set σ₁ := (σ.setReg (ρ 3) (M.nG * σ.reg (ρ 3) + M.gc g)).setReg (ρ 5) 0
    have e1 : σ₁.reg (ρ 1) = wp := by
      simp [σ₁, St.setReg_apply, ne 1 5 (by decide), ne 1 3 (by decide), h1]
    have e2 : σ₁.reg (ρ 2) = encL M T wp := by
      simp [σ₁, St.setReg_apply, ne 2 5 (by decide), ne 2 3 (by decide), h2]
    have e3 : σ₁.reg (ρ 3) = encR M (Function.update T wp g) wp (S + 1 - wp) := by
      simp only [σ₁, St.setReg_apply, if_neg (ne 3 5 (by decide)), if_true, h3]
      rw [show S + 1 - wp = (S - wp) + 1 by omega, encR, Function.update_self, eRu]
      ring
    have e3b : encR M (Function.update T wp g) wp (S + 1 - wp) < M.nG ^ (S + 1 - wp) :=
      encR_lt _ _ _ _
    refine ach_ite ?_
    by_cases hw0 : wp = 0
    · subst hw0
      rw [if_pos (by simp [Cond.eval, e1])]
      refine ach_skip ⟨rfl, rfl, e1, ?_, ?_, ?_⟩
      · simp [e2, encL]
      · simpa using e3
      · intro x hx1 hx2 hx3 hx4 hx5
        simp [σ₁, St.setReg_apply, hx3, hx5]
    · rw [if_neg (by simp [Cond.eval, e1, hw0])]
      obtain ⟨v, rfl⟩ : ∃ v, wp = v + 1 := ⟨wp - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hwp' ⊢
      refine ach_seq (ach_dec (ach_seq (ach_divMod _ _ _ (ne 2 5 (by decide))
        (ne 2 4 (by decide)) (ne 5 4 (by decide)) _ M.nG_pos _ _ ?_ ?_)))
      · simp only [St.setReg_apply, if_neg (ne 2 1 (by decide)), e2]
        have := hpow (v + 1) (by omega)
        omega
      have eL : (σ₁.setReg (ρ 1) (σ₁.reg (ρ 1) - 1)).reg (ρ 2) =
          M.nG * encL M T v + M.gc (T v) := by
        simp only [St.setReg_apply, if_neg (ne 2 1 (by decide)), e2, encL]
      have hdiv : (M.nG * encL M T v + M.gc (T v)) / M.nG = encL M T v := by
        rw [Nat.mul_add_div M.nG_pos, Nat.div_eq_of_lt (M.gc_lt _)]; simp
      have hmod : (M.nG * encL M T v + M.gc (T v)) % M.nG = M.gc (T v) := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt (M.gc_lt _)]
      rw [eL, hdiv, hmod]
      set σ₂ := (((σ₁.setReg (ρ 1) (σ₁.reg (ρ 1) - 1)).setReg (ρ 2) 0).setReg (ρ 5)
        (encL M T v)).setReg (ρ 4) (M.gc (T v))
      have f2 : σ₂.reg (ρ 2) = 0 := by
        simp [σ₂, St.setReg_apply, ne 2 5 (by decide), ne 2 4 (by decide)]
      have f5 : σ₂.reg (ρ 5) = encL M T v := by
        simp only [σ₂, St.setReg_apply, if_neg (ne 5 4 (by decide)), if_true]
      have f4 : σ₂.reg (ρ 4) = M.gc (T v) := by
        simp only [σ₂, St.setReg_apply, if_true]
      have f3 : σ₂.reg (ρ 3) = encR M (Function.update T (v + 1) g) (v + 1) (S - v) := by
        simp only [σ₂, St.setReg_apply, if_neg (ne 3 4 (by decide)), if_neg (ne 3 5 (by decide)),
          if_neg (ne 3 2 (by decide)), if_neg (ne 3 1 (by decide)), e3]
        congr 1; omega
      have f1 : σ₂.reg (ρ 1) = v := by
        simp only [σ₂, St.setReg_apply, if_neg (ne 1 4 (by decide)), if_neg (ne 1 5 (by decide)),
          if_neg (ne 1 2 (by decide)), if_true, e1]; omega
      have hLv := encL_lt M T v
      refine ach_seq (ach_addTo _ _ (ne 5 2 (by decide)) _ _ (by rw [f2, f5]; have := hpow v (by omega); omega) ?_)
      set σ₃ := (σ₂.setReg (ρ 5) 0).setReg (ρ 2) (σ₂.reg (ρ 2) + σ₂.reg (ρ 5))
      have g3 : σ₃.reg (ρ 3) = encR M (Function.update T (v + 1) g) (v + 1) (S - v) := by
        simp [σ₃, St.setReg_apply, ne 3 5 (by decide), ne 3 2 (by decide), f3]
      have hRv := encR_lt M (Function.update T (v + 1) g) (S - v) (v + 1)
      have hRv' : M.nG * encR M (Function.update T (v + 1) g) (v + 1) (S - v) + M.gc (T v) ≤ B := by
        have := M.gc_lt (T v)
        have : M.nG * encR M (Function.update T (v + 1) g) (v + 1) (S - v) + M.nG ≤
            M.nG ^ (S - v + 1) := by
          rw [pow_succ, ← Nat.mul_succ, mul_comm]; exact Nat.mul_le_mul_right _ hRv
        have := hpow (S - v + 1) (by omega)
        omega
      refine ach_seq (ach_mulAdd _ _ (ne 3 5 (by decide)) _ _ _ _ (by rw [g3]; omega) ?_)
      refine ach_addTo _ _ (ne 4 3 (by decide)) _ _ ?_ ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [St.setReg_apply, ne 3 5 (by decide), ne 4 5 (by decide), ne 4 3 (by decide),
          ne 4 2 (by decide), σ₃, f4]
        simpa [σ₃, St.setReg_apply, ne 3 5 (by decide), ne 3 2 (by decide), f3] using hRv'
      · rfl
      · rfl
      · simp [St.setReg_apply, ne 1 3 (by decide), ne 1 4 (by decide), ne 1 5 (by decide),
          ne 1 2 (by decide), σ₃, f1]
      · simp only [St.setReg_apply, if_neg (ne 2 3 (by decide)), if_neg (ne 2 4 (by decide)),
          if_neg (ne 2 5 (by decide)), σ₃, if_true, f2, f5, zero_add]
        exact encL_congr M v (fun j hj => by rw [Function.update_of_ne (by omega)])
      · simp only [St.setReg_apply, hρ.eq_iff, σ₃, f3, f4]
        simp only [Fin.reduceEq, if_false, if_true]
        rw [show S + 1 - v = (S - v) + 1 by omega, encR, Function.update_of_ne (by omega)]
        ring
      · intro x hx1 hx2 hx3 hx4 hx5
        simp [St.setReg_apply, hx1, hx2, hx3, hx4, hx5, σ₃, σ₂, σ₁]

lemma ach_simStep (inMv : InSym → Dir → Stmt K) (outAct : Option Bool → Stmt K) (S : ℕ)
    (st : M.Q) (wp : ℕ) (T : ℕ → M.Γ) (x : InSym) (σ : St K)
    (hRep : Rep M ρ S st wp T σ) (hs : σ.reg (ρ 7) = symCode x)
    (hwp' : (M.δ st x (T wp)).2.2.1.move wp ≤ S) (hB : M.nQ + S + 2 + M.nG ^ (S + 2) ≤ B)
    (Q : St K → Prop)
    (h : ∀ σ' : St K, Rep M ρ S (M.δ st x (T wp)).1 ((M.δ st x (T wp)).2.2.1.move wp)
        (Function.update T wp (M.δ st x (T wp)).2.1) σ' →
      σ'.reg (ρ 6) = (if M.halt (M.δ st x (T wp)).1 then 0 else 1) →
      (∀ y, (∀ i, y ≠ ρ i) → σ'.reg y = σ.reg y) → σ'.pos = σ.pos → σ'.out = σ.out →
      Ach w B (inMv x (M.δ st x (T wp)).2.2.2.1 ⨟ outAct (M.δ st x (T wp)).2.2.2.2) σ' Q) :
    Ach w B (simStep M ρ inMv outAct) σ Q := by
  obtain ⟨h0, h1, hwp, h2, h3⟩ := hRep
  have hG := M.nG_pos
  have hpow : ∀ n, n ≤ S + 2 → M.nG ^ n ≤ M.nG ^ (S + 2) := fun n hn =>
    Nat.pow_le_pow_right hG hn
  have ne : ∀ i j : Fin 8, i ≠ j → ρ i ≠ ρ j := fun i j h => hρ.ne h
  have hR := encR_lt M T (S + 1 - wp) wp
  have eR : encR M T wp (S + 1 - wp) = M.gc (T wp) + M.nG * encR M T (wp + 1) (S - wp) := by
    rw [show S + 1 - wp = (S - wp) + 1 by omega, encR]
  have hdiv : encR M T wp (S + 1 - wp) / M.nG = encR M T (wp + 1) (S - wp) := by
    rw [eR, Nat.add_mul_div_left _ _ hG, Nat.div_eq_of_lt (M.gc_lt _)]; simp
  have hmod : encR M T wp (S + 1 - wp) % M.nG = M.gc (T wp) := by
    rw [eR, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (M.gc_lt _)]
  unfold simStep
  refine ach_seq (ach_divMod _ _ _ (ne 3 5 (by decide)) (ne 3 4 (by decide)) (ne 5 4 (by decide))
    _ hG _ _ (by rw [h3]; have := hpow (S + 1 - wp) (by omega); omega) ?_)
  rw [h3, hdiv, hmod]
  refine ach_seq (ach_addTo _ _ (ne 5 3 (by decide)) _ _ ?_ ?_)
  · simp [St.setReg_apply, hρ.eq_iff]
    have := encR_lt M T (S - wp) (wp + 1)
    have := hpow (S - wp) (by omega)
    omega
  refine ach_caseReg _ _ (M.eQ st) (by simp) _
    (by simp [St.setReg_apply, hρ.eq_iff, h0]) _ ?_
  simp only [List.getElem_ofFn]
  refine ach_caseReg _ _ (symCode x) (by simp [symCode_lt]) _
    (by simp [St.setReg_apply, hρ.eq_iff, hs]) _ ?_
  simp only [List.getElem_ofFn]
  refine ach_caseReg _ _ (M.gc (T wp)) (by simp [M.gc_lt]) _
    (by simp [St.setReg_apply, hρ.eq_iff]) _ ?_
  simp only [List.getElem_ofFn]
  rw [show act M ρ inMv outAct (M.eQ.symm ⟨↑(M.eQ st), _⟩) (symOf ⟨symCode x, _⟩)
      (M.eG.symm ⟨M.gc (T wp), _⟩) = act M ρ inMv outAct st x (T wp) by
    simp [TM.gc, symOf_symCode]]
  unfold act
  set q' := (M.δ st x (T wp)).1
  refine ach_seq (ach_setC _ _ _ _ (by have := M.eQ_lt q'; omega) ?_)
  refine ach_seq (ach_setC _ _ _ _ (by split_ifs <;> omega) ?_)
  refine ach_seq (Ach.mono (ach_tapeAct M ρ hρ S _ _ wp T _ hwp hwp' (by omega) ?_ ?_ ?_) ?_)
  · simp [St.setReg_apply, hρ.eq_iff, h1]
  · simp [St.setReg_apply, hρ.eq_iff, h2]
  · simp [St.setReg_apply, hρ.eq_iff]
  rintro σ' ⟨hp, ho, g1, g2, g3, gfr⟩
  refine h σ' ⟨?_, g1, hwp', g2, g3⟩ ?_ ?_ (by simpa using hp) (by simpa using ho)
  · rw [gfr _ (ne 0 1 (by decide)) (ne 0 2 (by decide)) (ne 0 3 (by decide))
      (ne 0 4 (by decide)) (ne 0 5 (by decide))]
    simp [St.setReg_apply, hρ.eq_iff]
  · rw [gfr _ (ne 6 1 (by decide)) (ne 6 2 (by decide)) (ne 6 3 (by decide))
      (ne 6 4 (by decide)) (ne 6 5 (by decide))]
    simp [St.setReg_apply, hρ.eq_iff]
  · intro y hy
    rw [gfr _ (hy 1) (hy 2) (hy 3) (hy 4) (hy 5)]
    simp [St.setReg_apply, hy 0, hy 3, hy 4, hy 5, hy 6, hy 7]

end Correct

end LS

end PathChecking
