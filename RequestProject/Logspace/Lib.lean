module

public import RequestProject.Logspace.Prog

/-!
# A library of verified program fragments

Specifications are stated in weakest-precondition style: `Ach w B s σ Q` says that the
program `s`, started in state `σ` on input `w` with register bound `B`, terminates in some
state satisfying `Q`.
-/

@[expose] public section

namespace PathChecking

namespace LS

/-- Sequential composition. -/
scoped infixr:30 " ⨟ " => Stmt.seq

variable {K : ℕ} {w : Word} {B : ℕ}

/-- `s` started in `σ` terminates in a state satisfying `Q`. -/
def Ach (w : Word) (B : ℕ) (s : Stmt K) (σ : St K) (Q : St K → Prop) : Prop :=
  ∃ σ', Eval w B s σ σ' ∧ Q σ'

lemma Ach.mono {s : Stmt K} {σ : St K} {Q Q' : St K → Prop} (h : Ach w B s σ Q)
    (hQ : ∀ σ', Q σ' → Q' σ') : Ach w B s σ Q' := by
  obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', h1, hQ _ h2⟩

lemma ach_seq {s t : Stmt K} {σ : St K} {Q : St K → Prop}
    (h : Ach w B s σ (fun σ₁ => Ach w B t σ₁ Q)) : Ach w B (s ⨟ t) σ Q := by
  obtain ⟨σ₁, h1, σ₂, h2, hQ⟩ := h; exact ⟨σ₂, Eval.seq h1 h2, hQ⟩

lemma ach_skip {σ : St K} {Q : St K → Prop} (h : Q σ) : Ach w B .skip σ Q :=
  ⟨σ, Eval.skip σ, h⟩

lemma ach_inc {σ : St K} {r : Fin K} {Q : St K → Prop} (hr : σ.reg r < B)
    (h : Q (σ.setReg r (σ.reg r + 1))) : Ach w B (.inc r) σ Q :=
  ⟨_, Eval.inc σ r hr, h⟩

lemma ach_dec {σ : St K} {r : Fin K} {Q : St K → Prop}
    (h : Q (σ.setReg r (σ.reg r - 1))) : Ach w B (.dec r) σ Q :=
  ⟨_, Eval.dec σ r, h⟩

lemma ach_left {σ : St K} {Q : St K → Prop}
    (h : Q { σ with pos := σ.pos - 1 }) : Ach w B .left σ Q :=
  ⟨_, Eval.left σ, h⟩

lemma ach_right {σ : St K} {Q : St K → Prop}
    (h : Q { σ with pos := min (σ.pos + 1) (w.length + 1) }) : Ach w B .right σ Q :=
  ⟨_, Eval.right σ, h⟩

lemma ach_out {σ : St K} {b : Bool} {Q : St K → Prop}
    (h : Q { σ with out := σ.out ++ [b] }) : Ach w B (.out b) σ Q :=
  ⟨_, Eval.out σ b, h⟩

lemma ach_ite {c : Cond K} {s t : Stmt K} {σ : St K} {Q : St K → Prop}
    (h : if c.eval w σ then Ach w B s σ Q else Ach w B t σ Q) : Ach w B (.ite c s t) σ Q := by
  by_cases hc : c.eval w σ = true
  · rw [if_pos hc] at h; obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', Eval.iteT hc h1, h2⟩
  · rw [if_neg hc] at h; obtain ⟨σ', h1, h2⟩ := h
    exact ⟨σ', Eval.iteF (by simpa using hc) h1, h2⟩

lemma ach_iteT {c : Cond K} {s t : Stmt K} {σ : St K} {Q : St K → Prop}
    (hc : c.eval w σ = true) (h : Ach w B s σ Q) : Ach w B (.ite c s t) σ Q :=
  ach_ite (by rw [if_pos hc]; exact h)

lemma ach_iteF {c : Cond K} {s t : Stmt K} {σ : St K} {Q : St K → Prop}
    (hc : c.eval w σ = false) (h : Ach w B t σ Q) : Ach w B (.ite c s t) σ Q :=
  ach_ite (by rw [if_neg (by simp [hc])]; exact h)

/-- The loop rule, with a measure-indexed invariant. -/
lemma ach_loop {c : Cond K} {s : Stmt K} (I : ℕ → St K → Prop) (Q : St K → Prop)
    (h : ∀ n σ, I n σ → (c.eval w σ = false ∧ Q σ) ∨
      (c.eval w σ = true ∧ Ach w B s σ (fun σ' => ∃ m < n, I m σ'))) :
    ∀ n σ, I n σ → Ach w B (.loop c s) σ Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hI
    rcases h n σ hI with ⟨hc, hQ⟩ | ⟨hc, σ₁, h1, m, hm, hI'⟩
    · exact ⟨σ, Eval.loopF hc, hQ⟩
    · obtain ⟨σ₂, h2, hQ⟩ := ih m hm σ₁ hI'
      exact ⟨σ₂, Eval.loopT hc h1 h2, hQ⟩

/-! ## Register states -/

@[ext] lemma St.ext' {σ τ : St K} (h1 : σ.pos = τ.pos) (h2 : σ.reg = τ.reg)
    (h3 : σ.out = τ.out) : σ = τ := by
  cases σ; cases τ; simp_all

lemma St.setReg_apply (σ : St K) (r x : Fin K) (v : ℕ) :
    (σ.setReg r v).reg x = if x = r then v else σ.reg x := by
  simp [St.setReg, Function.update_apply]

/-- Close goals about register states built with `setReg`. -/
macro "st_tac" : tactic => `(tactic| (ext x <;> (try simp only [St.setReg, Function.update_apply]) <;>
  (try split_ifs) <;> (try simp_all) <;> (try omega)))

/-! ## Arithmetic -/

/-- `while r ≠ 0 do s`. -/
def whileNZ (r : Fin K) (s : Stmt K) : Stmt K := .loop (.not (.zero r)) s

lemma eval_nz (σ : St K) (r : Fin K) : (Cond.not (.zero r)).eval w σ = !decide (σ.reg r = 0) :=
  rfl

/-- `r := 0`. -/
def clear (r : Fin K) : Stmt K := whileNZ r (.dec r)

lemma ach_clear (r : Fin K) (σ : St K) (Q : St K → Prop) (h : Q (σ.setReg r 0)) :
    Ach w B (clear r) σ Q := by
  refine ach_loop (fun n τ => τ = σ.setReg r n) Q ?_ (σ.reg r) σ (by st_tac)
  intro n τ hτ
  subst hτ
  rcases n with _ | n
  · left; simp [Cond.eval, h]
  · right
    refine ⟨by simp [Cond.eval], ach_dec ⟨n, by omega, ?_⟩⟩
    st_tac

/-- `s := s + r; r := 0`. -/
def addTo (r s : Fin K) : Stmt K := whileNZ r (.dec r ⨟ .inc s)

lemma ach_addTo (r s : Fin K) (hrs : r ≠ s) (σ : St K) (Q : St K → Prop)
    (hB : σ.reg s + σ.reg r ≤ B) (h : Q ((σ.setReg r 0).setReg s (σ.reg s + σ.reg r))) :
    Ach w B (addTo r s) σ Q := by
  refine ach_loop (fun n τ => τ = (σ.setReg r n).setReg s (σ.reg s + (σ.reg r - n)) ∧
    n ≤ σ.reg r) Q ?_ (σ.reg r) σ ⟨by st_tac, le_rfl⟩
  intro n τ ⟨hτ, hn⟩
  subst hτ
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply, hrs], ?_⟩
    simpa using h
  · right
    have e1 : ((σ.setReg r (n + 1)).setReg s (σ.reg s + (σ.reg r - (n + 1)))).reg r = n + 1 := by
      simp [St.setReg_apply, hrs]
    refine ⟨by simp [Cond.eval, e1], ach_seq (ach_dec (ach_inc ?_ ⟨n, by omega, ?_, by omega⟩))⟩
    · simp [St.setReg_apply, hrs, Ne.symm hrs]; omega
    · st_tac

/-- `s := s + r; t := t + r; r := 0`. -/
def addTo2 (r s t : Fin K) : Stmt K := whileNZ r (.dec r ⨟ .inc s ⨟ .inc t)

lemma ach_addTo2 (r s t : Fin K) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (σ : St K)
    (Q : St K → Prop) (hB : σ.reg s + σ.reg r ≤ B) (hB' : σ.reg t + σ.reg r ≤ B)
    (h : Q (((σ.setReg r 0).setReg s (σ.reg s + σ.reg r)).setReg t (σ.reg t + σ.reg r))) :
    Ach w B (addTo2 r s t) σ Q := by
  refine ach_loop (fun n τ => τ = ((σ.setReg r n).setReg s (σ.reg s + (σ.reg r - n))).setReg t
    (σ.reg t + (σ.reg r - n)) ∧ n ≤ σ.reg r) Q ?_ (σ.reg r) σ ⟨by st_tac, le_rfl⟩
  intro n τ ⟨hτ, hn⟩
  subst hτ
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, St.setReg_apply, hrs, hrt], ?_⟩
    simpa using h
  · right
    have e1 : (((σ.setReg r (n + 1)).setReg s (σ.reg s + (σ.reg r - (n + 1)))).setReg t
        (σ.reg t + (σ.reg r - (n + 1)))).reg r = n + 1 := by
      simp [St.setReg_apply, hrs, hrt]
    refine ⟨by simp [Cond.eval, e1],
      ach_seq (ach_dec (ach_seq (ach_inc ?_ (ach_inc ?_ ⟨n, by omega, ?_, by omega⟩))))⟩
    · simp [St.setReg_apply, hrs, hst, Ne.symm hrs]; omega
    · simp [St.setReg_apply, hrt, hst, Ne.symm hst, Ne.symm hrt]; omega
    · st_tac

/-- `s := r` (using the temporary register `t`, which ends up `0`). -/
def copy (r s t : Fin K) : Stmt K := clear s ⨟ clear t ⨟ addTo2 r s t ⨟ addTo t r

lemma ach_copy (r s t : Fin K) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t) (σ : St K)
    (Q : St K → Prop) (hB : σ.reg r ≤ B) (h : Q ((σ.setReg s (σ.reg r)).setReg t 0)) :
    Ach w B (copy r s t) σ Q := by
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_clear _ _ _ (ach_seq (ach_addTo2 r s t hrs hrt
    hst _ _ ?_ ?_ (ach_addTo t r (Ne.symm hrt) _ _ ?_ ?_))))))
  · simp [St.setReg_apply, hrs, hrt]; omega
  · simp [St.setReg_apply, hrs, hrt]; omega
  · simp [St.setReg_apply, hrs, hrt, hst]; omega
  · convert h using 1
    st_tac

/-- `q := r / 2; b := r % 2; r := 0`. -/
def halve (r q b : Fin K) : Stmt K :=
  clear q ⨟ clear b ⨟ whileNZ r (.dec r ⨟ .ite (.zero r) (.inc b) (.dec r ⨟ .inc q))

lemma ach_halve (r q b : Fin K) (hrq : r ≠ q) (hrb : r ≠ b) (hqb : q ≠ b) (σ : St K)
    (Q : St K → Prop) (hB : σ.reg r / 2 ≤ B) (hB1 : 1 ≤ B)
    (h : Q (((σ.setReg r 0).setReg q (σ.reg r / 2)).setReg b (σ.reg r % 2))) :
    Ach w B (halve r q b) σ Q := by
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_clear _ _ _ ?_)))
  refine ach_loop (fun n τ => ∃ x y, τ = ((σ.setReg r n).setReg q x).setReg b y ∧
      2 * x + y + n = σ.reg r ∧ y ≤ 1 ∧ (y = 1 → n = 0)) Q ?_ (σ.reg r) _
    ⟨0, 0, by st_tac, by omega, by omega, by omega⟩
  intro n τ ⟨x, y, hτ, h1, h2, h3⟩
  subst hτ
  have er : ∀ m x y, (((σ.setReg r m).setReg q x).setReg b y).reg r = m := by
    intro m x y; simp [St.setReg_apply, hrq, hrb]
  rcases n with _ | n
  · left
    refine ⟨by simp [Cond.eval, er], ?_⟩
    have hx : x = σ.reg r / 2 := by omega
    have hy : y = σ.reg r % 2 := by omega
    subst hx hy; exact h
  · right
    have hy : y = 0 := by omega
    subst hy
    refine ⟨by simp [Cond.eval, er], ach_seq (ach_dec (ach_ite ?_))⟩
    rcases n with _ | n
    · rw [if_pos (by simp [Cond.eval, St.setReg_apply, hrq, hrb])]
      have hq : (((((σ.setReg r (0 + 1)).setReg q x).setReg b 0).setReg r
          ((((σ.setReg r (0 + 1)).setReg q x).setReg b 0).reg r - 1))).reg b < B := by
        simp [St.setReg_apply, hrb, Ne.symm hrb]; omega
      refine ach_inc hq ⟨0, by omega, x, 1, ?_, by omega, by omega, by omega⟩
      st_tac
    · rw [if_neg (by simp [Cond.eval, St.setReg_apply, hrq, hrb])]
      refine ach_seq (ach_dec (ach_inc ?_ ⟨n, by omega, x + 1, 0, ?_, by omega, by omega,
        by omega⟩))
      · simp [St.setReg_apply, hrq, hqb, Ne.symm hrq]; omega
      · st_tac

end LS

end PathChecking
