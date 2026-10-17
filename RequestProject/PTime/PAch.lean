module

public import RequestProject.PTime.Main
public import RequestProject.PTime.LSOps

/-!
# Weakest-precondition reasoning for programs with memory
-/

@[expose] public section

namespace PathChecking

namespace PT

open LS

variable {K : ℕ} {w : Word} {B : ℕ}

/-- `s` started in `σ` terminates in a state satisfying `Q`. -/
def PAch (w : Word) (B : ℕ) (s : PStmt K) (σ : PSt K) (Q : PSt K → Prop) : Prop :=
  ∃ σ', PEval w B s σ σ' ∧ Q σ'

lemma PAch.mono {s : PStmt K} {σ : PSt K} {Q Q' : PSt K → Prop} (h : PAch w B s σ Q)
    (hQ : ∀ σ', Q σ' → Q' σ') : PAch w B s σ Q' := by
  obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', h1, hQ _ h2⟩

lemma pach_seq {s t : PStmt K} {σ : PSt K} {Q : PSt K → Prop}
    (h : PAch w B s σ (fun σ₁ => PAch w B t σ₁ Q)) : PAch w B (.seq s t) σ Q := by
  obtain ⟨σ₁, h1, σ₂, h2, hQ⟩ := h; exact ⟨σ₂, PEval.seq h1 h2, hQ⟩

lemma pach_skip {σ : PSt K} {Q : PSt K → Prop} (h : Q σ) : PAch w B .skip σ Q :=
  ⟨σ, PEval.skip σ, h⟩

lemma pach_ite {c : PCond K} {s t : PStmt K} {σ : PSt K} {Q : PSt K → Prop}
    (h : if c.eval w σ then PAch w B s σ Q else PAch w B t σ Q) : PAch w B (.ite c s t) σ Q := by
  by_cases hc : c.eval w σ = true
  · rw [if_pos hc] at h; obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', PEval.iteT hc h1, h2⟩
  · rw [if_neg hc] at h; obtain ⟨σ', h1, h2⟩ := h
    exact ⟨σ', PEval.iteF (by simpa using hc) h1, h2⟩

lemma pach_loop {c : PCond K} {s : PStmt K} (I : ℕ → PSt K → Prop) (Q : PSt K → Prop)
    (h : ∀ n σ, I n σ → (c.eval w σ = false ∧ Q σ) ∨
      (c.eval w σ = true ∧ PAch w B s σ (fun σ' => ∃ k < n, I k σ'))) :
    ∀ n σ, I n σ → PAch w B (.loop c s) σ Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hI
    rcases h n σ hI with ⟨hc, hQ⟩ | ⟨hc, σ₁, h1, k, hk, hI'⟩
    · exact ⟨σ, PEval.loopF hc, hQ⟩
    · obtain ⟨σ₂, h2, hQ⟩ := ih k hk σ₁ hI'
      exact ⟨σ₂, PEval.loopT hc h1 h2, hQ⟩

/-- Embedded register programs. -/
lemma pach_lift {s : Stmt K} {σ : PSt K} {Q : PSt K → Prop}
    (h : Ach w B s σ.base (fun b => Q ⟨b, σ.cur, σ.mem⟩)) : PAch w B s.lift σ Q := by
  obtain ⟨b, hb, hQ⟩ := h
  exact ⟨_, peval_lift hb σ.cur σ.mem, hQ⟩

lemma pach_mset {σ : PSt K} {Q : PSt K → Prop} (h : Q { σ with mem := insert σ.cur σ.mem }) :
    PAch w B .mset σ Q := ⟨_, PEval.mset σ, h⟩

/-- Move the cursor right by the value of `r` (which is consumed). -/
def curR (r : Fin K) : PStmt K := .loop (.not (.zero r)) (.seq (.dec r) .cr)

/-- Move the cursor left by the value of `r` (which is consumed). -/
def curL (r : Fin K) : PStmt K := .loop (.not (.zero r)) (.seq (.dec r) .cl)

lemma pach_curR (r : Fin K) (σ : PSt K) (Q : PSt K → Prop) (hB : σ.cur + σ.base.reg r ≤ B)
    (h : ∀ τ : PSt K, τ.base = σ.base.setReg r 0 → τ.cur = σ.cur + σ.base.reg r →
      τ.mem = σ.mem → Q τ) : PAch w B (curR r) σ Q := by
  refine pach_loop (fun n τ => τ.base = σ.base.setReg r n ∧ τ.cur = σ.cur + (σ.base.reg r - n) ∧
    τ.mem = σ.mem ∧ n ≤ σ.base.reg r) Q ?_ (σ.base.reg r) σ ⟨by simp, by simp, rfl, le_rfl⟩
  intro n τ ⟨h1, h2, h3, h4⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [PCond.eval, h1], h τ h1 (by rw [h2]; simp) h3⟩
  · right
    refine ⟨by simp [PCond.eval, h1], ⟨_, PEval.seq (PEval.dec τ r) (PEval.cr _ ?_), n, by omega,
      ?_, ?_, ?_, by omega⟩⟩
    · simp only; omega
    · simp only [h1]; simp
    · simp only; omega
    · simpa using h3

lemma pach_curL (r : Fin K) (σ : PSt K) (Q : PSt K → Prop)
    (h : ∀ τ : PSt K, τ.base = σ.base.setReg r 0 → τ.cur = σ.cur - σ.base.reg r →
      τ.mem = σ.mem → Q τ) : PAch w B (curL r) σ Q := by
  refine pach_loop (fun n τ => τ.base = σ.base.setReg r n ∧ τ.cur = σ.cur - (σ.base.reg r - n) ∧
    τ.mem = σ.mem ∧ n ≤ σ.base.reg r) Q ?_ (σ.base.reg r) σ ⟨by simp, by simp, rfl, le_rfl⟩
  intro n τ ⟨h1, h2, h3, h4⟩
  rcases n with _ | n
  · left
    refine ⟨by simp [PCond.eval, h1], h τ h1 (by rw [h2]; simp) h3⟩
  · right
    refine ⟨by simp [PCond.eval, h1], ⟨_, PEval.seq (PEval.dec τ r) (PEval.cl _), n, by omega,
      ?_, ?_, ?_, by omega⟩⟩
    · simp only [h1]; simp
    · simp only; omega
    · simpa using h3

end PT

end PathChecking
