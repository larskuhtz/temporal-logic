module

public import RequestProject.PHard.Ops

/-!
# Arithmetic and boolean expressions over registers

Programs with 64 registers. `AE` are arithmetic expressions over registers (addressed by
natural numbers `< 64`) and constants, with `+`, truncated `-`, `*`, `/`, `%`. `evalTo e dst d`
computes the value of `e` into register `dst`, using the registers `d, d+1, …` as
temporaries. `ifB c s t d` branches on a boolean combination `c` of equalities and
comparisons of arithmetic expressions.
-/

@[expose] public section

namespace PathChecking

namespace LS

open scoped LS

variable {w : Word} {B : ℕ}

/-- Register number `i` (for `i < 64`). -/
def R (i : ℕ) : Fin 64 := ⟨i % 64, Nat.mod_lt _ (by norm_num)⟩

lemma R_val {i : ℕ} (h : i < 64) : (R i).val = i := Nat.mod_eq_of_lt h

lemma R_ne {i j : ℕ} (hi : i < 64) (hj : j < 64) (h : i ≠ j) : R i ≠ R j := by
  intro e; apply h; rw [← R_val hi, ← R_val hj, e]

/-- Arithmetic expressions. -/
inductive AE
  | reg (i : ℕ)
  | const (k : ℕ)
  | add (a b : AE)
  | sub (a b : AE)
  | mul (a b : AE)
  | div (a b : AE)
  | mod (a b : AE)

namespace AE

/-- Value of an expression. -/
def eval (ρ : Fin 64 → ℕ) : AE → ℕ
  | reg i => ρ (R i)
  | const k => k
  | add a b => a.eval ρ + b.eval ρ
  | sub a b => a.eval ρ - b.eval ρ
  | mul a b => a.eval ρ * b.eval ρ
  | div a b => a.eval ρ / b.eval ρ
  | mod a b => a.eval ρ % b.eval ρ

/-- Height. -/
def ht : AE → ℕ
  | reg _ => 0
  | const _ => 0
  | add a b => max a.ht b.ht + 1
  | sub a b => max a.ht b.ht + 1
  | mul a b => max a.ht b.ht + 1
  | div a b => max a.ht b.ht + 1
  | mod a b => max a.ht b.ht + 1

/-- All registers are below `d`. -/
def RL (d : ℕ) : AE → Prop
  | reg i => i < d
  | const _ => True
  | add a b => a.RL d ∧ b.RL d
  | sub a b => a.RL d ∧ b.RL d
  | mul a b => a.RL d ∧ b.RL d
  | div a b => a.RL d ∧ b.RL d
  | mod a b => a.RL d ∧ b.RL d

/-- All intermediate values are `≤ B` (and divisors are nonzero). -/
def Bnd (ρ : Fin 64 → ℕ) (B : ℕ) : AE → Prop
  | reg i => ρ (R i) ≤ B
  | const k => k ≤ B
  | add a b => a.Bnd ρ B ∧ b.Bnd ρ B ∧ a.eval ρ + b.eval ρ ≤ B
  | sub a b => a.Bnd ρ B ∧ b.Bnd ρ B
  | mul a b => a.Bnd ρ B ∧ b.Bnd ρ B ∧ a.eval ρ * b.eval ρ ≤ B
  | div a b => a.Bnd ρ B ∧ b.Bnd ρ B ∧ b.eval ρ ≠ 0
  | mod a b => a.Bnd ρ B ∧ b.Bnd ρ B ∧ b.eval ρ ≠ 0

lemma eval_le {ρ : Fin 64 → ℕ} {B : ℕ} : ∀ {e : AE}, e.Bnd ρ B → e.eval ρ ≤ B
  | reg _, h => h
  | const _, h => h
  | add _ _, h => h.2.2
  | sub a _, h => le_trans (Nat.sub_le _ _) (eval_le (e := a) h.1)
  | mul _ _, h => h.2.2
  | div a _, h => le_trans (Nat.div_le_self _ _) (eval_le (e := a) h.1)
  | mod a _, h => le_trans (Nat.mod_le _ _) (eval_le (e := a) h.1)

lemma eval_congr {ρ ρ' : Fin 64 → ℕ} {d : ℕ} (hρ : ∀ x : Fin 64, x.val < d → ρ' x = ρ x) :
    ∀ {e : AE}, e.RL d → e.eval ρ' = e.eval ρ
  | reg i, h => hρ _ (lt_of_le_of_lt (Nat.mod_le _ _) h)
  | const _, _ => rfl
  | add a b, h => by simp only [eval, eval_congr hρ (e := a) h.1, eval_congr hρ (e := b) h.2]
  | sub a b, h => by simp only [eval, eval_congr hρ (e := a) h.1, eval_congr hρ (e := b) h.2]
  | mul a b, h => by simp only [eval, eval_congr hρ (e := a) h.1, eval_congr hρ (e := b) h.2]
  | div a b, h => by simp only [eval, eval_congr hρ (e := a) h.1, eval_congr hρ (e := b) h.2]
  | mod a b, h => by simp only [eval, eval_congr hρ (e := a) h.1, eval_congr hρ (e := b) h.2]

lemma Bnd_congr {ρ ρ' : Fin 64 → ℕ} {d B : ℕ} (hρ : ∀ x : Fin 64, x.val < d → ρ' x = ρ x) :
    ∀ {e : AE}, e.RL d → e.Bnd ρ B → e.Bnd ρ' B
  | reg i, h, hb => by
      simp only [Bnd] at hb ⊢; rw [hρ _ (lt_of_le_of_lt (Nat.mod_le _ _) h)]; exact hb
  | const _, _, hb => hb
  | add a b, h, hb => ⟨Bnd_congr hρ h.1 hb.1, Bnd_congr hρ h.2 hb.2.1, by
      rw [eval_congr hρ h.1, eval_congr hρ h.2]; exact hb.2.2⟩
  | sub a b, h, hb => ⟨Bnd_congr hρ h.1 hb.1, Bnd_congr hρ h.2 hb.2⟩
  | mul a b, h, hb => ⟨Bnd_congr hρ h.1 hb.1, Bnd_congr hρ h.2 hb.2.1, by
      rw [eval_congr hρ h.1, eval_congr hρ h.2]; exact hb.2.2⟩
  | div a b, h, hb => ⟨Bnd_congr hρ h.1 hb.1, Bnd_congr hρ h.2 hb.2.1, by
      rw [eval_congr hρ h.2]; exact hb.2.2⟩
  | mod a b, h, hb => ⟨Bnd_congr hρ h.1 hb.1, Bnd_congr hρ h.2 hb.2.1, by
      rw [eval_congr hρ h.2]; exact hb.2.2⟩

lemma RL_mono {d d' : ℕ} (hd : d ≤ d') : ∀ {e : AE}, e.RL d → e.RL d'
  | reg _, h => lt_of_lt_of_le h hd
  | const _, _ => trivial
  | add _ _, h => ⟨RL_mono hd h.1, RL_mono hd h.2⟩
  | sub _ _, h => ⟨RL_mono hd h.1, RL_mono hd h.2⟩
  | mul _ _, h => ⟨RL_mono hd h.1, RL_mono hd h.2⟩
  | div _ _, h => ⟨RL_mono hd h.1, RL_mono hd h.2⟩
  | mod _ _, h => ⟨RL_mono hd h.1, RL_mono hd h.2⟩

end AE

/-- Compute `e` into register `dst`, with temporaries `d, d+1, …`. -/
def evalTo : AE → ℕ → ℕ → Stmt 64
  | .reg i, dst, d => if i = dst then .skip else copy (R i) (R dst) (R d)
  | .const k, dst, _ => setC (R dst) k
  | .add a b, dst, d => evalTo a d (d + 2) ⨟ evalTo b (d + 1) (d + 2) ⨟ opAdd (R d) (R (d + 1)) (R dst)
  | .sub a b, dst, d => evalTo a d (d + 2) ⨟ evalTo b (d + 1) (d + 2) ⨟ opSub (R d) (R (d + 1)) (R dst)
  | .mul a b, dst, d => evalTo a d (d + 2) ⨟ evalTo b (d + 1) (d + 2) ⨟
      opMul (R d) (R (d + 1)) (R dst) (R (d + 2)) (R (d + 3))
  | .div a b, dst, d => evalTo a d (d + 2) ⨟ evalTo b (d + 1) (d + 2) ⨟
      divModR (R d) (R (d + 1)) (R dst) (R (d + 2)) (R (d + 3)) (R (d + 4))
  | .mod a b, dst, d => evalTo a d (d + 2) ⨟ evalTo b (d + 1) (d + 2) ⨟
      divModR (R d) (R (d + 1)) (R (d + 2)) (R dst) (R (d + 3)) (R (d + 4))

/-- The registers below `d` (except possibly `dst`) are unchanged. -/
def Keep (d dst : ℕ) (σ τ : St 64) : Prop :=
  ∀ x : Fin 64, x.val < d → x ≠ R dst → τ.reg x = σ.reg x

lemma frame_keep {S : List (Fin 64)} {σ τ : St 64} {d dst : ℕ} (h : RegFrame S σ τ)
    (hS : ∀ z ∈ S, z.val < d → z = R dst) : Keep d dst σ τ := by
  intro x hx hne
  exact h x (fun hm => hne (hS x hm hx))

lemma R_eq_iff {i : ℕ} (hi : i < 64) (x : Fin 64) : x = R i ↔ x.val = i := by
  constructor
  · rintro rfl; exact R_val hi
  · intro h; ext; rw [h, R_val hi]

lemma ne_R {x : Fin 64} {i d : ℕ} (hx : x.val < d) (hi : d ≤ i) (h64 : i < 64) : x ≠ R i := by
  rw [Ne, R_eq_iff h64]; omega

macro "nm_tac" : tactic => `(tactic| (
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  (repeat' apply And.intro) <;>
    first | assumption | exact ne_R (by assumption) (by omega) (by omega)))

/-- The common part of binary operations: compute both operands. -/
lemma ach_bin {a b : AE} {d : ℕ} {op : Stmt 64} {σ : St 64} {Q : St 64 → Prop}
    (iha : ∀ (dst d : ℕ) (σ : St 64) (Q : St 64 → Prop), dst < d → a.RL d →
      d + 2 * a.ht + 5 ≤ 64 → a.Bnd σ.reg B →
      (∀ τ : St 64, τ.out = σ.out → τ.pos = σ.pos → τ.reg (R dst) = a.eval σ.reg →
        Keep d dst σ τ → Q τ) → Ach w B (evalTo a dst d) σ Q)
    (ihb : ∀ (dst d : ℕ) (σ : St 64) (Q : St 64 → Prop), dst < d → b.RL d →
      d + 2 * b.ht + 5 ≤ 64 → b.Bnd σ.reg B →
      (∀ τ : St 64, τ.out = σ.out → τ.pos = σ.pos → τ.reg (R dst) = b.eval σ.reg →
        Keep d dst σ τ → Q τ) → Ach w B (evalTo b dst d) σ Q)
    (hRa : a.RL d) (hRb : b.RL d) (hK : d + 2 * (max a.ht b.ht + 1) + 5 ≤ 64)
    (hBa : a.Bnd σ.reg B) (hBb : b.Bnd σ.reg B)
    (hop : ∀ τ₂ : St 64, τ₂.out = σ.out → τ₂.pos = σ.pos → τ₂.reg (R d) = a.eval σ.reg →
      τ₂.reg (R (d + 1)) = b.eval σ.reg → (∀ x : Fin 64, x.val < d → τ₂.reg x = σ.reg x) →
      Ach w B op τ₂ Q) :
    Ach w B (evalTo a d (d + 2) ⨟ evalTo b (d + 1) (d + 2) ⨟ op) σ Q := by
  refine ach_seq (iha d (d + 2) σ _ (by omega) (AE.RL_mono (by omega) hRa) (by omega) hBa ?_)
  intro τ₁ ho1 hp1 hv1 hk1
  have hk1' : ∀ x : Fin 64, x.val < d + 1 → τ₁.reg x = σ.reg x ∨ x = R d := by
    intro x hx
    by_cases hxd : x = R d
    · exact Or.inr hxd
    · exact Or.inl (hk1 x (by omega) hxd)
  have hρ : ∀ x : Fin 64, x.val < d → τ₁.reg x = σ.reg x := by
    intro x hx
    exact hk1 x (by omega) (by rw [Ne, R_eq_iff (by omega)]; omega)
  refine ach_seq (ihb (d + 1) (d + 2) τ₁ _ (by omega) (AE.RL_mono (by omega) hRb) (by omega)
    (AE.Bnd_congr hρ hRb hBb) ?_)
  intro τ₂ ho2 hp2 hv2 hk2
  refine hop τ₂ (by rw [ho2, ho1]) (by rw [hp2, hp1]) ?_ ?_ ?_
  · rw [hk2 _ (by rw [R_val (by omega)]; omega) (R_ne (by omega) (by omega) (by omega)), hv1]
  · rw [hv2]; exact AE.eval_congr hρ hRb
  · intro x hx
    rw [hk2 x (by omega) (by rw [Ne, R_eq_iff (by omega)]; omega), hρ x hx]

theorem ach_comp (e : AE) : ∀ (dst d : ℕ) (σ : St 64) (Q : St 64 → Prop), dst < d → e.RL d →
    d + 2 * e.ht + 5 ≤ 64 → e.Bnd σ.reg B →
    (∀ τ : St 64, τ.out = σ.out → τ.pos = σ.pos → τ.reg (R dst) = e.eval σ.reg →
      Keep d dst σ τ → Q τ) → Ach w B (evalTo e dst d) σ Q := by
  induction e with
  | reg i =>
    intro dst d σ Q hdst hRL hK hB h
    simp only [AE.RL] at hRL
    simp only [evalTo]
    by_cases hi : i = dst
    · subst hi; rw [if_pos rfl]
      exact ach_skip (h σ rfl rfl rfl (fun _ _ _ => rfl))
    · rw [if_neg hi]
      refine ach_copy _ _ _ (R_ne (by omega) (by omega) hi) (R_ne (by omega) (by omega) (by omega))
        (R_ne (by omega) (by omega) (by omega)) σ Q hB (h _ rfl rfl ?_ ?_)
      · simp [St.setReg_apply, R_ne (by omega) (by omega) (show dst ≠ d by omega), AE.eval]
      · intro x hx hne
        have : x ≠ R d := by rw [Ne, R_eq_iff (by omega)]; omega
        simp [St.setReg_apply, hne, this]
  | const k =>
    intro dst d σ Q hdst hRL hK hB h
    simp only [evalTo]
    refine ach_setC _ _ σ Q hB (h _ rfl rfl (by simp [St.setReg_apply, AE.eval]) ?_)
    intro x hx hne; simp [St.setReg_apply, hne]
  | add a b iha ihb =>
    intro dst d σ Q hdst hRL hK hB h
    simp only [AE.ht] at hK
    refine ach_bin iha ihb hRL.1 hRL.2 hK hB.1 hB.2.1 ?_
    intro τ₂ ho2 hp2 ea eb hk
    refine ach_opAdd _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) τ₂ Q
      (by rw [ea, eb]; exact hB.2.2) (fun τ ho hp hv hf => h τ (by rw [ho, ho2])
        (by rw [hp, hp2]) (by rw [hv, ea, eb]; rfl) ?_)
    intro x hx hne
    rw [hf x (by nm_tac), hk x hx]
  | sub a b iha ihb =>
    intro dst d σ Q hdst hRL hK hB h
    simp only [AE.ht] at hK
    refine ach_bin iha ihb hRL.1 hRL.2 hK hB.1 hB.2 ?_
    intro τ₂ ho2 hp2 ea eb hk
    refine ach_opSub _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) τ₂ Q
      (by rw [ea]; exact AE.eval_le hB.1) (fun τ ho hp hv hf => h τ (by rw [ho, ho2])
        (by rw [hp, hp2]) (by rw [hv, ea, eb]; rfl) ?_)
    intro x hx hne
    rw [hf x (by nm_tac), hk x hx]
  | mul a b iha ihb =>
    intro dst d σ Q hdst hRL hK hB h
    simp only [AE.ht] at hK
    refine ach_bin iha ihb hRL.1 hRL.2 hK hB.1 hB.2.1 ?_
    intro τ₂ ho2 hp2 ea eb hk
    refine ach_opMul _ _ _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) τ₂ Q
      (by rw [ea, eb]; exact hB.2.2) (by rw [eb]; exact AE.eval_le hB.2.1)
      (fun τ ho hp hv hf => h τ (by rw [ho, ho2]) (by rw [hp, hp2]) (by rw [hv, ea, eb]; rfl) ?_)
    intro x hx hne
    rw [hf x (by nm_tac), hk x hx]
  | div a b iha ihb =>
    intro dst d σ Q hdst hRL hK hB h
    simp only [AE.ht] at hK
    refine ach_bin iha ihb hRL.1 hRL.2 hK hB.1 hB.2.1 ?_
    intro τ₂ ho2 hp2 ea eb hk
    refine ach_divModR _ _ _ _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) τ₂ Q
      (by rw [ea]; exact AE.eval_le hB.1) (by rw [eb]; exact AE.eval_le hB.2.1)
      (by rw [eb]; have := hB.2.2; omega)
      (fun τ ho hp hv _ hf => h τ (by rw [ho, ho2]) (by rw [hp, hp2]) (by rw [hv, ea, eb]; rfl) ?_)
    intro x hx hne
    rw [hf x (by nm_tac), hk x hx]
  | mod a b iha ihb =>
    intro dst d σ Q hdst hRL hK hB h
    simp only [AE.ht] at hK
    refine ach_bin iha ihb hRL.1 hRL.2 hK hB.1 hB.2.1 ?_
    intro τ₂ ho2 hp2 ea eb hk
    refine ach_divModR _ _ _ _ _ _ (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) τ₂ Q
      (by rw [ea]; exact AE.eval_le hB.1) (by rw [eb]; exact AE.eval_le hB.2.1)
      (by rw [eb]; have := hB.2.2; omega)
      (fun τ ho hp _ hv hf => h τ (by rw [ho, ho2]) (by rw [hp, hp2]) (by rw [hv, ea, eb]; rfl) ?_)
    intro x hx hne
    rw [hf x (by nm_tac), hk x hx]

/-! ## Boolean conditions -/

/-- Boolean combinations of equalities and comparisons. -/
inductive BE
  | eq (a b : AE)
  | lt (a b : AE)
  | and (p q : BE)
  | or (p q : BE)
  | not (p : BE)
  | tt
  | ff

namespace BE

/-- Truth value. -/
def eval (ρ : Fin 64 → ℕ) : BE → Prop
  | eq a b => a.eval ρ = b.eval ρ
  | lt a b => a.eval ρ < b.eval ρ
  | and p q => p.eval ρ ∧ q.eval ρ
  | or p q => p.eval ρ ∨ q.eval ρ
  | not p => ¬ p.eval ρ
  | tt => True
  | ff => False

/-- Height. -/
def ht : BE → ℕ
  | eq a b => max a.ht b.ht
  | lt a b => max a.ht b.ht
  | and p q => max p.ht q.ht
  | or p q => max p.ht q.ht
  | not p => p.ht
  | tt => 0
  | ff => 0

/-- All registers are below `d`. -/
def RL (d : ℕ) : BE → Prop
  | eq a b => a.RL d ∧ b.RL d
  | lt a b => a.RL d ∧ b.RL d
  | and p q => p.RL d ∧ q.RL d
  | or p q => p.RL d ∧ q.RL d
  | not p => p.RL d
  | tt => True
  | ff => True

/-- Bounds on intermediate values. -/
def Bnd (ρ : Fin 64 → ℕ) (B : ℕ) : BE → Prop
  | eq a b => a.Bnd ρ B ∧ b.Bnd ρ B
  | lt a b => a.Bnd ρ B ∧ b.Bnd ρ B
  | and p q => p.Bnd ρ B ∧ q.Bnd ρ B
  | or p q => p.Bnd ρ B ∧ q.Bnd ρ B
  | not p => p.Bnd ρ B
  | tt => True
  | ff => True

lemma eval_congr {ρ ρ' : Fin 64 → ℕ} {d : ℕ} (hρ : ∀ x : Fin 64, x.val < d → ρ' x = ρ x) :
    ∀ {c : BE}, c.RL d → (c.eval ρ' ↔ c.eval ρ)
  | eq a b, h => by simp only [eval, AE.eval_congr hρ h.1, AE.eval_congr hρ h.2]
  | lt a b, h => by simp only [eval, AE.eval_congr hρ h.1, AE.eval_congr hρ h.2]
  | and p q, h => by simp only [eval, eval_congr hρ (c := p) h.1, eval_congr hρ (c := q) h.2]
  | or p q, h => by simp only [eval, eval_congr hρ (c := p) h.1, eval_congr hρ (c := q) h.2]
  | not p, h => by simp only [eval, eval_congr hρ (c := p) h]
  | tt, _ => Iff.rfl
  | ff, _ => Iff.rfl

lemma Bnd_congr {ρ ρ' : Fin 64 → ℕ} {d B : ℕ} (hρ : ∀ x : Fin 64, x.val < d → ρ' x = ρ x) :
    ∀ {c : BE}, c.RL d → c.Bnd ρ B → c.Bnd ρ' B
  | eq _ _, h, hb => ⟨AE.Bnd_congr hρ h.1 hb.1, AE.Bnd_congr hρ h.2 hb.2⟩
  | lt _ _, h, hb => ⟨AE.Bnd_congr hρ h.1 hb.1, AE.Bnd_congr hρ h.2 hb.2⟩
  | and _ _, h, hb => ⟨Bnd_congr hρ h.1 hb.1, Bnd_congr hρ h.2 hb.2⟩
  | or _ _, h, hb => ⟨Bnd_congr hρ h.1 hb.1, Bnd_congr hρ h.2 hb.2⟩
  | not p, h, hb => Bnd_congr hρ (c := p) h hb
  | tt, _, _ => trivial
  | ff, _, _ => trivial

end BE

/-- Branch on a condition, using temporaries `d, d+1, …`. -/
def ifB : BE → Stmt 64 → Stmt 64 → ℕ → Stmt 64
  | .eq a b, s, t, d => evalTo (.add (.sub a b) (.sub b a)) d (d + 1) ⨟ .ite (.zero (R d)) s t
  | .lt a b, s, t, d => evalTo (.sub b a) d (d + 1) ⨟ .ite (.zero (R d)) t s
  | .and p q, s, t, d => ifB p (ifB q s t d) t d
  | .or p q, s, t, d => ifB p s (ifB q s t d) d
  | .not p, s, t, d => ifB p t s d
  | .tt, s, _, _ => s
  | .ff, _, t, _ => t

/-- Output, head position and the registers below `d` agree. -/
def Agree (d : ℕ) (σ τ : St 64) : Prop :=
  τ.out = σ.out ∧ τ.pos = σ.pos ∧ ∀ x : Fin 64, x.val < d → τ.reg x = σ.reg x

lemma Agree.refl (d : ℕ) (σ : St 64) : Agree d σ σ := ⟨rfl, rfl, fun _ _ => rfl⟩

lemma Agree.trans {d : ℕ} {σ τ υ : St 64} (h1 : Agree d σ τ) (h2 : Agree d τ υ) : Agree d σ υ :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun x hx => (h2.2.2 x hx).trans (h1.2.2 x hx)⟩

theorem ach_ifB (c : BE) : ∀ (s t : Stmt 64) (d : ℕ) (σ : St 64) (Q : St 64 → Prop), c.RL d →
    d + 2 * c.ht + 10 ≤ 64 → c.Bnd σ.reg B →
    (c.eval σ.reg → ∀ τ, Agree d σ τ → Ach w B s τ Q) →
    (¬ c.eval σ.reg → ∀ τ, Agree d σ τ → Ach w B t τ Q) → Ach w B (ifB c s t d) σ Q := by
  induction c with
  | eq a b =>
    intro s t d σ Q hRL hK hB hs ht
    simp only [BE.ht] at hK
    refine ach_seq (ach_comp _ d (d + 1) σ _ (by omega) ⟨⟨AE.RL_mono (by omega) hRL.1,
      AE.RL_mono (by omega) hRL.2⟩, ⟨AE.RL_mono (by omega) hRL.2, AE.RL_mono (by omega) hRL.1⟩⟩
      (by simp only [AE.ht]; omega) ⟨⟨hB.1, hB.2⟩, ⟨hB.2, hB.1⟩, by
        simp only [AE.eval]; have := AE.eval_le hB.1; have := AE.eval_le hB.2; omega⟩ ?_)
    intro τ ho hp hv hk
    have hag : Agree d σ τ := ⟨ho, hp, fun x hx => hk x (by omega) (ne_R hx le_rfl (by omega))⟩
    refine ach_ite ?_
    simp only [Cond.eval, hv, AE.eval, decide_eq_true_eq]
    split_ifs with h0
    · exact hs (by simp only [BE.eval]; omega) τ hag
    · exact ht (by simp only [BE.eval]; omega) τ hag
  | lt a b =>
    intro s t d σ Q hRL hK hB hs ht
    simp only [BE.ht] at hK
    refine ach_seq (ach_comp _ d (d + 1) σ _ (by omega) ⟨AE.RL_mono (by omega) hRL.2,
      AE.RL_mono (by omega) hRL.1⟩ (by simp only [AE.ht]; omega) ⟨hB.2, hB.1⟩ ?_)
    intro τ ho hp hv hk
    have hag : Agree d σ τ := ⟨ho, hp, fun x hx => hk x (by omega) (ne_R hx le_rfl (by omega))⟩
    refine ach_ite ?_
    simp only [Cond.eval, hv, AE.eval, decide_eq_true_eq]
    split_ifs with h0
    · exact ht (by simp only [BE.eval]; omega) τ hag
    · exact hs (by simp only [BE.eval]; omega) τ hag
  | and p q ihp ihq =>
    intro s t d σ Q hRL hK hB hs ht
    simp only [BE.ht] at hK
    refine ihp _ _ d σ Q hRL.1 (by omega) hB.1 ?_ (fun hn τ hag => ht (fun h => hn h.1) τ hag)
    intro hpv τ hag
    refine ihq _ _ d τ Q hRL.2 (by omega) (BE.Bnd_congr hag.2.2 hRL.2 hB.2) ?_ ?_
    · intro hqv τ' hag'
      exact hs ⟨hpv, (BE.eval_congr hag.2.2 hRL.2).1 hqv⟩ τ' (hag.trans hag')
    · intro hqv τ' hag'
      exact ht (fun h => hqv ((BE.eval_congr hag.2.2 hRL.2).2 h.2)) τ' (hag.trans hag')
  | or p q ihp ihq =>
    intro s t d σ Q hRL hK hB hs ht
    simp only [BE.ht] at hK
    refine ihp _ _ d σ Q hRL.1 (by omega) hB.1 (fun h τ hag => hs (Or.inl h) τ hag) ?_
    intro hpv τ hag
    refine ihq _ _ d τ Q hRL.2 (by omega) (BE.Bnd_congr hag.2.2 hRL.2 hB.2) ?_ ?_
    · intro hqv τ' hag'
      exact hs (Or.inr ((BE.eval_congr hag.2.2 hRL.2).1 hqv)) τ' (hag.trans hag')
    · intro hqv τ' hag'
      exact ht (fun h => h.elim hpv (fun h => hqv ((BE.eval_congr hag.2.2 hRL.2).2 h))) τ'
        (hag.trans hag')
  | not p ihp =>
    intro s t d σ Q hRL hK hB hs ht
    simp only [BE.ht] at hK
    exact ihp _ _ d σ Q hRL hK hB (fun h τ hag => ht (fun h' => h' h) τ hag)
      (fun h τ hag => hs h τ hag)
  | tt =>
    intro s t d σ Q _ _ _ hs _
    exact hs trivial σ (Agree.refl d σ)
  | ff =>
    intro s t d σ Q _ _ _ _ ht
    exact ht (fun h => h) σ (Agree.refl d σ)

end LS

end PathChecking
