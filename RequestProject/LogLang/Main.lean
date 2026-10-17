module

public import RequestProject.LogLang.CompileP
public import RequestProject.Logspace.Machine

/-!
# Programs of the loop language compute logspace functions

`logspaceComputable_of_output`: if a program `P` of the loop language (with cap exponent `E`)
outputs `f w` on every input `w`, then `f` is logspace computable.
-/

@[expose] public section

namespace PathChecking

namespace LL

open LS
open scoped LS

/-- `s` repeated `k` times. -/
def rep {K : ℕ} (s : Stmt K) : ℕ → Stmt K
  | 0 => .skip
  | k + 1 => s ⨟ rep s k

/-- One multiplication step of `initCap`: `T := T * V`. -/
def mulStep (K V T : ℕ) : Stmt (K + 1) :=
  clear (R K (T + 1)) ⨟ mulR (R K T) (R K V) (R K (T + 1)) (R K (T + 2)) ⨟
    addTo (R K (T + 1)) (R K T)

/-- Initialisation: register `V` := `(|w| + 2)^E + 3` (scratch registers `T, T+1, T+2`). -/
def initCap (K V T E : ℕ) : Stmt (K + 1) :=
  lenR (R K V) ⨟ addConst (R K V) 2 ⨟ setC (R K T) 1 ⨟ rep (mulStep K V T) E ⨟
    clear (R K V) ⨟ addTo (R K T) (R K V) ⨟ addConst (R K V) 3

section
variable {w : Word} {B K : ℕ}

lemma ach_rep_pow (V T : ℕ) (hVT : V < T) (hK : T + 2 ≤ K) (m : ℕ) (hm1 : 1 ≤ m)
    (hmB : m ≤ B) :
    ∀ (E : ℕ) (σ : St (K + 1)) (Q : St (K + 1) → Prop), σ.reg (R K V) = m →
      σ.reg (R K T) * m ^ E ≤ B →
      (∀ σ' : St (K + 1), σ'.pos = σ.pos → σ'.out = σ.out →
        σ'.reg (R K T) = σ.reg (R K T) * m ^ E → σ'.reg (R K V) = m →
        (∀ i, i < V → σ'.reg (R K i) = σ.reg (R K i)) → Q σ') →
      Ach w B (rep (mulStep K V T) E) σ Q := by
  intro E
  induction E with
  | zero =>
    intro σ Q hm hB h
    exact ach_skip (h σ rfl rfl (by simp) hm (fun _ _ => rfl))
  | succ E ih =>
    intro σ Q hm hB h
    have hTm : σ.reg (R K T) * m ≤ B := by
      refine le_trans (Nat.mul_le_mul_left _ ?_) hB
      calc m = m ^ 1 := (pow_one m).symm
        _ ≤ m ^ (E + 1) := Nat.pow_le_pow_right hm1 (by omega)
    refine ach_seq (ach_seq (ach_clear _ _ _ (ach_seq (ach_mulR _ _ _ _
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega))
      (R_ne (by omega) (by omega) (by omega)) (R_ne (by omega) (by omega) (by omega)) _ _
      (by rs [hm]) (by rs [hm]) (ach_addTo _ _ (R_ne (by omega) (by omega) (by omega)) _ _
        (by rs [hm]) ?_)))))
    refine ih _ _ (by rs [hm]) ?_ ?_
    · rs [hm]
      calc σ.reg (R K T) * m * m ^ E = σ.reg (R K T) * m ^ (E + 1) := by ring
        _ ≤ B := hB
    · intro σ' hp ho hv hm' hfr
      refine h σ' (by simp [hp]) (by simp [ho]) ?_ hm' (fun i hi => ?_)
      · rw [hv]; rs [hm]; ring
      · rw [hfr i hi]; rs

lemma ach_initCap (V T E : ℕ) (hVT : V < T) (hK : T + 2 ≤ K) (σ : St (K + 1))
    (Q : St (K + 1) → Prop)
    (hB : capOf E w + w.length + 2 ≤ B)
    (h : ∀ σ' : St (K + 1), σ'.pos = w.length + 1 → σ'.out = σ.out →
      σ'.reg (R K V) = capOf E w → (∀ i, i < V → σ'.reg (R K i) = σ.reg (R K i)) → Q σ') :
    Ach w B (initCap K V T E) σ Q := by
  have hpow : (w.length + 2) ^ E ≤ B := by unfold capOf at hB; omega
  refine ach_seq (ach_lenR _ _ _ (by omega) (ach_seq (ach_addConst _ _ _ _ (by rs)
    (ach_seq (ach_setC _ _ _ _ (by omega) (ach_seq (ach_rep_pow V T hVT hK (w.length + 2)
      (by omega) (by omega) E _ _ (by rs) (by rs) ?_)))))))
  intro σ₁ hp1 ho1 hv1 hm1 hfr1
  refine ach_seq (ach_clear _ _ _ (ach_seq (ach_addTo _ _ (R_ne (by omega) (by omega)
    (by omega)) _ _ (by rs [hv1]) (ach_addConst _ _ _ _ (by rs [hv1]; unfold capOf at hB; omega)
    ?_))))
  refine h _ (by simp [hp1]) (by simp [ho1]) ?_ (fun i hi => ?_)
  · rs [hv1]; simp [capOf]
  · rs
    rw [hfr1 i hi]
    rs

/-- Number of registers used for a program: `K + 1` with this `K`. -/
def regK {V : ℕ} (P : Pr V) : ℕ := V + 2 * P.ld + 2 * P.ed + 8

/-- The compiled register program. -/
def compile {V : ℕ} (E : ℕ) (P : Pr V) : Stmt (regK P + 1) :=
  initCap (regK P) V (V + 1 + 2 * P.ld) E ⨟ compP (regK P) P.ld P 0

/-- The register bound for input `w`. -/
def regBound {V : ℕ} (E : ℕ) (P : Pr V) (w : Word) : ℕ :=
  capOf E w * capOf E w + 2 * capOf E w + w.length + P.mc + 1

theorem ach_compile {V : ℕ} (E : ℕ) (P : Pr V) (w : Word) :
    Ach w (regBound E P w) (compile E P) (St.init _) (fun σ' => σ'.out = P.output E w) := by
  have hC4 : 4 ≤ capOf E w := by
    have := Nat.one_le_pow E (w.length + 2) (by omega); unfold capOf; omega
  have hB : capOf E w + w.length + 2 ≤ regBound E P w := by
    unfold regBound; nlinarith
  refine ach_seq (ach_initCap V (V + 1 + 2 * P.ld) E (by omega) (by unfold regK; omega) _ _ hB ?_)
  intro σ₁ hp1 ho1 hcap1 hfr1
  refine ach_compP P 0 (fun _ => 0) σ₁ _ (by omega) (by unfold regK; omega)
    (by unfold regBound; omega) (fun x => ?_) (fun _ => Nat.zero_le _) hcap1 (by omega) hC4
    (by unfold regBound; omega) ?_
  · rw [hfr1 x x.isLt]; simp [St.init]
  · intro σ' _ _ _ ho _
    rw [ho, ho1]; simp [St.init, Pr.output]

/-- A polynomial bound on the register values. -/
lemma regBound_lt (E M : ℕ) (n : ℕ) :
    ((n + 2) ^ E + 3) * ((n + 2) ^ E + 3) + 2 * ((n + 2) ^ E + 3) + n + M + 1 <
      2 ^ ((4 * E + M + 28) * (Nat.log 2 n + 1)) := by
  have hpow : 2 ^ ((4 * E + M + 28) * (Nat.log 2 n + 1)) =
      (2 ^ (Nat.log 2 n + 1)) ^ (4 * E + M + 28) := by
    rw [← pow_mul, mul_comm]
  have hnX : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hX2' : 2 ≤ 2 ^ (Nat.log 2 n + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (Nat.log 2 n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hpow]
  generalize 2 ^ (Nat.log 2 n + 1) = X at hnX hX2' ⊢
  have hn2 : n + 2 ≤ X ^ 2 := by nlinarith
  have hpowE : (n + 2) ^ E ≤ X ^ (2 * E) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hn2 E
  have hY1 : 1 ≤ X ^ (2 * E) := Nat.one_le_pow _ _ (by omega)
  generalize hY : X ^ (2 * E) = Y at hpowE hY1
  have hC : (n + 2) ^ E + 3 ≤ 4 * Y := by omega
  have hM : M + 26 ≤ X ^ (M + 26) :=
    le_of_lt (lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hX2' _))
  have key : ((n + 2) ^ E + 3) * ((n + 2) ^ E + 3) + 2 * ((n + 2) ^ E + 3) + n + M + 1 ≤
      (M + 26) * (X * (Y * Y)) := by
    have h1 : ((n + 2) ^ E + 3) * ((n + 2) ^ E + 3) ≤ (4 * Y) * (4 * Y) := Nat.mul_le_mul hC hC
    have hYY : Y ≤ Y * Y := by nlinarith
    have hYY1 : 1 ≤ Y * Y := by nlinarith
    have hXY : X ≤ X * (Y * Y) := by nlinarith
    have hYYX : Y * Y ≤ X * (Y * Y) := by nlinarith
    nlinarith
  have heq : X ^ (M + 26) * (X * (Y * Y)) = X ^ (4 * E + M + 27) := by
    rw [← hY]; ring
  calc _ ≤ (M + 26) * (X * (Y * Y)) := key
    _ ≤ X ^ (M + 26) * (X * (Y * Y)) := Nat.mul_le_mul_right _ hM
    _ = X ^ (4 * E + M + 27) := heq
    _ < X ^ (4 * E + M + 28) := pow_lt_pow_right₀ (by omega) (by omega)

/-- **Programs of the loop language compute logspace functions.** -/
theorem logspaceComputable_of_output {V : ℕ} (E : ℕ) (P : Pr V) (f : Word → Word)
    (hf : ∀ w, P.output E w = f w) : LogspaceComputable f := by
  refine logspaceComputable_of_prog (compile E P) f (regBound E P) (4 * E + P.mc + 28)
    (fun w => ?_) (fun w => ?_)
  · unfold regBound capOf
    exact regBound_lt E P.mc w.length
  · obtain ⟨σ', hev, hout⟩ := ach_compile E P w
    exact ⟨σ', hev, hout.trans (hf w)⟩

end

end LL

end PathChecking
