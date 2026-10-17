module

public import RequestProject.LTLPath.FED

/-!
# A library of derived builders for the denotational calculus

* `bv P`: the value `1` if `P` holds, else `0` (classical);
* boolean builders `notT`, `andT`, `orT`, `leT`, bounded quantifiers `exT`, `allT`;
* `fgT`: the greatest `i ≤ n` with a property (`Nat.findGreatest`);
* facts about `findF` and `cntU`; weakening of contexts.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL

/-- Truth value of a proposition as a number. -/
noncomputable def bv (P : Prop) : ℕ := by classical exact if P then 1 else 0

lemma bv_pos {P : Prop} (h : P) : bv P = 1 := by simp [bv, h]
lemma bv_neg {P : Prop} (h : ¬ P) : bv P = 0 := by simp [bv, h]
@[simp] lemma bv_ne_zero {P : Prop} : bv P ≠ 0 ↔ P := by by_cases h : P <;> simp [bv, h]
@[simp] lemma bv_eq_zero {P : Prop} : bv P = 0 ↔ ¬ P := by by_cases h : P <;> simp [bv, h]
@[simp] lemma bv_eq_one {P : Prop} : bv P = 1 ↔ P := by by_cases h : P <;> simp [bv, h]
lemma bv_le_one (P : Prop) : bv P ≤ 1 := by by_cases h : P <;> simp [bv, h]
lemma bv_congr {P Q : Prop} (h : P ↔ Q) : bv P = bv Q := by rw [propext h]
lemma bv_decide (P : Prop) [Decidable P] : (decide P).toNat = bv P := by
  by_cases h : P <;> simp [bv, h]
lemma bv_bool (b : Bool) : b.toNat = bv (b = true) := by cases b <;> simp [bv]

/-! ## `findF` and `cntU` -/

lemma findF_spec (N : ℕ) (f : ℕ → ℕ) :
    (findF N f < N → f (findF N f) ≠ 0) ∧ (∀ j < findF N f, j < N → f j = 0) := by
  induction N with
  | zero => simp [findF]
  | succ N ih =>
    rw [findF_succ]
    obtain ⟨ih1, ih2⟩ := ih
    by_cases h1 : findF N f < N
    · rw [if_pos h1]
      exact ⟨fun _ => ih1 h1, fun j hj _ => ih2 j hj (by omega)⟩
    · have hN := findF_le N f
      have heq : findF N f = N := by omega
      rw [if_neg h1]
      by_cases h2 : f N ≠ 0
      · rw [if_pos h2]
        exact ⟨fun _ => h2, fun j hj _ => ih2 j (by omega) hj⟩
      · rw [if_neg h2]
        refine ⟨fun h => absurd h (by omega), fun j hj hjN => ?_⟩
        rcases (show j < N ∨ j = N by omega) with h | rfl
        · exact ih2 j (by omega) h
        · simpa using h2

lemma findF_lt_iff {N : ℕ} {f : ℕ → ℕ} : findF N f < N ↔ ∃ i < N, f i ≠ 0 := by
  obtain ⟨h1, h2⟩ := findF_spec N f
  constructor
  · intro h; exact ⟨_, h, h1 h⟩
  · rintro ⟨i, hi, hfi⟩
    by_contra hc
    exact hfi (h2 i (by have := findF_le N f; omega) hi)

lemma findF_eq_of_spec {N : ℕ} {f : ℕ → ℕ} {k : ℕ} (hk : k ≤ N) (hfk : k < N → f k ≠ 0)
    (hlt : ∀ j < k, f j = 0) : findF N f = k := by
  obtain ⟨h1, h2⟩ := findF_spec N f
  have hle := findF_le N f
  rcases lt_trichotomy (findF N f) k with h | h | h
  · exact absurd (hlt _ h) (h1 (by omega))
  · exact h
  · exact absurd (h2 k h (by omega)) (hfk (by omega))

lemma cntU_bv (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    cntU N (fun i => bv (P i)) = (List.range N).countP (fun i => decide (P i)) := by
  unfold cntU
  exact List.countP_congr fun i _ => by simp

lemma findGreatest_eq_findF (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    Nat.findGreatest P N = N - findF (N + 1) (fun i => bv (P (N - i))) := by
  obtain ⟨h1, h2⟩ := findF_spec (N + 1) (fun i => bv (P (N - i)))
  have hle := findF_le (N + 1) (fun i => bv (P (N - i)))
  set k := findF (N + 1) (fun i => bv (P (N - i)))
  rw [Nat.findGreatest_eq_iff]
  refine ⟨by omega, fun hne => ?_, fun n hn hnN hP => ?_⟩
  · have := h1 (by omega)
    simpa using this
  · have := h2 (N - n) (by omega) (by omega)
    rw [show N - (N - n) = n by omega] at this
    simp at this
    exact this hP

/-! ## Weakening -/

variable {x : Word} {Γ Γ' : Ctx}

lemma ctxOk_mono {d : ℕ} {ρ : ℕ → ℕ} (h : CtxOk Γ' d ρ) (hΓ : Γ ⊆ Γ') : CtxOk Γ d ρ :=
  fun kv hkv => h kv (hΓ hkv)

lemma Den.mono {t : T} {v : ℕ} (h : Den x Γ t v) (hΓ : Γ ⊆ Γ') : Den x Γ' t v :=
  fun d ρ hc => h d ρ (ctxOk_mono hc hΓ)

lemma Den.cons {t : T} {v : ℕ} (h : Den x Γ t v) (kv : ℕ × ℕ) : Den x (kv :: Γ) t v :=
  h.mono (List.subset_cons_self _ _)

lemma DenO.mono {o : TO} {v : Word} (h : DenO x Γ o v) (hΓ : Γ ⊆ Γ') : DenO x Γ' o v :=
  fun d ρ hc => h d ρ (ctxOk_mono hc hΓ)

/-- Denotation of a term builder: `f` maps terms denoting `v` to terms denoting `F v`, in every
context extending `Γ`. -/
def DenF (x : Word) (Γ : Ctx) (f : T → T) (F : ℕ → ℕ) : Prop :=
  ∀ Γ', Γ ⊆ Γ' → ∀ t v, Den x Γ' t v → Den x Γ' (f t) (F v)

/-- Denotation of a binary term builder. -/
def DenF2 (x : Word) (Γ : Ctx) (f : T → T → T) (F : ℕ → ℕ → ℕ) : Prop :=
  ∀ Γ', Γ ⊆ Γ' → ∀ t u v w, Den x Γ' t v → Den x Γ' u w → Den x Γ' (f t u) (F v w)

lemma DenF.app {f : T → T} {F : ℕ → ℕ} (hf : DenF x Γ f F) {t : T} {v : ℕ}
    (ht : Den x Γ' t v) (hΓ : Γ ⊆ Γ') : Den x Γ' (f t) (F v) := hf Γ' hΓ t v ht

lemma DenF.app0 {f : T → T} {F : ℕ → ℕ} (hf : DenF x [] f F) {t : T} {v : ℕ}
    (ht : Den x Γ' t v) : Den x Γ' (f t) (F v) := hf Γ' (List.nil_subset _) t v ht

lemma DenF2.app0 {f : T → T → T} {F : ℕ → ℕ → ℕ} (hf : DenF2 x [] f F) {t u : T} {v w : ℕ}
    (ht : Den x Γ' t v) (hu : Den x Γ' u w) : Den x Γ' (f t u) (F v w) :=
  hf Γ' (List.nil_subset _) t u v w ht hu

/-! ## Boolean builders -/

def notT (a : T) : T := eqT a (cT 0)
def andT (a b : T) : T := mulT a b
def orT (a b : T) : T := ltT (cT 0) (addT a b)
def leT (a b : T) : T := ltT a (addT b (cT 1))
def neT (a b : T) : T := notT (eqT a b)
def exT (n : T) (body : T → T) : T := ltT (findT n body) n
def allT (n : T) (body : T → T) : T := notT (exT n fun i => notT (body i))
def fgT (n : T) (body : T → T) : T := subT n (findT (addT n (cT 1)) fun i => body (subT n i))
def minT (a b : T) : T := iteT (ltT a b) a b

lemma den_lt' {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (ltT a b) (bv (u < v)) := by
  have := den_lt ha hb; rwa [bv_decide] at this

lemma den_eq' {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (eqT a b) (bv (u = v)) := by
  have := den_eq ha hb; rwa [bv_decide] at this

lemma den_not {a : T} {P : Prop} (ha : Den x Γ a (bv P)) : Den x Γ (notT a) (bv (¬ P)) := by
  have := den_eq' ha (den_c 0)
  rwa [bv_congr (show bv P = 0 ↔ ¬ P from bv_eq_zero)] at this

lemma den_and {a b : T} {P Q : Prop} (ha : Den x Γ a (bv P)) (hb : Den x Γ b (bv Q)) :
    Den x Γ (andT a b) (bv (P ∧ Q)) := by
  have := den_mul ha hb
  convert this using 1
  by_cases hP : P <;> by_cases hQ : Q <;> simp [bv, hP, hQ]

lemma den_or {a b : T} {P Q : Prop} (ha : Den x Γ a (bv P)) (hb : Den x Γ b (bv Q)) :
    Den x Γ (orT a b) (bv (P ∨ Q)) := by
  have := den_lt' (den_c 0) (den_add ha hb)
  convert this using 1
  apply bv_congr
  by_cases hP : P <;> by_cases hQ : Q <;> simp [bv, hP, hQ]

lemma den_le {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (leT a b) (bv (u ≤ v)) := by
  have := den_lt' ha (den_add hb (den_c 1))
  convert this using 1
  exact bv_congr (by omega)

lemma den_ne {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (neT a b) (bv (u ≠ v)) := den_not (den_eq' ha hb)

lemma den_ex {n : T} {body : T → T} {N : ℕ} {P : ℕ → Prop} (hn : Den x Γ n N)
    (hb : ∀ k i, i < N → Den x ((k, i) :: Γ) (body (varT k)) (bv (P i))) :
    Den x Γ (exT n body) (bv (∃ i < N, P i)) := by
  have := den_lt' (den_find hn hb) hn
  convert this using 1
  apply bv_congr
  rw [findF_lt_iff]
  simp

lemma den_all {n : T} {body : T → T} {N : ℕ} {P : ℕ → Prop} (hn : Den x Γ n N)
    (hb : ∀ k i, i < N → Den x ((k, i) :: Γ) (body (varT k)) (bv (P i))) :
    Den x Γ (allT n body) (bv (∀ i < N, P i)) := by
  have := den_not (den_ex (body := fun i => notT (body i)) (P := fun i => ¬ P i) hn
    fun k i hi => den_not (hb k i hi))
  convert this using 1
  apply bv_congr
  push_neg; rfl

lemma den_fg {n : T} {body : T → T} {N : ℕ} {P : ℕ → Prop} [DecidablePred P] (hn : Den x Γ n N)
    (hb : ∀ Γ', Γ ⊆ Γ' → ∀ t i, i ≤ N → Den x Γ' t i → Den x Γ' (body t) (bv (P i))) :
    Den x Γ (fgT n body) (Nat.findGreatest P N) := by
  rw [findGreatest_eq_findF]
  exact den_sub hn (den_find (den_add hn (den_c 1)) fun k i hi =>
    hb _ (List.subset_cons_self _ _) _ _ (by omega) (den_sub (hn.cons _) den_var0))

lemma Den.of_eq {t : T} {v v' : ℕ} (h : Den x Γ t v) (e : v = v') : Den x Γ t v' := e ▸ h

lemma den_ite_eq {c a b : T} {u v : ℕ} (hc : Den x Γ c u) (ha : u ≠ 0 → Den x Γ a v)
    (hb : u = 0 → Den x Γ b v) : Den x Γ (iteT c a b) v :=
  (den_ite hc ha hb).of_eq (by split_ifs <;> rfl)

lemma deno_ite_eq {c : T} {a b : TO} {u : ℕ} {v : Word} (hc : Den x Γ c u)
    (ha : u ≠ 0 → DenO x Γ a v) (hb : u = 0 → DenO x Γ b v) : DenO x Γ (iteO c a b) v :=
  (show (if u ≠ 0 then v else v) = v by split_ifs <;> rfl) ▸ deno_ite hc ha hb

lemma den_min {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (minT a b) (min u v) := by
  have := den_ite (den_lt' ha hb) (fun _ => ha) (fun _ => hb)
  convert this using 1
  by_cases h : u < v
  · simp [h, bv]; omega
  · simp [h, bv]; omega

end FD

end PathChecking
