module

public import RequestProject.LTLPath.FEO

/-!
# A denotational calculus for functional expressions

Expressions of `FE` use de Bruijn levels, so a term valid at every depth is a function
`T = ℕ → E` from the current depth to an expression.  Binders are written in higher-order style:
`findT n body` binds the level `d` of the current depth and passes the variable `varT d` to
`body`.

`Den x Γ t v` says that the term `t` denotes the value `v` on input `x`, in every environment
compatible with the context `Γ` (a list of pairs `(level, value)`).  Every builder comes with a
compositional rule, so the value of a large term is computed rule by rule.  `DenO` is the same
for output programs, and `logspace_of_DenO` turns a closed output program denoting `f x` on every
input `x` into a proof that `f` is logspace computable.
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL

/-- Terms: expressions indexed by the binder depth. -/
abbrev T := ℕ → E

/-- Output terms. -/
abbrev TO := ℕ → O

/-- Contexts: levels of bound variables with their values. -/
abbrev Ctx := List (ℕ × ℕ)

/-- An environment at depth `d` compatible with `Γ`. -/
def CtxOk (Γ : Ctx) (d : ℕ) (ρ : ℕ → ℕ) : Prop := ∀ kv ∈ Γ, kv.1 < d ∧ ρ kv.1 = kv.2

/-- `t` denotes `v` on input `x` in context `Γ`. -/
def Den (x : Word) (Γ : Ctx) (t : T) (v : ℕ) : Prop :=
  ∀ d ρ, CtxOk Γ d ρ → ev x d ρ (t d) = v

/-- `o` denotes the output `v` on input `x` in context `Γ`. -/
def DenO (x : Word) (Γ : Ctx) (o : TO) (v : Word) : Prop :=
  ∀ d ρ, CtxOk Γ d ρ → evO x d ρ (o d) = v

lemma ctxOk_cons {Γ : Ctx} {d : ℕ} {ρ : ℕ → ℕ} (h : CtxOk Γ d ρ) (i : ℕ) :
    CtxOk ((d, i) :: Γ) (d + 1) (Function.update ρ d i) := by
  intro kv hkv
  rcases List.mem_cons.1 hkv with rfl | hkv
  · simp
  · obtain ⟨h1, h2⟩ := h kv hkv
    refine ⟨by omega, ?_⟩
    rw [Function.update_of_ne (by omega)]; exact h2

/-! ## Builders -/

def cT (k : ℕ) : T := fun _ => .c k
def varT (k : ℕ) : T := fun _ => .v k
def lenT : T := fun _ => .len
def inpT (t : T) : T := fun d => .inp (t d)
def binT (o : BOp) (a b : T) : T := fun d => .bin o (a d) (b d)
def iteT (c a b : T) : T := fun d => .ite (c d) (a d) (b d)
def findT (n : T) (body : T → T) : T := fun d => .find (n d) (body (varT d) (d + 1))
def countT (n : T) (body : T → T) : T := fun d => .count (n d) (body (varT d) (d + 1))
def lettT (a : T) (body : T → T) : T := fun d => .lett (a d) (body (varT d) (d + 1))

def addT (a b : T) : T := binT .add a b
def subT (a b : T) : T := binT .sub a b
def mulT (a b : T) : T := binT .mul a b
def divT (a b : T) : T := binT .div a b
def modT (a b : T) : T := binT .mod a b
def ltT (a b : T) : T := binT .lt a b
def eqT (a b : T) : T := binT .eq a b

def nilO : TO := fun _ => .nil
def bitO (t : T) : TO := fun d => .bit (t d)
def natO (t : T) : TO := fun d => .nat (t d)
def seqO (a b : TO) : TO := fun d => .seq (a d) (b d)
def iteO (c : T) (a b : TO) : TO := fun d => .ite (c d) (a d) (b d)
def loopO (n : T) (body : T → TO) : TO := fun d => .loop (n d) (body (varT d) (d + 1))
def lettO (a : T) (body : T → TO) : TO := fun d => .lett (a d) (body (varT d) (d + 1))

/-! ## Rules -/

variable {x : Word} {Γ : Ctx}

lemma den_c (k : ℕ) : Den x Γ (cT k) k := fun _ _ _ => rfl

lemma den_var {k v : ℕ} (h : (k, v) ∈ Γ) : Den x Γ (varT k) v := fun _ _ hΓ => (hΓ _ h).2

lemma den_var0 {k v : ℕ} : Den x ((k, v) :: Γ) (varT k) v := den_var (by simp)

lemma den_len : Den x Γ lenT x.length := fun _ _ _ => rfl

lemma den_inp {t : T} {v : ℕ} (h : Den x Γ t v) : Den x Γ (inpT t) (symNum (inputSym x v)) :=
  fun d ρ hΓ => by simp [inpT, ev, h d ρ hΓ]

lemma den_bin (o : BOp) {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (binT o a b) (apU o u v) := fun d ρ hΓ => by
  simp [binT, ev, ha d ρ hΓ, hb d ρ hΓ]

lemma den_add {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (addT a b) (u + v) := den_bin .add ha hb
lemma den_sub {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (subT a b) (u - v) := den_bin .sub ha hb
lemma den_mul {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (mulT a b) (u * v) := den_bin .mul ha hb
lemma den_div {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (divT a b) (u / v) := den_bin .div ha hb
lemma den_mod {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (modT a b) (u % v) := den_bin .mod ha hb
lemma den_lt {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (ltT a b) (decide (u < v)).toNat := by
  have := den_bin .lt ha hb
  simp only [apU] at this
  convert this using 1; by_cases h : u < v <;> simp [h]
lemma den_eq {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (eqT a b) (decide (u = v)).toNat := by
  have := den_bin .eq ha hb
  simp only [apU] at this
  convert this using 1; by_cases h : u = v <;> simp [h]

lemma den_ite {c a b : T} {u v₁ v₂ : ℕ} (hc : Den x Γ c u) (ha : u ≠ 0 → Den x Γ a v₁)
    (hb : u = 0 → Den x Γ b v₂) : Den x Γ (iteT c a b) (if u ≠ 0 then v₁ else v₂) :=
  fun d ρ hΓ => by
    by_cases hu : u = 0
    · simp [iteT, ev, hc d ρ hΓ, hb hu d ρ hΓ, hu]
    · simp [iteT, ev, hc d ρ hΓ, ha hu d ρ hΓ, hu]

lemma den_find {n : T} {body : T → T} {N : ℕ} {f : ℕ → ℕ} (hn : Den x Γ n N)
    (hb : ∀ k i, i < N → Den x ((k, i) :: Γ) (body (varT k)) (f i)) :
    Den x Γ (findT n body) (findF N f) := fun d ρ hΓ => by
  simp only [findT, ev, hn d ρ hΓ]
  exact findF_congr fun i hi => hb d i hi (d + 1) _ (ctxOk_cons hΓ i)

lemma den_count {n : T} {body : T → T} {N : ℕ} {f : ℕ → ℕ} (hn : Den x Γ n N)
    (hb : ∀ k i, i < N → Den x ((k, i) :: Γ) (body (varT k)) (f i)) :
    Den x Γ (countT n body) (cntU N f) := fun d ρ hΓ => by
  simp only [countT, ev, hn d ρ hΓ]
  exact cntU_congr fun i hi => hb d i hi (d + 1) _ (ctxOk_cons hΓ i)

lemma den_lett {a : T} {body : T → T} {u v : ℕ} (ha : Den x Γ a u)
    (hb : ∀ k, Den x ((k, u) :: Γ) (body (varT k)) v) : Den x Γ (lettT a body) v :=
  fun d ρ hΓ => by
    simp only [lettT, ev, ha d ρ hΓ]
    exact hb d (d + 1) _ (ctxOk_cons hΓ u)

lemma deno_nil : DenO x Γ nilO [] := fun _ _ _ => rfl

lemma deno_bit {t : T} {v : ℕ} (h : Den x Γ t v) : DenO x Γ (bitO t) [decide (v ≠ 0)] :=
  fun d ρ hΓ => by simp [bitO, evO, h d ρ hΓ]

lemma deno_nat {t : T} {v : ℕ} (h : Den x Γ t v) : DenO x Γ (natO t) (encodeToks (natToks v)) :=
  fun d ρ hΓ => by simp [natO, evO, h d ρ hΓ]

lemma deno_seq {a b : TO} {u v : Word} (ha : DenO x Γ a u) (hb : DenO x Γ b v) :
    DenO x Γ (seqO a b) (u ++ v) := fun d ρ hΓ => by simp [seqO, evO, ha d ρ hΓ, hb d ρ hΓ]

lemma deno_ite {c : T} {a b : TO} {u : ℕ} {v₁ v₂ : Word} (hc : Den x Γ c u)
    (ha : u ≠ 0 → DenO x Γ a v₁) (hb : u = 0 → DenO x Γ b v₂) :
    DenO x Γ (iteO c a b) (if u ≠ 0 then v₁ else v₂) := fun d ρ hΓ => by
  by_cases hu : u = 0
  · simp [iteO, evO, hc d ρ hΓ, hb hu d ρ hΓ, hu]
  · simp [iteO, evO, hc d ρ hΓ, ha hu d ρ hΓ, hu]

lemma deno_loop {n : T} {body : T → TO} {N : ℕ} {f : ℕ → Word} (hn : Den x Γ n N)
    (hb : ∀ k i, i < N → DenO x ((k, i) :: Γ) (body (varT k)) (f i)) :
    DenO x Γ (loopO n body) ((List.range N).flatMap f) := fun d ρ hΓ => by
  simp only [loopO, evO, hn d ρ hΓ]
  refine List.flatMap_congr fun i hi => ?_
  exact hb d i (List.mem_range.1 hi) (d + 1) _ (ctxOk_cons hΓ i)

lemma deno_lett {a : T} {body : T → TO} {u : ℕ} {v : Word} (ha : Den x Γ a u)
    (hb : ∀ k, DenO x ((k, u) :: Γ) (body (varT k)) v) : DenO x Γ (lettO a body) v :=
  fun d ρ hΓ => by
    simp only [lettO, evO, ha d ρ hΓ]
    exact hb d (d + 1) _ (ctxOk_cons hΓ u)

/-- **Logspace functions from denotations.** -/
theorem logspace_of_DenO (o : TO) (ho : (o 0).wf 0 = true) (f : Word → Word)
    (hf : ∀ x, DenO x [] o (f x)) : LogspaceComputable f :=
  logspaceComputable_of_O (o 0) ho f fun x => hf x 0 _ (fun _ h => absurd h (by simp))

end FD

end PathChecking
