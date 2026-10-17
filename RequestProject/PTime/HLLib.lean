module

public import RequestProject.PTime.HLStmt

/-!
# A small library for structured programs

Arithmetic notation for expressions, derived Boolean operations (values `0`/`1`), frame
conditions and a loop rule with a measure.
-/

@[expose] public section

namespace PathChecking

namespace HL

variable {m : ℕ} {w : Word} {B : ℕ}

instance : Add (Ex m) := ⟨Ex.add⟩
instance : Sub (Ex m) := ⟨Ex.sub⟩
instance : Mul (Ex m) := ⟨Ex.mul⟩
instance (k : ℕ) : OfNat (Ex m) k := ⟨Ex.const k⟩

/-- Equality test. -/
def Ex.eq (a b : Ex m) : Ex m := Ex.const 1 - (Ex.lt a b + Ex.lt b a)
/-- Boolean negation. -/
def Ex.bnot (a : Ex m) : Ex m := Ex.const 1 - a
/-- Boolean conjunction. -/
def Ex.band (a b : Ex m) : Ex m := a * b
/-- Boolean disjunction. -/
def Ex.bor (a b : Ex m) : Ex m := Ex.lt (Ex.const 0) (a + b)
/-- Membership in a list of constants. -/
def Ex.inL (e : Ex m) : List ℕ → Ex m
  | [] => Ex.const 0
  | c :: L => Ex.bor (Ex.eq e (.const c)) (Ex.inL e L)

/-- Booleans as numbers. -/
def bv (b : Bool) : ℕ := if b then 1 else 0

@[simp] lemma bv_true : bv true = 1 := rfl
@[simp] lemma bv_false : bv false = 0 := rfl
lemma bv_le (b : Bool) : bv b ≤ 1 := by cases b <;> simp
@[simp] lemma bv_eq_zero (b : Bool) : bv b = 0 ↔ b = false := by cases b <;> simp
@[simp] lemma bv_ne_zero (b : Bool) : bv b ≠ 0 ↔ b = true := by cases b <;> simp

section ev
variable (σ : HSt m) (a b : Ex m)
@[simp] lemma ev_var (i : Fin m) : (Ex.var i).ev w σ = σ.v i := rfl
@[simp] lemma ev_const (k : ℕ) : (Ex.const k : Ex m).ev w σ = k := rfl
@[simp] lemma ev_ofNat (k : ℕ) : (no_index (OfNat.ofNat k : Ex m)).ev w σ = k := rfl
@[simp] lemma ev_add : (a + b).ev w σ = a.ev w σ + b.ev w σ := rfl
@[simp] lemma ev_sub : (a - b).ev w σ = a.ev w σ - b.ev w σ := rfl
@[simp] lemma ev_mul : (a * b).ev w σ = a.ev w σ * b.ev w σ := rfl
@[simp] lemma ev_lt : (Ex.lt a b).ev w σ = bv (decide (a.ev w σ < b.ev w σ)) := by
  simp [Ex.ev, bv]
@[simp] lemma ev_tok : (Ex.tok a).ev w σ = PT.rtok w (a.ev w σ) := rfl
@[simp] lemma ev_mem : (Ex.mem a).ev w σ = bv (decide (a.ev w σ ∈ σ.mem)) := by
  simp [Ex.ev, bv]
@[simp] lemma ev_eq : (Ex.eq a b).ev w σ = bv (decide (a.ev w σ = b.ev w σ)) := by
  simp only [Ex.eq, ev_sub, ev_const, ev_add, ev_lt, bv]
  (split_ifs <;> simp_all); omega
@[simp] lemma ev_band (x y : Bool) (ha : a.ev w σ = bv x) (hb : b.ev w σ = bv y) :
    (Ex.band a b).ev w σ = bv (x && y) := by
  simp only [Ex.band, ev_mul, ha, hb]; cases x <;> cases y <;> rfl
lemma ev_bnot (x : Bool) (ha : a.ev w σ = bv x) : (Ex.bnot a).ev w σ = bv (!x) := by
  simp only [Ex.bnot, ev_sub, ev_const, ha]; cases x <;> rfl
lemma ev_bor (x y : Bool) (ha : a.ev w σ = bv x) (hb : b.ev w σ = bv y) :
    (Ex.bor a b).ev w σ = bv (x || y) := by
  simp only [Ex.bor, ev_lt, ev_add, ev_const, ha, hb]; cases x <;> cases y <;> rfl
lemma ev_inL (L : List ℕ) : (Ex.inL a L).ev w σ = bv (decide (a.ev w σ ∈ L)) := by
  induction L with
  | nil => simp [Ex.inL]
  | cons c L ih =>
    simp only [Ex.inL]
    rw [ev_bor _ _ _ (decide (a.ev w σ = c)) _ (by simp) ih]
    simp
end ev

section bnd
variable (σ : HSt m) (a b : Ex m)
@[simp] lemma bnd_var (i : Fin m) : (Ex.var i).Bnd w B σ ↔ σ.v i ≤ B := Iff.rfl
@[simp] lemma bnd_const (k : ℕ) : (Ex.const k : Ex m).Bnd w B σ ↔ k ≤ B := Iff.rfl
@[simp] lemma bnd_ofNat (k : ℕ) : (no_index (OfNat.ofNat k : Ex m)).Bnd w B σ ↔ k ≤ B := Iff.rfl
@[simp] lemma bnd_add : (a + b).Bnd w B σ ↔ a.Bnd w B σ ∧ b.Bnd w B σ ∧ a.ev w σ + b.ev w σ ≤ B :=
  Iff.rfl
@[simp] lemma bnd_sub : (a - b).Bnd w B σ ↔ a.Bnd w B σ ∧ b.Bnd w B σ := Iff.rfl
@[simp] lemma bnd_mul : (a * b).Bnd w B σ ↔ a.Bnd w B σ ∧ b.Bnd w B σ ∧ a.ev w σ * b.ev w σ ≤ B :=
  Iff.rfl
@[simp] lemma bnd_lt : (Ex.lt a b).Bnd w B σ ↔ a.Bnd w B σ ∧ b.Bnd w B σ := Iff.rfl
@[simp] lemma bnd_tok : (Ex.tok a).Bnd w B σ ↔ a.Bnd w B σ := Iff.rfl
@[simp] lemma bnd_mem : (Ex.mem a).Bnd w B σ ↔ a.Bnd w B σ := Iff.rfl
lemma bnd_eq (hB : 2 ≤ B) : (Ex.eq a b).Bnd w B σ ↔ a.Bnd w B σ ∧ b.Bnd w B σ := by
  simp only [Ex.eq, bnd_sub, bnd_const, bnd_add, bnd_lt, ev_lt]
  constructor
  · rintro ⟨-, ⟨h1, h2⟩, -, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨by omega, ⟨h1, h2⟩, ⟨h2, h1⟩, ?_⟩
    have := bv_le (decide (a.ev w σ < b.ev w σ)); have := bv_le (decide (b.ev w σ < a.ev w σ))
    omega
lemma bnd_band (hB : 1 ≤ B) (x y : Bool) (ha : a.ev w σ = bv x) (hb : b.ev w σ = bv y) :
    (Ex.band a b).Bnd w B σ ↔ a.Bnd w B σ ∧ b.Bnd w B σ := by
  simp only [Ex.band, bnd_mul, ha, hb]
  have : bv x * bv y ≤ 1 := by cases x <;> cases y <;> simp
  constructor
  · rintro ⟨h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, by omega⟩
lemma bnd_bnot (hB : 1 ≤ B) : (Ex.bnot a).Bnd w B σ ↔ a.Bnd w B σ := by
  simp only [Ex.bnot, bnd_sub, bnd_const]; constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨hB, h⟩
lemma bnd_bor (hB : 2 ≤ B) (x y : Bool) (ha : a.ev w σ = bv x) (hb : b.ev w σ = bv y) :
    (Ex.bor a b).Bnd w B σ ↔ a.Bnd w B σ ∧ b.Bnd w B σ := by
  simp only [Ex.bor, bnd_lt, bnd_const, bnd_add, ha, hb]
  have := bv_le x; have := bv_le y
  constructor
  · rintro ⟨-, h1, h2, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2, by omega⟩
lemma bnd_inL (hB : 2 ≤ B) (L : List ℕ) (hL : ∀ c ∈ L, c ≤ B) (ha : a.Bnd w B σ) :
    (Ex.inL a L).Bnd w B σ := by
  induction L with
  | nil => simp only [Ex.inL, bnd_const]; omega
  | cons c L ih =>
    simp only [Ex.inL]
    rw [bnd_bor σ _ _ hB (decide (a.ev w σ = c)) _ (by simp) (ev_inL σ a L)]
    exact ⟨(bnd_eq σ _ _ hB).2 ⟨ha, by simpa using hL c (by simp)⟩,
      ih (fun c' hc => hL c' (by simp [hc]))⟩
end bnd

/-! ## Frames -/

/-- Only the variables in `cl` may have changed; memory and output are unchanged. -/
def Frame (cl : List (Fin m)) (σ σ' : HSt m) : Prop :=
  (∀ i, i ∉ cl → σ'.v i = σ.v i) ∧ σ'.mem = σ.mem ∧ σ'.out = σ.out

lemma Frame.refl (cl : List (Fin m)) (σ : HSt m) : Frame cl σ σ := ⟨fun _ _ => rfl, rfl, rfl⟩

lemma Frame.trans {cl : List (Fin m)} {σ₁ σ₂ σ₃ : HSt m} (h1 : Frame cl σ₁ σ₂)
    (h2 : Frame cl σ₂ σ₃) : Frame cl σ₁ σ₃ :=
  ⟨fun i hi => by rw [h2.1 i hi, h1.1 i hi], by rw [h2.2.1, h1.2.1], by rw [h2.2.2, h1.2.2]⟩

lemma Frame.mono {cl cl' : List (Fin m)} {σ σ' : HSt m} (h : Frame cl σ σ') (hs : cl ⊆ cl') :
    Frame cl' σ σ' :=
  ⟨fun i hi => h.1 i (fun h' => hi (hs h')), h.2.1, h.2.2⟩

lemma Frame.set {cl : List (Fin m)} {σ σ' : HSt m} (h : Frame cl σ σ') {i : Fin m}
    (hi : i ∈ cl) (x : ℕ) : Frame cl σ (σ'.set i x) :=
  ⟨fun j hj => by
    have : j ≠ i := fun e => hj (e ▸ hi)
    simp [HSt.set, this, h.1 j hj], h.2.1, h.2.2⟩

/-! ## Loops with a measure -/

lemma hach_while {e : Ex m} {body : Hs m} (inv : HSt m → Prop) (μ : HSt m → ℕ)
    (Q : HSt m → Prop) (hb : ∀ σ, inv σ → e.Bnd w B σ) (hQ : ∀ σ, inv σ → e.ev w σ = 0 → Q σ)
    (hstep : ∀ σ, inv σ → e.ev w σ ≠ 0 → HAch w B body σ (fun σ' => inv σ' ∧ μ σ' < μ σ)) :
    ∀ σ, inv σ → HAch w B (.loop e body) σ Q := by
  intro σ hσ
  refine hach_loop (fun k σ => inv σ ∧ μ σ = k) Q ?_ (μ σ) σ ⟨hσ, rfl⟩
  intro k σ ⟨hi, hk⟩
  refine ⟨hb σ hi, ?_⟩
  by_cases h0 : e.ev w σ = 0
  · exact Or.inl ⟨h0, hQ σ hi h0⟩
  · exact Or.inr ⟨h0, (hstep σ hi h0).mono fun σ' ⟨h1, h2⟩ => ⟨μ σ', by omega, h1, rfl⟩⟩

end HL

end PathChecking

namespace PathChecking

namespace HL

variable {m : ℕ} {w : Word} {B : ℕ}

/-! ## Normalising Boolean expressions -/

@[simp] lemma ev_band' (σ : HSt m) (a b : Ex m) : (Ex.band a b).ev w σ = a.ev w σ * b.ev w σ := rfl
@[simp] lemma ev_bor' (σ : HSt m) (a b : Ex m) :
    (Ex.bor a b).ev w σ = bv (decide (0 < a.ev w σ + b.ev w σ)) := by
  simp [Ex.bor]
@[simp] lemma ev_bnot' (σ : HSt m) (a : Ex m) : (Ex.bnot a).ev w σ = 1 - a.ev w σ := rfl
@[simp] lemma ev_inL' (σ : HSt m) (a : Ex m) (L : List ℕ) :
    (Ex.inL a L).ev w σ = bv (decide (a.ev w σ ∈ L)) := ev_inL σ a L

@[simp] lemma bv_mul_bv (x y : Bool) : bv x * bv y = bv (x && y) := by cases x <;> cases y <;> rfl
@[simp] lemma one_sub_bv (x : Bool) : 1 - bv x = bv (!x) := by cases x <;> rfl
@[simp] lemma pos_bv_add_bv (x y : Bool) : (0 < bv x + bv y) = (x || y = true) := by
  cases x <;> cases y <;> simp
@[simp] lemma bv_inj (x y : Bool) : bv x = bv y ↔ x = y := by cases x <;> cases y <;> simp
@[simp] lemma bv_eq_one (x : Bool) : bv x = 1 ↔ x = true := by cases x <;> simp

lemma bnd_band' {σ : HSt m} {a b : Ex m} (ha : a.Bnd w B σ) (hb : b.Bnd w B σ)
    (ha1 : a.ev w σ ≤ 1) (hb1 : b.ev w σ ≤ 1) (hB : 1 ≤ B) : (Ex.band a b).Bnd w B σ :=
  ⟨ha, hb, le_trans (Nat.mul_le_mul ha1 hb1) (by simpa using hB)⟩
lemma bnd_bor' {σ : HSt m} {a b : Ex m} (ha : a.Bnd w B σ) (hb : b.Bnd w B σ)
    (ha1 : a.ev w σ ≤ 1) (hb1 : b.ev w σ ≤ 1) (hB : 2 ≤ B) : (Ex.bor a b).Bnd w B σ :=
  ⟨show 0 ≤ B by omega, ha, hb, by omega⟩
lemma bnd_bnot' {σ : HSt m} {a : Ex m} (ha : a.Bnd w B σ) (hB : 1 ≤ B) :
    (Ex.bnot a).Bnd w B σ := ⟨hB, ha⟩
lemma bnd_eq' {σ : HSt m} {a b : Ex m} (ha : a.Bnd w B σ) (hb : b.Bnd w B σ) (hB : 2 ≤ B) :
    (Ex.eq a b).Bnd w B σ := (bnd_eq σ a b hB).2 ⟨ha, hb⟩
lemma bnd_inL' {σ : HSt m} {a : Ex m} {L : List ℕ} (ha : a.Bnd w B σ) (hB : 2 ≤ B)
    (hL : ∀ c ∈ L, c ≤ B) : (Ex.inL a L).Bnd w B σ := bnd_inL σ a hB L hL ha
lemma bnd_add' {σ : HSt m} {a b : Ex m} (ha : a.Bnd w B σ) (hb : b.Bnd w B σ)
    (h : a.ev w σ + b.ev w σ ≤ B) : (a + b).Bnd w B σ := ⟨ha, hb, h⟩
lemma bnd_sub' {σ : HSt m} {a b : Ex m} (ha : a.Bnd w B σ) (hb : b.Bnd w B σ) :
    (a - b).Bnd w B σ := ⟨ha, hb⟩
lemma bnd_mul' {σ : HSt m} {a b : Ex m} (ha : a.Bnd w B σ) (hb : b.Bnd w B σ)
    (h : a.ev w σ * b.ev w σ ≤ B) : (a * b).Bnd w B σ := ⟨ha, hb, h⟩
lemma bnd_lt' {σ : HSt m} {a b : Ex m} (ha : a.Bnd w B σ) (hb : b.Bnd w B σ) :
    (Ex.lt a b).Bnd w B σ := ⟨ha, hb⟩
lemma bnd_tok' {σ : HSt m} {a : Ex m} (ha : a.Bnd w B σ) : (Ex.tok a).Bnd w B σ := ha
lemma bnd_mem' {σ : HSt m} {a : Ex m} (ha : a.Bnd w B σ) : (Ex.mem a).Bnd w B σ := ha
lemma bnd_var' {σ : HSt m} {i : Fin m} (h : σ.v i ≤ B) : (Ex.var i).Bnd w B σ := h
lemma bnd_const' {σ : HSt m} {k : ℕ} (h : k ≤ B) : (Ex.const k : Ex m).Bnd w B σ := h

lemma bv_le' (b : Bool) : bv b ≤ 1 := bv_le b

/-- Reduce boundedness of an expression to arithmetic side conditions. -/
macro "bnd_tac" : tactic => `(tactic| (repeat' (first
  | with_reducible apply bnd_band' | with_reducible apply bnd_bor'
  | with_reducible apply bnd_bnot' | with_reducible apply bnd_eq'
  | with_reducible apply bnd_inL' | with_reducible apply bnd_add'
  | with_reducible apply bnd_sub' | with_reducible apply bnd_mul'
  | with_reducible apply bnd_lt' | with_reducible apply bnd_tok'
  | with_reducible apply bnd_mem')))

end HL

end PathChecking
