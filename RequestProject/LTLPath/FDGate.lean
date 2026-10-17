module

public import RequestProject.LTLPath.FDTree
public import RequestProject.LTLPath.TokSem

/-!
# Terms for the gates of the global circuit

The gate `(p, i, t)` of a formula tree is described by a *case number* (`gcase`) from which its
kind and arguments are read off (`gOfCase`).  Terms compute, for the formula tree of an encoded
instance, the case number, the kind code and the arguments of gate `h`.
-/

@[expose] public section

namespace PathChecking

namespace FT

variable (T : FT)

/-- Case number of the gate `(p, i, t)`. -/
def gcase (p i t : ℕ) : ℕ :=
  if T.nd p = true ∧ i < T.W p then
    if T.kd p ≤ 1 then (if t = 1 then 1 else 0)
    else if T.kd p = 2 then (if t = 1 then 2 else 0)
    else if T.kd p = 4 then (if t = 1 then 3 else 0)
    else if T.kd p = 3 then (if t = 1 then 4 else 0)
    else if t = 1 then (if i + 1 < T.W p then 5 else 6)
    else (if i + 1 < T.W p then 7 else 0)
  else 0

/-- The gate of a case. -/
def gOfCase (c p i : ℕ) : Gate :=
  if c = 1 then ⟨.const (T.lv p i != T.pol p), []⟩
  else if c = 2 then ⟨.and, [T.idx (p + 1) i 1]⟩
  else if c = 3 then ⟨.and, [T.idx (p + 1) (i + 1) 1]⟩
  else if c = 4 then ⟨andOr (T.pol p), [T.idx (p + 1) i 1, T.idx (T.c2 p) i 1]⟩
  else if c = 5 then ⟨andOr (!T.pol p), [T.idx (T.c2 p) i 1, T.idx p i 0]⟩
  else if c = 6 then ⟨.and, [T.idx (T.c2 p) i 1]⟩
  else if c = 7 then ⟨andOr (T.pol p), [T.idx (p + 1) i 1, T.idx p (i + 1) 1]⟩
  else cF

lemma gateAt_eq (p i t : ℕ) : T.gateAt p i t = T.gOfCase (T.gcase p i t) p i := by
  unfold gateAt gcase
  by_cases h1 : T.nd p = true ∧ i < T.W p
  · rw [if_pos h1, if_pos h1]
    by_cases ht : t = 1
    · simp only [ht, if_true]
      split_ifs <;> simp [gOfCase]
    · simp only [ht, if_false]
      split_ifs <;> simp [gOfCase, cF]
  · rw [if_neg h1, if_neg h1]; simp [gOfCase]

/-- Case number of gate `h`. -/
def hcase (h : ℕ) : ℕ := if h < T.Ng then T.gcase (T.pos h) (T.ix h) (ty h) else 0

lemma gate_eq (h : ℕ) : T.gate h = T.gOfCase (T.hcase h) (T.pos h) (T.ix h) := by
  unfold gate hcase
  split_ifs
  · exact T.gateAt_eq _ _ _
  · simp [gOfCase]

end FT

/-- Code of a gate kind (the tag of `Gate.toks`). -/
def kcode : GateKind → ℕ
  | .input _ => 0
  | .const false => 1
  | .const true => 2
  | .not => 3
  | .and => 4
  | .or => 5
  | .oracle => 6

/-- Kind code of a case. -/
def kcOf (c : ℕ) (lv pol : Bool) : ℕ :=
  if c = 1 then (if (lv != pol) = true then 2 else 1)
  else if c = 2 ∨ c = 3 ∨ c = 6 then 4
  else if c = 4 ∨ c = 7 then (if pol = true then 5 else 4)
  else if c = 5 then (if pol = true then 4 else 5)
  else 1

/-- Number of arguments of a case. -/
def naOf (c : ℕ) : ℕ := if c = 2 ∨ c = 3 ∨ c = 6 then 1 else if c = 4 ∨ c = 5 ∨ c = 7 then 2 else 0

namespace FT

variable (T : FT)

/-- First argument of a case. -/
def a0Of (c p i : ℕ) : ℕ :=
  if c = 3 then T.idx (p + 1) (i + 1) 1 else if c = 5 ∨ c = 6 then T.idx (T.c2 p) i 1
  else T.idx (p + 1) i 1

/-- Second argument of a case. -/
def a1Of (c p i : ℕ) : ℕ :=
  if c = 5 then T.idx p i 0 else if c = 7 then T.idx p (i + 1) 1 else T.idx (T.c2 p) i 1

lemma kcode_gOfCase (c p i : ℕ) :
    kcode (T.gOfCase c p i).kind = kcOf c (T.lv p i) (T.pol p) := by
  unfold gOfCase kcOf
  cases hl : T.lv p i <;> cases hp : T.pol p <;> split_ifs <;> simp_all [kcode, andOr, cF]

lemma args_gOfCase (c p i : ℕ) :
    (T.gOfCase c p i).args = [T.a0Of c p i, T.a1Of c p i].take (naOf c) := by
  unfold gOfCase naOf a0Of a1Of
  split_ifs <;> simp_all [cF]

/-- Gates of the global circuit are constants, `AND` or `OR`. -/
lemma gOfCase_kind (c p i : ℕ) : (∃ b, (T.gOfCase c p i).kind = .const b) ∨
    (T.gOfCase c p i).kind = .and ∨ (T.gOfCase c p i).kind = .or := by
  unfold gOfCase
  split_ifs <;> (try simp only [cF, andOr]) <;> (try split_ifs) <;> simp

lemma AO_gOfCase_iff (c p i : ℕ) : AO (T.gOfCase c p i) ↔ 2 ≤ c ∧ c ≤ 7 := by
  unfold AO gOfCase
  split_ifs <;> (try simp only [cF, andOr]) <;> (try split_ifs) <;> (try simp) <;> omega

end FT

namespace FD

open FE LL CTLP LTok

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool} {g : Gl}

/-! ## Terms -/

/-- Window `W p`. -/
def WT (g : Gl) (p : T) : T := addT g.s (mulT (addT p (cT 2)) g.l)
/-- Gate index of `(p, i, t)`. -/
def idxT (g : Gl) (p i t : T) : T :=
  addT (mulT (cT 2) (addT (mulT (subT (subT g.N (cT 1)) p) g.Wm) (subT (subT g.Wm (cT 1)) i))) t
/-- Number of gates. -/
def NgT (g : Gl) : T := mulT (mulT (cT 2) g.N) g.Wm
/-- Position of gate `h`. -/
def posT (g : Gl) (h : T) : T := subT (subT g.N (cT 1)) (divT (divT h (cT 2)) g.Wm)
/-- Time index of gate `h`. -/
def ixT (g : Gl) (h : T) : T := subT (subT g.Wm (cT 1)) (modT (divT h (cT 2)) g.Wm)
/-- Type of gate `h`. -/
def tyT (h : T) : T := modT h (cT 2)
/-- Second child. -/
def c2T (p : T) : T := fendT (addT p (cT 1))

/-- Case number of `(p, i, t)`. -/
def gcaseT (g : Gl) (p i t : T) : T :=
  lettT (WT g p) fun w => lettT (tkdT p) fun k => lettT (isT 1 t) fun t1 =>
  iteT (andT (tndT g p) (ltT i w))
    (iteT (leT k (cT 1)) (iteT t1 (cT 1) (cT 0))
    (iteT (isT 2 k) (iteT t1 (cT 2) (cT 0))
    (iteT (isT 4 k) (iteT t1 (cT 3) (cT 0))
    (iteT (isT 3 k) (iteT t1 (cT 4) (cT 0))
    (iteT t1 (iteT (ltT (addT i (cT 1)) w) (cT 5) (cT 6))
      (iteT (ltT (addT i (cT 1)) w) (cT 7) (cT 0)))))))
    (cT 0)

/-- Case number of gate `h`. -/
def hcaseT (g : Gl) (h : T) : T :=
  iteT (ltT h (NgT g)) (gcaseT g (posT g h) (ixT g h) (tyT h)) (cT 0)

/-- Kind code of a case. -/
def kcOfT (c lv pol : T) : T :=
  iteT (isT 1 c) (iteT (neT lv pol) (cT 2) (cT 1))
  (iteT (orT (isT 2 c) (orT (isT 3 c) (isT 6 c))) (cT 4)
  (iteT (orT (isT 4 c) (isT 7 c)) (iteT pol (cT 5) (cT 4))
  (iteT (isT 5 c) (iteT pol (cT 4) (cT 5)) (cT 1))))

/-- Number of arguments of a case. -/
def naOfT (c : T) : T :=
  iteT (orT (isT 2 c) (orT (isT 3 c) (isT 6 c))) (cT 1)
    (iteT (orT (isT 4 c) (orT (isT 5 c) (isT 7 c))) (cT 2) (cT 0))

/-- First argument of a case. -/
def a0OfT (g : Gl) (c p i : T) : T :=
  iteT (isT 3 c) (idxT g (addT p (cT 1)) (addT i (cT 1)) (cT 1))
    (iteT (orT (isT 5 c) (isT 6 c)) (idxT g (c2T p) i (cT 1)) (idxT g (addT p (cT 1)) i (cT 1)))

/-- Second argument of a case. -/
def a1OfT (g : Gl) (c p i : T) : T :=
  iteT (isT 5 c) (idxT g p i (cT 0))
    (iteT (isT 7 c) (idxT g p (addT i (cT 1)) (cT 1)) (idxT g (c2T p) i (cT 1)))

/-! ## Denotations -/

section

variable {φ : LTL} {p : LassoPath} (hE : Enc ts φ p)
  (hx : x = pack (encodeToks ts) q a) (hg : Gl.Ok x Γ ts g)
include hE hx hg

omit hx in
lemma den_W {p' : T} {P : ℕ} (hp : Den x Γ p' P) : Den x Γ (WT g p') ((tokFT hE).W P) :=
  den_add hg.s (den_mul (den_add hp (den_c 2)) hg.l)

omit hx in
lemma den_idx {p' i t : T} {P I U : ℕ} (hp : Den x Γ p' P) (hi : Den x Γ i I) (ht : Den x Γ t U) :
    Den x Γ (idxT g p' i t) ((tokFT hE).idx P I U) :=
  den_add (den_mul (den_c 2) (den_add (den_mul (den_sub (den_sub hg.N (den_c 1)) hp) hg.Wm)
    (den_sub (den_sub hg.Wm (den_c 1)) hi))) ht

omit hx in
lemma den_Ng : Den x Γ (NgT g) (tokFT hE).Ng :=
  den_mul (den_mul (den_c 2) hg.N) hg.Wm

omit hx in
lemma den_pos {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (posT g h) ((tokFT hE).pos H) :=
  den_sub (den_sub hg.N (den_c 1)) (den_div (den_div hh (den_c 2)) hg.Wm)

omit hx in
lemma den_ix {h : T} {H : ℕ} (hh : Den x Γ h H) : Den x Γ (ixT g h) ((tokFT hE).ix H) :=
  den_sub (den_sub hg.Wm (den_c 1)) (den_mod (den_div hh (den_c 2)) hg.Wm)

omit hE hg in
lemma den_c2' {p' : T} {P : ℕ} (hp : Den x Γ p' P) : Den x Γ (c2T p') (fend ts (P + 1)) :=
  den_fend hx (den_add hp (den_c 1))

lemma den_gcase {p' i t : T} {P I U : ℕ} (hp : Den x Γ p' P) (hi : Den x Γ i I)
    (ht : Den x Γ t U) : Den x Γ (gcaseT g p' i t) ((tokFT hE).gcase P I U) := by
  refine den_lett (den_W hE hg hp) fun kw => den_lett ((den_tkd hx hp).cons _) fun kk =>
    den_lett (((denP_is 1 _ (List.Subset.refl _) _ _ ht).cons _).cons _) fun kt => ?_
  set Γ' := (kt, (U == 1).toNat) :: (kk, tkd ts P) :: (kw, (tokFT hE).W P) :: Γ
  have hsub : Γ ⊆ Γ' := fun y hy => by simp [Γ', hy]
  have hw : Den x Γ' (varT kw) ((tokFT hE).W P) := den_var (by simp [Γ'])
  have hk : Den x Γ' (varT kk) (tkd ts P) := den_var (by simp [Γ'])
  have h1 : Den x Γ' (varT kt) (U == 1).toNat := den_var0
  have hp' := hp.mono hsub
  have hi' := hi.mono hsub
  have hkd : (tokFT hE).kd P = tkd ts P := rfl
  have hnd : (tokFT hE).nd P = tnd ts P := rfl
  unfold FT.gcase
  rw [hkd, hnd]
  refine den_ite_eq (den_and ((den_tnd hx (hg.mono hsub) hp').of_eq (bv_bool _)) (den_lt' hi' hw))
    (fun hc => ?_) (fun hc => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at hc
    rw [if_pos hc]
    have e1 : ∀ v₁ v₀ : ℕ, Den x Γ' (iteT (varT kt) (cT v₁) (cT v₀)) (if U = 1 then v₁ else v₀) :=
      fun v₁ v₀ => den_ite_eq h1 (fun h => (den_c v₁).of_eq (by simp at h; simp [h]))
        (fun h => (den_c v₀).of_eq (by simp at h; simp [h]))
    refine den_ite_eq (den_le hk (den_c 1)) (fun h => ?_) (fun h => ?_)
    · simp at h; rw [if_pos h]; exact e1 1 0
    · simp at h; rw [if_neg (by omega)]
      refine den_ite_eq (den_eq' hk (den_c 2)) (fun h2 => ?_) (fun h2 => ?_)
      · simp at h2; rw [if_pos h2]; exact e1 2 0
      · simp at h2; rw [if_neg h2]
        refine den_ite_eq (den_eq' hk (den_c 4)) (fun h4 => ?_) (fun h4 => ?_)
        · simp at h4; rw [if_pos h4]; exact e1 3 0
        · simp at h4; rw [if_neg h4]
          refine den_ite_eq (den_eq' hk (den_c 3)) (fun h3 => ?_) (fun h3 => ?_)
          · simp at h3; rw [if_pos h3]; exact e1 4 0
          · simp at h3; rw [if_neg h3]
            have e2 : ∀ v₁ v₀ : ℕ, Den x Γ' (iteT (ltT (addT i (cT 1)) (varT kw)) (cT v₁) (cT v₀))
                (if I + 1 < (tokFT hE).W P then v₁ else v₀) :=
              fun v₁ v₀ => den_ite_eq (den_lt' (den_add hi' (den_c 1)) hw)
                (fun h => (den_c v₁).of_eq (by simp at h; simp [h]))
                (fun h => (den_c v₀).of_eq (by simp at h; simp [h]))
            refine den_ite_eq h1 (fun ht1 => ?_) (fun ht1 => ?_)
            · simp at ht1; rw [if_pos ht1]; exact e2 5 6
            · simp at ht1; rw [if_neg ht1]; exact e2 7 0
  · simp only [bv_eq_zero] at hc
    rw [if_neg hc]; exact den_c 0

lemma den_hcase {h : T} {H : ℕ} (hh : Den x Γ h H) :
    Den x Γ (hcaseT g h) ((tokFT hE).hcase H) := by
  unfold FT.hcase
  refine den_ite_eq (den_lt' hh (den_Ng hE hg)) (fun h1 => ?_) (fun h1 => ?_)
  · simp at h1; rw [if_pos h1]
    exact den_gcase hE hx hg (den_pos hE hg hh) (den_ix hE hg hh) (den_mod hh (den_c 2))
  · simp at h1; rw [if_neg (by omega)]; exact den_c 0

omit hE hx hg in
lemma den_kcOf {c lv pol : T} {C : ℕ} {L B : Bool} (hc : Den x Γ c C) (hl : Den x Γ lv L.toNat)
    (hp : Den x Γ pol B.toNat) : Den x Γ (kcOfT c lv pol) (kcOf C L B) := by
  unfold kcOf kcOfT
  have hI := fun k => (denP_is k _ (List.Subset.refl Γ) _ _ hc)
  refine den_ite_eq (hI 1) (fun h => ?_) (fun h => ?_)
  · simp at h; rw [if_pos h]
    refine den_ite_eq (den_ne hl hp) (fun h' => (den_c 2).of_eq ?_) (fun h' => (den_c 1).of_eq ?_)
    · simp at h'; cases L <;> cases B <;> simp_all
    · simp at h'; cases L <;> cases B <;> simp_all
  · simp at h; rw [if_neg h]
    refine den_ite_eq (den_orB (hI 2) (den_orB (hI 3) (hI 6))) (fun h' => (den_c 4).of_eq ?_)
      (fun h' => ?_)
    · simp at h'; rw [if_pos (by omega)]
    · simp at h'; rw [if_neg (by omega)]
      refine den_ite_eq (den_orB (hI 4) (hI 7)) (fun h'' => ?_) (fun h'' => ?_)
      · simp at h''; rw [if_pos (by omega)]
        refine den_ite_eq hp (fun h3 => (den_c 5).of_eq ?_) (fun h3 => (den_c 4).of_eq ?_) <;>
          cases B <;> simp_all
      · simp at h''; rw [if_neg (by omega)]
        refine den_ite_eq (hI 5) (fun h5 => ?_) (fun h5 => (den_c 1).of_eq ?_)
        · simp at h5; rw [if_pos h5]
          refine den_ite_eq hp (fun h3 => (den_c 4).of_eq ?_) (fun h3 => (den_c 5).of_eq ?_) <;>
            cases B <;> simp_all
        · simp at h5; rw [if_neg h5]

omit hE hx hg in
lemma den_naOf {c : T} {C : ℕ} (hc : Den x Γ c C) : Den x Γ (naOfT c) (naOf C) := by
  unfold naOf naOfT
  have hI := fun k => (denP_is k _ (List.Subset.refl Γ) _ _ hc)
  refine den_ite_eq (den_orB (hI 2) (den_orB (hI 3) (hI 6))) (fun h => (den_c 1).of_eq ?_)
    (fun h => ?_)
  · simp at h; rw [if_pos (by omega)]
  · simp at h; rw [if_neg (by omega)]
    refine den_ite_eq (den_orB (hI 4) (den_orB (hI 5) (hI 7))) (fun h' => (den_c 2).of_eq ?_)
      (fun h' => (den_c 0).of_eq ?_)
    · simp at h'; rw [if_pos (by omega)]
    · simp at h'; rw [if_neg (by omega)]

lemma den_a0Of {c p' i : T} {C P I : ℕ} (hc : Den x Γ c C) (hp : Den x Γ p' P)
    (hi : Den x Γ i I) : Den x Γ (a0OfT g c p' i) ((tokFT hE).a0Of C P I) := by
  unfold FT.a0Of a0OfT
  have hI := fun k => (denP_is k _ (List.Subset.refl Γ) _ _ hc)
  refine den_ite_eq (hI 3) (fun h => ?_) (fun h => ?_)
  · simp at h; rw [if_pos h]
    exact den_idx hE hg (den_add hp (den_c 1)) (den_add hi (den_c 1)) (den_c 1)
  · simp at h; rw [if_neg h]
    refine den_ite_eq (den_orB (hI 5) (hI 6)) (fun h' => ?_) (fun h' => ?_)
    · simp at h'; rw [if_pos (show C = 5 ∨ C = 6 by omega)]
      exact den_idx hE hg (den_c2' hx hp) hi (den_c 1)
    · simp at h'; rw [if_neg (show ¬(C = 5 ∨ C = 6) by omega)]
      exact den_idx hE hg (den_add hp (den_c 1)) hi (den_c 1)

lemma den_a1Of {c p' i : T} {C P I : ℕ} (hc : Den x Γ c C) (hp : Den x Γ p' P)
    (hi : Den x Γ i I) : Den x Γ (a1OfT g c p' i) ((tokFT hE).a1Of C P I) := by
  unfold FT.a1Of a1OfT
  have hI := fun k => (denP_is k _ (List.Subset.refl Γ) _ _ hc)
  refine den_ite_eq (hI 5) (fun h => ?_) (fun h => ?_)
  · simp at h; rw [if_pos h]
    exact den_idx hE hg hp hi (den_c 0)
  · simp at h; rw [if_neg h]
    refine den_ite_eq (hI 7) (fun h' => ?_) (fun h' => ?_)
    · simp at h'; rw [if_pos h']
      exact den_idx hE hg hp (den_add hi (den_c 1)) (den_c 1)
    · simp at h'; rw [if_neg h']
      exact den_idx hE hg (den_c2' hx hp) hi (den_c 1)

end

end FD

end PathChecking
