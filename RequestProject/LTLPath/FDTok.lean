module

public import RequestProject.LTLPath.FDPack
public import RequestProject.LTLPath.ScanF
public import RequestProject.LTLPath.TokFT

/-!
# Token-level terms

Terms over inputs `pack (encodeToks ts) q a`: token codes (`tcT`), the number of tokens (`nT`),
counting tokens with a code predicate (`cntPT`), bounded search (`ffindT`) and bracket scans
(`scanFT`, `fendT`, `tend1T`, `numEndT`).
-/

@[expose] public section

namespace PathChecking

namespace FD

open FE LL CTLP LTok

variable {x : Word} {Γ : Ctx} {ts : List Tok} {q : ℕ} {a : List Bool}

/-- `P` maps terms denoting `v` to terms denoting the truth value of `Pb v`, in every context
extending `Γ`. -/
def DenP (x : Word) (Γ : Ctx) (P : T → T) (Pb : ℕ → Bool) : Prop :=
  ∀ Γ', Γ ⊆ Γ' → ∀ t v, Den x Γ' t v → Den x Γ' (P t) (Pb v).toNat

lemma DenP.mono {P : T → T} {Pb : ℕ → Bool} (h : DenP x Γ P Pb) {Γ' : Ctx} (hΓ : Γ ⊆ Γ') :
    DenP x Γ' P Pb := fun Γ'' h' t v ht => h Γ'' (hΓ.trans h') t v ht

lemma toNat_eq_bv {b : Bool} {P : Prop} (h : b = true ↔ P) : b.toNat = bv P := by
  rw [bv_bool]; exact bv_congr h

/-- Token code. -/
def tcT (p : T) : T := wcodeT p

lemma den_tc (hx : x = pack (encodeToks ts) q a) {p : T} {P : ℕ} (hp : Den x Γ p P) :
    Den x Γ (tcT p) (tc ts P) := (den_wcode hx hp).of_eq (wcode_encodeToks ts P)

/-- Number of tokens. -/
def nT : T := divT nwT (cT 5)

lemma den_n (hx : x = pack (encodeToks ts) q a) : Den x Γ nT ts.length :=
  (den_div (den_nw hx) (den_c 5)).of_eq (by rw [SQ.encodeToks_length]; omega)

/-- Maximum. -/
def maxT (a b : T) : T := iteT (ltT a b) b a

lemma den_max {a b : T} {u v : ℕ} (ha : Den x Γ a u) (hb : Den x Γ b v) :
    Den x Γ (maxT a b) (max u v) := by
  refine den_ite_eq (den_lt' ha hb) (fun h => hb.of_eq ?_) (fun h => ha.of_eq ?_)
  · simp at h; omega
  · simp at h; omega

/-- Counting the positions of `[a, b)` whose code satisfies `P`. -/
def cntPT (P : T → T) (a b : T) : T := countT (subT b a) fun m => P (tcT (addT a m))

lemma den_cntP (hx : x = pack (encodeToks ts) q a) {P : T → T} {Pb : ℕ → Bool}
    (hP : DenP x Γ P Pb) {a b : T} {A B : ℕ} (ha : Den x Γ a A) (hb : Den x Γ b B) :
    Den x Γ (cntPT P a b) (cntP ts Pb A B) := by
  refine (den_count (body := fun m => P (tcT (addT a m)))
    (f := fun i => (Pb (tc ts (A + i))).toNat) (den_sub hb ha) fun k i _ =>
    hP _ (List.subset_cons_self _ _) _ _ (den_tc hx (den_add (ha.cons _) den_var0))).of_eq ?_
  unfold cntU cntP
  exact List.countP_congr fun i _ => by cases h : Pb (tc ts (A + i)) <;> simp [h]

/-- Least `j ∈ [a, n)` satisfying `P`, or `n`. -/
def ffindT (P : T → T) (a n : T) : T := addT a (findT (subT n a) fun m => P (addT a m))

lemma den_ffind {P : T → T} {Pb : ℕ → Bool} (hP : DenP x Γ P Pb) {a n : T} {A N : ℕ}
    (ha : Den x Γ a A) (hn : Den x Γ n N) : Den x Γ (ffindT P a n) (ffind Pb A N) := by
  refine (den_add ha (den_find (body := fun m => P (addT a m)) (f := fun i => (Pb (A + i)).toNat)
    (den_sub hn ha) fun k i _ =>
    hP _ (List.subset_cons_self _ _) _ _ (den_add (ha.cons _) den_var0))).of_eq ?_
  unfold ffind
  congr 1
  exact findF_congr fun i _ => by cases Pb (A + i) <;> rfl

/-- Scans with counter `c ≥ 1`, by bounded search. -/
def scanFT (up down : T → T) (p c : T) : T :=
  lettT (ffindT (fun r => leT (addT c (cntPT up p (addT r (cT 1)))) (cntPT down p (addT r (cT 1))))
    p nT) fun f => iteT (ltT f nT) (addT f (cT 1)) (maxT p nT)

lemma den_scanF (hx : x = pack (encodeToks ts) q a) {up down : T → T} {upb downb : ℕ → Bool}
    (hu : DenP x Γ up upb) (hd : DenP x Γ down downb) {p c : T} {P C : ℕ}
    (hp : Den x Γ p P) (hc : Den x Γ c C) :
    Den x Γ (scanFT up down p c) (scanF ts upb downb P C) := by
  have hf := den_ffind (Pb := fun r => decide (C + cntP ts upb P (r + 1) ≤ cntP ts downb P (r + 1)))
    (P := fun r => leT (addT c (cntPT up p (addT r (cT 1)))) (cntPT down p (addT r (cT 1))))
    (fun Γ' hΓ t v ht => (den_le (den_add (hc.mono hΓ) (den_cntP hx (hu.mono hΓ) (hp.mono hΓ)
      (den_add ht (den_c 1)))) (den_cntP hx (hd.mono hΓ) (hp.mono hΓ) (den_add ht (den_c 1)))).of_eq
      (by rw [bv_decide])) hp (den_n hx)
  refine den_lett hf fun k => ?_
  have hv := den_var0 (x := x) (k := k) (v := ffind (fun r => decide (C + cntP ts upb P (r + 1) ≤
    cntP ts downb P (r + 1))) P ts.length) (Γ := Γ)
  unfold scanF
  refine den_ite_eq (den_lt' hv (den_n hx)) (fun h => ?_) (fun h => ?_)
  · simp only [ne_eq, bv_eq_zero, not_not] at h
    rw [if_pos h]; exact den_add hv (den_c 1)
  · simp only [bv_eq_zero] at h
    rw [if_neg h]; exact den_max (hp.cons _) (den_n hx)

/-- Scans with counter `c ≥ 1`. -/
lemma den_scan (hx : x = pack (encodeToks ts) q a) {up down : T → T} {upb downb : ℕ → Bool}
    (hdis : ∀ k, ¬ (upb k = true ∧ downb k = true))
    (hu : DenP x Γ up upb) (hd : DenP x Γ down downb) {p c : T} {P C : ℕ}
    (hp : Den x Γ p P) (hc : Den x Γ c C) (hC : 1 ≤ C) :
    Den x Γ (scanFT up down p c) (scan ts upb downb P C) :=
  (den_scanF hx hu hd hp hc).of_eq (scan_eq_scanF hdis _ P C rfl hC).symm

/-! ## Code predicates -/

/-- Code equal to `k`. -/
def isT (k : ℕ) (t : T) : T := eqT t (cT k)

lemma denP_is (k : ℕ) : DenP x Γ (isT k) (fun v => v == k) := fun _ _ t v ht =>
  (den_eq' ht (den_c k)).of_eq (toNat_eq_bv (by simp)).symm

def upFT (t : T) : T := orT (isT 8 t) (isT 10 t)
def downFT (t : T) : T := orT (isT 2 t) (isT 6 t)
def upTT (t : T) : T := isT 3 t
def downTT (t : T) : T := isT 4 t
def upNT (_ : T) : T := cT 0
def downNT (t : T) : T := isT 2 t

lemma denP_or {P Q : T → T} {Pb Qb : ℕ → Bool} (hP : DenP x Γ P Pb) (hQ : DenP x Γ Q Qb) :
    DenP x Γ (fun t => orT (P t) (Q t)) (fun v => Pb v || Qb v) := fun Γ' hΓ t v ht => by
  have := den_or (hP Γ' hΓ t v ht |>.of_eq (bv_bool _)) (hQ Γ' hΓ t v ht |>.of_eq (bv_bool _))
  exact this.of_eq (toNat_eq_bv (by simp)).symm

lemma denP_upF : DenP x Γ upFT upF := by
  have := denP_or (x := x) (Γ := Γ) (denP_is 8) (denP_is 10)
  exact fun Γ' hΓ t v ht => (this Γ' hΓ t v ht).of_eq (by simp [upF])
lemma denP_downF : DenP x Γ downFT downF := by
  have := denP_or (x := x) (Γ := Γ) (denP_is 2) (denP_is 6)
  exact fun Γ' hΓ t v ht => (this Γ' hΓ t v ht).of_eq (by simp [downF])
lemma denP_upT : DenP x Γ upTT upT := fun Γ' hΓ t v ht =>
  (denP_is 3 Γ' hΓ t v ht).of_eq (by simp [upT])
lemma denP_downT : DenP x Γ downTT downT := fun Γ' hΓ t v ht =>
  (denP_is 4 Γ' hΓ t v ht).of_eq (by simp [downT])
lemma denP_upN : DenP x Γ upNT upN := fun _ _ _ _ _ => (den_c 0).of_eq (by simp [upN])
lemma denP_downN : DenP x Γ downNT downN := fun Γ' hΓ t v ht =>
  (denP_is 2 Γ' hΓ t v ht).of_eq (by simp [downN])

/-! ## Ends of formulas, groups and numbers -/

/-- End of the formula starting at `p`. -/
def fendT (p : T) : T := scanFT upFT downFT p (cT 1)
/-- End of the bracketed group opened at `j`. -/
def tend1T (j : T) : T := scanFT upTT downTT (addT j (cT 1)) (cT 1)
/-- End of the number starting at `v`. -/
def numEndT (v : T) : T := scanFT upNT downNT v (cT 1)

lemma den_fend (hx : x = pack (encodeToks ts) q a) {p : T} {P : ℕ} (hp : Den x Γ p P) :
    Den x Γ (fendT p) (fend ts P) :=
  den_scan hx (fun k => by simp [upF, downF]; omega) denP_upF denP_downF hp (den_c 1) le_rfl

lemma den_tend1 (hx : x = pack (encodeToks ts) q a) {j : T} {J : ℕ} (hj : Den x Γ j J) :
    Den x Γ (tend1T j) (tend1 ts J) :=
  den_scan hx (fun k => by simp [upT, downT]; omega) denP_upT denP_downT (den_add hj (den_c 1))
    (den_c 1) le_rfl

lemma den_numEnd (hx : x = pack (encodeToks ts) q a) {v : T} {V : ℕ} (hv : Den x Γ v V) :
    Den x Γ (numEndT v) (numEnd ts V) :=
  den_scan hx (fun k => by simp [upN]) denP_upN denP_downN hv (den_c 1) le_rfl

end FD

end PathChecking
